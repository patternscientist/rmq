import RMQ.Core.WordRAM

/-!
# First-order register/control layer for Word-RAM queries

This module extends the small `WordRAM.Program` leaf interpreter with just
enough first-order control to express dynamic addresses: registers, arithmetic
expressions, option tests, and payload reads whose indices are computed from
registers.  It deliberately avoids higher-order continuations and domain
primitives such as whole-bitvector rank/select, BP close, LCA, or RMQ.
-/

namespace RMQ

namespace WordRAM

namespace Register

/-- A natural value fits in `bits` machine bits. -/
def FitsInBits (bits value : Nat) : Prop :=
  value < 2 ^ bits

/-- A payload address fits in `bits` machine bits. -/
def AddressFitsInBits (bits segment index : Nat) : Prop :=
  FitsInBits bits segment /\ FitsInBits bits index

theorem zero_fitsInBits (bits : Nat) :
    FitsInBits bits 0 := by
  unfold FitsInBits
  exact Nat.pow_pos (by decide : 0 < 2)

/-- Small register file used by the first dynamic-address layer. -/
structure RegFile where
  natRegs : Array Nat := #[]
  boolRegs : Array Bool := #[]
  optNatRegs : Array (Option Nat) := #[]

namespace RegFile

/-- Missing natural registers default to zero. -/
def nat (regs : RegFile) (idx : Nat) : Nat :=
  regs.natRegs[idx]?.getD 0

/-- Missing Boolean registers default to false. -/
def bool (regs : RegFile) (idx : Nat) : Bool :=
  regs.boolRegs[idx]?.getD false

/-- Missing optional-natural registers default to `none`. -/
def optNat (regs : RegFile) (idx : Nat) : Option Nat :=
  regs.optNatRegs[idx]?.getD none

/-- All natural register reads fit in the declared machine-bit bound. -/
def NatValuesFitInBits (regs : RegFile) (bits : Nat) : Prop :=
  forall idx, FitsInBits bits (regs.nat idx)

/-- All present optional-natural register reads fit in the declared bound. -/
def OptNatValuesFitInBits (regs : RegFile) (bits : Nat) : Prop :=
  forall {idx value : Nat}, regs.optNat idx = some value ->
    FitsInBits bits value

/-- Combined bounded-register policy for the current register file. -/
def ValuesFitInBits (regs : RegFile) (bits : Nat) : Prop :=
  regs.NatValuesFitInBits bits /\ regs.OptNatValuesFitInBits bits

/-- Initial register file with two optional natural inputs. -/
def withOptNat2 (left right : Option Nat) : RegFile where
  natRegs := #[]
  boolRegs := #[]
  optNatRegs := #[left, right]

/-- Initial register file with one natural input. -/
def withNat1 (pos : Nat) : RegFile where
  natRegs := #[pos]
  boolRegs := #[]
  optNatRegs := #[]

@[simp] theorem withNat1_nat_zero (pos : Nat) :
    (withNat1 pos).nat 0 = pos := by
  rfl

@[simp] theorem withOptNat2_optNat_zero (left right : Option Nat) :
    (withOptNat2 left right).optNat 0 = left := by
  cases left <;> rfl

@[simp] theorem withOptNat2_optNat_one (left right : Option Nat) :
    (withOptNat2 left right).optNat 1 = right := by
  cases left <;> cases right <;> rfl

theorem withNat1_valuesFitInBits
    {pos bits : Nat} (hpos : FitsInBits bits pos) :
    (withNat1 pos).ValuesFitInBits bits := by
  constructor
  · intro idx
    cases idx with
    | zero =>
        simpa using hpos
    | succ idx =>
        simp [nat, withNat1, zero_fitsInBits]
  · intro idx value hvalue
    cases hvalue

theorem withOptNat2_valuesFitInBits
    {left right : Option Nat} {bits : Nat}
    (hleft :
      forall value, left = some value -> FitsInBits bits value)
    (hright :
      forall value, right = some value -> FitsInBits bits value) :
    (withOptNat2 left right).ValuesFitInBits bits := by
  constructor
  · intro idx
    simp [nat, withOptNat2, zero_fitsInBits]
  · intro idx value hvalue
    cases idx with
    | zero =>
        exact hleft value (by simpa using hvalue)
    | succ idx =>
        cases idx with
        | zero =>
            exact hright value (by simpa using hvalue)
        | succ idx =>
            simp [optNat, withOptNat2] at hvalue

end RegFile

/-- First-order natural expressions over query constants and registers. -/
inductive NatExpr where
  | const (value : Nat)
  | reg (idx : Nat)
  | optNatD (idx fallback : Nat)
  | add (left right : NatExpr)
  | sub (left right : NatExpr)
  | mul (left right : NatExpr)
  | div (left right : NatExpr)
  | min (left right : NatExpr)
deriving Repr, DecidableEq

namespace NatExpr

/-- Evaluate a first-order natural expression against a register file. -/
def eval : NatExpr -> RegFile -> Nat
  | const value, _regs => value
  | reg idx, regs => regs.nat idx
  | optNatD idx fallback, regs => (regs.optNat idx).getD fallback
  | add left right, regs => left.eval regs + right.eval regs
  | sub left right, regs => left.eval regs - right.eval regs
  | mul left right, regs => left.eval regs * right.eval regs
  | div left right, regs => left.eval regs / right.eval regs
  | min left right, regs => Nat.min (left.eval regs) (right.eval regs)

@[simp] theorem eval_const (value : Nat) (regs : RegFile) :
    (const value).eval regs = value := by
  rfl

@[simp] theorem eval_reg (idx : Nat) (regs : RegFile) :
    (reg idx).eval regs = regs.nat idx := by
  rfl

@[simp] theorem eval_optNatD_zero (fallback : Nat)
    (left right : Option Nat) :
    (optNatD 0 fallback).eval (RegFile.withOptNat2 left right) =
      left.getD fallback := by
  cases left <;> rfl

@[simp] theorem eval_optNatD_one (fallback : Nat)
    (left right : Option Nat) :
    (optNatD 1 fallback).eval (RegFile.withOptNat2 left right) =
      right.getD fallback := by
  cases left <;> cases right <;> rfl

/--
No-overflow policy for natural expressions: evaluation is mathematical `Nat`
arithmetic, and consumers prove this side condition when the result must fit in
a machine word. There is no implicit wraparound.
-/
def NoOverflow (expr : NatExpr) (regs : RegFile) (bits : Nat) : Prop :=
  FitsInBits bits (expr.eval regs)

theorem eval_fitsInBits_of_noOverflow
    {expr : NatExpr} {regs : RegFile} {bits : Nat}
    (h : expr.NoOverflow regs bits) :
    FitsInBits bits (expr.eval regs) := h

theorem const_noOverflow
    {value bits : Nat} {regs : RegFile}
    (hvalue : FitsInBits bits value) :
    (const value).NoOverflow regs bits := by
  simpa [NoOverflow]

theorem reg_noOverflow_of_regFile
    {idx bits : Nat} {regs : RegFile}
    (hregs : regs.NatValuesFitInBits bits) :
    (reg idx).NoOverflow regs bits := by
  simpa [NoOverflow] using hregs idx

theorem optNatD_noOverflow
    {idx fallback bits : Nat} {regs : RegFile}
    (hregs : regs.OptNatValuesFitInBits bits)
    (hfallback : FitsInBits bits fallback) :
    (optNatD idx fallback).NoOverflow regs bits := by
  unfold NoOverflow
  cases hopt : regs.optNat idx with
  | none =>
      simpa [eval, hopt] using hfallback
  | some value =>
      simpa [eval, hopt] using hregs hopt

theorem add_noOverflow_of_eval
    {left right : NatExpr} {regs : RegFile} {bits : Nat}
    (h :
      FitsInBits bits (left.eval regs + right.eval regs)) :
    (add left right).NoOverflow regs bits := by
  simpa [NoOverflow, eval] using h

theorem mul_noOverflow_of_eval
    {left right : NatExpr} {regs : RegFile} {bits : Nat}
    (h :
      FitsInBits bits (left.eval regs * right.eval regs)) :
    (mul left right).NoOverflow regs bits := by
  simpa [NoOverflow, eval] using h

theorem sub_noOverflow_of_left
    {left right : NatExpr} {regs : RegFile} {bits : Nat}
    (hleft : left.NoOverflow regs bits) :
    (sub left right).NoOverflow regs bits := by
  unfold NoOverflow FitsInBits at *
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hleft

theorem div_noOverflow_of_left
    {left right : NatExpr} {regs : RegFile} {bits : Nat}
    (hleft : left.NoOverflow regs bits) :
    (div left right).NoOverflow regs bits := by
  unfold NoOverflow FitsInBits at *
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hleft

theorem min_noOverflow_left
    {left right : NatExpr} {regs : RegFile} {bits : Nat}
    (hleft : left.NoOverflow regs bits) :
    (min left right).NoOverflow regs bits := by
  unfold NoOverflow FitsInBits at *
  exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hleft

end NatExpr

/-- First-order optional-natural expressions over registers and constants. -/
inductive OptNatExpr where
  | const (value : Option Nat)
  | reg (idx : Nat)
deriving Repr, DecidableEq

namespace OptNatExpr

/-- Evaluate a first-order optional-natural expression. -/
def eval : OptNatExpr -> RegFile -> Option Nat
  | const value, _regs => value
  | reg idx, regs => regs.optNat idx

@[simp] theorem eval_const (value : Option Nat) (regs : RegFile) :
    (const value).eval regs = value := by
  rfl

end OptNatExpr

/--
Minimal first-order register program returning an optional natural number.

Branches inspect optional-natural registers.  `readJoinedOptionNat` performs
one payload word read at a register-computed index, decodes a fixed-width
optional natural, and joins the outer indexed-read option.
-/
inductive RegProgram where
  | pureOpt (value : OptNatExpr)
  | readJoinedOptionNat (segment width : Nat) (index : NatExpr)
  | ifSomeNat (reg : Nat) (thenProgram elseProgram : RegProgram)
deriving Repr

namespace RegProgram

/-- Syntactic upper bound on payload reads along any branch. -/
def readCount : RegProgram -> Nat
  | pureOpt _ => 0
  | readJoinedOptionNat _ _ _ => 1
  | ifSomeNat _ thenProgram elseProgram =>
      Nat.max thenProgram.readCount elseProgram.readCount

/-- Payload-read addresses selected by first-order control for these registers. -/
def readAddresses : RegProgram -> RegFile -> List (Nat × Nat)
  | pureOpt _, _regs => []
  | readJoinedOptionNat segment _ index, regs =>
      [(segment, index.eval regs)]
  | ifSomeNat reg thenProgram elseProgram, regs =>
      match regs.optNat reg with
      | some _ => thenProgram.readAddresses regs
      | none => elseProgram.readAddresses regs

/-- All selected payload-read addresses fit in the declared machine-bit bound. -/
def ReadAddressesFitInBits
    (program : RegProgram) (regs : RegFile) (bits : Nat) : Prop :=
  forall {segment index : Nat},
    (segment, index) ∈ program.readAddresses regs ->
      AddressFitsInBits bits segment index

/-- Deterministic evaluation of a register program. -/
def eval : RegProgram -> Store -> RegFile -> Result .optNat
  | pureOpt value, _store, regs =>
      { value := value.eval regs, trace := [] }
  | readJoinedOptionNat segment width index, store, regs =>
      let i := index.eval regs
      let word? := store.readWord? segment i
      { value := (word?.map (bitsToOptionNatLE width)).join
        trace := [TraceEvent.readWord segment i word?] }
  | ifSomeNat reg thenProgram elseProgram, store, regs =>
      match regs.optNat reg with
      | some _ => thenProgram.eval store regs
      | none => elseProgram.eval store regs

@[simp] theorem eval_pureOpt_value
    (value : OptNatExpr) (store : Store) (regs : RegFile) :
    (eval (pureOpt value) store regs).value = value.eval regs := by
  rfl

@[simp] theorem eval_pureOpt_trace
    (value : OptNatExpr) (store : Store) (regs : RegFile) :
    (eval (pureOpt value) store regs).trace = [] := by
  rfl

@[simp] theorem eval_readJoinedOptionNat_value
    (segment width : Nat) (index : NatExpr)
    (store : Store) (regs : RegFile) :
    (eval (readJoinedOptionNat segment width index) store regs).value =
      ((store.readWord? segment (index.eval regs)).map
        (bitsToOptionNatLE width)).join := by
  rfl

@[simp] theorem eval_readJoinedOptionNat_trace
    (segment width : Nat) (index : NatExpr)
    (store : Store) (regs : RegFile) :
    (eval (readJoinedOptionNat segment width index) store regs).trace =
      [TraceEvent.readWord segment (index.eval regs)
        (store.readWord? segment (index.eval regs))] := by
  rfl

/-- Cost is exactly the interpreted trace length. -/
theorem eval_toCosted_cost_eq_trace_length
    (program : RegProgram) (store : Store) (regs : RegFile) :
    (eval program store regs).toCosted.cost =
      (eval program store regs).trace.length := by
  rfl

/-- Every interpreted read event agrees with payload memory. -/
theorem eval_reads_subset_payload
    (program : RegProgram) (store : Store) (regs : RegFile) :
    forall event : TraceEvent,
      event ∈ (eval program store regs).trace ->
        event.matchesStore store := by
  induction program with
  | pureOpt value =>
      intro event hmem
      simp [eval] at hmem
  | readJoinedOptionNat segment width index =>
      intro event hmem
      simp [eval] at hmem
      subst event
      rfl
  | ifSomeNat reg thenProgram elseProgram thenIH elseIH =>
      intro event hmem
      cases hreg : regs.optNat reg with
      | none =>
          exact elseIH event (by simpa [eval, hreg] using hmem)
      | some value =>
          exact thenIH event (by simpa [eval, hreg] using hmem)

/--
Every read event in a register-program trace uses the address obtained by
evaluating a syntactic first-order address expression under the current
register file.
-/
theorem eval_readWord_address_mem
    (program : RegProgram) (store : Store) (regs : RegFile)
    {segment index : Nat} {word? : Option Word}
    (hmem :
      TraceEvent.readWord segment index word? ∈
        (eval program store regs).trace) :
    (segment, index) ∈ program.readAddresses regs := by
  induction program with
  | pureOpt value =>
      simp [eval] at hmem
  | readJoinedOptionNat segment' width indexExpr =>
      simp [eval] at hmem
      rcases hmem with ⟨hsegment, hindex, _hword⟩
      subst segment
      subst index
      simp [readAddresses]
  | ifSomeNat reg thenProgram elseProgram thenIH elseIH =>
      cases hreg : regs.optNat reg with
      | none =>
          have hmemElse :
              TraceEvent.readWord segment index word? ∈
                (eval elseProgram store regs).trace := by
            simpa [eval, hreg] using hmem
          simpa [eval, readAddresses, hreg] using
            elseIH hmemElse
      | some value =>
          have hmemThen :
              TraceEvent.readWord segment index word? ∈
                (eval thenProgram store regs).trace := by
            simpa [eval, hreg] using hmem
          simpa [eval, readAddresses, hreg] using
            thenIH hmemThen

/-- Read-address boundedness transfers to every read event in the trace. -/
theorem eval_readWord_address_fitsInBits
    (program : RegProgram) (store : Store) (regs : RegFile) {bits : Nat}
    (hfit : program.ReadAddressesFitInBits regs bits)
    {segment index : Nat} {word? : Option Word}
    (hmem :
      TraceEvent.readWord segment index word? ∈
        (eval program store regs).trace) :
    AddressFitsInBits bits segment index :=
  hfit (eval_readWord_address_mem program store regs hmem)

/-- Every read event in the trace uses a bounded first-order address. -/
theorem eval_event_address_fitsInBits
    (program : RegProgram) (store : Store) (regs : RegFile) {bits : Nat}
    (hfit : program.ReadAddressesFitInBits regs bits) :
    forall event : TraceEvent,
      event ∈ (eval program store regs).trace ->
        match event with
        | TraceEvent.readWord segment index _ =>
            AddressFitsInBits bits segment index
        | TraceEvent.wordRank _ _ _ => True
        | TraceEvent.wordSelect _ _ _ => True
        | TraceEvent.syntheticCostOnlyPrimitive => True := by
  intro event hmem
  cases event with
  | readWord segment index word? =>
      exact eval_readWord_address_fitsInBits program store regs hfit hmem
  | wordRank target limit result =>
      trivial
  | wordSelect target occurrence result =>
      trivial
  | syntheticCostOnlyPrimitive =>
      trivial

/-- All register-program trace events are payload reads or word primitives. -/
theorem eval_event_read_or_primitive
    (program : RegProgram) (store : Store) (regs : RegFile) :
    forall event : TraceEvent,
      event ∈ (eval program store regs).trace ->
        event.isReadWord \/ event.isWordPrimitive := by
  intro event _hmem
  exact TraceEvent.isReadWord_or_isWordPrimitive event

/-- Zero-cost register control never appears as a trace event. -/
theorem eval_no_zero_cost_control
    (program : RegProgram) (store : Store) (regs : RegFile) :
    forall event : TraceEvent,
      event ∈ (eval program store regs).trace ->
        ¬ event.isZeroCostControl := by
  intro event _hmem
  exact TraceEvent.not_zeroCostControl event

/-- Concrete read events report exactly the store value. -/
theorem eval_readWord_event_eq_store
    (program : RegProgram) (store : Store) (regs : RegFile)
    {segment index : Nat} {word? : Option Word}
    (hmem :
      TraceEvent.readWord segment index word? ∈
        (eval program store regs).trace) :
    store.readWord? segment index = word? := by
  exact eval_reads_subset_payload program store regs
    (TraceEvent.readWord segment index word?) hmem

/-- If payload memory is word-bounded, every returned trace word is bounded. -/
theorem eval_word_reads_length_le_machine
    (program : RegProgram) (store : Store) (regs : RegFile)
    {bound : Nat} (hbound : store.WordsBounded bound) :
    forall event : TraceEvent,
      event ∈ (eval program store regs).trace ->
        event.wordLengthBounded bound := by
  intro event hmem
  have hmatch := eval_reads_subset_payload program store regs event hmem
  cases event with
  | readWord segment index word? =>
      cases word? with
      | none =>
          simp [TraceEvent.wordLengthBounded]
      | some word =>
          exact hbound hmatch
  | wordRank target limit result =>
      simp [TraceEvent.wordLengthBounded]
  | wordSelect target occurrence result =>
      simp [TraceEvent.wordLengthBounded]
  | syntheticCostOnlyPrimitive =>
      simp [TraceEvent.wordLengthBounded]

/--
Evaluation is extensional in payload reads. Registers and arithmetic can choose
addresses, but the program cannot distinguish stores with the same read
interface.
-/
theorem eval_eq_of_readWord_eq
    (program : RegProgram) {storeA storeB : Store} (regs : RegFile)
    (hread :
      forall segment index,
        storeA.readWord? segment index = storeB.readWord? segment index) :
    eval program storeA regs = eval program storeB regs := by
  induction program with
  | pureOpt value =>
      rfl
  | readJoinedOptionNat segment width index =>
      simp [eval, hread segment (index.eval regs)]
  | ifSomeNat reg thenProgram elseProgram thenIH elseIH =>
      cases hreg : regs.optNat reg with
      | none =>
          simpa [eval, hreg] using elseIH
      | some value =>
          simpa [eval, hreg] using thenIH

/-- The `Costed` projection is also extensional in payload reads. -/
theorem eval_toCosted_eq_of_readWord_eq
    (program : RegProgram) {storeA storeB : Store} (regs : RegFile)
    (hread :
      forall segment index,
        storeA.readWord? segment index = storeB.readWord? segment index) :
    (eval program storeA regs).toCosted =
      (eval program storeB regs).toCosted := by
  rw [eval_eq_of_readWord_eq program regs hread]

/-- The trace length is bounded by the syntactic read count. -/
theorem eval_trace_length_le_readCount
    (program : RegProgram) (store : Store) (regs : RegFile) :
    (eval program store regs).trace.length <= program.readCount := by
  induction program with
  | pureOpt value =>
      simp [eval, readCount]
  | readJoinedOptionNat segment width index =>
      simp [eval, readCount]
  | ifSomeNat reg thenProgram elseProgram thenIH elseIH =>
      cases hreg : regs.optNat reg with
      | none =>
          exact Nat.le_trans (by simpa [eval, hreg] using elseIH)
            (Nat.le_max_right thenProgram.readCount elseProgram.readCount)
      | some value =>
          exact Nat.le_trans (by simpa [eval, hreg] using thenIH)
            (Nat.le_max_left thenProgram.readCount elseProgram.readCount)

end RegProgram

/--
Minimal first-order register program returning a natural number.

The first consumer is dynamic stored-word rank: sample and bit-word addresses
are register expressions, while the word-local rank primitive is still the
same unit-cost Word-RAM operation used by `Program.sampledRank`.
-/
inductive NatProgram where
  | pureNat (value : NatExpr)
  | sampledRank
      (target : Bool) (offset : NatExpr)
      (sampleSegment : Nat) (sampleIndex : NatExpr)
      (wordSegment : Nat) (wordIndex : NatExpr)
  | twoLevelSampledRank
      (target : Bool) (offset : NatExpr)
      (superSegment : Nat) (superIndex : NatExpr)
      (blockSegment : Nat) (blockIndex : NatExpr)
      (wordSegment : Nat) (wordIndex : NatExpr)
deriving Repr

namespace NatProgram

/-- Syntactic upper bound on trace events. -/
def stepCount : NatProgram -> Nat
  | pureNat _ => 0
  | sampledRank _ _ _ _ _ _ => 3
  | twoLevelSampledRank _ _ _ _ _ _ _ _ => 4

/-- Payload-read addresses selected by first-order natural-register programs. -/
def readAddresses : NatProgram -> RegFile -> List (Nat × Nat)
  | pureNat _, _regs => []
  | sampledRank _ _ sampleSegment sampleIndex wordSegment wordIndex, regs =>
      [(sampleSegment, sampleIndex.eval regs),
        (wordSegment, wordIndex.eval regs)]
  | twoLevelSampledRank _ _ superSegment superIndex
      blockSegment blockIndex wordSegment wordIndex, regs =>
      [(superSegment, superIndex.eval regs),
        (blockSegment, blockIndex.eval regs),
        (wordSegment, wordIndex.eval regs)]

/-- All selected payload-read addresses fit in the declared machine-bit bound. -/
def ReadAddressesFitInBits
    (program : NatProgram) (regs : RegFile) (bits : Nat) : Prop :=
  forall {segment index : Nat},
    (segment, index) ∈ program.readAddresses regs ->
      AddressFitsInBits bits segment index

/-- Deterministic evaluation of a natural-valued register program. -/
def eval : NatProgram -> Store -> RegFile -> Result .nat
  | pureNat value, _store, regs =>
      { value := value.eval regs, trace := [] }
  | sampledRank target offset sampleSegment sampleIndex
      wordSegment wordIndex, store, regs =>
      let sampleI := sampleIndex.eval regs
      let wordI := wordIndex.eval regs
      let sampleWord? := store.readWord? sampleSegment sampleI
      let word? := store.readWord? wordSegment wordI
      let sample? := sampleWord?.map bitsToNatLE
      match sample?, word? with
      | some sample, some word =>
          let localRank := RAM.boolRankPrefix target word (offset.eval regs)
          { value := sample + localRank
            trace :=
              [TraceEvent.readWord sampleSegment sampleI sampleWord?,
                TraceEvent.readWord wordSegment wordI word?,
                TraceEvent.wordRank target (offset.eval regs) localRank] }
      | _, _ =>
          { value := (0 : Nat)
            trace :=
              [TraceEvent.readWord sampleSegment sampleI sampleWord?,
                TraceEvent.readWord wordSegment wordI word?] }
  | twoLevelSampledRank target offset superSegment superIndex
      blockSegment blockIndex wordSegment wordIndex, store, regs =>
      let superI := superIndex.eval regs
      let blockI := blockIndex.eval regs
      let wordI := wordIndex.eval regs
      let superWord? := store.readWord? superSegment superI
      let blockWord? := store.readWord? blockSegment blockI
      let word? := store.readWord? wordSegment wordI
      let super? := superWord?.map bitsToNatLE
      let block? := blockWord?.map bitsToNatLE
      match super?, block?, word? with
      | some super, some block, some word =>
          let localRank := RAM.boolRankPrefix target word (offset.eval regs)
          { value := super + block + localRank
            trace :=
              [TraceEvent.readWord superSegment superI superWord?,
                TraceEvent.readWord blockSegment blockI blockWord?,
                TraceEvent.readWord wordSegment wordI word?,
                TraceEvent.wordRank target (offset.eval regs) localRank] }
      | _, _, _ =>
          { value := (0 : Nat)
            trace :=
              [TraceEvent.readWord superSegment superI superWord?,
                TraceEvent.readWord blockSegment blockI blockWord?,
                TraceEvent.readWord wordSegment wordI word?] }

/-- Cost is exactly the interpreted trace length. -/
theorem eval_toCosted_cost_eq_trace_length
    (program : NatProgram) (store : Store) (regs : RegFile) :
    (eval program store regs).toCosted.cost =
      (eval program store regs).trace.length := by
  rfl

/-- Every interpreted read event agrees with payload memory. -/
theorem eval_reads_subset_payload
    (program : NatProgram) (store : Store) (regs : RegFile) :
    forall event : TraceEvent,
      event ∈ (eval program store regs).trace ->
        event.matchesStore store := by
  cases program with
  | pureNat value =>
      intro event hmem
      simp [eval] at hmem
  | sampledRank target offset sampleSegment sampleIndex
      wordSegment wordIndex =>
      intro event hmem
      cases hsample :
          (store.readWord? sampleSegment (sampleIndex.eval regs)).map
            bitsToNatLE with
      | none =>
          cases hword :
              store.readWord? wordSegment (wordIndex.eval regs) with
          | none =>
              simp [eval, hsample, hword] at hmem
              rcases hmem with h | h
              · subst event
                rfl
              · subst event
                exact hword
          | some word =>
              simp [eval, hsample, hword] at hmem
              rcases hmem with h | h
              · subst event
                rfl
              · subst event
                exact hword
      | some sample =>
          cases hword :
              store.readWord? wordSegment (wordIndex.eval regs) with
          | none =>
              simp [eval, hsample, hword] at hmem
              rcases hmem with h | h
              · subst event
                rfl
              · subst event
                exact hword
          | some word =>
              simp [eval, hsample, hword] at hmem
              rcases hmem with h | htail
              · subst event
                rfl
              · rcases htail with h | h
                · subst event
                  exact hword
                · subst event
                  trivial
  | twoLevelSampledRank target offset superSegment superIndex
      blockSegment blockIndex wordSegment wordIndex =>
      intro event hmem
      cases hsuperRaw :
          store.readWord? superSegment (superIndex.eval regs) with
      | none =>
          have hsuper :
              (store.readWord? superSegment (superIndex.eval regs)).map
                bitsToNatLE = none := by
            simp [hsuperRaw]
          cases hblock :
              (store.readWord? blockSegment (blockIndex.eval regs)).map
                bitsToNatLE <;>
            cases hword :
              store.readWord? wordSegment (wordIndex.eval regs) <;>
            simp [eval, hsuper, hblock, hword] at hmem <;>
            (rcases hmem with h | htail
             · subst event
               rfl
             · rcases htail with h | h
               · subst event
                 rfl
               · subst event
                 exact hword)
      | some superWord =>
          have hsuper :
              (store.readWord? superSegment (superIndex.eval regs)).map
                bitsToNatLE = some (bitsToNatLE superWord) := by
            simp [hsuperRaw]
          cases hblock :
              (store.readWord? blockSegment (blockIndex.eval regs)).map
                bitsToNatLE with
          | none =>
              cases hword :
                  store.readWord? wordSegment (wordIndex.eval regs) <;>
                simp [eval, hsuper, hblock, hword] at hmem <;>
                (rcases hmem with h | htail
                 · subst event
                   rfl
                 · rcases htail with h | h
                   · subst event
                     rfl
                   · subst event
                     exact hword)
          | some block =>
              cases hword :
                  store.readWord? wordSegment (wordIndex.eval regs) with
              | none =>
                  simp [eval, hsuper, hblock, hword] at hmem
                  rcases hmem with h | htail
                  · subst event
                    rfl
                  · rcases htail with h | h
                    · subst event
                      rfl
                    · subst event
                      exact hword
              | some word =>
                  simp [eval, hsuper, hblock, hword] at hmem
                  rcases hmem with h | htail
                  · subst event
                    rfl
                  · rcases htail with h | htail
                    · subst event
                      rfl
                    · rcases htail with h | h
                      · subst event
                        exact hword
                      · subst event
                        trivial

/--
Every read event in a natural-register program trace uses an address computed
from first-order syntax and the current register file.
-/
theorem eval_readWord_address_mem
    (program : NatProgram) (store : Store) (regs : RegFile)
    {segment index : Nat} {word? : Option Word}
    (hmem :
      TraceEvent.readWord segment index word? ∈
        (eval program store regs).trace) :
    (segment, index) ∈ program.readAddresses regs := by
  cases program with
  | pureNat value =>
      simp [eval] at hmem
  | sampledRank target offset sampleSegment sampleIndex
      wordSegment wordIndex =>
      cases hsample :
          (store.readWord? sampleSegment (sampleIndex.eval regs)).map
            bitsToNatLE <;>
        cases hword :
          store.readWord? wordSegment (wordIndex.eval regs) <;>
        simp [eval, readAddresses, hsample, hword] at hmem ⊢ <;>
        (rcases hmem with h | htail
         · rcases h with ⟨hsegment, hindex, _hword⟩
           subst segment
           subst index
           simp
         · first
           | rcases htail with ⟨hsegment, hindex, _hword⟩
             subst segment
             subst index
             simp
           | simp at htail)
  | twoLevelSampledRank target offset superSegment superIndex
      blockSegment blockIndex wordSegment wordIndex =>
      cases hsuper :
          (store.readWord? superSegment (superIndex.eval regs)).map
            bitsToNatLE <;>
        cases hblock :
          (store.readWord? blockSegment (blockIndex.eval regs)).map
            bitsToNatLE <;>
        cases hword :
          store.readWord? wordSegment (wordIndex.eval regs) <;>
        simp [eval, readAddresses, hsuper, hblock, hword] at hmem ⊢ <;>
        (rcases hmem with h | htail
         · rcases h with ⟨hsegment, hindex, _hword⟩
           subst segment
           subst index
           simp
         · rcases htail with h | htail
           · rcases h with ⟨hsegment, hindex, _hword⟩
             subst segment
             subst index
             simp
           · first
             | rcases htail with ⟨hsegment, hindex, _hword⟩
               subst segment
               subst index
               simp
             | simp at htail)

/-- Read-address boundedness transfers to every read event in the trace. -/
theorem eval_readWord_address_fitsInBits
    (program : NatProgram) (store : Store) (regs : RegFile) {bits : Nat}
    (hfit : program.ReadAddressesFitInBits regs bits)
    {segment index : Nat} {word? : Option Word}
    (hmem :
      TraceEvent.readWord segment index word? ∈
        (eval program store regs).trace) :
    AddressFitsInBits bits segment index :=
  hfit (eval_readWord_address_mem program store regs hmem)

/-- Every read event in the trace uses a bounded first-order address. -/
theorem eval_event_address_fitsInBits
    (program : NatProgram) (store : Store) (regs : RegFile) {bits : Nat}
    (hfit : program.ReadAddressesFitInBits regs bits) :
    forall event : TraceEvent,
      event ∈ (eval program store regs).trace ->
        match event with
        | TraceEvent.readWord segment index _ =>
            AddressFitsInBits bits segment index
        | TraceEvent.wordRank _ _ _ => True
        | TraceEvent.wordSelect _ _ _ => True
        | TraceEvent.syntheticCostOnlyPrimitive => True := by
  intro event hmem
  cases event with
  | readWord segment index word? =>
      exact eval_readWord_address_fitsInBits program store regs hfit hmem
  | wordRank target limit result =>
      trivial
  | wordSelect target occurrence result =>
      trivial
  | syntheticCostOnlyPrimitive =>
      trivial

/-- All natural-register program trace events are reads or word primitives. -/
theorem eval_event_read_or_primitive
    (program : NatProgram) (store : Store) (regs : RegFile) :
    forall event : TraceEvent,
      event ∈ (eval program store regs).trace ->
        event.isReadWord \/ event.isWordPrimitive := by
  intro event _hmem
  exact TraceEvent.isReadWord_or_isWordPrimitive event

/-- Zero-cost natural-register control never appears as a trace event. -/
theorem eval_no_zero_cost_control
    (program : NatProgram) (store : Store) (regs : RegFile) :
    forall event : TraceEvent,
      event ∈ (eval program store regs).trace ->
        ¬ event.isZeroCostControl := by
  intro event _hmem
  exact TraceEvent.not_zeroCostControl event

theorem eval_no_syntheticCostOnlyPrimitive
    (program : NatProgram) (store : Store) (regs : RegFile) :
    forall event : TraceEvent,
      event ∈ (eval program store regs).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  cases program with
  | pureNat value =>
      intro event hmem
      simp [eval] at hmem
  | sampledRank target offset sampleSegment sampleIndex
      wordSegment wordIndex =>
      intro event hmem
      cases hsample :
          (store.readWord? sampleSegment (sampleIndex.eval regs)).map
            bitsToNatLE <;>
        cases hword :
          store.readWord? wordSegment (wordIndex.eval regs) <;>
        simp [eval, hsample, hword] at hmem
      all_goals
        intro hsynth
        cases event <;>
          simp [TraceEvent.isSyntheticCostOnlyPrimitive] at hmem hsynth
  | twoLevelSampledRank target offset superSegment superIndex
      blockSegment blockIndex wordSegment wordIndex =>
      intro event hmem
      cases hsuper :
          (store.readWord? superSegment (superIndex.eval regs)).map
            bitsToNatLE <;>
        cases hblock :
          (store.readWord? blockSegment (blockIndex.eval regs)).map
            bitsToNatLE <;>
        cases hword :
          store.readWord? wordSegment (wordIndex.eval regs) <;>
        simp [eval, hsuper, hblock, hword] at hmem
      all_goals
        intro hsynth
        cases event <;>
          simp [TraceEvent.isSyntheticCostOnlyPrimitive] at hmem hsynth

/-- Concrete read events report exactly the store value. -/
theorem eval_readWord_event_eq_store
    (program : NatProgram) (store : Store) (regs : RegFile)
    {segment index : Nat} {word? : Option Word}
    (hmem :
      TraceEvent.readWord segment index word? ∈
        (eval program store regs).trace) :
    store.readWord? segment index = word? := by
  exact eval_reads_subset_payload program store regs
    (TraceEvent.readWord segment index word?) hmem

/-- If payload memory is word-bounded, every returned trace word is bounded. -/
theorem eval_word_reads_length_le_machine
    (program : NatProgram) (store : Store) (regs : RegFile)
    {bound : Nat} (hbound : store.WordsBounded bound) :
    forall event : TraceEvent,
      event ∈ (eval program store regs).trace ->
        event.wordLengthBounded bound := by
  intro event hmem
  have hmatch := eval_reads_subset_payload program store regs event hmem
  cases event with
  | readWord segment index word? =>
      cases word? with
      | none =>
          simp [TraceEvent.wordLengthBounded]
      | some word =>
          exact hbound hmatch
  | wordRank target limit result =>
      simp [TraceEvent.wordLengthBounded]
  | wordSelect target occurrence result =>
      simp [TraceEvent.wordLengthBounded]
  | syntheticCostOnlyPrimitive =>
      simp [TraceEvent.wordLengthBounded]

/-- Evaluation is extensional in payload reads. -/
theorem eval_eq_of_readWord_eq
    (program : NatProgram) {storeA storeB : Store} (regs : RegFile)
    (hread :
      forall segment index,
        storeA.readWord? segment index = storeB.readWord? segment index) :
    eval program storeA regs = eval program storeB regs := by
  cases program with
  | pureNat value =>
      rfl
  | sampledRank target offset sampleSegment sampleIndex
      wordSegment wordIndex =>
      simp [eval, hread sampleSegment (sampleIndex.eval regs),
        hread wordSegment (wordIndex.eval regs)]
  | twoLevelSampledRank target offset superSegment superIndex
      blockSegment blockIndex wordSegment wordIndex =>
      simp [eval, hread superSegment (superIndex.eval regs),
        hread blockSegment (blockIndex.eval regs),
        hread wordSegment (wordIndex.eval regs)]

/-- The `Costed` projection is also extensional in payload reads. -/
theorem eval_toCosted_eq_of_readWord_eq
    (program : NatProgram) {storeA storeB : Store} (regs : RegFile)
    (hread :
      forall segment index,
        storeA.readWord? segment index = storeB.readWord? segment index) :
    (eval program storeA regs).toCosted =
      (eval program storeB regs).toCosted := by
  rw [eval_eq_of_readWord_eq program regs hread]

/-- The trace length is bounded by the syntactic step count. -/
theorem eval_trace_length_le_stepCount
    (program : NatProgram) (store : Store) (regs : RegFile) :
    (eval program store regs).trace.length <= program.stepCount := by
  cases program with
  | pureNat value =>
      simp [eval, stepCount]
  | sampledRank target offset sampleSegment sampleIndex
      wordSegment wordIndex =>
      cases hsample :
          (store.readWord? sampleSegment (sampleIndex.eval regs)).map
            bitsToNatLE <;>
        cases hword :
          store.readWord? wordSegment (wordIndex.eval regs) <;>
        simp [eval, stepCount, hsample, hword]
  | twoLevelSampledRank target offset superSegment superIndex
      blockSegment blockIndex wordSegment wordIndex =>
      cases hsuper :
          (store.readWord? superSegment (superIndex.eval regs)).map
            bitsToNatLE <;>
        cases hblock :
          (store.readWord? blockSegment (blockIndex.eval regs)).map
            bitsToNatLE <;>
        cases hword :
          store.readWord? wordSegment (wordIndex.eval regs) <;>
        simp [eval, stepCount, hsuper, hblock, hword]

end NatProgram

end Register

end WordRAM

end RMQ
