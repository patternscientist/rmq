import RMQ.Core.WordRAM

/-!
# E1 amended familiar small-step machine (core semantics)

The amended E1 target (DD-20260717-C05-001,
`docs/internal/OPTION_B_CHARGED_FRINGE_DESIGN.md`) asks for a standard
word-RAM instruction semantics: memory read into a register, register
move/write, integer arithmetic, comparison, conditional branch, and halt,
over `machineWordBits`-width operands, with every executed instruction
charging exactly one step.

This module defines the machine only: the instruction vocabulary, the
one-instruction step function, the fueled run loop, the frozen charge
categories, the accounting identities, and the constructor-exhaustive
field-width predicate.  The concrete whole-query program, its simulation
theorems against
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult`, and the
derived literal step bound live in later E1 modules.

Design constraints realized here (frozen matrix
`docs/internal/E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md`, REQ-E1-01/02):

* every instruction is atomic: the step function executes one constructor
  by a single non-recursive `match`; only the outer fueled run loop
  recurses, and it recurses on the fuel counter alone;
* at most one memory-read trace event per executed instruction, and the
  event is produced against the supplied `WordRAM.ReadStore` at the moment
  of execution (`run_readLog_readWord_shape`);
* exactly one charge category tick per executed instruction
  (`run_steps_eq_catLog_length`), with the six frozen categories
  partitioning the total (`catCount_partition`);
* arithmetic is `add`/`sub` plus multiplication/division by an encoded
  CONSTANT (`mulConst`/`divConst`).  The accepted route needs no
  register-by-register multiplication or division: every divisor and
  multiplier in the route's address/decode arithmetic (chunk width `c`,
  mixed radices `c + 1`, `2 * c + 1`, block sizes, region strides) is a
  per-shape program constant.  `x % k` is compiled as
  `x - (x / k) * k` over the constant forms.  Recorded as a design
  decision in `docs/internal/DESIGN_DECISIONS.md` (E1 ISA entry);
* a memory read decodes its fetched word by one bounded expression
  (`decodeRead`): a missing word decodes to `0`, a stored word to its
  little-endian value shifted by one, so read success is testable by an
  ordinary register comparison and no separate option channel exists.

This machine is a refinement target for the accepted charged trace; it is
a mathematical cost model, not a compiled-runtime or wall-clock claim.
-/

namespace RMQ
namespace WordRAM
namespace E1Machine

/-- Register file: a total map from register identifiers to word values. -/
def RegFile := Nat → Nat

instance : Inhabited RegFile := ⟨fun _ => 0⟩

/-- Point update of one register. -/
def RegFile.write (regs : RegFile) (target value : Nat) : RegFile :=
  fun r => if r = target then value else regs r

@[simp] theorem RegFile.write_same (regs : RegFile) (target value : Nat) :
    regs.write target value target = value := by
  simp [RegFile.write]

theorem RegFile.write_other (regs : RegFile) {target r : Nat} (value : Nat)
    (h : r ≠ target) : regs.write target value r = regs r := by
  simp [RegFile.write, h]

/--
The familiar first-order instruction vocabulary.  Each constructor is one
atomic machine transition; none hides recursion, a variable-length scan,
or more than one memory read.
-/
inductive Instr where
  /-- Read payload word `(segment, R addrReg)` from the store; decode it by
  `decodeRead` into `R dst`; emit the `readWord` trace event. -/
  | readMem (dst segment addrReg : Nat)
  /-- Load the encoded constant into `R dst`. -/
  | const (dst value : Nat)
  /-- Copy `R src` into `R dst`. -/
  | move (dst src : Nat)
  /-- `R dst := R src₁ + R src₂`. -/
  | add (dst src₁ src₂ : Nat)
  /-- `R dst := R src₁ - R src₂` (truncated natural subtraction, matching
  the route's `Nat` arithmetic). -/
  | sub (dst src₁ src₂ : Nat)
  /-- `R dst := R src * k` for the encoded constant `k`. -/
  | mulConst (dst src k : Nat)
  /-- `R dst := R src / k` for the encoded constant `k`. -/
  | divConst (dst src k : Nat)
  /-- `R dst := if R src₁ < R src₂ then 1 else 0`. -/
  | natLt (dst src₁ src₂ : Nat)
  /-- `R dst := if R src₁ ≤ R src₂ then 1 else 0`. -/
  | natLe (dst src₁ src₂ : Nat)
  /-- `R dst := if R src₁ = R src₂ then 1 else 0`. -/
  | natEq (dst src₁ src₂ : Nat)
  /-- If `R cond ≠ 0` jump to absolute instruction index `target`, else
  fall through. -/
  | brNZ (cond target : Nat)
  /-- Stop the machine. -/
  | halt
deriving Repr, DecidableEq

/-- The six frozen charge categories (matrix REQ-E1-06). -/
inductive Category where
  | memoryRead
  | registerWrite
  | arithmetic
  | comparison
  | branch
  | control
deriving Repr, DecidableEq

/-- Every instruction belongs to exactly one frozen charge category. -/
def Instr.category : Instr → Category
  | .readMem .. => .memoryRead
  | .const .. => .registerWrite
  | .move .. => .registerWrite
  | .add .. => .arithmetic
  | .sub .. => .arithmetic
  | .mulConst .. => .arithmetic
  | .divConst .. => .arithmetic
  | .natLt .. => .comparison
  | .natLe .. => .comparison
  | .natEq .. => .comparison
  | .brNZ .. => .branch
  | .halt => .control

/--
The single bounded decode a memory read applies to its fetched word: a
missing word decodes to `0`, a stored word to `bitsToNatLE word + 1`.  The
shift makes read success testable by one register comparison against `0`.
-/
def decodeRead : Option Word → Nat
  | none => 0
  | some word => bitsToNatLE word + 1

@[simp] theorem decodeRead_none : decodeRead none = 0 := rfl

@[simp] theorem decodeRead_some (word : Word) :
    decodeRead (some word) = bitsToNatLE word + 1 := rfl

/-- Machine state: registers, program counter, halt flag. -/
structure State where
  regs : RegFile
  pc : Nat
  halted : Bool

/-- A program is a finite instruction list addressed by the pc. -/
abbrev Program := List Instr

/--
Execute ONE instruction.  This is a single non-recursive `match`: no
constructor's arm loops, scans, or reads more than once.  The result is
the successor state, the one charge-category tick, and at most one trace
event.
-/
def execInstr (store : ReadStore) (instr : Instr) (s : State) :
    State × Category × Option TraceEvent :=
  match instr with
  | .readMem dst segment addrReg =>
      let address := s.regs addrReg
      let word? := store.readWord? segment address
      (⟨s.regs.write dst (decodeRead word?), s.pc + 1, false⟩,
        .memoryRead, some (.readWord segment address word?))
  | .const dst value =>
      (⟨s.regs.write dst value, s.pc + 1, false⟩, .registerWrite, none)
  | .move dst src =>
      (⟨s.regs.write dst (s.regs src), s.pc + 1, false⟩, .registerWrite, none)
  | .add dst src₁ src₂ =>
      (⟨s.regs.write dst (s.regs src₁ + s.regs src₂), s.pc + 1, false⟩,
        .arithmetic, none)
  | .sub dst src₁ src₂ =>
      (⟨s.regs.write dst (s.regs src₁ - s.regs src₂), s.pc + 1, false⟩,
        .arithmetic, none)
  | .mulConst dst src k =>
      (⟨s.regs.write dst (s.regs src * k), s.pc + 1, false⟩, .arithmetic, none)
  | .divConst dst src k =>
      (⟨s.regs.write dst (s.regs src / k), s.pc + 1, false⟩, .arithmetic, none)
  | .natLt dst src₁ src₂ =>
      (⟨s.regs.write dst (if s.regs src₁ < s.regs src₂ then 1 else 0),
          s.pc + 1, false⟩, .comparison, none)
  | .natLe dst src₁ src₂ =>
      (⟨s.regs.write dst (if s.regs src₁ ≤ s.regs src₂ then 1 else 0),
          s.pc + 1, false⟩, .comparison, none)
  | .natEq dst src₁ src₂ =>
      (⟨s.regs.write dst (if s.regs src₁ = s.regs src₂ then 1 else 0),
          s.pc + 1, false⟩, .comparison, none)
  | .brNZ cond target =>
      (⟨s.regs, if s.regs cond = 0 then s.pc + 1 else target, false⟩,
        .branch, none)
  | .halt =>
      (⟨s.regs, s.pc, true⟩, .control, none)

/-- One machine step: fetch at the pc, execute, or refuse (halted / no
instruction).  A refused step charges nothing. -/
def step (store : ReadStore) (program : Program) (s : State) :
    Option (State × Category × Option TraceEvent) :=
  if s.halted then none
  else
    match program[s.pc]? with
    | none => none
    | some instr => some (execInstr store instr s)

/-- The observable outcome of a fueled run: final state, the ordered
memory-read receipt log, the ordered per-step category log, and the total
charged step count. -/
structure RunResult where
  final : State
  readLog : List TraceEvent
  catLog : List Category
  steps : Nat

theorem RunResult.ext {a b : RunResult}
    (hfinal : a.final = b.final) (hread : a.readLog = b.readLog)
    (hcat : a.catLog = b.catLog) (hsteps : a.steps = b.steps) : a = b := by
  cases a; cases b; cases hfinal; cases hread; cases hcat; cases hsteps; rfl

/--
Fueled execution.  The ONLY recursion in the machine semantics: it
recurses on the fuel counter, executing exactly one instruction per unit
of consumed fuel and charging exactly one step for it.
-/
def run (store : ReadStore) (program : Program) : Nat → State → RunResult
  | 0, s => ⟨s, [], [], 0⟩
  | fuel + 1, s =>
    match step store program s with
    | none => ⟨s, [], [], 0⟩
    | some (s', cat, event?) =>
      let rest := run store program fuel s'
      ⟨rest.final, event?.toList ++ rest.readLog, cat :: rest.catLog,
        rest.steps + 1⟩

@[simp] theorem run_zero (store : ReadStore) (program : Program) (s : State) :
    run store program 0 s = ⟨s, [], [], 0⟩ := rfl

theorem run_succ (store : ReadStore) (program : Program) (fuel : Nat)
    (s : State) :
    run store program (fuel + 1) s =
      match step store program s with
      | none => ⟨s, [], [], 0⟩
      | some (s', cat, event?) =>
        let rest := run store program fuel s'
        ⟨rest.final, event?.toList ++ rest.readLog, cat :: rest.catLog,
          rest.steps + 1⟩ := rfl

/-- A refused step stops the whole run without charging, for any fuel. -/
theorem run_stuck (store : ReadStore) (program : Program) {s : State}
    (h : step store program s = none) (fuel : Nat) :
    run store program fuel s = ⟨s, [], [], 0⟩ := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [run_succ, h]

/-- Inversion: a successful step is the execution of the fetched
instruction. -/
theorem step_some (store : ReadStore) (program : Program) {s : State}
    {out : State × Category × Option TraceEvent}
    (h : step store program s = some out) :
    ∃ instr, program[s.pc]? = some instr ∧ execInstr store instr s = out := by
  unfold step at h
  by_cases hhalt : s.halted = true
  · rw [if_pos hhalt] at h
    exact Option.noConfusion h
  · rw [if_neg hhalt] at h
    cases hfetch : program[s.pc]? with
    | none =>
      rw [hfetch] at h
      exact Option.noConfusion h
    | some instr =>
      rw [hfetch] at h
      exact ⟨instr, rfl, Option.some.inj h⟩

/-! ## Category accounting -/

/-- Occurrences of one category in a category log. -/
def catCount : List Category → Category → Nat
  | [], _ => 0
  | c :: rest, target =>
      (if c = target then 1 else 0) + catCount rest target

@[simp] theorem catCount_nil (target : Category) : catCount [] target = 0 :=
  rfl

theorem catCount_cons (c : Category) (rest : List Category)
    (target : Category) :
    catCount (c :: rest) target =
      (if c = target then 1 else 0) + catCount rest target := rfl

/-- The six frozen categories partition every category log: the per-
category counts sum to the log length.  With
`run_steps_eq_catLog_length` this is the REQ-E1-06 accounting identity:
total machine steps = sum of the explicit category counts. -/
theorem catCount_partition (log : List Category) :
    catCount log .memoryRead + catCount log .registerWrite +
        catCount log .arithmetic + catCount log .comparison +
        catCount log .branch + catCount log .control =
      log.length := by
  induction log with
  | nil => rfl
  | cons c rest ih =>
    cases c <;> simp [catCount_cons] <;> omega

/--
THE VOCABULARY BRIDGE.

Machine-level accounting (`run_steps_eq_category_sum`,
`run_readLog_length_eq_memoryRead_count`) is written with `catCount`.
Every BLOCK-level cap in this development is written with
`(log.filter (· == c)).length` — e.g.
`interiorChunkFoldCats_memoryRead_count` and
`fringeArmPrologueCats_memoryRead_count`.  Until this lemma the two
vocabularies had no connecting fact anywhere in the tree, so no block cap
could be composed into a machine-level step or receipt claim.

`Category` derives `DecidableEq` and no `BEq`, so `a == c` is
`instBEqOfDecidableEq`, i.e. `decide (a = c)`; the two sides therefore
agree constructor-by-constructor and the induction is immediate. -/
theorem catCount_eq_filter_length (log : List Category) (c : Category) :
    catCount log c = (log.filter (· == c)).length := by
  induction log with
  | nil => rfl
  | cons a rest ih =>
    by_cases h : a = c
    · simp [catCount_cons, h, ih]
      omega
    · simp [catCount_cons, h, ih]

/-- The bridge in the direction block caps are stated in: a `filter`-form
cap transfers to a `catCount` bound with no arithmetic in between. -/
theorem catCount_le_of_filter_length_le {log : List Category}
    {c : Category} {n : Nat}
    (h : (log.filter (· == c)).length ≤ n) : catCount log c ≤ n := by
  rw [catCount_eq_filter_length]; exact h

/-- Every executed instruction charges exactly one step: the charged step
count is the length of the per-instruction category log. -/
theorem run_steps_eq_catLog_length (store : ReadStore) (program : Program) :
    ∀ (fuel : Nat) (s : State),
      (run store program fuel s).steps =
        (run store program fuel s).catLog.length := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
    intro s
    rw [run_succ]
    cases h : step store program s with
    | none => rfl
    | some out =>
      obtain ⟨s', cat, event?⟩ := out
      simpa using ih s'

/-- Total machine steps = sum of the six frozen category counts (the
REQ-E1-06 accounting identity at run level). -/
theorem run_steps_eq_category_sum (store : ReadStore) (program : Program)
    (fuel : Nat) (s : State) :
    (run store program fuel s).steps =
      catCount (run store program fuel s).catLog .memoryRead +
        catCount (run store program fuel s).catLog .registerWrite +
        catCount (run store program fuel s).catLog .arithmetic +
        catCount (run store program fuel s).catLog .comparison +
        catCount (run store program fuel s).catLog .branch +
        catCount (run store program fuel s).catLog .control := by
  rw [run_steps_eq_catLog_length, catCount_partition]

/-! ## Read receipts -/

/-- Per instruction: the executed step emits a memory-read event exactly
when its category tick is `memoryRead` (so no other constructor can hide
a read, and `readMem` cannot hide more than one). -/
theorem execInstr_readCount_eq_memoryRead_indicator (store : ReadStore)
    (instr : Instr) (s : State) :
    (execInstr store instr s).2.2.toList.length =
      (if (execInstr store instr s).2.1 = Category.memoryRead then 1
        else 0) := by
  cases instr <;> simp [execInstr]

/-- At most one memory read per executed instruction. -/
theorem execInstr_reads_le_one (store : ReadStore) (instr : Instr)
    (s : State) : (execInstr store instr s).2.2.toList.length ≤ 1 := by
  cases instr <;> simp [execInstr]

/-- The receipt log length is exactly the `memoryRead` category count:
reads are charged one-for-one, and only `readMem` produces them. -/
theorem run_readLog_length_eq_memoryRead_count (store : ReadStore)
    (program : Program) :
    ∀ (fuel : Nat) (s : State),
      (run store program fuel s).readLog.length =
        catCount (run store program fuel s).catLog .memoryRead := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
    intro s
    rw [run_succ]
    cases h : step store program s with
    | none => rfl
    | some out =>
      obtain ⟨s', cat, event?⟩ := out
      obtain ⟨instr, _, hexec⟩ := step_some store program h
      have hcount :=
        execInstr_readCount_eq_memoryRead_indicator store instr s
      rw [hexec] at hcount
      simp only at hcount
      simp only [List.length_append, catCount_cons, ih s']
      by_cases hcat : cat = Category.memoryRead <;>
        simp [hcat] at hcount ⊢ <;> omega

/-- Per instruction: every emitted event is a `readWord` against the
supplied store at the executed address. -/
theorem execInstr_event_shape (store : ReadStore) (instr : Instr)
    (s : State) :
    ∀ event ∈ (execInstr store instr s).2.2.toList,
      ∃ segment index,
        event =
          TraceEvent.readWord segment index
            (store.readWord? segment index) := by
  cases instr <;> intro event hmem <;> simp [execInstr] at hmem
  case readMem dst segment addrReg =>
    exact ⟨segment, s.regs addrReg, hmem⟩

/-- Machine read receipts are genuine store reads: every event in the
receipt log is a `readWord` produced against the supplied store at the
executed address (so the log contains no `wordRank`/`wordSelect`/
`syntheticCostOnlyPrimitive` events and post-hoc replay is impossible at
the semantics level). -/
theorem run_readLog_readWord_shape (store : ReadStore) (program : Program) :
    ∀ (fuel : Nat) (s : State),
      ∀ event ∈ (run store program fuel s).readLog,
        ∃ segment index,
          event =
            TraceEvent.readWord segment index
              (store.readWord? segment index) := by
  intro fuel
  induction fuel with
  | zero => intro s event hmem; simp at hmem
  | succ fuel ih =>
    intro s event hmem
    rw [run_succ] at hmem
    cases h : step store program s with
    | none => rw [h] at hmem; simp at hmem
    | some out =>
      obtain ⟨s', cat, event?⟩ := out
      rw [h] at hmem
      simp only [List.mem_append] at hmem
      cases hmem with
      | inr hrest => exact ih s' event hrest
      | inl hhead =>
        obtain ⟨instr, _, hexec⟩ := step_some store program h
        refine execInstr_event_shape store instr s event ?_
        rw [hexec]
        exact hhead

/-- Every receipt agrees with the supplied read store. -/
theorem run_readLog_matchesReadStore (store : ReadStore) (program : Program)
    (fuel : Nat) (s : State) :
    ∀ event ∈ (run store program fuel s).readLog,
      event.matchesReadStore store := by
  intro event hmem
  obtain ⟨segment, index, rfl⟩ :=
    run_readLog_readWord_shape store program fuel s event hmem
  simp [TraceEvent.matchesReadStore]

/-- No synthetic cost-only event can appear in a machine receipt log. -/
theorem run_readLog_no_syntheticCostOnlyPrimitive (store : ReadStore)
    (program : Program) (fuel : Nat) (s : State) :
    ∀ event ∈ (run store program fuel s).readLog,
      event ≠ TraceEvent.syntheticCostOnlyPrimitive := by
  intro event hmem
  obtain ⟨segment, index, rfl⟩ :=
    run_readLog_readWord_shape store program fuel s event hmem
  intro hcontra
  cases hcontra

/-! ## Composition -/

/-- Fuel splits compose: running `f₁ + f₂` units is running `f₁`, then
`f₂` from the reached state, with logs concatenated in order and steps
added.  This is the backbone for compositional simulation proofs. -/
theorem run_add (store : ReadStore) (program : Program) (f₁ f₂ : Nat)
    (s : State) :
    run store program (f₁ + f₂) s =
      ⟨(run store program f₂ (run store program f₁ s).final).final,
        (run store program f₁ s).readLog ++
          (run store program f₂ (run store program f₁ s).final).readLog,
        (run store program f₁ s).catLog ++
          (run store program f₂ (run store program f₁ s).final).catLog,
        (run store program f₁ s).steps +
          (run store program f₂ (run store program f₁ s).final).steps⟩ := by
  induction f₁ generalizing s with
  | zero =>
    apply RunResult.ext <;> simp
  | succ f₁ ih =>
    have hshift : f₁ + 1 + f₂ = (f₁ + f₂) + 1 := by omega
    rw [hshift, run_succ, run_succ (fuel := f₁)]
    cases h : step store program s with
    | none =>
      have hstuck := run_stuck store program h f₂
      apply RunResult.ext <;> simp [hstuck]
    | some out =>
      obtain ⟨s', cat, event?⟩ := out
      have := ih s'
      apply RunResult.ext <;>
        simp [this, List.append_assoc] <;> omega

/-- The charged step count never exceeds the supplied fuel. -/
theorem run_steps_le_fuel (store : ReadStore) (program : Program) :
    ∀ (fuel : Nat) (s : State), (run store program fuel s).steps ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro s; exact Nat.le_refl 0
  | succ fuel ih =>
    intro s
    rw [run_succ]
    cases h : step store program s with
    | none => exact Nat.zero_le _
    | some out =>
      obtain ⟨s', cat, event?⟩ := out
      simpa using Nat.succ_le_succ (ih s')

/-! ## Constructor-exhaustive field-width accounting (REQ-E1-02)

The predicate matches every constructor explicitly.  There is no wildcard
arm: adding a constructor without extending this predicate fails to
compile, and each operand-carrying arm constrains every encoded field.
-/

/-- Every encoded field of the instruction fits the modeled `w`-bit word:
register identifiers, segment numbers, immediate constants,
multiplier/divisor constants, and branch targets are all below `2 ^ w`
(divisors are additionally positive). -/
def Instr.FieldsFit (w : Nat) : Instr → Prop
  | .readMem dst segment addrReg =>
      dst < 2 ^ w ∧ segment < 2 ^ w ∧ addrReg < 2 ^ w
  | .const dst value => dst < 2 ^ w ∧ value < 2 ^ w
  | .move dst src => dst < 2 ^ w ∧ src < 2 ^ w
  | .add dst src₁ src₂ => dst < 2 ^ w ∧ src₁ < 2 ^ w ∧ src₂ < 2 ^ w
  | .sub dst src₁ src₂ => dst < 2 ^ w ∧ src₁ < 2 ^ w ∧ src₂ < 2 ^ w
  | .mulConst dst src k => dst < 2 ^ w ∧ src < 2 ^ w ∧ k < 2 ^ w
  | .divConst dst src k =>
      dst < 2 ^ w ∧ src < 2 ^ w ∧ 0 < k ∧ k < 2 ^ w
  | .natLt dst src₁ src₂ => dst < 2 ^ w ∧ src₁ < 2 ^ w ∧ src₂ < 2 ^ w
  | .natLe dst src₁ src₂ => dst < 2 ^ w ∧ src₁ < 2 ^ w ∧ src₂ < 2 ^ w
  | .natEq dst src₁ src₂ => dst < 2 ^ w ∧ src₁ < 2 ^ w ∧ src₂ < 2 ^ w
  | .brNZ cond target => cond < 2 ^ w ∧ target < 2 ^ w
  | .halt => True

/-- A program fits width `w` when every instruction's fields do. -/
def ProgramFits (w : Nat) (program : Program) : Prop :=
  ∀ instr ∈ program, instr.FieldsFit w

/-! Oversizing rejection witnesses: for every operand-carrying
constructor, an instruction with one field at `2 ^ w` fails the
certificate at width `w`.  (`halt` carries no encoded field; its arm is
the trivially-true empty conjunction, which is the correct accounting for
a field-free constructor, not an unhandled-constructor default.) -/

theorem fieldsFit_rejects_oversized_readMem (w : Nat) :
    ¬ Instr.FieldsFit w (.readMem 0 (2 ^ w) 0) := fun h =>
  Nat.lt_irrefl _ h.2.1

theorem fieldsFit_rejects_oversized_const (w : Nat) :
    ¬ Instr.FieldsFit w (.const 0 (2 ^ w)) := fun h =>
  Nat.lt_irrefl _ h.2

theorem fieldsFit_rejects_oversized_move (w : Nat) :
    ¬ Instr.FieldsFit w (.move (2 ^ w) 0) := fun h =>
  Nat.lt_irrefl _ h.1

theorem fieldsFit_rejects_oversized_add (w : Nat) :
    ¬ Instr.FieldsFit w (.add 0 (2 ^ w) 0) := fun h =>
  Nat.lt_irrefl _ h.2.1

theorem fieldsFit_rejects_oversized_sub (w : Nat) :
    ¬ Instr.FieldsFit w (.sub 0 0 (2 ^ w)) := fun h =>
  Nat.lt_irrefl _ h.2.2

theorem fieldsFit_rejects_oversized_mulConst (w : Nat) :
    ¬ Instr.FieldsFit w (.mulConst 0 0 (2 ^ w)) := fun h =>
  Nat.lt_irrefl _ h.2.2

theorem fieldsFit_rejects_oversized_divConst (w : Nat) :
    ¬ Instr.FieldsFit w (.divConst 0 0 (2 ^ w)) := fun h =>
  Nat.lt_irrefl _ h.2.2.2

theorem fieldsFit_rejects_zero_divisor (w : Nat) :
    ¬ Instr.FieldsFit w (.divConst 0 0 0) := fun h =>
  Nat.lt_irrefl _ h.2.2.1

theorem fieldsFit_rejects_oversized_natLt (w : Nat) :
    ¬ Instr.FieldsFit w (.natLt (2 ^ w) 0 0) := fun h =>
  Nat.lt_irrefl _ h.1

theorem fieldsFit_rejects_oversized_natLe (w : Nat) :
    ¬ Instr.FieldsFit w (.natLe 0 (2 ^ w) 0) := fun h =>
  Nat.lt_irrefl _ h.2.1

theorem fieldsFit_rejects_oversized_natEq (w : Nat) :
    ¬ Instr.FieldsFit w (.natEq 0 0 (2 ^ w)) := fun h =>
  Nat.lt_irrefl _ h.2.2

theorem fieldsFit_rejects_oversized_brNZ (w : Nat) :
    ¬ Instr.FieldsFit w (.brNZ 0 (2 ^ w)) := fun h =>
  Nat.lt_irrefl _ h.2

end E1Machine
end WordRAM
end RMQ
