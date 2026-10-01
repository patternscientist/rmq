import RMQ.Core.WordRAM.Lifecycle.ArrayRun
import RMQ.Core.WordRAM.Lifecycle.Input
import RMQ.Core.WordRAM.Lifecycle.QueryBridge
import RMQ.Core.WordRAM.Lifecycle.Finalization
import RMQ.Core.WordRAM.Lifecycle.ServiceSafety
import RMQ.Core.WordRAM.Lifecycle.Reusable

/-! # Finite supplied owners and executable lifecycle refinement

Input materialization supplies only the numeric input representation, two
request cells, and the separately counted comparison resources. It does not
construct the final RMQ allocation. Numeric capacity is tracked separately
from the functional abstraction, which erases that capacity.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Executable

open PackedConstruction (Operand Prim BInstr put)
open PackedConstruction.Structured (Block)

attribute [local irreducible] Layout.program Service.program Service.entry Service.budget

def inputArray (model : InputModel) (xs : List Int) : Array (Option Nat) :=
  match model with
  | .word => (some xs.length :: xs.map (fun x => some (PackedConstruction.encodeInt
      (PackedWordRAM.wordWidth xs.length) x))).toArray
  | .comparison => #[some xs.length]

def initialOwnerAt (model : InputModel) (xs : List Int) (left right entry : Nat) : Owner :=
  { regs := Array.replicate 8273 0
    memory := ((inputArray model xs).push (some left)).push (some right)
    keys := if model = .comparison then (xs.map some).toArray else #[]
    keyRegs := if model = .comparison then Array.replicate 2 0 else #[]
    pc := entry
    status := .running }

theorem inputArray_size (model : InputModel) (xs : List Int) :
    (inputArray model xs).size = (inputCore model xs).extent := by
  cases model <;> simp [inputArray, inputCore, PackedConstruction.wordInputState,
    PackedConstruction.comparisonInputState, PackedConstruction.inputCellCount]

theorem inputArray_memory (model : InputModel) (xs : List Int) :
    (fun a => (inputArray model xs).getD a none) = (inputCore model xs).memory := by
  funext a
  cases model with
  | comparison => cases a <;> rfl
  | word =>
      cases a with
      | zero => simp [inputArray, Array.getD_eq_getD_getElem?, inputCore,
          PackedConstruction.wordInputState]
      | succ a =>
          cases h : xs[a]? <;>
            simp [inputArray, Array.getD_eq_getD_getElem?, List.getElem?_map, h,
              inputCore, PackedConstruction.wordInputState, PackedConstruction.encodeInput]

private theorem lookup_push {α : Type} (xs : Array α) (v default : α) :
    (fun a => (xs.push v).getD a default) =
      put (fun a => xs.getD a default) xs.size v := by
  funext a
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, put]
  by_cases ha : a = xs.size
  · simp [ha]
  · simp [ha]

theorem initialOwnerAt_toState (model : InputModel) (xs : List Int)
    (left right entry : Nat) :
    (initialOwnerAt model xs left right entry).toState =
      initialState model xs left right entry := by
  have hm : (fun a => (initialOwnerAt model xs left right entry).memory.getD a none) =
      (initialState model xs left right entry).core.memory := by
    change (fun a => (((inputArray model xs).push (some left)).push (some right)).getD a none) = _
    rw [lookup_push, lookup_push, Array.size_push, inputArray_size, inputArray_memory]
    rfl
  have hr : (fun r => (Array.replicate 8273 (0 : Nat)).getD r 0) = fun _ => 0 := by
    funext r
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  have hk : (fun a => ((xs.map some).toArray).getD a none) = fun a => xs[a]? := by
    funext a
    cases h : xs[a]? <;> simp [Array.getD_eq_getD_getElem?, List.getElem?_map, h]
  have hkr : (fun r => (Array.replicate 2 (0 : Int)).getD r 0) = fun _ => 0 := by
    funext r
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  cases model <;>
    simp only [Owner.toState, PackedConstruction.ExecState.abstract, initialOwnerAt,
      initialState, inputCore, PackedConstruction.wordInputState,
      PackedConstruction.comparisonInputState, reduceCtorEq, ↓reduceIte,
      Array.size_push, Array.size_replicate, List.size_toArray, List.length_map,
      inputArray_size, hr, hk, hkr] at hm ⊢
  all_goals simp only [hm] <;> rfl

theorem initialOwnerAt_regs_size (model : InputModel) (xs : List Int) (left right entry : Nat) :
    (initialOwnerAt model xs left right entry).regs.size = 8273 := by
  simp [initialOwnerAt]

theorem initialOwnerAt_memory_size (model : InputModel) (xs : List Int) (left right entry : Nat) :
    (initialOwnerAt model xs left right entry).memory.size = (inputCore model xs).extent + 2 := by
  simp [initialOwnerAt, inputArray_size, Nat.add_assoc]

theorem initialOwnerAt_key_sizes (model : InputModel) (xs : List Int) (left right entry : Nat) :
    (initialOwnerAt model xs left right entry).keys.size =
      (if model = .comparison then xs.length else 0) ∧
    (initialOwnerAt model xs left right entry).keyRegs.size =
      (if model = .comparison then 2 else 0) := by
  cases model <;> simp [initialOwnerAt]

/-- Numeric destinations and comparison destinations are distinct static inventories. -/
def NumericBelow (R : Nat) : Instruction → Prop
  | .old p => ∀ d, p.destination? = some d → d.val < R
  | _ => True

def KeyBelow (K : Nat) : Instruction → Prop
  | .old (.loadKey dst _) => dst.val < K
  | _ => True

theorem keyBelow_mono {K L : Nat} {i : Instruction} (h : KeyBelow K i) (hle : K ≤ L) :
    KeyBelow L i := by
  cases i with
  | old p => cases p <;> simp_all [KeyBelow] <;> omega
  | releaseCell | releaseKey | releaseKeyRegister => trivial

theorem destinations_of_separate {R : Nat} {i : Instruction} {s : State}
    (numeric : NumericBelow R i) (keys : KeyBelow s.keyRegExtent i) :
    i.AbstractDestinationsFit R s := by
  cases i with
  | old p =>
      cases p <;> simp_all [NumericBelow, KeyBelow, PackedConstruction.Prim.destination?,
        Instruction.AbstractDestinationsFit, destinationsBelow]
  | releaseCell | releaseKey | releaseKeyRegister => trivial

theorem numeric_of_registersBelow {R S : Nat} (i : BInstr)
    (bound : i.primitive.RegistersBelow R) (le : R ≤ S) : NumericBelow S (oldInstruction i) := by
  intro d hd
  exact Nat.lt_of_lt_of_le (PackedConstruction.Proof.Prim.dest_lt_of_registersBelow bound d hd) le

theorem translated_numeric (i : PackedWordRAM.Instruction) {R : Nat}
    (writes : i.WritesOnly (fun r => r < R)) :
    NumericBelow R (oldInstruction (PackedConstruction.Conservative.translate i)) := by
  unfold PackedConstruction.Conservative.translate
  split
  next fields =>
    cases i <;>
      simp_all [oldInstruction, NumericBelow, PackedConstruction.Prim.destination?,
        PackedConstruction.Conservative.instruction, PackedWordRAM.Instruction.WritesOnly]
  next => simp [oldInstruction, NumericBelow, PackedConstruction.Prim.destination?]

theorem translated_key_free (i : PackedWordRAM.Instruction) :
    KeyBelow 0 (oldInstruction (PackedConstruction.Conservative.translate i)) := by
  unfold PackedConstruction.Conservative.translate
  split
  next fields => cases i <;> trivial
  next => trivial

theorem compile_keyBelow (block : Block) (base K : Nat)
    (bound : Builder.keyRegisterLimit block ≤ K) :
    ∀ i ∈ block.compileAt base, KeyBelow K (oldInstruction i) := by
  induction block generalizing base with
  | skip => simp [Block.compileAt]
  | action op =>
      intro i hi
      have eq : i = ⟨op.prim⟩ := List.mem_singleton.mp hi
      subst i
      cases op <;> simp_all [Builder.keyRegisterLimit, oldInstruction,
        PackedConstruction.Structured.Action.prim, KeyBelow] <;> omega
  | exit src =>
      intro i hi
      have eq : i = ⟨.halt src⟩ := List.mem_singleton.mp hi
      subst i
      trivial
  | seq a b iha ihb =>
      intro i hi
      rcases List.mem_append.mp hi with ha | hb
      · exact iha _ (Nat.le_trans (Nat.le_max_left ..) bound) i ha
      · exact ihb _ (Nat.le_trans (Nat.le_max_right ..) bound) i hb
  | ifZero c a b iha ihb =>
      intro i hi
      simp only [Block.compileAt, List.mem_append, List.mem_singleton] at hi
      rcases hi with ((rfl | hi) | rfl) | hi
      · trivial
      · exact ihb _ (Nat.le_trans (Nat.le_max_right ..) bound) i hi
      · trivial
      · exact iha _ (Nat.le_trans (Nat.le_max_left ..) bound) i hi
  | loop c body ih =>
      intro i hi
      simp only [Block.compileAt, List.mem_append, List.mem_singleton] at hi
      rcases hi with (rfl | hi) | rfl
      · trivial
      · exact ih _ bound i hi
      · trivial

theorem eval_add_keys {P : PackedConstruction.State → PackedConstruction.Structured.Action → Prop}
    {b : Block} {s t : PackedConstruction.State} {steps : Nat}
    (e : PackedConstruction.Structured.EvalG P b s t steps) (K : Nat)
    (bound : Builder.keyRegisterLimit b ≤ K) :
    PackedConstruction.Structured.EvalG
      (fun s op => P s op ∧ KeyBelow K (.old op.prim)) b s t steps := by
  induction e generalizing K with
  | stopped b s h => exact .stopped b s h
  | skip s h => exact .skip s h
  | action op s h hp =>
      refine .action op s h ⟨hp, ?_⟩
      cases op <;> simp_all [Builder.keyRegisterLimit,
        PackedConstruction.Structured.Action.prim, KeyBelow] <;> omega
  | exit src s h => exact .exit src s h
  | seq _ _ iha ihb =>
      exact .seq (iha K (Nat.le_trans (Nat.le_max_left ..) bound))
        (ihb K (Nat.le_trans (Nat.le_max_right ..) bound))
  | ifZeroTaken h hc _ ih =>
      exact .ifZeroTaken h hc (ih K (Nat.le_trans (Nat.le_max_left ..) bound))
  | ifZeroFallthrough h hc _ hr ih =>
      exact .ifZeroFallthrough h hc (ih K (Nat.le_trans (Nat.le_max_right ..) bound)) hr
  | ifZeroFallthroughStopped h hc _ hr ih =>
      exact .ifZeroFallthroughStopped h hc (ih K (Nat.le_trans (Nat.le_max_right ..) bound)) hr
  | loopExit h hc => exact .loopExit h hc
  | loopStep h hc _ hr _ ihb ihr =>
      exact .loopStep h hc (ihb K bound) hr (ihr K bound)
  | loopStopped h hc _ hr ih => exact .loopStopped h hc (ih K bound) hr

/-- Recompile the same derivation with a structural key-write inventory and
identify the resulting trace with the original execution by determinism. -/
theorem hosted_key_trace {W base : Nat} {program : List BInstr} {leaf : Block}
    {xs : List Int} {s abstract final : PackedConstruction.State}
    {ts : List PackedConstruction.Transition}
    (body : Builder.HostedBody W program base leaf xs s abstract final ts)
    (entry : s.pc = base)
    (host : PackedConstruction.Structured.HostedAt program base
      ((PackedConstruction.builderSource leaf).compileAt base))
    (bound : base + (PackedConstruction.builderSource leaf).size < 2^32) :
    ∀ t ∈ ts, KeyBelow (Builder.keyRegisterLimit (PackedConstruction.builderSource leaf))
      (oldInstruction t.instruction) := by
  let K := Builder.keyRegisterLimit (PackedConstruction.builderSource leaf)
  have e := eval_add_keys body.evaluation K (Nat.le_refl _)
  obtain ⟨mid, us, execution, len, agree, pc, shapes⟩ := e.compile_realizes
    (fun _ q _ h => ⟨h.1.pc_set q, h.2⟩) program base host bound
  have running : mid.status = .running := by
    have ar : abstract.status = .running := by
      have hr := body.running
      rw [body.intermediate] at hr
      exact hr
    exact agree.status.trans ar
  have finalEq : mid = final := by rw [agree.eq_set, pc running, body.intermediate]
  have startEq : ({s with pc := base} : PackedConstruction.State) = s := by rw [← entry]
  rw [finalEq, startEq] at execution
  have traces : us = ts := by
    unfold PackedConstruction.RunsTo at execution
    rw [len] at execution
    exact congrArg PackedConstruction.Run.transitions (execution.symm.trans body.execution)
  subst us
  intro t ht
  rcases shapes t ht with ⟨op, action, _, keys⟩ | ⟨condition, target, action, _⟩ |
    ⟨target, action, _⟩ | ⟨src, action⟩
  · simpa only [action, oldInstruction] using keys
  all_goals simp [action, oldInstruction, KeyBelow]

/-- A property of the actual trace, including its actual pre-state key extent. -/
def TraceKeysFit (ts : List Transition) : Prop :=
  ∀ t ∈ ts, ∀ i, t.action = .instruction i → KeyBelow t.before.keyRegExtent i

theorem traceKeysFit_append {a b : List Transition}
    (ha : TraceKeysFit a) (hb : TraceKeysFit b) : TraceKeysFit (a ++ b) := by
  intro t ht i hi
  exact (List.mem_append.mp ht).elim (fun h => ha t h i hi) (fun h => hb t h i hi)

theorem traceKeysFit_of_key_free {ts : List Transition}
    (free : ∀ t ∈ ts, ∀ i, t.action = .instruction i → KeyBelow 0 i) : TraceKeysFit ts :=
  fun t ht i hi => keyBelow_mono (free t ht i hi) (Nat.zero_le _)

theorem traceDestinations_of_keys {program : List Instruction} {fuel : Nat} {s : State}
    (numeric : ∀ i ∈ program, NumericBelow 8273 i)
    (keys : TraceKeysFit (run program fuel s).transitions) :
    TraceDestinationsFit 8273 (run program fuel s).transitions := by
  intro k t ht i hi
  obtain ⟨_, _, actual, fetch, action, _⟩ := step_spec (run_transition_at ht).2
  have eq : actual = i := by rw [hi] at action; exact (Action.instruction.inj action).symm
  subst actual
  exact destinations_of_separate (numeric i (List.mem_of_getElem? fetch))
    (keys t (List.mem_of_getElem? ht) i hi)

def initialOwner (model : InputModel) (xs : List Int) (left right : Nat) : Owner :=
  initialOwnerAt model xs left right Layout.builderBase

theorem initialOwner_toState (model : InputModel) (xs : List Int) (left right : Nat) :
    (initialOwner model xs left right).toState =
      initialState model xs left right Layout.builderBase :=
  initialOwnerAt_toState model xs left right Layout.builderBase

theorem initialOwner_regs_size (model : InputModel) (xs : List Int) (left right : Nat) :
    (initialOwner model xs left right).regs.size = 8273 :=
  initialOwnerAt_regs_size model xs left right Layout.builderBase

theorem initialOwner_memory_size (model : InputModel) (xs : List Int) (left right : Nat) :
    (initialOwner model xs left right).memory.size =
      (match model with | .word => xs.length + 3 | .comparison => 3) := by
  change (initialOwnerAt model xs left right Layout.builderBase).memory.size = _
  rw [initialOwnerAt_memory_size]
  cases model <;> rfl

theorem initialOwner_key_sizes (model : InputModel) (xs : List Int) (left right : Nat) :
    (initialOwner model xs left right).keys.size =
      (if model = .comparison then xs.length else 0) ∧
    (initialOwner model xs left right).keyRegs.size =
      (if model = .comparison then 2 else 0) :=
  initialOwnerAt_key_sizes model xs left right Layout.builderBase

theorem builder_numeric (model : InputModel) :
    ∀ i ∈ Layout.builderCode model, NumericBelow 8273 (oldInstruction i) := by
  have rb : (PackedConstruction.builderSource model.source).RegsBelow 400 :=
    ⟨by simp [Block.RegsBelow, PackedConstruction.Structured.Action.prim,
      Prim.RegistersBelow], Construction.source_bank model⟩
  intro i hi
  exact numeric_of_registersBelow i
    (Block.compile_regsBelow 400 _ rb Layout.builderBase i hi) (by decide)

theorem descriptor_numeric (model : InputModel) :
    ∀ i ∈ Descriptor.code model, NumericBelow 8273 i := by
  cases model <;> simp [Descriptor.code, NumericBelow, Prim.destination?]

theorem descriptor_key_free (model : InputModel) :
    ∀ i ∈ Descriptor.code model, KeyBelow 0 i := by
  cases model <;> simp [Descriptor.code, KeyBelow]

theorem finalizer_numeric (base : Nat) (bound : base+14 < 2^32) :
    ∀ i ∈ Finalizer.code base bound, NumericBelow 8273 i := by
  simp [Finalizer.code, NumericBelow, Prim.destination?]

theorem finalizer_key_free (base : Nat) (bound : base+14 < 2^32) :
    ∀ i ∈ Finalizer.code base bound, KeyBelow 0 i := by
  simp [Finalizer.code, KeyBelow]

theorem retirement_numeric (base : Nat) (bound : base+8 < 2^32) :
    ∀ i ∈ Retirement.code base bound, NumericBelow 8273 i := by
  simp [Retirement.code, NumericBelow, Prim.destination?]

theorem retirement_key_free (base : Nat) (bound : base+8 < 2^32) :
    ∀ i ∈ Retirement.code base bound, KeyBelow 0 i := by
  simp [Retirement.code, KeyBelow]

/-- Every canonical instruction has a numeric destination in the actual bank.
The query bound is structural, not a reflection pass over the large program. -/
theorem program_numeric (model : InputModel) :
    ∀ i ∈ Layout.program model, NumericBelow 8273 i := by
  intro i hi
  rw [Layout.program] at hi
  rcases List.mem_append.mp hi with prefixMember | tail
  · obtain ⟨old, member, rfl⟩ := List.mem_map.mp prefixMember
    rw [Layout.oldPrefix] at member
    rcases List.mem_append.mp member with service | rest
    · obtain ⟨query, serviceMember, rfl⟩ := List.mem_map.mp service
      exact translated_numeric query (ServiceSafety.program_writes query serviceMember)
    · rcases List.mem_append.mp rest with builder | descriptor
      · exact builder_numeric model old builder
      · apply descriptor_numeric model
        rw [Descriptor.code_eq]
        exact List.mem_map.mpr ⟨old, descriptor, rfl⟩
  · rw [Layout.tail] at tail
    rcases List.mem_append.mp tail with finalizer | rest
    · exact finalizer_numeric _ _ i finalizer
    · rcases List.mem_append.mp rest with retirement | jump
      · cases model with
        | word => cases retirement
        | comparison => exact retirement_numeric Layout.retirementBase (by decide) i retirement
      · have equal := List.mem_singleton.mp jump
        subst i
        simp [NumericBelow, Prim.destination?]

theorem body_keys_fit {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (body : Construction.Body model xs left right abstract producer ts) :
    TraceKeysFit (Construction.producedTrace model xs left right ts) := by
  have keys := hosted_key_trace body rfl (Layout.old_builder_host model)
    (Construction.source_bound model)
  intro t ht i hi
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp ht
  change Action.instruction (oldInstruction old.instruction) = .instruction i at hi
  have eq := Action.instruction.inj hi
  subst i
  change KeyBelow (if model = .comparison then 2 else 0) (oldInstruction old.instruction)
  have bound := keys old member
  cases model with
  | word => simpa only [InputModel.source, Builder.word_keyRegister_limit] using bound
  | comparison => simpa only [InputModel.source, Builder.comparison_keyRegister_limit] using bound

theorem trace_keys_of_uses {code : List Instruction} {r : Run}
    (free : ∀ i ∈ code, KeyBelow 0 i)
    (uses : ∀ t ∈ r.transitions, ∃ i ∈ code, t.action = .instruction i) :
    TraceKeysFit r.transitions := by
  apply traceKeysFit_of_key_free
  intro t ht i hi
  obtain ⟨actual, member, action⟩ := uses t ht
  rw [hi] at action
  have eq := Action.instruction.inj action
  subst actual
  exact free i member

theorem finalization_keys_fit {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    TraceKeysFit (Finalization.finalTrace model xs left right producer) := by
  have descriptor : TraceKeysFit (Finalization.descriptorRun model xs left right producer).transitions :=
    trace_keys_of_uses (descriptor_key_free model)
      (Descriptor.execution_shape (Layout.descriptor_host model) built.descriptor).1
  have copy : TraceKeysFit (Finalization.copyRun model xs left right producer).transitions :=
    trace_keys_of_uses (finalizer_key_free _ _)
      (Finalizer.finalizer_uses (Layout.finalizer_host model)
        (Finalization.descriptor_to_finalizer built))
  have retirement : TraceKeysFit (Finalization.retirementRun model xs left right producer).transitions := by
    cases model with
    | word => intro t ht; cases ht
    | comparison =>
        have copied := (Finalization.copy_stage built).1
        have entry : Retirement.Entry Layout.retirementBase xs.length
            (Finalization.copyRun .comparison xs left right producer).final :=
          ⟨copied.running, copied.pc, copied.keyExtent, copied.keyRegExtent, copied.size, copied.closed⟩
        obtain ⟨_, _, _, _, _, _, uses⟩ := Retirement.comparison_run Layout.retirement_host entry
        exact trace_keys_of_uses (retirement_key_free _ _) uses
  intro t ht i hi
  simp only [Finalization.finalTrace, List.mem_append, List.mem_singleton] at ht
  rcases ht with ((ht | ht) | ht) | rfl
  · exact descriptor t ht i hi
  · exact copy t ht i hi
  · exact retirement t ht i hi
  · cases hi
    trivial

theorem full_keys_fit {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    TraceKeysFit (Finalization.fullTrace model xs left right producer ts) :=
  traceKeysFit_append (body_keys_fit built.body) (finalization_keys_fit built)

theorem full_destinations_fit {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    TraceDestinationsFit 8273
      (run (Layout.program model) (Finalization.fullTrace model xs left right producer ts).length
        (initialState model xs left right Layout.builderBase)).transitions := by
  apply traceDestinations_of_keys (program_numeric model)
  rw [show run (Layout.program model) (Finalization.fullTrace model xs left right producer ts).length
      (initialState model xs left right Layout.builderBase) =
      ⟨Finalization.finalState model xs left right producer,
        Finalization.fullTrace model xs left right producer ts⟩ from Finalization.full_execution built]
  exact full_keys_fit built

/-- Production execution retains only arrays/control. The state equality and
the numeric-array length are both needed, since abstraction forgets capacity. -/
theorem preparation_owner_refinement {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    let fuel := (Finalization.fullTrace model xs left right producer ts).length
    let final := runOwner (Layout.program model).toArray fuel (initialOwner model xs left right)
    final.toState = Finalization.finalState model xs left right producer ∧ final.regs.size = 8273 := by
  have bounds : TraceDestinationsFit 8273
      (run (Layout.program model) (Finalization.fullTrace model xs left right producer ts).length
        (initialOwner model xs left right).toState).transitions := by
    rw [initialOwner_toState]
    exact full_destinations_fit built
  have refined := runOwner_toState_of_abstract (Layout.program model)
    (Finalization.fullTrace model xs left right producer ts).length (initialOwner model xs left right)
    8273 (initialOwner_regs_size model xs left right) bounds
  rw [initialOwner_toState, show run (Layout.program model)
      (Finalization.fullTrace model xs left right producer ts).length
      (initialState model xs left right Layout.builderBase) =
      ⟨Finalization.finalState model xs left right producer,
        Finalization.fullTrace model xs left right producer ts⟩ from Finalization.full_execution built] at refined
  exact refined

/-- Optional observations preserve the same complete run, including ordered
states and instructions; the production owner theorem above retains no history. -/
theorem preparation_array_refinement {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    let fuel := (Finalization.fullTrace model xs left right producer ts).length
    let actual := runArray (Layout.program model).toArray fuel (initialOwner model xs left right)
    actual.toRun = ⟨Finalization.finalState model xs left right producer,
      Finalization.fullTrace model xs left right producer ts⟩ ∧ actual.final.regs.size = 8273 := by
  have bounds : TraceDestinationsFit 8273
      (run (Layout.program model) (Finalization.fullTrace model xs left right producer ts).length
        (initialOwner model xs left right).toState).transitions := by
    rw [initialOwner_toState]
    exact full_destinations_fit built
  have refined := runArray_toState_of_abstract (Layout.program model)
    (Finalization.fullTrace model xs left right producer ts).length (initialOwner model xs left right)
    8273 (initialOwner_regs_size model xs left right) bounds
  rw [initialOwner_toState, show run (Layout.program model)
      (Finalization.fullTrace model xs left right producer ts).length
      (initialState model xs left right Layout.builderBase) =
      ⟨Finalization.finalState model xs left right producer,
        Finalization.fullTrace model xs left right producer ts⟩ from Finalization.full_execution built] at refined
  exact refined

theorem entered_of_inputs (left right : Nat) (s : State)
    (inputs : Service.Inputs left right (Retained.projectQueryState s)) :
    ServiceSafety.Entered left right s := by
  refine ⟨?_, inputs.2.1, inputs.2.2.1, inputs.2.2.2.1⟩
  have hr := inputs.1
  cases status : s.core.status <;>
    simp_all [Retained.projectQueryState, Retained.projectStatus]

theorem service_keys_fit (model : InputModel) (xs : List Int) (left right fuel : Nat) (s : State)
    (canonical : Retained.Canonical xs s) (entered : ServiceSafety.Entered left right s)
    (within : fuel ≤ Service.budget) :
    TraceKeysFit (run (Layout.program model) fuel s).transitions := by
  rw [Layout.service_split]
  change TraceKeysFit (run (QuerySafetyBridge.host Service.program
    ((Layout.builderCode model ++ Descriptor.coreCode model).map oldInstruction ++ Layout.tail model))
    fuel s).transitions
  rw [ServiceSafety.actual_prefix xs _ left right fuel s canonical entered within]
  intro t ht i hi
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp ht
  change Action.instruction (oldInstruction (PackedConstruction.Conservative.translate old.instruction)) =
    .instruction i at hi
  have eq := Action.instruction.inj hi
  subst i
  exact translated_key_free old.instruction

theorem service_stopped (model : InputModel) (xs : List Int) (left right : Nat) (s : State)
    (canonical : Retained.Canonical xs s) (entered : ServiceSafety.Entered left right s) :
    (run (Layout.program model) Service.budget s).final.core.status ≠ .running := by
  rw [Layout.service_split]
  change (run (QuerySafetyBridge.host Service.program
    ((Layout.builderCode model ++ Descriptor.coreCode model).map oldInstruction ++ Layout.tail model))
    Service.budget s).final.core.status ≠ .running
  rw [ServiceSafety.actual_prefix xs _ left right Service.budget s canonical entered (Nat.le_refl _)]
  have stopped := ServiceSafety.stopped xs left right (Retained.projectQueryState s)
    (ServiceSafety.entered_inputs xs left right s canonical entered)
  cases status : (PackedWordRAM.run (PackedWordRAM.buildMemory xs) Service.program Service.budget
      (Retained.projectQueryState s)).final.status <;>
    simp_all [QuerySafetyBridge.embedded, ofCore, PackedConstruction.Conservative.state,
      PackedConstruction.Conservative.status]

theorem first_query_keys_fit {model : InputModel} {xs : List Int} {left right queryFuel : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts)
    (within : queryFuel ≤ Service.budget) :
    TraceKeysFit (run (Layout.program model)
      ((Finalization.fullTrace model xs left right producer ts).length + queryFuel)
      (initialState model xs left right Layout.builderBase)).transitions := by
  rw [run_add, show run (Layout.program model)
      (Finalization.fullTrace model xs left right producer ts).length
      (initialState model xs left right Layout.builderBase) =
      ⟨Finalization.finalState model xs left right producer,
        Finalization.fullTrace model xs left right producer ts⟩ from Finalization.full_execution built]
  have completed := Finalization.completed built
  exact traceKeysFit_append (full_keys_fit built)
    (service_keys_fit model xs left right queryFuel _ completed.2.1
      (entered_of_inputs left right _ completed.2.2.1) within)

theorem first_query_stopped {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    (run (Layout.program model)
      ((Finalization.fullTrace model xs left right producer ts).length + Service.budget)
      (initialState model xs left right Layout.builderBase)).final.core.status ≠ .running := by
  rw [run_add, show run (Layout.program model)
      (Finalization.fullTrace model xs left right producer ts).length
      (initialState model xs left right Layout.builderBase) =
      ⟨Finalization.finalState model xs left right producer,
        Finalization.fullTrace model xs left right producer ts⟩ from Finalization.full_execution built]
  have completed := Finalization.completed built
  dsimp only
  exact service_stopped model xs left right (Finalization.finalState model xs left right producer) completed.2.1
    (entered_of_inputs left right _ completed.2.2.1)

theorem trace_keys_prefix (program : List Instruction) (s : State) {fuel total : Nat}
    (within : fuel ≤ total) (keys : TraceKeysFit (run program total s).transitions) :
    TraceKeysFit (run program fuel s).transitions := by
  intro t ht i hi
  apply keys t _ i hi
  rw [← Nat.add_sub_of_le within, run_add]
  exact List.mem_append_left _ ht

/-- All actual canonical prefixes satisfy their current bank bounds. Once the
first query stops, additional fuel cannot introduce a further instruction. -/
theorem canonical_keys_fit {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) (fuel : Nat) :
    TraceKeysFit (run (Layout.program model) fuel
      (initialState model xs left right Layout.builderBase)).transitions := by
  let total := (Finalization.fullTrace model xs left right producer ts).length + Service.budget
  have keys := first_query_keys_fit built (Nat.le_refl Service.budget)
  by_cases within : fuel ≤ total
  · exact trace_keys_prefix _ _ within keys
  · have split : fuel = total + (fuel-total) := by omega
    have stopped : (run (Layout.program model) total
        (initialState model xs left right Layout.builderBase)).final.core.status ≠ .running :=
      first_query_stopped built
    rw [split, run_add]
    dsimp only
    rw [run_of_stopped _ _ _ stopped]
    simpa only [List.append_nil] using keys

theorem canonical_destinations_fit {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) (fuel : Nat) :
    TraceDestinationsFit 8273 (run (Layout.program model) fuel
      (initialState model xs left right Layout.builderBase)).transitions :=
  traceDestinations_of_keys (program_numeric model) (canonical_keys_fit built fuel)

/-- Arbitrary fuel, actual whole program, supplied finite owner, and no
unchecked destination guard in the consumer's assumptions. -/
theorem canonical_owner_refinement {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) (fuel : Nat) :
    (runOwner (Layout.program model).toArray fuel (initialOwner model xs left right)).toState =
      (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final ∧
    (runOwner (Layout.program model).toArray fuel (initialOwner model xs left right)).regs.size = 8273 := by
  have bounds : TraceDestinationsFit 8273
      (run (Layout.program model) fuel (initialOwner model xs left right).toState).transitions := by
    rw [initialOwner_toState]
    exact canonical_destinations_fit built fuel
  simpa only [initialOwner_toState] using runOwner_toState_of_abstract (Layout.program model) fuel
    (initialOwner model xs left right) 8273 (initialOwner_regs_size model xs left right) bounds

theorem canonical_array_refinement {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) (fuel : Nat) :
    (runArray (Layout.program model).toArray fuel (initialOwner model xs left right)).toRun =
      run (Layout.program model) fuel (initialState model xs left right Layout.builderBase) ∧
    (runArray (Layout.program model).toArray fuel (initialOwner model xs left right)).final.regs.size = 8273 := by
  have bounds : TraceDestinationsFit 8273
      (run (Layout.program model) fuel (initialOwner model xs left right).toState).transitions := by
    rw [initialOwner_toState]
    exact canonical_destinations_fit built fuel
  simpa only [initialOwner_toState] using runArray_toState_of_abstract (Layout.program model) fuel
    (initialOwner model xs left right) 8273 (initialOwner_regs_size model xs left right) bounds

/-- The construction witness and every destination bound are derived from the
represented input contract. No output state, answer, or trace is supplied. -/
theorem initial_destinations_fit (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs)
    (hl : left < 2^PackedWordRAM.wordWidth xs.length)
    (hr : right < 2^PackedWordRAM.wordWidth xs.length) (fuel : Nat) :
    TraceDestinationsFit 8273 (run (Layout.program model) fuel
      (initialState model xs left right Layout.builderBase)).transitions := by
  obtain ⟨abstract, producer, ts, built⟩ := Construction.build_stage model xs left right domain hl hr
  exact canonical_destinations_fit built fuel

theorem initial_owner_refinement (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs)
    (hl : left < 2^PackedWordRAM.wordWidth xs.length)
    (hr : right < 2^PackedWordRAM.wordWidth xs.length) (fuel : Nat) :
    (runOwner (Layout.program model).toArray fuel (initialOwner model xs left right)).toState =
      (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final ∧
    (runOwner (Layout.program model).toArray fuel (initialOwner model xs left right)).regs.size = 8273 := by
  obtain ⟨abstract, producer, ts, built⟩ := Construction.build_stage model xs left right domain hl hr
  exact canonical_owner_refinement built fuel

theorem initial_array_refinement (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs)
    (hl : left < 2^PackedWordRAM.wordWidth xs.length)
    (hr : right < 2^PackedWordRAM.wordWidth xs.length) (fuel : Nat) :
    (runArray (Layout.program model).toArray fuel (initialOwner model xs left right)).toRun =
      run (Layout.program model) fuel (initialState model xs left right Layout.builderBase) ∧
    (runArray (Layout.program model).toArray fuel (initialOwner model xs left right)).final.regs.size = 8273 := by
  obtain ⟨abstract, producer, ts, built⟩ := Construction.build_stage model xs left right domain hl hr
  exact canonical_array_refinement built fuel

theorem service_keys_all_fuel (model : InputModel) (xs : List Int) (left right fuel : Nat) (s : State)
    (canonical : Retained.Canonical xs s) (entered : ServiceSafety.Entered left right s) :
    TraceKeysFit (run (Layout.program model) fuel s).transitions := by
  by_cases within : fuel ≤ Service.budget
  · exact service_keys_fit model xs left right fuel s canonical entered within
  · have split : fuel = Service.budget + (fuel-Service.budget) := by omega
    rw [split, run_add]
    dsimp only
    rw [run_of_stopped _ _ _ (service_stopped model xs left right s canonical entered)]
    simpa only [List.append_nil] using
      service_keys_fit model xs left right Service.budget s canonical entered (Nat.le_refl _)

/-- The retained finite owner may come from any prior query. Its bank capacity,
canonical data and charged entry state suffice; its other registers may be dirty. -/
theorem service_owner_refinement (model : InputModel) (xs : List Int) (left right fuel : Nat)
    (owner : Owner) (bank : owner.regs.size = 8273)
    (canonical : Retained.Canonical xs owner.toState)
    (entered : ServiceSafety.Entered left right owner.toState) :
    (runOwner (Layout.program model).toArray fuel owner).toState =
      (run (Layout.program model) fuel owner.toState).final ∧
    (runOwner (Layout.program model).toArray fuel owner).regs.size = 8273 :=
  runOwner_toState_of_abstract (Layout.program model) fuel owner 8273 bank
    (traceDestinations_of_keys (program_numeric model)
      (service_keys_all_fuel model xs left right fuel owner.toState canonical entered))

theorem service_array_refinement (model : InputModel) (xs : List Int) (left right fuel : Nat)
    (owner : Owner) (bank : owner.regs.size = 8273)
    (canonical : Retained.Canonical xs owner.toState)
    (entered : ServiceSafety.Entered left right owner.toState) :
    (runArray (Layout.program model).toArray fuel owner).toRun =
      run (Layout.program model) fuel owner.toState ∧
    (runArray (Layout.program model).toArray fuel owner).final.regs.size = 8273 :=
  runArray_toState_of_abstract (Layout.program model) fuel owner 8273 bank
    (traceDestinations_of_keys (program_numeric model)
      (service_keys_all_fuel model xs left right fuel owner.toState canonical entered))

def queryOwner (model : InputModel) (left right : Nat) (owner : Owner) : Owner :=
  runOwner (Layout.program model).toArray Service.budget
    (requestProtocolOwner Layout.serviceEntry left right owner)

def queryArray (model : InputModel) (left right : Nat) (owner : Owner) : ArrayRun :=
  let admission := requestProtocolArray Layout.serviceEntry left right owner
  let service := runArray (Layout.program model).toArray Service.budget admission.final
  ⟨service.final, admission.transitions ++ service.transitions⟩

theorem queryOwner_projection (model : InputModel) (left right : Nat) (owner : Owner) :
    queryOwner model left right owner = (queryArray model left right owner).final := by
  unfold queryOwner queryArray requestProtocolOwner requestProtocolArray
  rw [runBoundaryOwner_projection, runOwner_projection]

private theorem append_array_toRun (first second : ArrayRun) :
    (⟨second.final, first.transitions ++ second.transitions⟩ : ArrayRun).toRun =
      ⟨second.toRun.final, first.toRun.transitions ++ second.toRun.transitions⟩ := by
  simp [ArrayRun.toRun, List.map_append]

/-- The exact four charged boundary transitions are preserved along with the
same subsequent scalar service trace, even when the incoming bank is dirty. -/
theorem query_array_refinement (model : InputModel) (xs : List Int) (left right answer : Nat)
    (owner : Owner) (bank : owner.regs.size = 8273)
    (canonical : Retained.Canonical xs owner.toState)
    (halted : owner.status = .halted answer)
    (hl : left < 2^PackedWordRAM.wordWidth xs.length)
    (hr : right < 2^PackedWordRAM.wordWidth xs.length) :
    (queryArray model left right owner).toRun = Reusable.queryRun model left right owner.toState ∧
    (queryArray model left right owner).final.regs.size = 8273 := by
  have hleft : requestLeftRegister < owner.regs.size := by rw [bank]; decide
  have hright : requestRightRegister < owner.regs.size := by rw [bank]; decide
  have admission := requestProtocolArray_toState Layout.serviceEntry left right owner hleft hright
  have admittedState : (requestProtocolArray Layout.serviceEntry left right owner).final.toState =
      (requestProtocol Layout.serviceEntry left right owner.toState).final :=
    congrArg Run.final admission
  have width : Layout.serviceEntry.val < 2^PackedWordRAM.wordWidth xs.length :=
    Nat.lt_trans (Reusable.entry_inside model) (Reusable.program_fits model xs.length)
  have admittedCanonical : Retained.Canonical xs
      (requestProtocolArray Layout.serviceEntry left right owner).final.toState := by
    rw [admittedState]
    exact canonical.requestProtocol Layout.serviceEntry left right (Layout.program model).length
      hl hr (Reusable.entry_inside model) width
  have entered : ServiceSafety.Entered left right
      (requestProtocolArray Layout.serviceEntry left right owner).final.toState := by
    rw [admittedState]
    exact Reusable.entered_after_admission left right answer owner.toState halted
  have admittedBank : (requestProtocolArray Layout.serviceEntry left right owner).final.regs.size = 8273 :=
    (requestProtocolArray_regs_size Layout.serviceEntry left right owner).trans bank
  have service := service_array_refinement model xs left right Service.budget
    (requestProtocolArray Layout.serviceEntry left right owner).final admittedBank admittedCanonical entered
  refine ⟨?_, service.2⟩
  unfold queryArray
  rw [append_array_toRun, service.1, admittedState, admission]
  rfl

/-- The production query runner retains only its final arrays/control. -/
theorem query_owner_refinement (model : InputModel) (xs : List Int) (left right answer : Nat)
    (owner : Owner) (bank : owner.regs.size = 8273)
    (canonical : Retained.Canonical xs owner.toState)
    (halted : owner.status = .halted answer)
    (hl : left < 2^PackedWordRAM.wordWidth xs.length)
    (hr : right < 2^PackedWordRAM.wordWidth xs.length) :
    (queryOwner model left right owner).toState =
      (Reusable.queryRun model left right owner.toState).final ∧
    (queryOwner model left right owner).regs.size = 8273 := by
  have full := query_array_refinement model xs left right answer owner bank canonical halted hl hr
  rw [queryOwner_projection]
  exact ⟨congrArg Run.final full.1, full.2⟩

end RMQ.SuccinctFinal.PackedLifecycle.Executable
