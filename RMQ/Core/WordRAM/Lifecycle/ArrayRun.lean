import RMQ.Core.WordRAM.Lifecycle.Calculus
import RMQ.Core.WordRAM.Construction.ArrayRun

/-! # Finite-container lifecycle execution

The retained `Owner` contains only numeric/key arrays and scalar control. Optional
validation transitions are separate from this owner. Array sizes describe logical
ownership; no theorem here identifies native allocation capacity or external aliases.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle

open PackedConstruction (Prim Operand put execPrim execPrimArray)

abbrev Owner := PackedConstruction.ExecState

def Owner.toState (es : Owner) : State :=
  ⟨es.abstract, es.keys.size, es.keyRegs.size⟩

@[simp] theorem Owner.toState_pc (es : Owner) : es.toState.core.pc = es.pc := rfl
@[simp] theorem Owner.toState_status (es : Owner) : es.toState.core.status = es.status := rfl

/-- Reads use the same default outside a finite bank. Only destinations need a
bound; numeric and comparison-key banks can have different sizes, including zero. -/
def destinationsBelow (R K : Nat) : Prim → Prop
  | .load dst _ | .constant dst _ | .move dst _ | .arithmetic _ dst _ _
  | .comparison _ dst _ _ | .reserve dst | .compareKey dst _ _ => dst.val < R
  | .loadKey dst _ => dst.val < K
  | .jump _ | .jumpRegister _ | .branchZero _ _ | .halt _ | .store _ _ => True

def Instruction.DestinationsFit (i : Instruction) (es : Owner) : Prop :=
  match i with
  | .old p => destinationsBelow es.regs.size es.keyRegs.size p
  | _ => True

def Boundary.DestinationsFit (b : Boundary) (es : Owner) : Prop :=
  match b with
  | .left _ => requestLeftRegister < es.regs.size
  | .right _ => requestRightRegister < es.regs.size
  | .entry _ | .activate => True

private theorem lookup_set {α : Type} (xs : Array α) (i : Nat) (v d : α)
    (hi : i < xs.size) :
    (fun j => (xs.setIfInBounds i v).getD j d) = put (fun j => xs.getD j d) i v := by
  funext j
  simp only [put, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : j = i
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

private theorem lookup_push_none {α : Type} (xs : Array (Option α)) :
    (fun j => (xs.push none).getD j none) = fun j => xs.getD j none := by
  funext j
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases h : j = xs.size
  · subst h; simp
  · simp [h]

/-- A pop removes exactly the tail lookup, including when earlier cells already
contain the default. The nonempty guard is discharged by the release evaluator. -/
theorem lookup_pop {α : Type} (xs : Array α) (d : α) (h : 0 < xs.size) :
    (fun j => xs.pop.getD j d) = put (fun j => xs.getD j d) (xs.size - 1) d := by
  funext j
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_pop, put]
  by_cases hj : j < xs.size - 1
  · simp [hj, show j ≠ xs.size - 1 by omega]
  · by_cases he : j = xs.size - 1
    · simp [he]
    · have hh : xs.size ≤ j := by omega
      simp [hj, he, Array.getElem?_eq_none hh]

private theorem numeric_write (es : Owner) (dst value : Nat) (h : dst < es.regs.size) :
    ({ es with regs := es.regs.setIfInBounds dst value, pc := es.pc + 1 } : Owner).abstract =
      es.abstract.writeNext dst value := by
  simp only [PackedConstruction.ExecState.abstract, PackedConstruction.State.writeNext,
    PackedConstruction.State.next, lookup_set _ _ _ _ h]

private theorem key_write (es : Owner) (dst : Nat) (value : Int)
    (h : dst < es.keyRegs.size) :
    ({ es with keyRegs := es.keyRegs.setIfInBounds dst value, pc := es.pc + 1 } : Owner).abstract =
      { es.abstract.next with keyRegs := put es.abstract.keyRegs dst value } := by
  simp only [PackedConstruction.ExecState.abstract, PackedConstruction.State.next,
    lookup_set _ _ _ _ h]

/-- The old executable evaluator is reused unchanged. Unlike its predecessor
wrapper, this refinement does not require equal numeric/key register banks. -/
theorem oldArray_core (p : Prim) (es : Owner)
    (hp : destinationsBelow es.regs.size es.keyRegs.size p) :
    (execPrimArray p es).abstract = execPrim p es.abstract := by
  cases p with
  | load dst address =>
      simp only [execPrimArray, execPrim, PackedConstruction.ExecState.abstract]
      by_cases ha : es.regs.getD address.val 0 < es.memory.size
      · rw [if_pos ha, if_pos ha]
        cases es.memory.getD (es.regs.getD address.val 0) none with
        | some value => exact numeric_write es _ _ hp
        | none => rfl
      · rw [if_neg ha, if_neg ha]
  | constant dst value => exact numeric_write es _ _ hp
  | move dst src => exact numeric_write es _ _ hp
  | arithmetic op dst lhs rhs => exact numeric_write es _ _ hp
  | comparison op dst lhs rhs => exact numeric_write es _ _ hp
  | jump target => rfl
  | jumpRegister src => rfl
  | branchZero condition target => rfl
  | halt src => rfl
  | store address value =>
      simp only [execPrimArray, execPrim, PackedConstruction.ExecState.abstract]
      by_cases ha : es.regs.getD address.val 0 < es.memory.size
      · rw [if_pos ha, if_pos ha]
        simp only [PackedConstruction.State.next,
          lookup_set _ _ _ _ ha, Array.size_setIfInBounds]
      · rw [if_neg ha, if_neg ha]
  | reserve dst =>
      simp only [execPrimArray, execPrim, PackedConstruction.ExecState.abstract,
        PackedConstruction.State.writeNext, PackedConstruction.State.next,
        lookup_set _ _ _ _ hp, lookup_push_none, Array.size_push]
  | loadKey dst address =>
      simp only [execPrimArray, execPrim, PackedConstruction.ExecState.abstract]
      cases es.keys.getD (es.regs.getD address.val 0) none with
      | some key => exact key_write es _ key hp
      | none => rfl
  | compareKey dst lhs rhs => exact numeric_write es _ _ hp

theorem oldArray_bank_sizes (p : Prim) (es : Owner) :
    (execPrimArray p es).regs.size = es.regs.size ∧
    (execPrimArray p es).keys.size = es.keys.size ∧
    (execPrimArray p es).keyRegs.size = es.keyRegs.size := by
  cases p <;> simp only [execPrimArray]
  all_goals repeat first | split | exact ⟨rfl, rfl, rfl⟩ |
    exact ⟨Array.size_setIfInBounds, rfl, rfl⟩ |
    exact ⟨rfl, rfl, Array.size_setIfInBounds⟩ |
    simp only [Array.size_setIfInBounds, and_self]

def executeArray : Instruction → Owner → Owner
  | .old p, es => execPrimArray p es
  | .releaseCell, es =>
      if es.memory.size = 0 then { es with status := .fault }
      else { es with memory := es.memory.pop, pc := es.pc + 1 }
  | .releaseKey, es =>
      if es.keys.size = 0 then { es with status := .fault }
      else { es with keys := es.keys.pop, pc := es.pc + 1 }
  | .releaseKeyRegister, es =>
      if es.keyRegs.size = 0 then { es with status := .fault }
      else { es with keyRegs := es.keyRegs.pop, pc := es.pc + 1 }

theorem executeArray_toState (i : Instruction) (es : Owner)
    (h : i.DestinationsFit es) :
    (executeArray i es).toState = execute i es.toState := by
  cases i with
  | old p =>
      simp only [executeArray, execute, Owner.toState, oldArray_core p es h,
        (oldArray_bank_sizes p es).2.1, (oldArray_bank_sizes p es).2.2]
  | releaseCell =>
      by_cases hz : es.memory.size = 0
      · simp [executeArray, execute, Owner.toState, PackedConstruction.ExecState.abstract, hz]
      · simp [executeArray, execute, Owner.toState, PackedConstruction.ExecState.abstract,
          PackedConstruction.State.next, hz]
        simpa only [Array.getD_eq_getD_getElem?] using lookup_pop es.memory none (by omega)
  | releaseKey =>
      by_cases hz : es.keys.size = 0
      · simp [executeArray, execute, Owner.toState, PackedConstruction.ExecState.abstract, hz]
      · simp [executeArray, execute, Owner.toState, PackedConstruction.ExecState.abstract,
          PackedConstruction.State.next, hz]
        simpa only [Array.getD_eq_getD_getElem?] using lookup_pop es.keys none (by omega)
  | releaseKeyRegister =>
      by_cases hz : es.keyRegs.size = 0
      · simp [executeArray, execute, Owner.toState, PackedConstruction.ExecState.abstract, hz]
      · simp [executeArray, execute, Owner.toState, PackedConstruction.ExecState.abstract,
          PackedConstruction.State.next, hz]
        simpa only [Array.getD_eq_getD_getElem?] using lookup_pop es.keyRegs 0 (by omega)

def executeBoundaryArray : Boundary → Owner → Owner
  | .left value, es => { es with regs := es.regs.setIfInBounds requestLeftRegister value }
  | .right value, es => { es with regs := es.regs.setIfInBounds requestRightRegister value }
  | .entry target, es => { es with pc := target }
  | .activate, es => { es with status := .running }

theorem executeBoundaryArray_toState (b : Boundary) (es : Owner)
    (h : b.DestinationsFit es) :
    (executeBoundaryArray b es).toState = executeBoundary b es.toState := by
  cases b <;> simp only [executeBoundaryArray, executeBoundary, Owner.toState,
    PackedConstruction.ExecState.abstract]
  · rw [lookup_set _ _ _ _ h]
  · rw [lookup_set _ _ _ _ h]

theorem Owner.closed (es : Owner) : es.toState.Closed := by
  refine ⟨es.abstract_cleanTail, ?_, ?_⟩
  · intro a ha
    change es.keys.getD a none = none
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none ha]
  · intro a ha
    change es.keyRegs.getD a 0 = 0
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none ha]

theorem Owner.key_banks_empty (es : Owner)
    (hk : es.toState.keyExtent = 0) (hr : es.toState.keyRegExtent = 0) :
    es.keys = #[] ∧ es.keyRegs = #[] :=
  ⟨Array.eq_empty_of_size_eq_zero hk, Array.eq_empty_of_size_eq_zero hr⟩

theorem Owner.numeric_register_tail (es : Owner) (r : Nat) (h : es.regs.size ≤ r) :
    es.toState.core.regs r = 0 := by
  change es.regs.getD r 0 = 0
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

theorem executeArray_regs_size (i : Instruction) (es : Owner) :
    (executeArray i es).regs.size = es.regs.size := by
  cases i with
  | old p => exact (oldArray_bank_sizes p es).1
  | releaseCell => simp [executeArray]; split <;> rfl
  | releaseKey => simp [executeArray]; split <;> rfl
  | releaseKeyRegister => simp [executeArray]; split <;> rfl

theorem executeBoundaryArray_regs_size (b : Boundary) (es : Owner) :
    (executeBoundaryArray b es).regs.size = es.regs.size := by
  cases b <;> simp [executeBoundaryArray]

/-- Optional validation observations preserve full producing states and action
identity. They are never fields of the retained owner. -/
structure ArrayTransition where
  before : Owner
  action : Action
  after : Owner

def ArrayTransition.toTransition (t : ArrayTransition) : Transition :=
  ⟨t.before.toState, t.action, t.after.toState⟩

def stepArray (program : Array Instruction) (es : Owner) : Option ArrayTransition :=
  if es.status = .running then
    (program[es.pc]?).map fun i => ⟨es, .instruction i, executeArray i es⟩
  else none

def boundaryStepArray (b : Boundary) (es : Owner) : Option ArrayTransition :=
  match es.status with
  | .halted _ => some ⟨es, .boundary b, executeBoundaryArray b es⟩
  | _ => none

def StepDestinationsFit (program : Array Instruction) (es : Owner) : Prop :=
  ∀ i, es.status = .running → program[es.pc]? = some i → i.DestinationsFit es

theorem stepArray_toState (program : List Instruction) (es : Owner)
    (h : StepDestinationsFit program.toArray es) :
    (stepArray program.toArray es).map ArrayTransition.toTransition = step program es.toState := by
  by_cases hs : es.status = .running
  · cases hf : program[es.pc]? with
    | none => simp [stepArray, step, hs, hf]
    | some i =>
        have hi : i.DestinationsFit es := h i hs (by simpa using hf)
        simp [stepArray, step, hs, hf, ArrayTransition.toTransition, executeArray_toState i es hi]
  · simp [stepArray, step, hs]

theorem boundaryStepArray_toState (b : Boundary) (es : Owner)
    (h : b.DestinationsFit es) :
    (boundaryStepArray b es).map ArrayTransition.toTransition = boundaryStep b es.toState := by
  cases hs : es.status <;>
    simp [boundaryStepArray, boundaryStep, hs, ArrayTransition.toTransition,
      executeBoundaryArray_toState b es h]

structure ArrayRun where
  final : Owner
  transitions : List ArrayTransition

def ArrayRun.toRun (r : ArrayRun) : Run :=
  ⟨r.final.toState, r.transitions.map ArrayTransition.toTransition⟩

def runArray (program : Array Instruction) : Nat → Owner → ArrayRun
  | 0, es => ⟨es, []⟩
  | fuel + 1, es =>
      match stepArray program es with
      | none => ⟨es, []⟩
      | some t => let rest := runArray program fuel t.after
                  ⟨rest.final, t :: rest.transitions⟩

/-- Bounds only on destinations of instructions actually encountered. This
condition contains no answer, memory-equality or completion assumption. -/
def RunDestinationsFit (program : Array Instruction) : Nat → Owner → Prop
  | 0, _ => True
  | fuel + 1, es => StepDestinationsFit program es ∧
      match stepArray program es with
      | none => True
      | some t => RunDestinationsFit program fuel t.after

theorem runArray_toState (program : List Instruction) (fuel : Nat) (es : Owner)
    (h : RunDestinationsFit program.toArray fuel es) :
    (runArray program.toArray fuel es).toRun = run program fuel es.toState := by
  induction fuel generalizing es with
  | zero => rfl
  | succ fuel ih =>
      obtain ⟨hstep, hrest⟩ := h
      have hs := stepArray_toState program es hstep
      cases he : stepArray program.toArray es with
      | none =>
          have ha : step program es.toState = none := by simpa [he] using hs.symm
          simp [runArray, run, he, ha, ArrayRun.toRun]
      | some t =>
          have ha : step program es.toState = some t.toTransition := by simpa [he] using hs.symm
          have hr := ih t.after (by simpa [he] using hrest)
          simpa only [runArray, he, run, ha, ArrayRun.toRun, List.map_cons,
            ArrayTransition.toTransition] using
            congrArg (fun r : Run => Run.mk r.final (t.toTransition :: r.transitions)) hr

def runBoundaryArray : List Boundary → Owner → ArrayRun
  | [], es => ⟨es, []⟩
  | b :: bs, es =>
      match boundaryStepArray b es with
      | none => ⟨es, []⟩
      | some t => let rest := runBoundaryArray bs t.after
                  ⟨rest.final, t :: rest.transitions⟩

def BoundaryRunDestinationsFit : List Boundary → Owner → Prop
  | [], _ => True
  | b :: bs, es => b.DestinationsFit es ∧
      match boundaryStepArray b es with
      | none => True
      | some t => BoundaryRunDestinationsFit bs t.after

theorem runBoundaryArray_toState (bs : List Boundary) (es : Owner)
    (h : BoundaryRunDestinationsFit bs es) :
    (runBoundaryArray bs es).toRun = runBoundary bs es.toState := by
  induction bs generalizing es with
  | nil => rfl
  | cons b bs ih =>
      obtain ⟨hb, hrest⟩ := h
      have hs := boundaryStepArray_toState b es hb
      cases he : boundaryStepArray b es with
      | none =>
          have ha : boundaryStep b es.toState = none := by simpa [he] using hs.symm
          simp [runBoundaryArray, runBoundary, he, ha, ArrayRun.toRun]
      | some t =>
          have ha : boundaryStep b es.toState = some t.toTransition := by simpa [he] using hs.symm
          have hr := ih t.after (by simpa [he] using hrest)
          simpa only [runBoundaryArray, he, runBoundary, ha, ArrayRun.toRun, List.map_cons,
            ArrayTransition.toTransition] using
            congrArg (fun r : Run => Run.mk r.final (t.toTransition :: r.transitions)) hr

/-- Production execution retains only the next owner, never a trace list. -/
def runOwner (program : Array Instruction) : Nat → Owner → Owner
  | 0, es => es
  | fuel + 1, es =>
      match stepArray program es with
      | none => es
      | some t => runOwner program fuel t.after

theorem runOwner_projection (program : Array Instruction) (fuel : Nat) (es : Owner) :
    runOwner program fuel es = (runArray program fuel es).final := by
  induction fuel generalizing es with
  | zero => rfl
  | succ fuel ih =>
      cases h : stepArray program es <;> simp [runOwner, runArray, h, ih]

def runBoundaryOwner : List Boundary → Owner → Owner
  | [], es => es
  | b :: bs, es =>
      match boundaryStepArray b es with
      | none => es
      | some t => runBoundaryOwner bs t.after

theorem runBoundaryOwner_projection (bs : List Boundary) (es : Owner) :
    runBoundaryOwner bs es = (runBoundaryArray bs es).final := by
  induction bs generalizing es with
  | nil => rfl
  | cons b bs ih =>
      cases h : boundaryStepArray b es <;> simp [runBoundaryOwner, runBoundaryArray, h, ih]

/-- These read/reply observations are computed at the producing array state,
including failed reads and repeated equal addresses. -/
def ArrayTransition.read? (t : ArrayTransition) : Option (Nat × Option Nat) :=
  match t.action with
  | .instruction (.old (.load _ address)) =>
      let a := t.before.regs.getD address 0
      some (a, if a < t.before.memory.size then t.before.memory.getD a none else none)
  | _ => none

def ArrayTransition.write? (t : ArrayTransition) : Option (Nat × Nat) :=
  match t.action with
  | .instruction (.old (.store address value)) =>
      if t.before.regs.getD address 0 < t.before.memory.size then
        some (t.before.regs.getD address 0, t.before.regs.getD value 0) else none
  | _ => none

theorem ArrayTransition.read_toTransition (t : ArrayTransition) :
    t.toTransition.read? = t.read? := rfl

theorem ArrayTransition.write_toTransition (t : ArrayTransition) :
    t.toTransition.write? = t.write? := rfl

def ArrayRun.steps (r : ArrayRun) : Nat := r.transitions.length
def ArrayRun.categories (r : ArrayRun) : List Category := r.transitions.map (·.action.category)
def ArrayRun.categoryCount (r : ArrayRun) (c : Category) : Nat := r.categories.count c
def ArrayRun.reads (r : ArrayRun) : List (Nat × Option Nat) := r.transitions.filterMap ArrayTransition.read?
def ArrayRun.writes (r : ArrayRun) : List (Nat × Nat) := r.transitions.filterMap ArrayTransition.write?

theorem ArrayRun.observations_toRun (r : ArrayRun) :
    r.toRun.steps = r.steps ∧ r.toRun.categories = r.categories ∧
    r.toRun.reads = r.reads ∧ r.toRun.writes = r.writes := by
  simp [ArrayRun.toRun, Run.steps, Run.categories, Run.reads, Run.writes,
    ArrayRun.steps, ArrayRun.categories, ArrayRun.reads, ArrayRun.writes,
    List.map_map, List.filterMap_map, ArrayTransition.toTransition]
  exact ⟨rfl, rfl⟩

/-- The equalities concern the actual ordered whole run, not a second replay.
The stronger `runArray_toState` also preserves every positional pre/post state. -/
theorem runArray_observations (program : List Instruction) (fuel : Nat) (es : Owner)
    (h : RunDestinationsFit program.toArray fuel es) :
    (runArray program.toArray fuel es).steps = (run program fuel es.toState).steps ∧
    (runArray program.toArray fuel es).categories = (run program fuel es.toState).categories ∧
    (runArray program.toArray fuel es).reads = (run program fuel es.toState).reads ∧
    (runArray program.toArray fuel es).writes = (run program fuel es.toState).writes := by
  have hr := runArray_toState program fuel es h
  obtain ⟨hs, hc, hread, hw⟩ := (runArray program.toArray fuel es).observations_toRun
  rw [hr] at hs hc hread hw
  exact ⟨hs.symm, hc.symm, hread.symm, hw.symm⟩

theorem runArray_categoryCount (program : List Instruction) (fuel : Nat) (es : Owner)
    (h : RunDestinationsFit program.toArray fuel es) (c : Category) :
    (runArray program.toArray fuel es).categoryCount c =
      (run program fuel es.toState).categoryCount c := by
  simp only [ArrayRun.categoryCount, Run.categoryCount, (runArray_observations program fuel es h).2.1]

theorem runArray_occurrence (program : List Instruction) (fuel : Nat) (es : Owner)
    (h : RunDestinationsFit program.toArray fuel es) (k : Nat) :
    ((runArray program.toArray fuel es).transitions[k]?).map ArrayTransition.toTransition =
      (run program fuel es.toState).transitions[k]? := by
  simpa [ArrayRun.toRun] using
    congrArg (fun r : Run => r.transitions[k]?) (runArray_toState program fuel es h)

theorem runBoundaryArray_observations (bs : List Boundary) (es : Owner)
    (h : BoundaryRunDestinationsFit bs es) :
    (runBoundaryArray bs es).steps = (runBoundary bs es.toState).steps ∧
    (runBoundaryArray bs es).categories = (runBoundary bs es.toState).categories ∧
    (runBoundaryArray bs es).reads = (runBoundary bs es.toState).reads ∧
    (runBoundaryArray bs es).writes = (runBoundary bs es.toState).writes := by
  have hr := runBoundaryArray_toState bs es h
  obtain ⟨hs, hc, hread, hw⟩ := (runBoundaryArray bs es).observations_toRun
  rw [hr] at hs hc hread hw
  exact ⟨hs.symm, hc.symm, hread.symm, hw.symm⟩

theorem runOwner_toState (program : List Instruction) (fuel : Nat) (es : Owner)
    (h : RunDestinationsFit program.toArray fuel es) :
    (runOwner program.toArray fuel es).toState = (run program fuel es.toState).final := by
  rw [runOwner_projection]
  exact congrArg Run.final (runArray_toState program fuel es h)

theorem runOwner_retired_keys (program : List Instruction) (fuel : Nat) (es : Owner)
    (h : RunDestinationsFit program.toArray fuel es)
    (hk : (run program fuel es.toState).final.keyExtent = 0)
    (hr : (run program fuel es.toState).final.keyRegExtent = 0) :
    (runOwner program.toArray fuel es).keys = #[] ∧
    (runOwner program.toArray fuel es).keyRegs = #[] := by
  apply Owner.key_banks_empty
  · rw [runOwner_toState program fuel es h]; exact hk
  · rw [runOwner_toState program fuel es h]; exact hr

def requestProtocolArray (entry : Operand) (left right : Nat) (es : Owner) : ArrayRun :=
  runBoundaryArray [.left left, .right right, .entry entry, .activate] es

def requestProtocolOwner (entry : Operand) (left right : Nat) (es : Owner) : Owner :=
  runBoundaryOwner [.left left, .right right, .entry entry, .activate] es

theorem requestProtocolArray_bounds (entry : Operand) (left right : Nat) (es : Owner)
    (hl : requestLeftRegister < es.regs.size) (hr : requestRightRegister < es.regs.size) :
    BoundaryRunDestinationsFit [.left left, .right right, .entry entry, .activate] es := by
  cases hs : es.status <;>
    simp [BoundaryRunDestinationsFit, Boundary.DestinationsFit, boundaryStepArray,
      executeBoundaryArray, hs, hl, hr]

theorem requestProtocolArray_toState (entry : Operand) (left right : Nat) (es : Owner)
    (hl : requestLeftRegister < es.regs.size) (hr : requestRightRegister < es.regs.size) :
    (requestProtocolArray entry left right es).toRun = requestProtocol entry left right es.toState :=
  runBoundaryArray_toState _ es (requestProtocolArray_bounds entry left right es hl hr)

theorem requestProtocolOwner_toState (entry : Operand) (left right : Nat) (es : Owner)
    (hl : requestLeftRegister < es.regs.size) (hr : requestRightRegister < es.regs.size) :
    (requestProtocolOwner entry left right es).toState =
      (requestProtocol entry left right es.toState).final := by
  rw [requestProtocolOwner, runBoundaryOwner_projection]
  exact congrArg Run.final (requestProtocolArray_toState entry left right es hl hr)

/-! ## Exact numeric-bank capacity and destination-bound transport -/

theorem stepArray_spec {program : Array Instruction} {es : Owner} {t : ArrayTransition}
    (h : stepArray program es = some t) :
    t.before = es ∧ es.status = .running ∧
      ∃ i, program[es.pc]? = some i ∧ t.action = .instruction i ∧
        t.after = executeArray i es := by
  simp only [stepArray] at h
  split at h
  next hs =>
    cases hf : program[es.pc]? with
    | none => simp [hf] at h
    | some i =>
        simp [hf] at h
        subst t
        exact ⟨rfl, hs, i, rfl, rfl, rfl⟩
  next => simp at h

theorem stepArray_regs_size {program : Array Instruction} {es : Owner} {t : ArrayTransition}
    (h : stepArray program es = some t) : t.after.regs.size = es.regs.size := by
  obtain ⟨_, _, i, _, _, he⟩ := stepArray_spec h
  rw [he, executeArray_regs_size]

theorem runOwner_regs_size (program : Array Instruction) (fuel : Nat) (es : Owner) :
    (runOwner program fuel es).regs.size = es.regs.size := by
  induction fuel generalizing es with
  | zero => rfl
  | succ fuel ih =>
      cases h : stepArray program es with
      | none => simp [runOwner, h]
      | some t =>
          simpa [runOwner, h] using (ih t.after).trans (stepArray_regs_size h)

theorem runArray_regs_size (program : Array Instruction) (fuel : Nat) (es : Owner) :
    (runArray program fuel es).final.regs.size = es.regs.size := by
  rw [← runOwner_projection]
  exact runOwner_regs_size program fuel es

/-- Numeric bank capacity is preserved at every producing state, not only at
the final abstraction where this finite-container size is erased. -/
theorem runArray_occurrence_regs_size {program : Array Instruction} {fuel : Nat} {es : Owner}
    {k : Nat} {t : ArrayTransition} (h : (runArray program fuel es).transitions[k]? = some t) :
    t.before.regs.size = es.regs.size ∧ t.after.regs.size = es.regs.size := by
  induction fuel generalizing es k with
  | zero => simp [runArray] at h
  | succ fuel ih =>
      cases hs : stepArray program es with
      | none => simp [runArray, hs] at h
      | some first =>
          cases k with
          | zero =>
              simp only [runArray, hs, List.getElem?_cons_zero, Option.some.injEq] at h
              subst t
              exact ⟨congrArg (fun x : Owner => x.regs.size) (stepArray_spec hs).1,
                stepArray_regs_size hs⟩
          | succ k =>
              simp only [runArray, hs, List.getElem?_cons_succ] at h
              obtain ⟨hb, ha⟩ := ih h
              exact ⟨hb.trans (stepArray_regs_size hs), ha.trans (stepArray_regs_size hs)⟩

theorem boundaryStepArray_regs_size {b : Boundary} {es : Owner} {t : ArrayTransition}
    (h : boundaryStepArray b es = some t) :
    t.before.regs.size = es.regs.size ∧ t.after.regs.size = es.regs.size := by
  cases hs : es.status <;> simp [boundaryStepArray, hs] at h
  subst t
  exact ⟨rfl, executeBoundaryArray_regs_size b es⟩

theorem runBoundaryOwner_regs_size (bs : List Boundary) (es : Owner) :
    (runBoundaryOwner bs es).regs.size = es.regs.size := by
  induction bs generalizing es with
  | nil => rfl
  | cons b bs ih =>
      cases h : boundaryStepArray b es with
      | none => simp [runBoundaryOwner, h]
      | some t =>
          simpa [runBoundaryOwner, h] using (ih t.after).trans (boundaryStepArray_regs_size h).2

theorem runBoundaryArray_regs_size (bs : List Boundary) (es : Owner) :
    (runBoundaryArray bs es).final.regs.size = es.regs.size := by
  rw [← runBoundaryOwner_projection]
  exact runBoundaryOwner_regs_size bs es

theorem runBoundaryArray_occurrence_regs_size {bs : List Boundary} {es : Owner}
    {k : Nat} {t : ArrayTransition} (h : (runBoundaryArray bs es).transitions[k]? = some t) :
    t.before.regs.size = es.regs.size ∧ t.after.regs.size = es.regs.size := by
  induction bs generalizing es k with
  | nil => simp [runBoundaryArray] at h
  | cons b bs ih =>
      cases hs : boundaryStepArray b es with
      | none => simp [runBoundaryArray, hs] at h
      | some first =>
          cases k with
          | zero =>
              simp only [runBoundaryArray, hs, List.getElem?_cons_zero, Option.some.injEq] at h
              subst t
              exact boundaryStepArray_regs_size hs
          | succ k =>
              simp only [runBoundaryArray, hs, List.getElem?_cons_succ] at h
              obtain ⟨hb, ha⟩ := ih h
              exact ⟨hb.trans (boundaryStepArray_regs_size hs).2,
                ha.trans (boundaryStepArray_regs_size hs).2⟩

theorem requestProtocolOwner_regs_size (entry : Operand) (left right : Nat) (es : Owner) :
    (requestProtocolOwner entry left right es).regs.size = es.regs.size :=
  runBoundaryOwner_regs_size _ es

theorem requestProtocolArray_regs_size (entry : Operand) (left right : Nat) (es : Owner) :
    (requestProtocolArray entry left right es).final.regs.size = es.regs.size :=
  runBoundaryArray_regs_size _ es

/-- A destination bound stated on the abstract execution. `R` is the separately
counted numeric bank; the current key-register extent is part of `State`. -/
def Instruction.AbstractDestinationsFit (i : Instruction) (R : Nat) (s : State) : Prop :=
  match i with
  | .old p => destinationsBelow R s.keyRegExtent p
  | _ => True

theorem Instruction.destinationsFit_of_abstract (i : Instruction) (es : Owner) (R : Nat)
    (hR : es.regs.size = R) (h : i.AbstractDestinationsFit R es.toState) :
    i.DestinationsFit es := by
  cases i with
  | old p =>
      simpa [Instruction.DestinationsFit, Instruction.AbstractDestinationsFit,
        Owner.toState, hR] using h
  | releaseCell | releaseKey | releaseKeyRegister => trivial

/-- Every actual occurrence has a destination in its own bank. Code operands
that are only read are not required for this refinement; their word/address
encoding bounds remain a separate whole-machine obligation. -/
def TraceDestinationsFit (R : Nat) (ts : List Transition) : Prop :=
  ∀ (k : Nat) (t : Transition), ts[k]? = some t → ∀ (i : Instruction), t.action = .instruction i →
    i.AbstractDestinationsFit R t.before

/-- Independently established abstract trace bounds imply executable bounds.
No executable guard or final abstraction equality is assumed as a field. -/
theorem runDestinationsFit_of_abstract (program : List Instruction) (fuel : Nat)
    (es : Owner) (R : Nat) (hR : es.regs.size = R)
    (htrace : TraceDestinationsFit R (run program fuel es.toState).transitions) :
    RunDestinationsFit program.toArray fuel es := by
  induction fuel generalizing es with
  | zero => trivial
  | succ fuel ih =>
      have hstep : StepDestinationsFit program.toArray es := by
        intro i hrun hfetch
        have hf : program[es.pc]? = some i := by simpa using hfetch
        have hs : step program es.toState =
            some ⟨es.toState, .instruction i, execute i es.toState⟩ :=
          step_of_running (by simpa using hrun) (by simpa using hf)
        have hi := htrace 0 ⟨es.toState, .instruction i, execute i es.toState⟩
          (by simp [run, hs]) i rfl
        exact i.destinationsFit_of_abstract es R hR hi
      refine ⟨hstep, ?_⟩
      cases hs : stepArray program.toArray es with
      | none => trivial
      | some t =>
          have ha : step program es.toState = some t.toTransition := by
            simpa [hs] using (stepArray_toState program es hstep).symm
          apply ih t.after ((stepArray_regs_size hs).trans hR)
          intro k a hpos i hi
          apply htrace (k + 1) a ?_ i hi
          simpa [run, ha, ArrayTransition.toTransition] using hpos

theorem runArray_toState_of_abstract (program : List Instruction) (fuel : Nat)
    (es : Owner) (R : Nat) (hR : es.regs.size = R)
    (htrace : TraceDestinationsFit R (run program fuel es.toState).transitions) :
    (runArray program.toArray fuel es).toRun = run program fuel es.toState ∧
    (runArray program.toArray fuel es).final.regs.size = R :=
  ⟨runArray_toState program fuel es (runDestinationsFit_of_abstract program fuel es R hR htrace),
    (runArray_regs_size program.toArray fuel es).trans hR⟩

theorem runOwner_toState_of_abstract (program : List Instruction) (fuel : Nat)
    (es : Owner) (R : Nat) (hR : es.regs.size = R)
    (htrace : TraceDestinationsFit R (run program fuel es.toState).transitions) :
    (runOwner program.toArray fuel es).toState = (run program fuel es.toState).final ∧
    (runOwner program.toArray fuel es).regs.size = R :=
  ⟨runOwner_toState program fuel es (runDestinationsFit_of_abstract program fuel es R hR htrace),
    (runOwner_regs_size program.toArray fuel es).trans hR⟩

/-! Tiny executable controls use directly specified expected values. They run
this array layer, preserve repeated read occurrences, retire both key banks and
reuse the halted owner through the charged boundary. -/

private def toyOwner : Owner :=
  ⟨Array.replicate 302 0, #[some 9, some 17], #[some (-2)], #[0], 0, .running⟩

private def toyProgram : Array Instruction :=
  #[.old (.loadKey 0 0), .old (.load 1 0), .old (.load 1 0),
    .releaseCell, .releaseKey, .releaseKeyRegister, .old (.halt 1)]

#guard (runArray toyProgram 10 toyOwner).steps = 7
#guard (runArray toyProgram 10 toyOwner).reads = [(0, some 9), (0, some 9)]
#guard (runArray toyProgram 10 toyOwner).categories =
  [.old .keyRead, .old .read, .old .read, .numericRelease, .keyRelease,
    .keyRegisterRelease, .old .control]
#guard (runOwner toyProgram 10 toyOwner).memory = #[some 9]
#guard (runOwner toyProgram 10 toyOwner).keys.isEmpty
#guard (runOwner toyProgram 10 toyOwner).keyRegs.isEmpty
#guard (runOwner toyProgram 10 toyOwner).status = .halted 9
#guard (requestProtocolArray 0 0 1 (runOwner toyProgram 10 toyOwner)).steps = 4
#guard (requestProtocolArray 0 0 1 (runOwner toyProgram 10 toyOwner)).categories =
  [.requestAdmission, .requestAdmission, .controlEntry, .controlEntry]
#guard (runOwner #[.old (.load 1 300), .old (.halt 1)] 2
  (requestProtocolOwner 0 0 1 (runOwner toyProgram 10 toyOwner))).status = .halted 9
#guard (boundaryStepArray .activate toyOwner).isNone
#guard (executeArray .releaseCell { toyOwner with memory := #[] }).status = .fault
#guard (executeArray .releaseKey { toyOwner with keys := #[] }).status = .fault
#guard (executeArray .releaseKeyRegister { toyOwner with keyRegs := #[] }).status = .fault
#guard (runArray #[.old (.load 1 0)] 1 { toyOwner with memory := #[] }).reads = [(0, none)]

end RMQ.SuccinctFinal.PackedLifecycle
