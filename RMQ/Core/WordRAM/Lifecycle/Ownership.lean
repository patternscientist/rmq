import RMQ.Core.WordRAM.Lifecycle.Continuous
import RMQ.Core.WordRAM.Lifecycle.Executable
import RMQ.Core.WordRAM.Lifecycle.Accounting

/-! # The executed retained owner and its complete numeric capacity

The production endpoint has arrays and scalar control only. Observation traces
are separately returned by the validation evaluator and are not owner fields.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Ownership

open PackedWordRAM (wordWidth buildMemory)
set_option maxRecDepth 30000

def owner (model : InputModel) (xs : List Int) (left right : Nat) : Owner :=
  runOwner (Layout.program model).toArray (Continuous.lifecycleBudget xs.length)
    (Executable.initialOwner model xs left right)

def observations (model : InputModel) (xs : List Int) (left right : Nat) : ArrayRun :=
  runArray (Layout.program model).toArray (Continuous.lifecycleBudget xs.length)
    (Executable.initialOwner model xs left right)

attribute [local irreducible] owner observations

def Ready (xs : List Int) (es : Owner) : Prop :=
  es.regs.size = numericBank ∧ Retained.Canonical xs es.toState

def capacity (model : InputModel) (es : Owner) : Nat :=
  es.memory.size + (encodedProgram model).length + es.regs.size + controlWords

theorem ready_of_projection {xs : List Int} {es : Owner} {s : State}
    (bank : es.regs.size = numericBank) (projection : es.toState = s)
    (canonical : Retained.Canonical xs s) : Ready xs es := by
  refine ⟨bank, ?_⟩
  rw [projection]
  exact canonical

theorem status_of_projection {es : Owner} {s : State} {status : PackedConstruction.Status}
    (projection : es.toState = s) (halted : s.core.status = status) : es.status = status :=
  (congrArg (fun t : State => t.core.status) projection).trans halted

theorem refinement (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) :
    (owner model xs left right).toState = (Continuous.continuousRun model xs left right).final ∧
      (owner model xs left right).regs.size = numericBank ∧
      (observations model xs left right).toRun = Continuous.continuousRun model xs left right := by
  have production := Executable.initial_owner_refinement model xs left right domain hl hr
    (Continuous.lifecycleBudget xs.length)
  have observed := Executable.initial_array_refinement model xs left right domain hl hr
    (Continuous.lifecycleBudget xs.length)
  unfold owner observations Continuous.continuousRun
  exact ⟨production.1, production.2, observed.1⟩

theorem ready (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) : Ready xs (owner model xs left right) := by
  obtain ⟨abstract, producer, ts, built⟩ := Construction.build_stage model xs left right domain hl hr
  have refines := refinement model xs left right domain hl hr
  exact ready_of_projection refines.2.1 refines.1 (Continuous.canonical built)

theorem halted (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) :
    (owner model xs left right).status = .halted
      (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) := by
  obtain ⟨abstract, producer, ts, built⟩ := Construction.build_stage model xs left right domain hl hr
  exact status_of_projection (refinement model xs left right domain hl hr).1 (Continuous.halts built)

theorem Ready.empty_keys {xs : List Int} {es : Owner} (ready : Ready xs es) :
    es.keys = #[] ∧ es.keyRegs = #[] :=
  Owner.key_banks_empty es ready.2.1.2.2.2.2.1 ready.2.1.2.2.2.2.2

theorem Ready.memory_size {xs : List Int} {es : Owner} (ready : Ready xs es) :
    es.memory.size = (buildMemory xs).length := ready.2.1.2.1

theorem Ready.capacity_bound {xs : List Int} {es : Owner} (ready : Ready xs es)
    (model : InputModel) :
    capacity model es * wordWidth xs.length ≤ 2 * xs.length + retainedRho xs.length := by
  unfold capacity
  rw [ready.memory_size, ready.1]
  exact retained_capacity model xs

theorem Ready.query {xs : List Int} {es : Owner} (ready : Ready xs es)
    (model : InputModel) (left right answer : Nat) (halted : es.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    Ready xs (Executable.queryOwner model left right es) ∧
      (Executable.queryOwner model left right es).status = .halted
        (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
      (Executable.queryOwner model left right es).memory = es.memory ∧
      (Executable.queryArray model left right es).toRun = Reusable.queryRun model left right es.toState ∧
      (Reusable.queryRun model left right es.toState).steps ≤ Reusable.queryBudget := by
  have refines := Executable.query_owner_refinement model xs left right answer es ready.1 ready.2 halted hl hr
  have observed := Executable.query_array_refinement model xs left right answer es ready.1 ready.2 halted hl hr
  have correct := Reusable.query_correct model xs left right answer es.toState ready.2 halted hl hr
  refine ⟨⟨refines.2, ?_⟩,
    (congrArg (fun s : State => s.core.status) refines.1).trans correct.2.1, ?_, observed.1,
    correct.2.2.2.2.2⟩
  · rw [refines.1]; exact correct.1
  ·
    apply Array.ext
    · change (Executable.queryOwner model left right es).toState.core.extent = es.toState.core.extent
      rw [refines.1]
      exact correct.2.2.2.1
    · intro i hleft hright
      have memory := (congrArg (fun s : State => s.core.memory i) refines.1).trans
        (congrFun correct.2.2.1 i)
      change (Executable.queryOwner model left right es).memory.getD i none = es.memory.getD i none at memory
      simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hleft,
        Array.getElem?_eq_getElem hright, Option.getD_some] using memory

end RMQ.SuccinctFinal.PackedLifecycle.Ownership
