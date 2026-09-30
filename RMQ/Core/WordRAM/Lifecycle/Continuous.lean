import RMQ.Core.WordRAM.Lifecycle.Finalization
import RMQ.Core.WordRAM.Lifecycle.Reusable

/-! # Construction and the first query in one uninterrupted run

The fixed fuel selects a completed trace; completion is derived from the
builder, finalizer and query executions before padding the halted endpoint.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Continuous

open PackedWordRAM (wordWidth buildMemory)
set_option maxRecDepth 30000

def constructionBudget (n : Nat) : Nat := 1100000000 * (n + 1)
def lifecycleBudget (n : Nat) : Nat := constructionBudget n + Service.budget

def continuousRun (model : InputModel) (xs : List Int) (left right : Nat) : Run :=
  run (Layout.program model) (lifecycleBudget xs.length)
    (initialState model xs left right Layout.builderBase)

theorem entered_of_inputs {left right : Nat} {s : State}
    (inputs : Service.Inputs left right (Retained.projectQueryState s)) :
    ServiceSafety.Entered left right s := by
  refine ⟨?_, inputs.2.1, inputs.2.2.1, inputs.2.2.2.1⟩
  have hs := inputs.1
  change Retained.projectStatus s.core.status = .running at hs
  cases status : s.core.status <;> simp_all [Retained.projectStatus]

theorem service_safe {model : InputModel} {xs : List Int} {left right : Nat} {s : State}
    (canonical : Retained.Canonical xs s) (entered : ServiceSafety.Entered left right s) :
    ∀ t ∈ (Reusable.serviceRun model s).transitions,
      t.Safe (wordWidth xs.length) (Layout.program model).length := by
  have h := ServiceSafety.actual_prefix_safe xs (Reusable.continuation model) left right
    Service.budget s canonical entered (Nat.le_refl _)
  rwa [← Reusable.program_host model] at h

theorem joined_execution {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    RunsTo (Layout.program model) (initialState model xs left right Layout.builderBase)
      (Reusable.serviceRun model (Finalization.finalState model xs left right producer)).final
      (Finalization.fullTrace model xs left right producer ts ++
        (Reusable.serviceRun model (Finalization.finalState model xs left right producer)).transitions) :=
  (Finalization.full_execution built).trans
    (run_exact_steps (Layout.program model) Service.budget _)

theorem exact_run {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    continuousRun model xs left right =
      ⟨(Reusable.serviceRun model (Finalization.finalState model xs left right producer)).final,
        Finalization.fullTrace model xs left right producer ts ++
          (Reusable.serviceRun model (Finalization.finalState model xs left right producer)).transitions⟩ := by
  let ready := Finalization.finalState model xs left right producer
  have hc : Retained.Canonical xs ready := (Finalization.completed built).2.1
  have he := entered_of_inputs (Finalization.completed built).2.2.1
  have stop := Reusable.service_halts model xs left right ready hc he
  have work := Finalization.linear_cost built
  have queryWork := (Reusable.service_steps model xs left right ready hc he).2
  have total : (Finalization.fullTrace model xs left right producer ts ++
      (Reusable.serviceRun model ready).transitions).length ≤ lifecycleBudget xs.length := by
    rw [List.length_append]
    change (Finalization.fullTrace model xs left right producer ts).length +
      (Reusable.serviceRun model ready).steps ≤ constructionBudget xs.length + Service.budget
    rw [Service.budget_eq]
    exact Nat.add_le_add work queryWork
  have stopped : (Reusable.serviceRun model ready).final.core.status ≠ .running := by rw [stop]; intro h; cases h
  have completed := (joined_execution built).fuel_extension stopped
    (lifecycleBudget xs.length - (Finalization.fullTrace model xs left right producer ts ++
      (Reusable.serviceRun model ready).transitions).length)
  rw [Nat.add_sub_of_le total] at completed
  exact completed

theorem canonical {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    Retained.Canonical xs (continuousRun model xs left right).final := by
  rw [exact_run built]
  exact Reusable.service_canonical model xs left right _ (Finalization.completed built).2.1
    (entered_of_inputs (Finalization.completed built).2.2.1)

theorem halts {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    (continuousRun model xs left right).final.core.status = .halted
      (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) := by
  rw [exact_run built]
  exact Reusable.service_halts model xs left right _ (Finalization.completed built).2.1
    (entered_of_inputs (Finalization.completed built).2.2.1)

theorem safe {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    ∀ t ∈ (continuousRun model xs left right).transitions,
      t.Safe (wordWidth xs.length) (Layout.program model).length := by
  rw [exact_run built]
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact Finalization.full_safe built t ht
  · exact service_safe (Finalization.completed built).2.1
      (entered_of_inputs (Finalization.completed built).2.2.1) t ht

theorem transition_fits {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) :
    ∀ t ∈ (continuousRun model xs left right).transitions,
      t.before.Fits (wordWidth xs.length) ∧ t.after.Fits (wordWidth xs.length) :=
  (run_fits (initial_fits model xs left right Layout.builderBase domain hl hr
    (Construction.initial_pc_fits xs)) (Reusable.program_fits model xs.length) (safe built)).2

theorem prefix_resources {model : InputModel} {xs : List Int} {left right fuel : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts)
    (within : fuel ≤ (continuousRun model xs left right).steps) :
    let s := (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final
    s.core.extent ≤ 5000000 * (xs.length + 1) ∧ ∀ r, 8273 ≤ r → s.core.regs r = 0 := by
  let construction := Finalization.fullTrace model xs left right producer ts
  let ready := Finalization.finalState model xs left right producer
  by_cases short : fuel ≤ construction.length
  · exact ⟨Finalization.full_prefix_peak built short, Finalization.full_prefix_finite built short⟩
  · have queryWork := (Reusable.service_steps model xs left right ready
      (Finalization.completed built).2.1 (entered_of_inputs (Finalization.completed built).2.2.1)).2
    have fuelBound : fuel - construction.length ≤ Service.budget := by
      rw [exact_run built] at within
      change (fuel : Nat) ≤ (construction ++ (Reusable.serviceRun model ready).transitions).length at within
      rw [List.length_append] at within
      rw [Service.budget_eq]
      change (Reusable.serviceRun model ready).transitions.length ≤ 160253 at queryWork
      omega
    have hc := ServiceSafety.actual_prefix_canonical xs (Reusable.continuation model) left right
      (fuel - construction.length) ready (Finalization.completed built).2.1
      (entered_of_inputs (Finalization.completed built).2.2.1) fuelBound
    rw [← Reusable.program_host model] at hc
    have whole : run (Layout.program model) construction.length
        (initialState model xs left right Layout.builderBase) = ⟨ready, construction⟩ :=
      Finalization.full_execution built
    dsimp only
    rw [show fuel = construction.length + (fuel - construction.length) by omega, run_add, whole]
    refine ⟨?_, hc.2.1⟩
    rw [hc.1.2.1]
    have hm := PackedConstruction.Spec.buildMemory_length_le xs
    omega

theorem transition_resources {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts)
    {t : Transition} (member : t ∈ (continuousRun model xs left right).transitions) :
    t.before.core.extent ≤ 5000000 * (xs.length + 1) ∧
      ∀ r, 8273 ≤ r → t.before.core.regs r = 0 := by
  obtain ⟨index, occurs⟩ := List.mem_iff_getElem?.mp member
  have within : index ≤ (continuousRun model xs left right).steps :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.mp occurs).1
  rw [(run_transition_at occurs).1]
  exact prefix_resources built within

/-- Complete accepted transitions, rather than only their read projection,
occur as the suffix after the charged preparation and full finite-bank clear. -/
theorem query_suffix {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    ∃ entryTransitions : List Transition,
      entryTransitions.length = 4 + QueryEntry.setupCost ∧
      (continuousRun model xs left right).transitions =
        Finalization.fullTrace model xs left right producer ts ++ entryTransitions ++
          (PackedWordRAM.Optimization.compactQueryRun (buildMemory xs) xs.length left right).transitions.map
            (QuerySafetyBridge.liftTransition (buildMemory xs)) := by
  let ready := Finalization.finalState model xs left right producer
  let state := Retained.projectQueryState ready
  have inputs : Service.Inputs left right state := (Finalization.completed built).2.2.1
  obtain ⟨setup, execution, length, _⟩ := Service.completed (buildMemory xs) xs.length left right
    state (ServiceSafety.canonical_header xs) inputs
  have preparation := (Service.prepare_exec (buildMemory xs) xs.length left right state
    (ServiceSafety.canonical_header xs) inputs).2.1
  refine ⟨((PackedWordRAM.run (buildMemory xs) Service.program 4 state).transitions ++ setup).map
    (QuerySafetyBridge.liftTransition (buildMemory xs)), ?_, ?_⟩
  · rw [List.length_map, List.length_append, ← PackedWordRAM.Run.steps, preparation, length]
  · rw [exact_run built, Reusable.service_exact model xs left right ready
      (Finalization.completed built).2.1 (entered_of_inputs inputs), execution]
    simp only [List.map_append, List.append_assoc]

theorem cost {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    (continuousRun model xs left right).steps =
      (Finalization.fullTrace model xs left right producer ts).length + 4 + QueryEntry.setupCost +
        (PackedWordRAM.Optimization.compactQueryRun (buildMemory xs) xs.length left right).steps ∧
    (continuousRun model xs left right).steps ≤ constructionBudget xs.length + 160253 := by
  have service := Reusable.service_steps model xs left right _ (Finalization.completed built).2.1
    (entered_of_inputs (Finalization.completed built).2.2.1)
  have work := Finalization.linear_cost built
  rw [exact_run built]
  simp only [Run.steps, List.length_append]
  change (Finalization.fullTrace model xs left right producer ts).length +
      (Reusable.serviceRun model (Finalization.finalState model xs left right producer)).steps = _ ∧
    (Finalization.fullTrace model xs left right producer ts).length +
      (Reusable.serviceRun model (Finalization.finalState model xs left right producer)).steps ≤ _
  constructor
  · rw [service.1]; omega
  · exact Nat.add_le_add work service.2

end RMQ.SuccinctFinal.PackedLifecycle.Continuous
