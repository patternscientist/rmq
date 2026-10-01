import RMQ.Core.WordRAM.Lifecycle.Continuous
import RMQ.Core.WordRAM.Lifecycle.Resources
import RMQ.Core.WordRAM.Lifecycle.Physical

/-! # Bounds and physical reads on the completed continuous run -/

namespace RMQ.SuccinctFinal.PackedLifecycle.Continuous

open PackedWordRAM (wordWidth buildMemory)
set_option maxRecDepth 30000

def PrefixProfile (model : InputModel) (xs : List Int) (s : State) : Prop :=
  s.Fits (wordWidth xs.length) ∧ PackedConstruction.CleanTail s.core ∧
    Retained.FiniteBank s ∧ s.core.extent ≤ 5000000 * (xs.length + 1) ∧
    s.keyExtent ≤ (if model = .comparison then xs.length else 0) ∧
    s.keyRegExtent ≤ (if model = .comparison then 2 else 0)

theorem prefix_profile {model : InputModel} {xs : List Int} {left right fuel : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length)
    (within : fuel ≤ (continuousRun model xs left right).steps) :
    PrefixProfile model xs
      (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final := by
  have resources := prefix_resources built within
  have clean := (Resources.run_numeric_closed (Layout.program model) fuel
    (initialState model xs left right Layout.builderBase) (initial_clean model xs left right _).1).1
  have keys := (Resources.run_key_extents (Layout.program model) fuel
    (initialState model xs left right Layout.builderBase)).1
  have bound := Resources.run_steps_le_fuel (Layout.program model) (lifecycleBudget xs.length)
    (initialState model xs left right Layout.builderBase)
  have hle : fuel ≤ lifecycleBudget xs.length := Nat.le_trans within bound
  have fits := (run_fits (initial_fits model xs left right Layout.builderBase domain hl hr
    (Construction.initial_pc_fits xs)) (Reusable.program_fits model xs.length)
    (show ∀ t ∈ (run (Layout.program model) fuel
      (initialState model xs left right Layout.builderBase)).transitions,
      t.Safe (wordWidth xs.length) (Layout.program model).length from by
        intro t ht
        apply safe built t
        unfold continuousRun
        rw [← Nat.add_sub_of_le hle, run_add]
        exact List.mem_append_left _ ht)).1
  exact ⟨fits, clean, resources.2, resources.1, keys⟩

theorem physical_read {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length)
    (index : Nat) (t : Transition) (address : Nat) (reply : Option Nat)
    (occurs : (continuousRun model xs left right).transitions[index]? = some t)
    (read : t.read? = some (address, reply)) :
    t.before = (run (Layout.program model) index (initialState model xs left right Layout.builderBase)).final ∧
      (Physical.imageTrace model (continuousRun model xs left right).transitions)[index]? =
        some ⟨Physical.view model t.before, t.action, Physical.view model t.after⟩ ∧
      ∃ physical value, Physical.checkedAddress model t.before address = some physical ∧
        reply = some value ∧ Physical.lookup model t.before physical = some value ∧
        physical < 2 ^ wordWidth xs.length ∧ address < 2 ^ wordWidth xs.length ∧
        value < 2 ^ wordWidth xs.length := by
  have member : t ∈ (continuousRun model xs left right).transitions := List.mem_of_getElem? occurs
  exact ⟨(run_transition_at occurs).1,
    Physical.image_occurrence model _ index t occurs,
    Physical.safe_read model xs.length (Layout.program model).length t address reply read
      (safe built t member) (transition_fits built domain hl hr t member).1
      (transition_resources built member).1⟩

theorem physical_prefix {model : InputModel} {xs : List Int} {left right fuel : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length)
    (within : fuel ≤ (continuousRun model xs left right).steps) :
    let s := (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final
    Physical.extent model s < 2 ^ wordWidth xs.length ∧
      (∀ p value, Physical.lookup model s p = some value → value < 2 ^ wordWidth xs.length) := by
  have profile := prefix_profile built domain hl hr within
  exact ⟨Physical.extent_fit model xs.length _ profile.2.2.2.1,
    Physical.lookup_word_fits model xs.length _ profile.1⟩

end RMQ.SuccinctFinal.PackedLifecycle.Continuous
