import RMQ.Core.WordRAM.Lifecycle.BoundarySafety

/-! # Resource laws for actual scalar execution

The separately owned comparison banks never grow under an instruction or
request event. Numeric clean tails are preserved even by faulting execution.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Resources

theorem execute_key_extents (i : Instruction) (s : State) :
    (execute i s).keyExtent ≤ s.keyExtent ∧
      (execute i s).keyRegExtent ≤ s.keyRegExtent := by
  cases i <;> simp only [execute]
  · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  all_goals split <;> simp only <;> omega

theorem execute_numeric_closed (i : Instruction) (s : State)
    (closed : PackedConstruction.CleanTail s.core) :
    PackedConstruction.CleanTail (execute i s).core := by
  cases i with
  | old p => exact PackedConstruction.execPrim_cleanTail p s.core closed
  | releaseCell =>
    by_cases hz : s.core.extent = 0
    · simpa [execute, hz, PackedConstruction.CleanTail] using closed
    · simp only [execute, hz, ↓reduceIte, PackedConstruction.CleanTail,
        PackedConstruction.State.next]
      intro a ha
      by_cases he : a = s.core.extent - 1
      · simp [PackedConstruction.put, he]
      · simp [PackedConstruction.put, he, closed a (by omega)]
  | releaseKey =>
    simp only [execute]
    split <;> exact closed
  | releaseKeyRegister =>
    simp only [execute]
    split <;> exact closed

theorem run_preserves (P : State → Prop) (program : List Instruction) (fuel : Nat) (s : State)
    (initial : P s) (preserves : ∀ i t, P t → P (execute i t)) :
    P (run program fuel s).final ∧
      ∀ t ∈ (run program fuel s).transitions, P t.before ∧ P t.after := by
  induction fuel generalizing s with
  | zero => exact ⟨initial, fun _ h => by cases h⟩
  | succ fuel ih =>
    cases hs : step program s with
    | none => simpa [run, hs] using And.intro initial (show ∀ t ∈ ([] : List Transition),
        P t.before ∧ P t.after from fun _ h => by cases h)
    | some first =>
      obtain ⟨hb, _, i, _, _, ha⟩ := step_spec hs
      have next : P first.after := ha ▸ preserves i s initial
      have rest := ih first.after next
      refine ⟨by simpa [run, hs] using rest.1, ?_⟩
      intro t ht
      simp only [run, hs, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact ⟨hb ▸ initial, next⟩
      · exact rest.2 t ht

theorem run_key_extents (program : List Instruction) (fuel : Nat) (s : State) :
    ((run program fuel s).final.keyExtent ≤ s.keyExtent ∧
      (run program fuel s).final.keyRegExtent ≤ s.keyRegExtent) ∧
      ∀ t ∈ (run program fuel s).transitions,
        (t.before.keyExtent ≤ s.keyExtent ∧ t.before.keyRegExtent ≤ s.keyRegExtent) ∧
        (t.after.keyExtent ≤ s.keyExtent ∧ t.after.keyRegExtent ≤ s.keyRegExtent) := by
  apply run_preserves (fun t => t.keyExtent ≤ s.keyExtent ∧ t.keyRegExtent ≤ s.keyRegExtent)
    program fuel s ⟨Nat.le_refl _, Nat.le_refl _⟩
  intro i t ht
  have step := execute_key_extents i t
  exact ⟨Nat.le_trans step.1 ht.1, Nat.le_trans step.2 ht.2⟩

theorem run_numeric_closed (program : List Instruction) (fuel : Nat) (s : State)
    (closed : PackedConstruction.CleanTail s.core) :
    PackedConstruction.CleanTail (run program fuel s).final.core ∧
      ∀ t ∈ (run program fuel s).transitions,
        PackedConstruction.CleanTail t.before.core ∧ PackedConstruction.CleanTail t.after.core :=
  run_preserves (fun t => PackedConstruction.CleanTail t.core) program fuel s closed
    execute_numeric_closed

theorem run_steps_le_fuel (program : List Instruction) (fuel : Nat) (s : State) :
    (run program fuel s).steps ≤ fuel := by
  induction fuel generalizing s with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    cases hs : step program s with
    | none => simp [run, hs, Run.steps]
    | some t => simpa [run, hs, Run.steps] using Nat.succ_le_succ (ih t.after)

theorem run_transition_after {program : List Instruction} {fuel : Nat} {s : State}
    {index : Nat} {t : Transition}
    (occurs : (run program fuel s).transitions[index]? = some t) :
    t.after = (run program (index + 1) s).final := by
  obtain ⟨before, step⟩ := run_transition_at occurs
  rw [run_add]
  simp [← before, run, step]

theorem runBoundary_preserves (P : State → Prop) (bs : List Boundary) (s : State)
    (initial : P s) (preserves : ∀ b ∈ bs, ∀ t, P t → P (executeBoundary b t)) :
    P (runBoundary bs s).final ∧
      ∀ t ∈ (runBoundary bs s).transitions, P t.before ∧ P t.after := by
  induction bs generalizing s with
  | nil => exact ⟨initial, fun _ h => by cases h⟩
  | cons b bs ih =>
    cases status : s.core.status with
    | running => simp [runBoundary, boundaryStep, status]; exact initial
    | fault => simp [runBoundary, boundaryStep, status]; exact initial
    | halted value =>
      have next := preserves b (by simp) s initial
      have rest := ih (executeBoundary b s) next (fun c hc => preserves c (by simp [hc]))
      simp only [runBoundary, boundaryStep, status]
      refine ⟨rest.1, ?_⟩
      intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact ⟨initial, next⟩
      · exact rest.2 t ht

theorem runBoundary_reads (bs : List Boundary) (s : State) :
    (runBoundary bs s).reads = [] := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    cases status : s.core.status with
    | running => simp [runBoundary, boundaryStep, status, Run.reads]
    | fault => simp [runBoundary, boundaryStep, status, Run.reads]
    | halted value =>
      simp only [runBoundary, boundaryStep, status, Run.reads, List.filterMap_cons, Transition.read?]
      exact ih (executeBoundary b s)

end RMQ.SuccinctFinal.PackedLifecycle.Resources
