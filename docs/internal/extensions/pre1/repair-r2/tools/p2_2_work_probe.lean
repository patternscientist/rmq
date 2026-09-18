import RMQ.Core.WordRAM.Construction.Capstone

/-! PRE-1-R2 reproduction of audit PRE-1-A2 finding P2-2 (not a consumer; not
built by any target). The exported `work` literal of `BuilderRunFacts` is the
fuel `builderBudget n`, so the `work` field holds for every program and every
state, the empty program included; `halts` does not hold for the empty program.
The linear-work content of the capstone is `halts` together with `work` at the
pinned fuel. -/

namespace PRE1R2WorkProbe

open RMQ.SuccinctFinal.PackedConstruction

/-- The `work` literal is a consequence of `run_steps_le_fuel` alone. -/
theorem work_literal_is_fuel (program : List BInstr) (s : State) (xs : List Int) :
    (run program (builderBudget xs.length) s).steps ≤ 1000000000 * xs.length + 1000000000 :=
  Nat.le_trans (run_steps_le_fuel program _ s) (Nat.le_of_eq (Proof.builderBudget_eq_mul_add xs.length))

/-- In particular the empty program satisfies the `work` field on the comparison input. -/
theorem empty_program_work (xs : List Int) :
    (run [] (builderBudget xs.length) (comparisonInputState xs)).steps ≤
      1000000000 * xs.length + 1000000000 :=
  work_literal_is_fuel [] _ xs

theorem run_nil (fuel : Nat) (s : State) : run [] fuel s = ⟨s, []⟩ := by
  cases fuel with
  | zero => rfl
  | succ k => simp [run, stepProgram, fetch]

/-- The empty program does not satisfy the `halts` field. -/
theorem empty_program_never_halts (xs : List Int) :
    ¬ ∃ outBase, (run [] (builderBudget xs.length) (comparisonInputState xs)).final.status =
      .halted outBase := by
  intro ⟨outBase, h⟩
  rw [run_nil] at h
  simp [comparisonInputState] at h

#print axioms work_literal_is_fuel
#print axioms empty_program_work
#print axioms empty_program_never_halts

end PRE1R2WorkProbe
