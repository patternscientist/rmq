import RMQ.Core.WordRAM.Construction.Compiler

namespace RMQ.SuccinctFinal.PackedConstruction

/-- Trial copy of the mutant: the transition-safety conjunct at `program.length + 1`. -/
def RunSafeW (W : Nat) (program : List BInstr) (r : Run) : Prop :=
  ∀ t ∈ r.transitions,
    Prim.Safe W (program.length + 1) t.before t.instruction.primitive ∧ t.after.Fits W

theorem Prim.Safe.succ_length {W len : Nat} {s : State} {p : Prim} (h : Prim.Safe W len s p) :
    Prim.Safe W (len + 1) s p := by
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  cases p <;> simp only [Prim.SafeAt] at h2 ⊢ <;> first | exact h2 | omega

instance {W len : Nat} {s : State} {p : Prim} : Coe (Prim.Safe W len s p) (Prim.Safe W (len + 1) s p) :=
  ⟨Prim.Safe.succ_length⟩

/-- The unchanged proof text of `Run.Safe.of_transitions`. -/
theorem RunSafeW.of_transitions (program : List BInstr) (W : Nat)
    (hlen : program.length < 2 ^ W) (fuel : Nat) (s : State) (hfit : s.Fits W)
    (hsafe : ∀ t ∈ (run program fuel s).transitions,
      Prim.Safe W program.length t.before t.instruction.primitive) :
    RunSafeW W program (run program fuel s) := by
  intro t ht
  exact ⟨hsafe t ht, ((run_trace_fits program W hlen fuel s hfit hsafe).1 t ht).2⟩

/-- The unchanged proof text of `Run.Safe.not_fault`. -/
theorem RunSafeW.not_fault {W : Nat} {program : List BInstr} {fuel : Nat} {s : State}
    (hsafe : RunSafeW W program (run program fuel s)) (hs : s.status ≠ .fault) :
    (run program fuel s).final.status ≠ .fault := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
      cases hstep : stepProgram program s with
      | none => rw [run_of_step_none program s _ hstep]; exact hs
      | some t =>
          obtain ⟨hb, _, _, he⟩ := step_spec hstep
          subst hb
          have hhead := hsafe t (by simp [run, hstep])
          have hafter : t.after.status ≠ .fault := by
            rw [he]
            exact Prim.safe_not_fault hhead.1 hs
          have hrest : RunSafeW W program (run program fuel t.after) := by
            intro u hu
            exact hsafe u (by simp [run, hstep, hu])
          simpa [run, hstep] using ih hrest hafter

/-- The unchanged proof text of `Run.Safe.final_fits`. -/
theorem RunSafeW.final_fits {W : Nat} {program : List BInstr} {fuel : Nat} {s : State}
    (hsafe : RunSafeW W program (run program fuel s)) (hfit : s.Fits W) :
    (run program fuel s).final.Fits W := by
  induction fuel generalizing s with
  | zero => exact hfit
  | succ fuel ih =>
      cases hstep : stepProgram program s with
      | none => rw [run_of_step_none program s _ hstep]; exact hfit
      | some t =>
          have hhead := hsafe t (by simp [run, hstep])
          have hrest : RunSafeW W program (run program fuel t.after) := by
            intro u hu
            exact hsafe u (by simp [run, hstep, hu])
          simpa [run, hstep] using ih hrest hhead.2

/-- Strictly weaker: a jump to one past the end is admitted. -/
example : RunSafeW 32 [] ⟨{ comparisonInputState [] with pc := 0 },
    [⟨comparisonInputState [], ⟨.jump 0⟩, comparisonInputState []⟩]⟩ →
    True := fun _ => trivial

/-- The frozen pin shape must reject the mutant body. -/
theorem pin_rejects : ∀ (W : Nat) (program : List BInstr) (r : Run),
    RunSafeW W program r ↔ ∀ t ∈ r.transitions,
      Prim.Safe W program.length t.before t.instruction.primitive ∧ t.after.Fits W :=
  fun _ _ _ => Iff.rfl

end RMQ.SuccinctFinal.PackedConstruction
