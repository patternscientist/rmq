import RMQ.Core.WordRAM.Construction.Compiler

/-! # Loop composition rules for the structured semantics

Stage proofs reason about `loop` blocks only through these rules, so no fuel
arithmetic leaks into them. `loop_iterate` composes a counted loop whose
invariant carries the remaining trip count; `loop_iterate_potential` adds an
amortization potential for loops whose iterations have data-dependent cost
(the monotone stack: total pops are bounded by total pushes);
`loop_measure` bounds a loop by a strictly decreasing measure (the halving
`log2` loop). All costs are exact `EvalG` costs and therefore, through the
compiler theorem, exact transition counts of the interpreter.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

namespace Structured

/-- Counted loop composition: if from every state satisfying the invariant at
trip count `k + 1` the guard is nonzero and the body evaluates in at most `J`
steps to a running state at trip count `k`, and the invariant at trip count `0`
forces a zero guard, then the loop from trip count `k` evaluates to an
invariant-`0` state in at most `k * (J + 2) + 1` steps. -/
theorem EvalG.loop_iterate {P : State → Action → Prop} (Q : Nat → State → Prop)
    (c : Operand) (body : Block) (J : Nat)
    (hrun : ∀ k s, Q k s → s.status = .running)
    (hguard : ∀ k s, Q (k + 1) s → s.regs c ≠ 0)
    (hexit : ∀ s, Q 0 s → s.regs c = 0)
    (hbody : ∀ k s, Q (k + 1) s → ∃ s' j, EvalG P body s s' j ∧ j ≤ J ∧ Q k s') :
    ∀ k s, Q k s →
      ∃ s' j, EvalG P (.loop c body) s s' j ∧ j ≤ k * (J + 2) + 1 ∧ Q 0 s' := by
  intro k
  induction k with
  | zero =>
      intro s hs
      exact ⟨s, 1, EvalG.loopExit (hrun 0 s hs) (hexit s hs), by simp, hs⟩
  | succ k ih =>
      intro s hs
      obtain ⟨s₁, j₁, hbody₁, hj₁, hq₁⟩ := hbody k s hs
      obtain ⟨s₂, j₂, hrest, hj₂, hq₂⟩ := ih s₁ hq₁
      refine ⟨s₂, j₁ + j₂ + 2,
        EvalG.loopStep (hrun _ s hs) (hguard k s hs) hbody₁ (hrun k s₁ hq₁) hrest, ?_, hq₂⟩
      rw [Nat.succ_mul]
      omega

/-- Counted loop composition with an amortization potential `Φ`: each
iteration may cost `J` plus `β` times the drop of `Φ`, so the whole loop costs
at most `k * (J + 2) + 1 + β * Φ s₀`. -/
theorem EvalG.loop_iterate_potential {P : State → Action → Prop} (Q : Nat → State → Prop)
    (Φ : State → Nat) (c : Operand) (body : Block) (J β : Nat)
    (hrun : ∀ k s, Q k s → s.status = .running)
    (hguard : ∀ k s, Q (k + 1) s → s.regs c ≠ 0)
    (hexit : ∀ s, Q 0 s → s.regs c = 0)
    (hbody : ∀ k s, Q (k + 1) s →
      ∃ s' j, EvalG P body s s' j ∧ j + β * Φ s' ≤ J + β * Φ s ∧ Q k s') :
    ∀ k s, Q k s →
      ∃ s' j, EvalG P (.loop c body) s s' j ∧
        j + β * Φ s' ≤ k * (J + 2) + 1 + β * Φ s ∧ Q 0 s' := by
  intro k
  induction k with
  | zero =>
      intro s hs
      refine ⟨s, 1, EvalG.loopExit (hrun 0 s hs) (hexit s hs), ?_, hs⟩
      simp
  | succ k ih =>
      intro s hs
      obtain ⟨s₁, j₁, hbody₁, hj₁, hq₁⟩ := hbody k s hs
      obtain ⟨s₂, j₂, hrest, hj₂, hq₂⟩ := ih s₁ hq₁
      refine ⟨s₂, j₁ + j₂ + 2,
        EvalG.loopStep (hrun _ s hs) (hguard k s hs) hbody₁ (hrun k s₁ hq₁) hrest, ?_, hq₂⟩
      rw [Nat.succ_mul]
      omega

theorem EvalG.loop_iterate_potential_cost {P : State → Action → Prop} (Q : Nat → State → Prop)
    (Φ : State → Nat) (c : Operand) (body : Block) (J β : Nat)
    (hrun : ∀ k s, Q k s → s.status = .running)
    (hguard : ∀ k s, Q (k + 1) s → s.regs c ≠ 0)
    (hexit : ∀ s, Q 0 s → s.regs c = 0)
    (hbody : ∀ k s, Q (k + 1) s →
      ∃ s' j, EvalG P body s s' j ∧ j + β * Φ s' ≤ J + β * Φ s ∧ Q k s') :
    ∀ k s, Q k s →
      ∃ s' j, EvalG P (.loop c body) s s' j ∧ j ≤ k * (J + 2) + 1 + β * Φ s ∧ Q 0 s' := by
  intro k s hs
  obtain ⟨s', j, h, hj, hq⟩ :=
    EvalG.loop_iterate_potential Q Φ c body J β hrun hguard hexit hbody k s hs
  exact ⟨s', j, h, by omega, hq⟩

/-- Loop composition by a strictly decreasing measure: every iteration from an
invariant state with nonzero guard keeps the invariant and strictly decreases
`μ`, so the loop terminates with a zero guard in at most `μ s * (J + 2) + 1`
steps. -/
theorem EvalG.loop_measure {P : State → Action → Prop} (Q : State → Prop) (μ : State → Nat)
    (c : Operand) (body : Block) (J : Nat)
    (hrun : ∀ s, Q s → s.status = .running)
    (hbody : ∀ s, Q s → s.regs c ≠ 0 →
      ∃ s' j, EvalG P body s s' j ∧ j ≤ J ∧ Q s' ∧ μ s' < μ s) :
    ∀ n s, μ s ≤ n → Q s →
      ∃ s' j, EvalG P (.loop c body) s s' j ∧ j ≤ μ s * (J + 2) + 1 ∧ Q s' ∧ s'.regs c = 0 := by
  intro n
  induction n with
  | zero =>
      intro s hn hs
      by_cases hc : s.regs c = 0
      · exact ⟨s, 1, EvalG.loopExit (hrun s hs) hc, by omega, hs, hc⟩
      · obtain ⟨_, _, _, _, _, hlt⟩ := hbody s hs hc
        omega
  | succ n ih =>
      intro s hn hs
      by_cases hc : s.regs c = 0
      · exact ⟨s, 1, EvalG.loopExit (hrun s hs) hc, by omega, hs, hc⟩
      · obtain ⟨s₁, j₁, hbody₁, hj₁, hq₁, hlt⟩ := hbody s hs hc
        obtain ⟨s₂, j₂, hrest, hj₂, hq₂, hc₂⟩ := ih s₁ (by omega) hq₁
        refine ⟨s₂, j₁ + j₂ + 2,
          EvalG.loopStep (hrun s hs) hc hbody₁ (hrun s₁ hq₁) hrest, ?_, hq₂, hc₂⟩
        have hmul : (μ s₁ + 1) * (J + 2) ≤ μ s * (J + 2) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.succ_mul] at hmul
        omega

theorem EvalG.loop_measure' {P : State → Action → Prop} (Q : State → Prop) (μ : State → Nat)
    (c : Operand) (body : Block) (J : Nat)
    (hrun : ∀ s, Q s → s.status = .running)
    (hbody : ∀ s, Q s → s.regs c ≠ 0 →
      ∃ s' j, EvalG P body s s' j ∧ j ≤ J ∧ Q s' ∧ μ s' < μ s)
    (s : State) (hs : Q s) :
    ∃ s' j, EvalG P (.loop c body) s s' j ∧ j ≤ μ s * (J + 2) + 1 ∧ Q s' ∧ s'.regs c = 0 :=
  EvalG.loop_measure Q μ c body J hrun hbody (μ s) s (Nat.le_refl _) hs

end Structured

end RMQ.SuccinctFinal.PackedConstruction
