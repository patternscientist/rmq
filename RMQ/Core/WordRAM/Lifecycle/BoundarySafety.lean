import RMQ.Core.WordRAM.Lifecycle.Safety

/-! # Represented charged request admission

Instruction safety and external boundary safety are separate cases of the
whole trace. The boundary's fixed entry and finite destination bank are explicit.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle

def Boundary.Safe (W len bank entry : Nat) : Boundary → Prop
  | .left v => requestLeftRegister < bank ∧ v < 2^W
  | .right v => requestRightRegister < bank ∧ v < 2^W
  | .entry target => target.val = entry ∧ entry < len ∧ entry < 2^W
  | .activate => True

def Transition.ActionSafe (W len bank entry : Nat) (t : Transition) : Prop :=
  t.Safe W len ∨ ∃ b, t.action = .boundary b ∧ b.Safe W len bank entry

theorem instruction_action_safe {W len bank entry : Nat} {t : Transition}
    (h : t.Safe W len) : t.ActionSafe W len bank entry := Or.inl h

theorem boundary_execute_fits {W len bank entry : Nat} {s : State} {b : Boundary}
    (fit : s.Fits W) (safe : b.Safe W len bank entry) : (executeBoundary b s).Fits W := by
  obtain ⟨⟨hr, hp, he, hm, hh⟩, hk, hkr⟩ := fit
  cases b with
  | left v =>
    refine ⟨⟨?_, hp, he, hm, hh⟩, hk, hkr⟩
    intro r
    change (PackedConstruction.put s.core.regs requestLeftRegister v) r < 2^W
    by_cases h : r = requestLeftRegister
    · simpa [PackedConstruction.put, h] using safe.2
    · simpa [PackedConstruction.put, h] using hr r
  | right v =>
    refine ⟨⟨?_, hp, he, hm, hh⟩, hk, hkr⟩
    intro r
    change (PackedConstruction.put s.core.regs requestRightRegister v) r < 2^W
    by_cases h : r = requestRightRegister
    · simpa [PackedConstruction.put, h] using safe.2
    · simpa [PackedConstruction.put, h] using hr r
  | entry target =>
    refine ⟨⟨hr, ?_, he, hm, hh⟩, hk, hkr⟩
    change target.val < 2^W
    rw [safe.1]
    exact safe.2.2
  | activate => exact ⟨⟨hr, hp, he, hm, fun _ h => by cases h⟩, hk, hkr⟩

theorem boundary_execute_closed (b : Boundary) (s : State) (closed : s.Closed) :
    (executeBoundary b s).Closed := by cases b <;> exact closed

theorem boundary_execute_tail {W len bank entry : Nat} {s : State} {b : Boundary}
    (safe : b.Safe W len bank entry) (tail : ∀ r, bank ≤ r → s.core.regs r = 0) :
    ∀ r, bank ≤ r → (executeBoundary b s).core.regs r = 0 := by
  intro r hr
  cases b with
  | left v => simp [executeBoundary, PackedConstruction.put,
      show r ≠ requestLeftRegister by have := safe.1; omega, tail r hr]
  | right v => simp [executeBoundary, PackedConstruction.put,
      show r ≠ requestRightRegister by have := safe.1; omega, tail r hr]
  | entry target => exact tail r hr
  | activate => exact tail r hr

theorem runBoundary_safe {W len bank entry : Nat} (bs : List Boundary) (s : State)
    (allSafe : ∀ b ∈ bs, b.Safe W len bank entry) (fit : s.Fits W) (closed : s.Closed)
    (tail : ∀ r, bank ≤ r → s.core.regs r = 0) :
    (runBoundary bs s).final.Fits W ∧ (runBoundary bs s).final.Closed ∧
      (∀ r, bank ≤ r → (runBoundary bs s).final.core.regs r = 0) ∧
      ∀ t ∈ (runBoundary bs s).transitions,
        t.ActionSafe W len bank entry ∧ t.before.Fits W ∧ t.after.Fits W ∧
          t.before.Closed ∧ t.after.Closed := by
  induction bs generalizing s with
  | nil => exact ⟨fit, closed, tail, fun _ h => by cases h⟩
  | cons b bs ih =>
    have hb := allSafe b (by simp)
    have restSafe : ∀ c ∈ bs, c.Safe W len bank entry := fun c hc => allSafe c (by simp [hc])
    cases hs : s.core.status with
    | running => simpa [runBoundary, boundaryStep, hs] using
        (show s.Fits W ∧ s.Closed ∧ (∀ r, bank ≤ r → s.core.regs r = 0) ∧
          ∀ t ∈ ([] : List Transition), t.ActionSafe W len bank entry ∧
            t.before.Fits W ∧ t.after.Fits W ∧ t.before.Closed ∧ t.after.Closed from
          ⟨fit, closed, tail, fun _ h => by cases h⟩)
    | fault => simpa [runBoundary, boundaryStep, hs] using
        (show s.Fits W ∧ s.Closed ∧ (∀ r, bank ≤ r → s.core.regs r = 0) ∧
          ∀ t ∈ ([] : List Transition), t.ActionSafe W len bank entry ∧
            t.before.Fits W ∧ t.after.Fits W ∧ t.before.Closed ∧ t.after.Closed from
          ⟨fit, closed, tail, fun _ h => by cases h⟩)
    | halted value =>
      have hf := boundary_execute_fits fit hb
      have hc := boundary_execute_closed b s closed
      have ht := boundary_execute_tail hb tail
      have rest := ih (executeBoundary b s) restSafe hf hc ht
      simp only [runBoundary, boundaryStep, hs]
      refine ⟨rest.1, rest.2.1, rest.2.2.1, ?_⟩
      intro t hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ⟨Or.inr ⟨b, rfl, hb⟩, fit, hf, closed, hc⟩
      · exact rest.2.2.2 t hm

theorem requestProtocol_safe {W len bank : Nat} (entry : PackedConstruction.Operand)
    (left right : Nat) (s : State)
    (hl : left < 2^W) (hr : right < 2^W) (he : entry.val < len) (hw : entry.val < 2^W)
    (hbank : 301 < bank) (fit : s.Fits W) (closed : s.Closed)
    (tail : ∀ r, bank ≤ r → s.core.regs r = 0) :
    (requestProtocol entry left right s).final.Fits W ∧
      (requestProtocol entry left right s).final.Closed ∧
      (∀ r, bank ≤ r → (requestProtocol entry left right s).final.core.regs r = 0) ∧
      ∀ t ∈ (requestProtocol entry left right s).transitions,
        t.ActionSafe W len bank entry.val ∧ t.before.Fits W ∧ t.after.Fits W ∧
          t.before.Closed ∧ t.after.Closed := by
  apply runBoundary_safe _ s _ fit closed tail
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨by change 300 < bank; omega, hl⟩
  · exact ⟨hbank, hr⟩
  · exact ⟨rfl, he, hw⟩
  · trivial

end RMQ.SuccinctFinal.PackedLifecycle
