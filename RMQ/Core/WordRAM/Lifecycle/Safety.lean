import RMQ.Core.WordRAM.Lifecycle.Calculus

/-! # Width and scalar retirement laws

Key values remain in the comparison model. Numeric words, program control and
owned extents use the same declared width throughout each execution segment.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle

theorem execute_safe_fits {W len : Nat} {s : State} {i : Instruction}
    (hf : s.Fits W) (hs : i.Safe W len s) (hpc : s.core.pc < len)
    (hlen : len < 2 ^ W) : (execute i s).Fits W := by
  obtain ⟨hc, hk, hkr⟩ := hf
  cases i with
  | old p => exact ⟨PackedConstruction.Prim.safe_fits hc hs hpc hlen, hk, hkr⟩
  | releaseCell =>
    have hp : 0 < s.core.extent := hs.2
    obtain ⟨hr, _, he, hm, hh⟩ := hc
    simp only [execute, Nat.ne_of_gt hp, ↓reduceIte, State.Fits,
      PackedConstruction.State.Fits, PackedConstruction.State.next]
    refine ⟨⟨hr, by omega, by omega, ?_, hh⟩, hk, hkr⟩
    intro a v hv
    by_cases ha : a = s.core.extent - 1
    · simp [PackedConstruction.put, ha] at hv
    · exact hm a v (by simpa [PackedConstruction.put, ha] using hv)
  | releaseKey =>
    have hp : 0 < s.keyExtent := hs.2
    obtain ⟨hr, _, he, hm, hh⟩ := hc
    simp only [execute, Nat.ne_of_gt hp, ↓reduceIte, State.Fits,
      PackedConstruction.State.Fits, PackedConstruction.State.next]
    exact ⟨⟨hr, by omega, he, hm, hh⟩, by omega, hkr⟩
  | releaseKeyRegister =>
    have hp : 0 < s.keyRegExtent := hs.2
    obtain ⟨hr, _, he, hm, hh⟩ := hc
    simp only [execute, Nat.ne_of_gt hp, ↓reduceIte, State.Fits,
      PackedConstruction.State.Fits, PackedConstruction.State.next]
    exact ⟨⟨hr, by omega, he, hm, hh⟩, hk, by omega⟩

def Transition.Safe (W len : Nat) (t : Transition) : Prop :=
  ∃ i, t.action = .instruction i ∧ i.Safe W len t.before

theorem step_safe_fits {program : List Instruction} {s : State} {t : Transition} {W : Nat}
    (hstep : step program s = some t) (hf : s.Fits W)
    (hlen : program.length < 2 ^ W) (hs : t.Safe W program.length) : t.after.Fits W := by
  obtain ⟨hb, _, i, hfetch, hi, ha⟩ := step_spec hstep
  obtain ⟨j, hj, hjSafe⟩ := hs
  have heq : j = i := Action.instruction.inj (hj.symm.trans hi)
  subst j
  rw [hb] at hjSafe
  rw [ha]
  exact execute_safe_fits hf hjSafe (List.getElem?_eq_some_iff.mp hfetch).1 hlen

theorem run_fits {program : List Instruction} {fuel : Nat} {s : State} {W : Nat}
    (hf : s.Fits W) (hlen : program.length < 2 ^ W)
    (hs : ∀ t ∈ (run program fuel s).transitions, t.Safe W program.length) :
    (run program fuel s).final.Fits W ∧
      ∀ t ∈ (run program fuel s).transitions, t.before.Fits W ∧ t.after.Fits W := by
  induction fuel generalizing s with
  | zero => simp [run]; exact hf
  | succ fuel ih =>
    cases h : step program s with
    | none => simpa [run, h] using hf
    | some t =>
      have ht := step_safe_fits h hf hlen (hs t (by simp [run, h]))
      have hrest := ih ht (fun u hu => hs u (by simp [run, h, hu]))
      refine ⟨by simpa [run, h] using hrest.1, ?_⟩
      intro u hu
      simp only [run, h, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact ⟨(step_spec h).1 ▸ hf, ht⟩
      · exact hrest.2 u hu

theorem releaseCell_closed (s : State) (h : s.Closed) : (execute .releaseCell s).Closed := by
  obtain ⟨hm, hk, hkr⟩ := h
  by_cases hz : s.core.extent = 0
  · simpa [execute, hz, State.Closed, PackedConstruction.CleanTail] using
      (show s.Closed from ⟨hm, hk, hkr⟩)
  · simp only [execute, hz, ↓reduceIte, State.Closed, PackedConstruction.CleanTail,
      PackedConstruction.State.next]
    refine ⟨?_, hk, hkr⟩
    intro a ha
    by_cases he : a = s.core.extent - 1
    · simp [PackedConstruction.put, he]
    · simp [PackedConstruction.put, he, hm a (by omega)]

theorem releaseKey_closed (s : State) (h : s.Closed) : (execute .releaseKey s).Closed := by
  obtain ⟨hm, hk, hkr⟩ := h
  by_cases hz : s.keyExtent = 0
  · simpa [execute, hz, State.Closed, PackedConstruction.CleanTail] using
      (show s.Closed from ⟨hm, hk, hkr⟩)
  · simp only [execute, hz, ↓reduceIte, State.Closed, PackedConstruction.CleanTail,
      PackedConstruction.State.next]
    refine ⟨hm, ?_, hkr⟩
    intro a ha
    by_cases he : a = s.keyExtent - 1
    · simp [PackedConstruction.put, he]
    · simp [PackedConstruction.put, he, hk a (by omega)]

theorem releaseKeyRegister_closed (s : State) (h : s.Closed) :
    (execute .releaseKeyRegister s).Closed := by
  obtain ⟨hm, hk, hkr⟩ := h
  by_cases hz : s.keyRegExtent = 0
  · simpa [execute, hz, State.Closed, PackedConstruction.CleanTail] using
      (show s.Closed from ⟨hm, hk, hkr⟩)
  · simp only [execute, hz, ↓reduceIte, State.Closed, PackedConstruction.CleanTail,
      PackedConstruction.State.next]
    refine ⟨hm, hk, ?_⟩
    intro r hr
    by_cases he : r = s.keyRegExtent - 1
    · simp [PackedConstruction.put, he]
    · simp [PackedConstruction.put, he, hkr r (by omega)]

theorem empty_keys_of_closed (s : State) (h : s.Closed)
    (hk : s.keyExtent = 0) (hkr : s.keyRegExtent = 0) :
    s.core.keys = (fun _ => none) ∧ s.core.keyRegs = (fun _ => 0) := by
  constructor
  · funext a; exact h.2.1 a (by omega)
  · funext r; exact h.2.2 r (by omega)

theorem requestProtocol_preserves_allocation (entry : PackedConstruction.Operand)
    (left right answer : Nat) (s : State) (hs : s.core.status = .halted answer) :
    let final := (requestProtocol entry left right s).final
    final.core.memory = s.core.memory ∧ final.core.extent = s.core.extent ∧
      final.core.keys = s.core.keys ∧ final.core.keyRegs = s.core.keyRegs ∧
      final.keyExtent = s.keyExtent ∧ final.keyRegExtent = s.keyRegExtent := by
  simp [(requestProtocol_exact entry left right answer s hs).1]

end RMQ.SuccinctFinal.PackedLifecycle
