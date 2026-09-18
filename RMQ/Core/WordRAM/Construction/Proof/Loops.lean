import RMQ.Core.WordRAM.Construction.Proof.RegSpec

/-! # PRE-1 builder proofs: counted loops and zero-initialized arrays

Outside the builder firewall. `forSlots_spec` is the generic counted loop:
a caller-supplied invariant `Inv k` at slot `k`, established from the initial
state up to the loop registers and advanced by the body, holds at slot
`regs cnt` after the loop. `reserveArray_spec` appends `regs cnt + 1` zero cells
and records the address of the first; `ArrayAt` names a stored array.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder

/-- **Counted loop.** -/
theorem forSlots_spec {W : Nat} (hW : 32 ≤ W) (i go cnt : Operand) (body : Block) (J : Nat)
    (hig : (i : Nat) ≠ go) (hic : (i : Nat) ≠ cnt) (hgc : (go : Nat) ≠ cnt)
    (hi2 : (i : Nat) ≠ 2) (hg2 : (go : Nat) ≠ 2)
    (Inv : Nat → State → Prop) (s : State) (hrun : s.status = .running)
    (hone : s.regs 2 = 1) (hN : s.regs cnt < 2 ^ W)
    (hinit : ∀ u : State, u.status = .running →
      (∀ r : Nat, r ≠ i → r ≠ go → u.regs r = s.regs r) →
      u.memory = s.memory → u.extent = s.extent → u.keys = s.keys → u.keyRegs = s.keyRegs →
      Inv 0 u)
    (hbody : ∀ k (u : State), k < s.regs cnt → Inv k u → u.status = .running →
      u.regs i = k → u.regs cnt = s.regs cnt → u.regs 2 = 1 →
      ∃ u' j, SafeEval W body u u' j ∧ j ≤ J ∧ u'.status = .running ∧ u'.regs i = k ∧
        u'.regs cnt = s.regs cnt ∧ u'.regs 2 = 1 ∧
        ∀ v : State, v.status = .running →
          (∀ r : Nat, r ≠ i → r ≠ go → v.regs r = u'.regs r) →
          v.memory = u'.memory → v.extent = u'.extent → v.keys = u'.keys →
          v.keyRegs = u'.keyRegs → Inv (k + 1) v) :
    ∃ s' k, SafeEval W (forSlots i go cnt body) s s' k ∧ k ≤ s.regs cnt * (J + 4) + 3 ∧
      s'.status = .running ∧ Inv (s.regs cnt) s' ∧ s'.regs i = s.regs cnt ∧
      s'.regs cnt = s.regs cnt := by
  generalize hNdef : s.regs cnt = N at hN hbody ⊢
  have hgi : (go : Nat) ≠ i := fun h => hig h.symm
  have hci : (cnt : Nat) ≠ i := fun h => hic h.symm
  have hcg : (cnt : Nat) ≠ go := fun h => hgc h.symm
  have h2i : (2 : Nat) ≠ i := fun h => hi2 h.symm
  have h2g : (2 : Nat) ≠ go := fun h => hg2 h.symm
  -- initialization
  obtain ⟨t, k0, e0, hk0, ht, htr, htm, hte, htk, htkr⟩ :=
    RegSpec.pure hW [.constant i 0, .comparison .lt go i cnt] s hrun
      (by simp [pureOKs, pureOK])
  have tr : ∀ r : Nat, t.regs r =
      if r = go then (if 0 < N then 1 else 0) else if r = i then 0 else s.regs r := by
    intro r
    rw [htr]
    simp only [pureRegs, pureReg, Comparison.eval, put]
    by_cases hrg : r = go
    · simp [hrg, hci, hNdef]
    · simp [hrg]
  let Q : Nat → State → Prop := fun m u =>
    m ≤ N ∧ u.status = .running ∧ u.regs i = N - m ∧
      u.regs go = (if N - m < N then 1 else 0) ∧ u.regs cnt = N ∧ u.regs 2 = 1 ∧
      Inv (N - m) u
  have hQ : Q N t := by
    refine ⟨Nat.le_refl _, ht, ?_, ?_, ?_, ?_, ?_⟩
    · rw [tr, if_neg hig, if_pos rfl, Nat.sub_self]
    · rw [tr, if_pos rfl, Nat.sub_self]
    · rw [tr, if_neg hcg, if_neg hci, hNdef]
    · rw [tr, if_neg h2g, if_neg h2i, hone]
    · rw [Nat.sub_self]
      exact hinit t ht (fun r hri hrg => by rw [tr, if_neg hrg, if_neg hri]) htm hte htk htkr
  have hloop := EvalG.loop_iterate (P := Action.Safe W) Q go
    (.seq body (acts [.arithmetic .add i i rONE, .comparison .lt go i cnt])) (J + 2)
    (fun m u hu => hu.2.1)
    (fun m u hu => by rw [hu.2.2.2.1, if_pos (by have := hu.1; omega)]; decide)
    (fun u hu => by rw [hu.2.2.2.1, Nat.sub_zero, if_neg (Nat.lt_irrefl _)])
    (by
      intro m u hu
      obtain ⟨hm, hurun, hui, _, hucnt, huone, hinv⟩ := hu
      have hk : N - (m + 1) < N := by omega
      obtain ⟨u', j, hb, hj, hu'run, hu'i, hu'cnt, hu'one, hcont⟩ :=
        hbody (N - (m + 1)) u hk hinv hurun hui hucnt huone
      obtain ⟨v, k2, e2, hk2, hv, hvr, hvm, hve, hvk, hvkr⟩ :=
        RegSpec.pure hW [.arithmetic .add i i rONE, .comparison .lt go i cnt] u' hu'run
          (by
            have h1 : u'.regs i + u'.regs 2 < 2 ^ W := by rw [hu'i, hu'one]; omega
            exact ⟨⟨h1, by simp, by simp, by simp⟩, trivial, trivial⟩)
      have vr : v.regs = put (put u'.regs i (N - (m + 1) + 1)) go
          (if N - (m + 1) + 1 < N then 1 else 0) := by
        rw [hvr]
        show put (put u'.regs i (u'.regs i + u'.regs 2)) go
          (if put u'.regs i (u'.regs i + u'.regs 2) i <
              put u'.regs i (u'.regs i + u'.regs 2) cnt then 1 else 0) = _
        rw [put_same, put_ne _ _ hci, hu'i, hu'one, hu'cnt]
      have hsucc : N - (m + 1) + 1 = N - m := by omega
      refine ⟨v, j + k2, EvalG.seq hb e2, by simp at hk2; omega, ⟨by omega, hv, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [vr, put_ne _ _ hig, put_same, hsucc]
      · rw [vr, put_same, hsucc]
      · rw [vr, put_ne _ _ hcg, put_ne _ _ hci, hu'cnt]
      · rw [vr, put_ne _ _ h2g, put_ne _ _ h2i, hu'one]
      · rw [← hsucc]
        exact hcont v hv (fun r hri hrg => by rw [vr, put_ne _ _ hrg, put_ne _ _ hri])
          (by rw [hvm]) (by rw [hve]) (by rw [hvk]) (by rw [hvkr]))
    N t hQ
  obtain ⟨s', j, hl, hj, hq⟩ := hloop
  obtain ⟨_, hs'run, hs'i, _, hs'cnt, _, hs'inv⟩ := hq
  refine ⟨s', k0 + j, EvalG.seq e0 hl, ?_, hs'run, by simpa using hs'inv,
    by simpa using hs'i, hs'cnt⟩
  simp at hk0
  have : N * (J + 2 + 2) = N * (J + 4) := rfl
  omega

/-- **Counted loop with an amortization potential.** The body may cost `J` plus
`β` times the drop of a potential `Φ` that ignores the two loop registers. -/
theorem forSlots_spec_pot {W : Nat} (hW : 32 ≤ W) (i go cnt : Operand) (body : Block) (J β : Nat)
    (Φ : State → Nat)
    (hig : (i : Nat) ≠ go) (hic : (i : Nat) ≠ cnt) (hgc : (go : Nat) ≠ cnt)
    (hi2 : (i : Nat) ≠ 2) (hg2 : (go : Nat) ≠ 2)
    (Inv : Nat → State → Prop) (s : State) (hrun : s.status = .running)
    (hone : s.regs 2 = 1) (hN : s.regs cnt < 2 ^ W)
    (hΦ : ∀ u v : State, (∀ r : Nat, r ≠ i → r ≠ go → v.regs r = u.regs r) →
      v.memory = u.memory → v.extent = u.extent → Φ v = Φ u)
    (hinit : ∀ u : State, u.status = .running →
      (∀ r : Nat, r ≠ i → r ≠ go → u.regs r = s.regs r) →
      u.memory = s.memory → u.extent = s.extent → u.keys = s.keys → u.keyRegs = s.keyRegs →
      Inv 0 u)
    (hbody : ∀ k (u : State), k < s.regs cnt → Inv k u → u.status = .running →
      u.regs i = k → u.regs cnt = s.regs cnt → u.regs 2 = 1 →
      ∃ u' j, SafeEval W body u u' j ∧ j + β * Φ u' ≤ J + β * Φ u ∧ u'.status = .running ∧
        u'.regs i = k ∧
        u'.regs cnt = s.regs cnt ∧ u'.regs 2 = 1 ∧
        ∀ v : State, v.status = .running →
          (∀ r : Nat, r ≠ i → r ≠ go → v.regs r = u'.regs r) →
          v.memory = u'.memory → v.extent = u'.extent → v.keys = u'.keys →
          v.keyRegs = u'.keyRegs → Inv (k + 1) v) :
    ∃ s' k, SafeEval W (forSlots i go cnt body) s s' k ∧
      k + β * Φ s' ≤ s.regs cnt * (J + 4) + 3 + β * Φ s ∧
      s'.status = .running ∧ Inv (s.regs cnt) s' ∧ s'.regs i = s.regs cnt ∧
      s'.regs cnt = s.regs cnt := by
  generalize hNdef : s.regs cnt = N at hN hbody ⊢
  have hgi : (go : Nat) ≠ i := fun h => hig h.symm
  have hci : (cnt : Nat) ≠ i := fun h => hic h.symm
  have hcg : (cnt : Nat) ≠ go := fun h => hgc h.symm
  have h2i : (2 : Nat) ≠ i := fun h => hi2 h.symm
  have h2g : (2 : Nat) ≠ go := fun h => hg2 h.symm
  -- initialization
  obtain ⟨t, k0, e0, hk0, ht, htr, htm, hte, htk, htkr⟩ :=
    RegSpec.pure hW [.constant i 0, .comparison .lt go i cnt] s hrun
      (by simp [pureOKs, pureOK])
  have tr : ∀ r : Nat, t.regs r =
      if r = go then (if 0 < N then 1 else 0) else if r = i then 0 else s.regs r := by
    intro r
    rw [htr]
    simp only [pureRegs, pureReg, Comparison.eval, put]
    by_cases hrg : r = go
    · simp [hrg, hci, hNdef]
    · simp [hrg]
  let Q : Nat → State → Prop := fun m u =>
    m ≤ N ∧ u.status = .running ∧ u.regs i = N - m ∧
      u.regs go = (if N - m < N then 1 else 0) ∧ u.regs cnt = N ∧ u.regs 2 = 1 ∧
      Inv (N - m) u
  have hQ : Q N t := by
    refine ⟨Nat.le_refl _, ht, ?_, ?_, ?_, ?_, ?_⟩
    · rw [tr, if_neg hig, if_pos rfl, Nat.sub_self]
    · rw [tr, if_pos rfl, Nat.sub_self]
    · rw [tr, if_neg hcg, if_neg hci, hNdef]
    · rw [tr, if_neg h2g, if_neg h2i, hone]
    · rw [Nat.sub_self]
      exact hinit t ht (fun r hri hrg => by rw [tr, if_neg hrg, if_neg hri]) htm hte htk htkr
  have htΦ : Φ t = Φ s := hΦ s t (fun r hri hrg => by rw [tr, if_neg hrg, if_neg hri]) htm hte
  have hloop := EvalG.loop_iterate_potential (P := Action.Safe W) Q Φ go
    (.seq body (acts [.arithmetic .add i i rONE, .comparison .lt go i cnt])) (J + 2) β
    (fun m u hu => hu.2.1)
    (fun m u hu => by rw [hu.2.2.2.1, if_pos (by have := hu.1; omega)]; decide)
    (fun u hu => by rw [hu.2.2.2.1, Nat.sub_zero, if_neg (Nat.lt_irrefl _)])
    (by
      intro m u hu
      obtain ⟨hm, hurun, hui, _, hucnt, huone, hinv⟩ := hu
      have hk : N - (m + 1) < N := by omega
      obtain ⟨u', j, hb, hj, hu'run, hu'i, hu'cnt, hu'one, hcont⟩ :=
        hbody (N - (m + 1)) u hk hinv hurun hui hucnt huone
      obtain ⟨v, k2, e2, hk2, hv, hvr, hvm, hve, hvk, hvkr⟩ :=
        RegSpec.pure hW [.arithmetic .add i i rONE, .comparison .lt go i cnt] u' hu'run
          (by
            have h1 : u'.regs i + u'.regs 2 < 2 ^ W := by rw [hu'i, hu'one]; omega
            exact ⟨⟨h1, by simp, by simp, by simp⟩, trivial, trivial⟩)
      have vr : v.regs = put (put u'.regs i (N - (m + 1) + 1)) go
          (if N - (m + 1) + 1 < N then 1 else 0) := by
        rw [hvr]
        show put (put u'.regs i (u'.regs i + u'.regs 2)) go
          (if put u'.regs i (u'.regs i + u'.regs 2) i <
              put u'.regs i (u'.regs i + u'.regs 2) cnt then 1 else 0) = _
        rw [put_same, put_ne _ _ hci, hu'i, hu'one, hu'cnt]
      have hsucc : N - (m + 1) + 1 = N - m := by omega
      have hvΦ : Φ v = Φ u' := hΦ u' v (fun r hri hrg => by rw [vr, put_ne _ _ hrg, put_ne _ _ hri])
        (by rw [hvm]) (by rw [hve])
      refine ⟨v, j + k2, EvalG.seq hb e2, by simp at hk2; rw [hvΦ]; omega,
        ⟨by omega, hv, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [vr, put_ne _ _ hig, put_same, hsucc]
      · rw [vr, put_same, hsucc]
      · rw [vr, put_ne _ _ hcg, put_ne _ _ hci, hu'cnt]
      · rw [vr, put_ne _ _ h2g, put_ne _ _ h2i, hu'one]
      · rw [← hsucc]
        exact hcont v hv (fun r hri hrg => by rw [vr, put_ne _ _ hrg, put_ne _ _ hri])
          (by rw [hvm]) (by rw [hve]) (by rw [hvk]) (by rw [hvkr]))
    N t hQ
  obtain ⟨s', j, hl, hj, hq⟩ := hloop
  obtain ⟨_, hs'run, hs'i, _, hs'cnt, _, hs'inv⟩ := hq
  refine ⟨s', k0 + j, EvalG.seq e0 hl, ?_, hs'run, by simpa using hs'inv,
    by simpa using hs'i, hs'cnt⟩
  simp at hk0
  have : N * (J + 2 + 2) = N * (J + 4) := rfl
  rw [htΦ] at hj
  omega


/-- `Emits` depends only on the memory and extent of the later state. -/
theorem Emits.congr_right {s₀ u v : State} {vals : List Nat} (h : Emits s₀ u vals)
    (hm : v.memory = u.memory) (he : v.extent = u.extent) : Emits s₀ v vals := by
  refine ⟨by rw [he]; exact h.1, fun a => ?_⟩
  rw [hm]; exact h.2 a

theorem flatMap_range_succ (g : Nat → List Nat) (k : Nat) :
    (List.range (k + 1)).flatMap g = (List.range k).flatMap g ++ g k := by
  rw [List.range_succ, List.flatMap_append]
  simp

/-- **Flat-map emission.** A counted loop whose body, at slot `k`, appends the
cells `g k` emits `(List.range (regs cnt)).flatMap g`. `Keep` carries the
caller's frame facts; it must be insensitive to the two loop registers. -/
theorem emitFlatMap_spec {W : Nat} (hW : 32 ≤ W) (i go cnt : Operand) (body : Block) (J : Nat)
    (g : Nat → List Nat) (Keep : State → Prop)
    (hig : (i : Nat) ≠ go) (hic : (i : Nat) ≠ cnt) (hgc : (go : Nat) ≠ cnt)
    (hi2 : (i : Nat) ≠ 2) (hg2 : (go : Nat) ≠ 2)
    (s : State) (hrun : s.status = .running) (hone : s.regs 2 = 1) (hN : s.regs cnt < 2 ^ W)
    (hKeep0 : ∀ u : State, u.status = .running →
      (∀ r : Nat, r ≠ i → r ≠ go → u.regs r = s.regs r) →
      u.memory = s.memory → u.extent = s.extent → u.keys = s.keys → u.keyRegs = s.keyRegs →
      Keep u)
    (hKeep : ∀ u v : State, Keep u → (∀ r : Nat, r ≠ i → r ≠ go → v.regs r = u.regs r) →
      v.memory = u.memory → v.extent = u.extent → v.keys = u.keys → v.keyRegs = u.keyRegs →
      Keep v)
    (hbody : ∀ k (u : State), k < s.regs cnt → Keep u → u.status = .running →
      u.regs i = k → u.regs cnt = s.regs cnt → u.regs 2 = 1 →
      ∃ u' j, SafeEval W body u u' j ∧ j ≤ J ∧ u'.status = .running ∧ u'.regs i = k ∧
        u'.regs cnt = s.regs cnt ∧ u'.regs 2 = 1 ∧ Emits u u' (g k) ∧ Keep u') :
    ∃ s' k, SafeEval W (forSlots i go cnt body) s s' k ∧ k ≤ s.regs cnt * (J + 4) + 3 ∧
      s'.status = .running ∧ Emits s s' ((List.range (s.regs cnt)).flatMap g) ∧ Keep s' := by
  obtain ⟨s', k, e, hk, hr, ⟨hemit, hkeep⟩, _, _⟩ :=
    forSlots_spec hW i go cnt body J hig hic hgc hi2 hg2
      (fun k u => Emits s u ((List.range k).flatMap g) ∧ Keep u) s hrun hone hN
      (fun u hu hregs hm he hk hkr => ⟨by
          simp only [List.range_zero, List.flatMap_nil]
          exact (Emits.refl s).congr_right hm he, hKeep0 u hu hregs hm he hk hkr⟩)
      (fun k u hk ⟨hue, huk⟩ hur hui hucnt huone => by
        obtain ⟨u', j, eb, hj, hu'r, hu'i, hu'cnt, hu'one, hu'e, hu'k⟩ :=
          hbody k u hk huk hur hui hucnt huone
        refine ⟨u', j, eb, hj, hu'r, hu'i, hu'cnt, hu'one, fun v _ hvr hvm hve hvk hvkr => ?_⟩
        refine ⟨?_, hKeep u' v hu'k hvr hvm hve hvk hvkr⟩
        rw [flatMap_range_succ]
        exact (hue.trans hu'e).congr_right hvm hve)
  exact ⟨s', k, e, hk, hr, hemit, hkeep⟩

/-- Loop composition by an exactly accounted decreasing measure: the cost pays
`J + 2` per unit of measure actually consumed. -/
theorem EvalG.loop_measure_pot {P : State → Action → Prop} (Q : State → Prop) (μ : State → Nat)
    (c : Operand) (body : Block) (J : Nat)
    (hrun : ∀ s, Q s → s.status = .running)
    (hbody : ∀ s, Q s → s.regs c ≠ 0 →
      ∃ s' j, EvalG P body s s' j ∧ j ≤ J ∧ Q s' ∧ μ s' < μ s) :
    ∀ N s, μ s ≤ N → Q s →
      ∃ s' j, EvalG P (.loop c body) s s' j ∧ j + μ s' * (J + 2) ≤ μ s * (J + 2) + 1 ∧
        Q s' ∧ s'.regs c = 0 := by
  intro N
  induction N with
  | zero =>
      intro s hN hs
      by_cases hc : s.regs c = 0
      · exact ⟨s, 1, EvalG.loopExit (hrun s hs) hc, by omega, hs, hc⟩
      · obtain ⟨_, _, _, _, _, hlt⟩ := hbody s hs hc
        omega
  | succ N ih =>
      intro s hN hs
      by_cases hc : s.regs c = 0
      · exact ⟨s, 1, EvalG.loopExit (hrun s hs) hc, by omega, hs, hc⟩
      · obtain ⟨s₁, j₁, hb₁, hj₁, hq₁, hlt⟩ := hbody s hs hc
        obtain ⟨s₂, j₂, hr₂, hj₂, hq₂, hc₂⟩ := ih s₁ (by omega) hq₁
        refine ⟨s₂, j₁ + j₂ + 2, EvalG.loopStep (hrun s hs) hc hb₁ (hrun s₁ hq₁) hr₂, ?_, hq₂, hc₂⟩
        have hmul : (μ s₁ + 1) * (J + 2) ≤ μ s * (J + 2) := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.succ_mul] at hmul
        omega

/-! ## Zero-initialized arrays -/

/-- **Array reservation.** -/
theorem reserveArray_spec {W : Nat} (hW : 32 ≤ W) (base cnt : Operand)
    (hb0 : (base : Nat) ≠ 0) (hb2 : (base : Nat) ≠ 2) (hb10 : (base : Nat) ≠ 10)
    (hb12 : (base : Nat) ≠ 12) (hcb : (cnt : Nat) ≠ base)
    (s : State) (hrun : s.status = .running) (hzero : s.regs 0 = 0) (hone : s.regs 2 = 1)
    (hext : s.extent + s.regs cnt + 1 < 2 ^ W) :
    ∃ s' k, SafeEval W (reserveArray base cnt) s s' k ∧ k ≤ 5 * s.regs cnt + 4 ∧
      s'.status = .running ∧ Emits s s' (List.replicate (s.regs cnt + 1) 0) ∧
      s'.regs base = s.extent ∧
      (∀ r : Nat, r ≠ base → r ≠ 10 → r ≠ 12 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  generalize hNdef : s.regs cnt = N at hext ⊢
  have n0 : (0 : Nat) ≠ base := fun h => hb0 h.symm
  have n2 : (2 : Nat) ≠ base := fun h => hb2 h.symm
  have hW2 : 2 < 2 ^ W := two_le_two_pow hW
  -- initialization: reserve base; store base ZERO; move ECNT cnt
  let t1 := execPrim (Prim.reserve base) s
  have f1 := exec_reserve s base
  have t1r : t1.regs = put s.regs base s.extent := by simp [t1, f1]
  have t1lt : t1.regs base < t1.extent := by simp [t1, f1]
  let t2 := execPrim (Prim.store base rZERO) t1
  have f2 := exec_store t1 base rZERO t1lt
  let t3 := execPrim (Prim.move rECNT cnt) t2
  have f3 := exec_move t2 rECNT cnt
  have t1zero : t1.regs 0 = 0 := by rw [t1r, put_ne _ _ n0, hzero]
  have t3r : t3.regs = put (put s.regs base s.extent) 12 N := by
    simp only [t3, f3, t2, f2, t1r]
    rw [put_ne _ _ hcb, hNdef]
    rfl
  have t3m : t3.memory = put s.memory s.extent (some 0) := by
    simp only [t3, f3, t2, f2]
    show put t1.memory (t1.regs base) (some (t1.regs 0)) = _
    rw [t1zero]
    simp [t1, f1]
  have t3e : t3.extent = s.extent + 1 := by simp [t3, f3, t2, f2, t1, f1]
  have t3s : t3.status = .running := by simp [t3, f3, t2, f2, t1, f1, hrun]
  have t3k : t3.keys = s.keys ∧ t3.keyRegs = s.keyRegs := by simp [t3, f3, t2, f2, t1, f1]
  have hinit : SafeEval W (acts [.reserve base, .store base rZERO, .move rECNT cnt]) s t3 3 :=
    acts_evalG (P := Action.Safe W) _ s hrun
      ⟨safe_reserve hW s _ (by omega), by simp [Action.prim, f1, hrun],
        safe_store hW t1 _ _ t1lt (by simp only [operand_val_0]; rw [t1zero]; omega),
        by show (execPrim (Prim.store base rZERO) t1).status = .running
           rw [f2]; simp [t1, f1, hrun],
        safe_move hW t2 _ _, t3s, trivial⟩
  let Q : Nat → State → Prop := fun m u =>
    m ≤ N ∧ u.status = .running ∧ u.regs 12 = m ∧ u.regs base = s.extent ∧
      Emits s u (List.replicate (N + 1 - m) 0) ∧
      (∀ r : Nat, r ≠ base → r ≠ 10 → r ≠ 12 → u.regs r = s.regs r) ∧
      u.keyRegs = s.keyRegs ∧ u.keys = s.keys
  have hQ : Q N t3 := by
    refine ⟨Nat.le_refl _, t3s, by rw [t3r]; simp, ?_, ?_, ?_, t3k.2, t3k.1⟩
    · rw [t3r, put_ne _ _ hb12, put_same]
    · refine ⟨by simp [t3e], fun a => ?_⟩
      rw [t3m, show N + 1 - N = 1 by omega]
      by_cases ha : a = s.extent
      · subst ha; simp
      · rw [put_ne _ _ ha, if_neg (by simp; omega)]
    · intro r hrb _ h12
      rw [t3r, put_ne _ _ h12, put_ne _ _ hrb]
  have hloop := EvalG.loop_iterate (P := Action.Safe W) Q rECNT
    (.seq (emitBit rZERO) (.action (.arithmetic .sub rECNT rECNT rONE))) 3
    (fun m u hu => hu.2.1)
    (fun m u hu => by simp only [operand_val_12]; rw [hu.2.2.1]; omega)
    (fun u hu => by simp only [operand_val_12]; exact hu.2.2.1)
    (by
      intro m u hu
      obtain ⟨hm, hurun, hucnt, hubase, huemit, hufr, hukr, huk⟩ := hu
      have hu0 : u.regs 0 = 0 := by rw [hufr 0 n0 (by decide) (by decide), hzero]
      have hu2 : u.regs 2 = 1 := by rw [hufr 2 n2 (by decide) (by decide), hone]
      have huext : u.extent = s.extent + (N - m) := by
        rw [huemit.1]; simp only [List.length_replicate]; omega
      obtain ⟨u1, e1, hu1run, hu1emit, hu1fr, hu1kr, hu1k⟩ :=
        emitBit_spec hW rZERO (by decide) u hurun (by simp only [operand_val_0]; rw [hu0]; omega)
          (by rw [huext]; omega)
      have hu1cnt : u1.regs 12 = m + 1 := by rw [hu1fr 12 (by decide), hucnt]
      have hu1one : u1.regs 2 = 1 := by rw [hu1fr 2 (by decide), hu2]
      let u2 := execPrim (Prim.arithmetic .sub rECNT rECNT rONE) u1
      have g2 := exec_arithmetic u1 .sub rECNT rECNT rONE
      have u2r : u2.regs = put u1.regs 12 m := by
        simp [u2, g2, Arithmetic.eval, hu1cnt, hu1one]
      have u2s : u2.status = .running := by simp [u2, g2, hu1run]
      have hsafe : Action.Safe W u1 (.arithmetic .sub rECNT rECNT rONE) :=
        safe_sub hW u1 _ _ _ (by simp only [operand_val_12, operand_val_2]; rw [hu1cnt, hu1one]; omega)
          (by simp only [operand_val_12]; rw [hu1cnt]; omega)
      refine ⟨u2, 2 + 1, EvalG.seq e1 (EvalG.action _ u1 hu1run hsafe), by omega,
        by omega, u2s, by rw [u2r, put_same], ?_, ?_, ?_, ?_, ?_⟩
      · rw [u2r, put_ne _ _ hb12, hu1fr base hb10, hubase]
      · have hm' : N + 1 - m = (N + 1 - (m + 1)) + 1 := by omega
        have hemit : Emits u u2 [0] := by
          have h0 : u.regs rZERO = 0 := hu0
          rw [h0] at hu1emit
          refine ⟨by simp [u2, g2, hu1emit.1], fun a => ?_⟩
          simp only [u2, g2]
          exact hu1emit.2 a
        rw [hm', List.replicate_succ']
        exact huemit.trans hemit
      · intro r hrb h10 h12
        rw [u2r, put_ne _ _ h12, hu1fr r h10, hufr r hrb h10 h12]
      · simp [u2, g2, hu1kr, hukr]
      · simp [u2, g2, hu1k, huk])
    N t3 hQ
  obtain ⟨s', j, hl, hj, hq⟩ := hloop
  obtain ⟨_, hs'run, _, hs'base, hs'emit, hs'fr, hs'kr, hs'k⟩ := hq
  refine ⟨s', 3 + j, EvalG.seq hinit hl, ?_, hs'run, by simpa using hs'emit, hs'base,
    hs'fr, hs'kr, hs'k⟩
  have : N * (3 + 2) = 5 * N := by rw [Nat.mul_comm]
  omega

/-- The array stored at `base`: `len` present cells holding `f 0, …, f (len - 1)`. -/
def ArrayAt (s : State) (base len : Nat) (f : Nat → Nat) : Prop :=
  base + len ≤ s.extent ∧ ∀ i, i < len → s.memory (base + i) = some (f i)

theorem Emits.arrayAt {s₀ s : State} {vals : List Nat} (h : Emits s₀ s vals) :
    ArrayAt s s₀.extent vals.length (fun i => vals.getD i 0) := by
  refine ⟨by rw [h.1]; exact Nat.le_refl _, fun i hi => ?_⟩
  rw [h.memory_at hi]
  simp [List.getD, List.getElem?_eq_getElem hi]

end RMQ.SuccinctFinal.PackedConstruction.Proof
