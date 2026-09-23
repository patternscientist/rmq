import RMQ.Core.WordRAM.Construction.Proof.Cartesian

/-! # PRE-1 builder proofs: the stack step and the stack pass (stage S3)

Outside the builder firewall. `StackInv xs e0 sA i u` is the stack-pass
invariant after `i` indices: the stack region holds the right spine
`spineFrom (buildTree (xs.take i)) 0` (input indices, bottom to top), the
leftmost-descendant region holds the spine's leftmost indices at the spine
nodes, and the count region holds `openCounts (buildTree (xs.take i)).shape`.
`stackStep_spec` establishes it for `i + 1` from `i`, through the reference
insertion law `openCounts_insertRight`, the spine insertion law
`spineFrom_insertRight`, `insertPoint_eq_find` and the sorted spine;
`stackPass_spec` iterates it over all indices with an amortized cost.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec Spec.StackCartesianTreeSpec RMQ.Cartesian

/-! ## One stack step -/

/-- An input predicate that only reads memory below `e0`, extent and keys. -/
def InpBelow (Inp : State → Prop) (e0 : Nat) : Prop :=
  ∀ u v : State, Inp u → (∀ b, b < e0 → v.memory b = u.memory b) → u.extent ≤ v.extent →
    v.keys = u.keys → Inp v

theorem InpBelow.stable {Inp : State → Prop} {e0 : Nat} (h : InpBelow Inp e0) : InpStable Inp :=
  fun u v hu hm he hk => h u v hu (fun b _ => by rw [hm]) (Nat.le_of_eq he.symm) hk

/-- The right spine of the stack tree of the first `i` keys. -/
abbrev spineAt (xs : List Int) (i : Nat) : List (Nat × Nat × Int) :=
  spineFrom (StackCartesianTree.buildTree (xs.take i)) 0

/-- The open counts of the stack tree of the first `i` keys. -/
abbrev countsAt (xs : List Int) (i : Nat) : List Nat :=
  openCounts (StackCartesianTree.buildTree (xs.take i)).shape

/-- **Stack-pass invariant** after `i` indices, relative to the pass start `sA`. -/
def StackInv (xs : List Int) (e0 : Nat) (sA : State) (i : Nat) (u : State) : Prop :=
  u.regs 103 = (spineAt xs i).length ∧ u.extent = sA.extent ∧ u.keys = sA.keys ∧
    (∀ b, (b < e0 ∨ e0 + 3 * (xs.length + 1) ≤ b) → u.memory b = sA.memory b) ∧
    (∀ r : Nat, ¬ (4 ≤ r ∧ r ≤ 8) → ¬ (103 ≤ r ∧ r ≤ 112) → u.regs r = sA.regs r) ∧
    ∃ M : Nat → Nat, Region u e0 (3 * (xs.length + 1)) M ∧
      (∀ k (hk : k < (spineAt xs i).length), M k = ((spineAt xs i)[k]).1) ∧
      (∀ k (hk : k < (spineAt xs i).length),
        M (xs.length + 1 + ((spineAt xs i)[k]).1) = ((spineAt xs i)[k]).2.1) ∧
      (∀ j, j ≤ xs.length → M (2 * (xs.length + 1) + j) = (countsAt xs i).getD j 0)

/-- Hypotheses on the pass start state. -/
structure PassStart (xs : List Int) (e0 : Nat) (sA : State) : Prop where
  base0 : sA.regs 100 = e0
  base1 : sA.regs 101 = e0 + (xs.length + 1)
  base2 : sA.regs 102 = e0 + 2 * (xs.length + 1)
  one : sA.regs 2 = 1
  len : sA.regs 1 = xs.length
  ext : e0 + 3 * (xs.length + 1) ≤ sA.extent

theorem spine_length_le (xs : List Int) (i : Nat) (hi : i ≤ xs.length) :
    (spineAt xs i).length ≤ i := by
  have hnodup : ∀ (k : Nat) (hk : k < (spineAt xs i).length), ((spineAt xs i)[k]).1 < i := by
    intro k hk
    exact (spine_entry_facts xs i hi _ (List.getElem_mem hk)).2.1
  -- spine indices are strictly increasing, hence at most `i` of them
  have hinc : ∀ (t : StackCartesianTree) (o : Nat) (k : Nat) (hk : k < (spineFrom t o).length),
      o + k ≤ ((spineFrom t o)[k]).1 := by
    intro t
    induction t with
    | empty => intro o k hk; simp [spineFrom] at hk
    | node l p r _ ihr =>
        intro o k hk
        cases k with
        | zero => simp [spineFrom]
        | succ k =>
            simp only [spineFrom, List.length_cons] at hk
            simp only [spineFrom, List.getElem_cons_succ]
            have := ihr (o + l.shape.size + 1) k (by omega)
            omega
  by_cases h : (spineAt xs i).length = 0
  · omega
  · have h1 : 0 + ((spineAt xs i).length - 1) ≤
        ((spineAt xs i)[(spineAt xs i).length - 1]'(by omega)).1 :=
      hinc (StackCartesianTree.buildTree (xs.take i)) 0 _ _
    have h2 := hnodup ((spineAt xs i).length - 1) (by omega)
    omega

set_option maxHeartbeats 1600000 in
/-- **One stack step.** -/
theorem stackStep_spec {W : Nat} (hW : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (hleaf : KeySpec W xs Inp leaf) (e0 : Nat) (hInp : InpBelow Inp e0)
    (sA : State) (hA : PassStart xs e0 sA) (hinpA : Inp sA)
    (hcap : e0 + 3 * (xs.length + 1) + xs.length + 2 < 2 ^ W)
    (i : Nat) (hi : i < xs.length) (u : State) (hrun : u.status = .running)
    (hinv : StackInv xs e0 sA i u) (hui : u.regs 104 = i) :
    ∃ u' j, SafeEval W (stackStepBlock leaf) u u' j ∧ j + 18 * u'.regs 103 ≤ 46 + 18 * u.regs 103 ∧
      u'.status = .running ∧ u'.regs 104 = i ∧ u'.regs 1 = xs.length ∧ u'.regs 2 = 1 ∧
      ∀ v : State, v.status = .running → (∀ r : Nat, r ≠ 104 → r ≠ 105 → v.regs r = u'.regs r) →
        v.memory = u'.memory → v.extent = u'.extent → v.keys = u'.keys →
        StackInv xs e0 sA (i + 1) v := by
  obtain ⟨hsp, hext, hkeys, hout, hfr, M, hR, hstk, hld, hcnt⟩ := hinv
  generalize hn : xs.length = n at hi hcap hR hstk hld hcnt hout ⊢
  have hA0 := hA.base0
  have hA1 := hA.base1
  have hA2 := hA.base2
  have hAo := hA.one
  have hAl := hA.len
  have hAe := hA.ext
  rw [hn] at hA1 hA2 hAl hAe
  generalize hL : spineAt xs i = L at hsp hstk hld
  generalize hC : countsAt xs i = C at hcnt
  have hLi : L.length ≤ i := by rw [← hL]; exact spine_length_le xs i (by omega)
  have hfacts : ∀ e ∈ L, e.2.1 ≤ e.1 ∧ e.1 < i ∧ xs.getD e.1 0 = e.2.2 := by
    rw [← hL]; exact spine_entry_facts xs i (by omega)
  have hsorted : L.Pairwise (fun a b => a.2.2 ≤ b.2.2) := by
    rw [← hL]; exact spineFrom_sorted (StackCartesianTree.buildTree_valid _) 0
  have hCi : C.length = i := by
    rw [← hC, openCounts_length, buildTree_take_size xs i (by omega)]
  have hCle : ∀ j, C.getD j 0 ≤ i := by
    intro j; rw [← hC]
    have := openCounts_getD_le (StackCartesianTree.buildTree (xs.take i)).shape j
    rwa [buildTree_take_size xs i (by omega)] at this
  -- registers of u
  have u100 : u.regs 100 = e0 := by rw [hfr 100 (by omega) (by omega), hA0]
  have u101 : u.regs 101 = e0 + (n + 1) := by rw [hfr 101 (by omega) (by omega), hA1]
  have u102 : u.regs 102 = e0 + 2 * (n + 1) := by rw [hfr 102 (by omega) (by omega), hA2]
  have u2 : u.regs 2 = 1 := by rw [hfr 2 (by omega) (by omega), hAo]
  have u1n : u.regs 1 = n := by rw [hfr 1 (by omega) (by omega), hAl]
  have hinpu : Inp u := hInp sA u hinpA (fun b hb => hout b (Or.inl hb)) (Nat.le_of_eq hext.symm) hkeys
  have hextu : e0 + 3 * (n + 1) ≤ u.extent := by rw [hext]; exact hAe
  -- stack part of the region
  have hRs : Region u e0 (xs.length + 1) M := by
    rw [hn]; exact hR.mono (by omega)
  have hstkv : ∀ k, k < L.length → M k < n := by
    intro k hk; rw [hstk k hk]; have := (hfacts _ (List.getElem_mem hk)).2.1; omega
  -- step 1: constant rPOP 0
  let u1 := execPrim (Prim.constant rPOP 0) u
  have f1 := exec_constant u rPOP 0
  have u1r : u1.regs = put u.regs 107 0 := by simp only [u1, f1]; rfl
  have u1s : u1.status = .running := by simp [u1, f1, hrun]
  have ev1 : SafeEval W (acts [.constant rPOP 0]) u u1 1 :=
    EvalG.action _ u hrun (safe_constant hW u _ _)
  have hR1 : Region u1 e0 (xs.length + 1) M := by intro a ha; simp only [u1, f1]; exact hRs a ha
  have u1m : u1.memory = u.memory := by simp [u1, f1]
  have u1e : u1.extent = u.extent := by simp [u1, f1]
  have u1k : u1.keys = u.keys := by simp [u1, f1]
  have u1g : ∀ r : Nat, r ≠ 107 → u1.regs r = u.regs r := fun r h => by rw [u1r, put_ne _ _ h]
  -- step 2: the first pop guard
  obtain ⟨u2', j2, e2, hj2, hu2s, hu2g, hu2t, hu2fr, hu2m, hu2e, hu2k⟩ :=
    popGuard_spec hW xs Inp leaf hleaf hInp.stable u1 u1s
      (hInp.stable u u1 hinpu u1m u1e u1k) (by rw [u1g 2 (by decide), u2]) e0 M
      (by rw [u1g 100 (by decide), u100]) hR1 (by rw [hn, u1e]; omega)
      (by rw [u1g 103 (by decide), hsp, hn]; omega) (by rw [u1g 104 (by decide), hui, hn]; exact hi)
      (fun k hk => by rw [u1g 103 (by decide), hsp] at hk; rw [hn]; exact hstkv k hk)
      (by rw [hn]; omega)
  simp only [u1g 103 (by decide), u1g 104 (by decide), hsp, hui] at hu2g hu2t
  have fr2 : ∀ r : Nat, r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 107 → r ≠ 108 → r ≠ 109 →
      r ≠ 110 → u2'.regs r = u.regs r := by
    intro r a b c d e f g h k; rw [hu2fr r a b c d e g h k, u1g r f]
  -- step 3: the pop loop
  have hR2 : Region u2' e0 (xs.length + 1) M := by intro a ha; rw [hu2m]; exact hR1 a ha
  obtain ⟨u3, j3, e3, hj3, hu3s, hsp3, hpops, hstop, h107, h106, hfr3, hu3m, hu3e, hu3k⟩ :=
    popLoop_spec hW xs Inp leaf hleaf hInp.stable u2' hu2s
      (hInp.stable u1 u2' (hInp.stable u u1 hinpu u1m u1e u1k) hu2m hu2e hu2k)
      (by rw [fr2 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), u2]) e0 M
      (by rw [fr2 100 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), u100]) hR2
      (by rw [hn, hu2e, u1e]; omega)
      (by rw [fr2 103 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), hsp, hn]; omega)
      (by rw [fr2 104 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), hui, hn]; exact hi)
      (fun k hk => by
        rw [fr2 103 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), hsp] at hk
        rw [hn]; exact hstkv k hk)
      (by rw [hn]; omega)
      (by rw [hu2fr 107 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), u1r, put_same])
      (by
        rw [fr2 103 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), fr2 104 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsp, hui]
        exact hu2g)
      (by
        rw [fr2 103 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), hsp]
        exact hu2t)
  have u2'103 : u2'.regs 103 = L.length := by
    rw [fr2 103 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hsp]
  have u2'104 : u2'.regs 104 = i := by
    rw [fr2 104 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hui]
  simp only [u2'103, u2'104] at hsp3 hpops h107 h106 hstop
  generalize hspE : u3.regs 103 = spE at hsp3 hpops hstop h107 h106
  -- abstract consequences of the pop loop
  obtain ⟨v, hv⟩ : ∃ v, v = xs.getD i 0 := ⟨_, rfl⟩
  have hkey : ∀ k (hk : k < L.length), xs.getD (M k) 0 = (L[k]).2.2 := by
    intro k hk; rw [hstk k hk]; exact (hfacts _ (List.getElem_mem hk)).2.2
  have hsplit1 : ∀ k (hk : k < L.length), k < spE → popsFor v (L[k]) = false := by
    intro k hk hks
    simp only [popsFor, decide_eq_false_iff_not]
    intro hvk
    rcases hstop with h0 | hns
    · omega
    · apply hns
      have hle : (L[k]).2.2 ≤ (L[spE - 1]'(by omega)).2.2 := by
        by_cases hke : k = spE - 1
        · subst hke; exact Int.le_refl _
        · exact List.pairwise_iff_getElem.mp hsorted k (spE - 1) hk (by omega) (by omega)
      rw [hkey (spE - 1) (by omega), ← hv]
      exact Int.lt_of_lt_of_le hvk hle
  have hsplit2 : ∀ k (hk : k < L.length), spE ≤ k → popsFor v (L[k]) = true := by
    intro k hk hks
    simp only [popsFor, decide_eq_true_eq]
    have := hpops k hks hk
    rwa [hkey k hk, ← hv] at this
  obtain ⟨htw, hfind⟩ := takeWhile_find_of_split (popsFor v) L spE hsplit1 hsplit2
  -- registers after the pop loop
  have f3 : ∀ r : Nat, ¬ (4 ≤ r ∧ r ≤ 8) → r ≠ 103 → ¬ (106 ≤ r ∧ r ≤ 112) →
      u3.regs r = u.regs r := by
    intro r h48 h103 h106
    rw [hfr3 r h48 h103 (by omega), fr2 r (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)]
  have u3_2 : u3.regs 2 = 1 := by rw [f3 2 (by omega) (by omega) (by omega), u2]
  have u3_100 : u3.regs 100 = e0 := by rw [f3 100 (by omega) (by omega) (by omega), u100]
  have u3_101 : u3.regs 101 = e0 + (n + 1) := by rw [f3 101 (by omega) (by omega) (by omega), u101]
  have u3_102 : u3.regs 102 = e0 + 2 * (n + 1) := by
    rw [f3 102 (by omega) (by omega) (by omega), u102]
  have u3_104 : u3.regs 104 = i := by rw [f3 104 (by omega) (by omega) (by omega), hui]
  have hu3mem : u3.memory = u.memory := by rw [hu3m, hu2m, u1m]
  have hu3ext : u3.extent = u.extent := by rw [hu3e, hu2e, u1e]
  have hu3keys : u3.keys = u.keys := by rw [hu3k, hu2k, u1k]
  have hR3 : Region u3 e0 (3 * (n + 1)) M := by intro a ha; rw [hu3mem]; exact hR a ha
  have hspEn : spE ≤ n := by omega
  let popped : Bool := decide (spE < L.length)
  have hpopped : u3.regs 107 = if popped then 1 else 0 := by
    rw [h107]; by_cases h : spE < L.length <;> simp [popped, h]
  obtain ⟨u4, j4, e4, hj4, hu4s, hR4, hu4sp, hfr4, hout4, hu4e, hu4k⟩ :=
    linkPush_spec hW n u3 hu3s u3_2 e0 M u3_100 u3_101 u3_102 hR3 (by rw [hu3ext]; exact hextu)
      (by omega) i spE u3_104 hi hspE hspEn popped hpopped (by
        intro hp
        have hlt : spE < L.length := by simpa [popped] using hp
        rw [h106 hlt, hstk spE hlt, hld spE hlt]
        have hf := hfacts _ (List.getElem_mem hlt)
        refine ⟨by omega, by omega, ?_⟩
        rw [hcnt _ (by omega)]
        have := hCle ((L[spE]).2.1)
        omega)
  -- the new spine and counts
  have hilen : i < xs.length := by rw [hn]; exact hi
  have htake : xs.take (i + 1) = xs.take i ++ [xs.getD i 0] := take_succ_getD hilen
  have ht : StackCartesianTree.buildTree (xs.take (i + 1)) =
      (StackCartesianTree.buildTree (xs.take i)).insertRight v := by
    rw [htake, hv]
    exact buildTree_append_singleton (xs.take i) (xs.getD i 0)
  have hsize : (StackCartesianTree.buildTree (xs.take i)).shape.size = i :=
    buildTree_take_size xs i (by omega)
  let ldNew : Nat := if h : spE < L.length then (L[spE]).2.1 else i
  have hL' : spineAt xs (i + 1) = L.take spE ++ [(i, ldNew, v)] := by
    show spineFrom (StackCartesianTree.buildTree (xs.take (i + 1))) 0 = _
    rw [ht, spineFrom_insertRight]
    have hL0 : spineFrom (StackCartesianTree.buildTree (xs.take i)) 0 = L := hL
    rw [hL0, htw, hfind, hsize, Nat.zero_add]
    congr 3
    by_cases h : spE < L.length
    · simp [ldNew, h]
    · simp [ldNew, h]
  have hIP : insertPoint (StackCartesianTree.buildTree (xs.take i)) v =
      if h : spE < L.length then some ((L[spE]).2.1) else none := by
    have := insertPoint_eq_find (StackCartesianTree.buildTree (xs.take i)) v 0
    have hL0 : spineFrom (StackCartesianTree.buildTree (xs.take i)) 0 = L := hL
    rw [hL0, hfind] at this
    simp only [Nat.zero_add, Option.map_id'] at this
    rw [this]
    by_cases h : spE < L.length
    · simp [h]
    · simp [h]
  have hC' : countsAt xs (i + 1) =
      if h : spE < L.length then C.modify ((L[spE]).2.1) (· + 1) ++ [0] else C ++ [1] := by
    show openCounts (StackCartesianTree.buildTree (xs.take (i + 1))).shape = _
    rw [ht, openCounts_insertRight, hIP]
    have hC0 : openCounts (StackCartesianTree.buildTree (xs.take i)).shape = C := hC
    by_cases h : spE < L.length
    · simp only [h, dite_true]; rw [hC0]
    · simp only [h, dite_false]; rw [hC0]
  refine ⟨u4, 1 + (j2 + (j3 + j4)), EvalG.seq ev1 (EvalG.seq e2 (EvalG.seq e3 e4)), ?_, hu4s,
    ?_, ?_, ?_, ?_⟩
  · rw [hu4sp, hsp]; omega
  · rw [hfr4 104 (by decide) (by decide) (by decide) (by decide), u3_104]
  · rw [hfr4 1 (by decide) (by decide) (by decide) (by decide),
      f3 1 (by omega) (by omega) (by omega), u1n]
  · rw [hfr4 2 (by decide) (by decide) (by decide) (by decide), u3_2]
  intro w hwr hwregs hwm hwe hwk
  have hLlen' : (spineAt xs (i + 1)).length = spE + 1 := by
    rw [hL']; simp; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwregs 103 (by decide) (by decide), hu4sp, hLlen']
  · rw [hwe, hu4e, hu3ext, hext]
  · rw [hwk, hu4k, hu3keys, hkeys]
  · intro b hb
    rw [hwm, hout4 b (by rw [hn] at hb; exact hb), hu3mem, hout b (by rw [hn] at hb; exact hb)]
  · intro r h48 h103
    rw [hwregs r (by omega) (by omega), hfr4 r (by omega) (by omega) (by omega) (by omega),
      f3 r h48 (by omega) (by omega), hfr r h48 h103]
  refine ⟨linkPushM n i spE (if popped then M (n + 1 + u3.regs 106) else 0) popped M, ?_, ?_, ?_, ?_⟩
  · rw [hn]; intro a ha; rw [hwm]; exact hR4 a ha
  · -- stack entries
    intro k hk
    rw [hLlen'] at hk
    have hentry : ((spineAt xs (i + 1))[k]'(by rw [hLlen']; exact hk)) =
        if hks : k < spE then L[k]'(by omega) else (i, ldNew, v) := by
      simp only [hL']
      by_cases hks : k < spE
      · rw [dif_pos hks, List.getElem_append_left (by simp; omega), List.getElem_take]
      · rw [dif_neg hks, List.getElem_append_right (by simp; omega)]
        simp <;> omega
    rw [hentry]
    by_cases hks : k < spE
    · rw [dif_pos hks]
      cases hp : popped <;>
        simp only [linkPushM, if_true, if_false, Bool.false_eq_true] <;>
        rw [put_ne _ _ (by omega), put_ne _ _ (by omega), put_ne _ _ (by omega), hstk k (by omega)]
    · rw [dif_neg hks]
      have hke : k = spE := by omega
      subst hke
      cases hp : popped <;> simp [linkPushM, put_same]
  · -- leftmost descendants
    intro k hk
    have hk' : k < spE + 1 := by rw [hLlen'] at hk; exact hk
    by_cases hks : k < spE
    · have hentry : ((spineAt xs (i + 1))[k]'hk) = L[k]'(by omega) := by
        simp only [hL']
        rw [List.getElem_append_left (by simp; omega), List.getElem_take]
      rw [hentry, hn]
      have hf := hfacts _ (List.getElem_mem (show k < L.length by omega))
      cases hp : popped <;>
        simp only [linkPushM, if_true, if_false, Bool.false_eq_true] <;>
        rw [put_ne _ _ (by omega), put_ne _ _ (by omega), put_ne _ _ (by omega), hld k (by omega)]
    · have hke : k = spE := by omega
      subst hke
      have hentry : ((spineAt xs (i + 1))[k]'hk) = (i, ldNew, v) := by
        simp only [hL']
        rw [List.getElem_append_right (by simp; omega)]
        simp <;> omega
      rw [hentry, hn]
      by_cases hlt : k < L.length
      · have hp : popped = true := by simp [popped, hlt]
        simp only [linkPushM, hp, if_true]
        rw [put_ne _ _ (by omega), put_same, h106 hlt, hstk k hlt, hld k hlt]
        simp [ldNew, hlt]
      · have hp : popped = false := by simp [popped, hlt]
        simp only [linkPushM, hp, if_false, Bool.false_eq_true]
        rw [put_ne _ _ (by omega), put_ne _ _ (by omega), put_same]
        simp [ldNew, hlt]
  · -- open counts
    intro jj hjj
    rw [hn] at hjj
    rw [hn, hC']
    by_cases hlt : spE < L.length
    · have hp : popped = true := by simp [popped, hlt]
      rw [dif_pos hlt, getD_append_singleton, List.length_modify, hCi]
      have hf := hfacts _ (List.getElem_mem hlt)
      simp only [linkPushM, hp, if_true]
      rw [put_ne _ _ (by omega), put_ne _ _ (by omega), h106 hlt, hstk spE hlt, hld spE hlt]
      by_cases hji : jj < i
      · rw [if_pos hji, getD_modify_succ _ _ _ (by omega)]
        by_cases hjl : jj = (L[spE]).2.1
        · subst hjl; rw [put_same, if_pos rfl, hcnt _ (by omega)]
        · rw [put_ne _ _ (by omega), if_neg hjl, hcnt _ (by omega)]
      · rw [if_neg hji, put_ne _ _ (by omega), hcnt _ hjj, getD_of_ge (by omega)]
        split <;> rfl
    · have hp : popped = false := by simp [popped, hlt]
      rw [dif_neg hlt, getD_append_singleton, hCi]
      simp only [linkPushM, hp, if_false, Bool.false_eq_true]
      rw [put_ne _ _ (by omega)]
      by_cases hji : jj = i
      · subst hji; rw [put_same, if_neg (by omega), if_pos rfl]
      · rw [put_ne _ _ (by omega), put_ne _ _ (by omega), hcnt _ hjj]
        by_cases hjl : jj < i
        · rw [if_pos hjl]
        · rw [if_neg hjl, if_neg hji, getD_of_ge (by omega)]


/-! ## The stack pass -/

/-- **Stack pass.** After the pass, the count region holds
`openCounts (buildTree xs).shape` and the stack the right spine of the whole
tree, in at most `50 * n + 4` steps. -/
theorem stackPass_spec {W : Nat} (hW : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (hleaf : KeySpec W xs Inp leaf) (e0 : Nat) (hInp : InpBelow Inp e0)
    (sA : State) (hA : PassStart xs e0 sA) (hinpA : Inp sA) (hrun : sA.status = .running)
    (hzero : Region sA e0 (3 * (xs.length + 1)) (fun _ => 0))
    (hcap : e0 + 3 * (xs.length + 1) + xs.length + 2 < 2 ^ W) :
    ∃ s' k, SafeEval W (stackPassBlock leaf) sA s' k ∧ k ≤ 50 * xs.length + 4 ∧
      s'.status = .running ∧ StackInv xs e0 sA xs.length s' ∧ s'.regs 1 = xs.length ∧
      s'.regs 2 = 1 := by
  -- rSTKH := 0
  let t := execPrim (Prim.constant rSTKH 0) sA
  have ft := exec_constant sA rSTKH 0
  have tr : t.regs = put sA.regs 103 0 := by simp only [t, ft]; rfl
  have ts : t.status = .running := by simp [t, ft, hrun]
  have ev0 : SafeEval W (acts [.constant rSTKH 0]) sA t 1 :=
    EvalG.action _ sA hrun (safe_constant hW sA _ _)
  have t1 : t.regs 1 = xs.length := by rw [tr, put_ne _ _ (by decide), hA.len]
  have t2 : t.regs 2 = 1 := by rw [tr, put_ne _ _ (by decide), hA.one]
  obtain ⟨s', k, e, hk, hs'r, hinv, hs'i, hs'n⟩ :=
    forSlots_spec_pot hW rI rIGO rN (stackStepBlock leaf) 46 18 (fun w => w.regs 103)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (StackInv xs e0 sA) t ts t2 (by rw [show ((rN : Operand) : Nat) = 1 from rfl, t1]; omega)
      (fun u w hregs _ _ => by
        show w.regs 103 = u.regs 103
        exact hregs 103 (by decide) (by decide))
      (by
        intro u hu hregs hm he hk hkr
        have hsp0 : spineAt xs 0 = [] := by simp [spineAt, spineFrom]
        have hc0 : countsAt xs 0 = [] := by
          show openCounts (StackCartesianTree.buildTree (xs.take 0)).shape = []
          rw [List.take_zero]; rfl
        refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => 0, ?_, ?_, ?_, ?_⟩
        · rw [hregs 103 (by decide) (by decide), tr, put_same, hsp0]; rfl
        · rw [he]; simp [t, ft]
        · rw [hk]; simp [t, ft]
        · intro b _; rw [hm]; simp [t, ft]
        · intro r h48 h103
          rw [hregs r (by show r ≠ 104; omega) (by show r ≠ 105; omega), tr,
            put_ne _ _ (by omega)]
        · intro a ha; rw [hm]; simp only [t, ft]; exact hzero a ha
        · intro k hk; simp [hsp0] at hk
        · intro k hk; simp [hsp0] at hk
        · intro j _; simp [hc0])
      (by
        intro kk u hkk hinv hur hui hucnt huone
        rw [show ((rN : Operand) : Nat) = 1 from rfl, t1] at hkk hucnt
        obtain ⟨u', j, eb, hj, hu'r, hu'i, hu'1, hu'2, hcont⟩ :=
          stackStep_spec hW xs Inp leaf hleaf e0 hInp sA hA hinpA hcap kk hkk u hur hinv hui
        refine ⟨u', j, eb, by omega, hu'r, hu'i, ?_, hu'2, ?_⟩
        · rw [show ((rN : Operand) : Nat) = 1 from rfl, t1]; exact hu'1
        · intro w hw hregs hm he hk _
          exact hcont w hw (fun r h104 h105 => hregs r h104 h105) hm he hk)
  rw [show ((rN : Operand) : Nat) = 1 from rfl, t1] at hk hinv hs'i hs'n
  have ht103 : t.regs 103 = 0 := by rw [tr, put_same]
  simp only [ht103] at hk
  refine ⟨s', 1 + k, EvalG.seq ev0 e, by omega, hs'r, hinv, ?_, ?_⟩
  · exact hs'n
  · obtain ⟨_, _, _, _, hfr, _⟩ := hinv
    rw [hfr 2 (by omega) (by omega), hA.one]

end RMQ.SuccinctFinal.PackedConstruction.Proof
