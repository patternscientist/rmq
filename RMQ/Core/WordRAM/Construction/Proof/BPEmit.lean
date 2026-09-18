import RMQ.Core.WordRAM.Construction.Proof.StackPass

/-! # PRE-1 builder proofs: BP emission from the open counts (stage S3)

Outside the builder firewall. `bpUnit_spec`: for slot `j`, the unit block
appends `count[j]` many 1-cells and one 0-cell. `bpEmit_spec`: the emission pass
appends `(C.take n).flatMap unit` for the count list `C` held in the count
region, with amortized cost `14 * n + 3`. `bpSegment_eq`: after the stack pass
and the emission pass, the appended cells are exactly the BP code of the
canonical Cartesian shape of `xs` as 0/1 cells.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec Spec.StackCartesianTreeSpec RMQ.Cartesian

/-- The 0/1 cells of one BP unit. -/
def unitCells (c : Nat) : List Nat := List.replicate c 1 ++ [0]

theorem unitCells_length (c : Nat) : (unitCells c).length = c + 1 := by simp [unitCells]

theorem flatMap_unitCells_length : ∀ (L : List Nat),
    (L.flatMap unitCells).length = L.sum + L.length
  | [] => rfl
  | c :: L => by
      simp only [List.flatMap_cons, List.length_append, unitCells_length,
        flatMap_unitCells_length L, List.sum_cons, List.length_cons]
      omega

/-- **One BP unit.** -/
theorem bpUnit_spec {W : Nat} (hW : 32 ≤ W) (w : State) (hrun : w.status = .running)
    (hzero : w.regs 0 = 0) (hone : w.regs 2 = 1) (e0 n : Nat) (M : Nat → Nat)
    (h102 : w.regs 102 = e0 + 2 * (n + 1)) (hR : Region w e0 (3 * (n + 1)) M)
    (hext : e0 + 3 * (n + 1) ≤ w.extent) (j : Nat) (hj : w.regs 113 = j) (hjn : j ≤ n)
    (hcap : w.extent + M (2 * (n + 1) + j) + 1 < 2 ^ W) :
    ∃ w' k, SafeEval W bpUnitBlock w w' k ∧ k ≤ 5 * M (2 * (n + 1) + j) + 5 ∧
      w'.status = .running ∧ Emits w w' (unitCells (M (2 * (n + 1) + j))) ∧
      (∀ r : Nat, r ≠ 10 → r ≠ 108 → r ≠ 112 → w'.regs r = w.regs r) ∧
      w'.keys = w.keys := by
  generalize hc : M (2 * (n + 1) + j) = c at hcap ⊢
  -- ADDR := CNT base + j; CC := CNT[j]
  let w1 := execPrim (Prim.arithmetic .add rADDR rCNTB rJ) w
  have f1 := exec_arithmetic w .add rADDR rCNTB rJ
  have w1r : w1.regs = put w.regs 108 (e0 + (2 * (n + 1) + j)) := by
    simp only [w1, f1, Arithmetic.eval]
    rw [show ((rCNTB : Operand) : Nat) = 102 from rfl, show ((rJ : Operand) : Nat) = 113 from rfl,
      h102, hj, show e0 + 2 * (n + 1) + j = e0 + (2 * (n + 1) + j) by omega]; rfl
  have hR1 : Region w1 e0 (3 * (n + 1)) M := by intro a ha; simp only [w1, f1]; exact hR a ha
  have w1e : w1.extent = w.extent := by simp [w1, f1]
  have w1a : w1.regs rADDR = e0 + (2 * (n + 1) + j) := by
    show w1.regs 108 = _; rw [w1r, put_same]
  let w2 := execPrim (Prim.load rCC rADDR) w1
  have f2 := load_region hR1 (by rw [w1e]; exact hext) rCC rADDR (a := 2 * (n + 1) + j)
    (by omega) w1a
  rw [hc] at f2
  have w2r : w2.regs = put (put w.regs 108 (e0 + (2 * (n + 1) + j))) 112 c := by
    simp only [w2, f2, w1r]; rfl
  have w2s : w2.status = .running := by simp only [w2, f2]; simp [w1, f1, hrun]
  have w2e : w2.extent = w.extent := by simp only [w2, f2]; exact w1e
  have w2m : w2.memory = w.memory := by simp only [w2, f2]; simp [w1, f1]
  have w2k : w2.keys = w.keys := by simp only [w2, f2]; simp [w1, f1]
  have w1s : w1.status = .running := by simp [w1, f1, hrun]
  have hsafe : ActsOK (Action.Safe W) [.arithmetic .add rADDR rCNTB rJ, .load rCC rADDR] w := by
    refine ⟨safe_add hW w _ _ _ ?_, w1s, ?_⟩
    · show w.regs 102 + w.regs 113 < 2 ^ W
      rw [h102, hj]; omega
    exact ⟨safe_load_region hW hR1 (by rw [w1e]; exact hext) _ _ (by omega) w1a
      (by rw [hc]; omega), w2s, trivial⟩
  have ev1 := acts_evalG (P := Action.Safe W) _ w hrun hsafe
  -- the ones loop
  let Q : Nat → State → Prop := fun k u =>
    u.status = .running ∧ u.regs 112 = k ∧ k ≤ c ∧ u.regs 2 = 1 ∧ u.regs 0 = 0 ∧
      Emits w2 u (List.replicate (c - k) 1) ∧
      (∀ r : Nat, r ≠ 10 → r ≠ 112 → u.regs r = w2.regs r) ∧ u.keys = w2.keys
  have hQ : Q c w2 := by
    refine ⟨w2s, by rw [w2r, put_same], Nat.le_refl _, ?_, ?_, by simp [Emits.refl], fun _ _ _ => rfl,
      rfl⟩
    · rw [w2r, put_ne _ _ (by decide), put_ne _ _ (by decide), hone]
    · rw [w2r, put_ne _ _ (by decide), put_ne _ _ (by decide), hzero]
  have hloop := EvalG.loop_iterate (P := Action.Safe W) Q rCC
    (.seq (emitBit rONE) (acts [.arithmetic .sub rCC rCC rONE])) 3
    (fun k u hu => hu.1)
    (fun k u hu => by show u.regs 112 ≠ 0; rw [hu.2.1]; omega)
    (fun u hu => hu.2.1)
    (by
      intro k u hu
      obtain ⟨hur, hucc, hkc, huo, huz, huem, hufr, huk⟩ := hu
      have huext : u.extent = w.extent + (c - (k + 1)) := by
        rw [huem.1, w2e]; simp
      obtain ⟨u1, e1, hu1r, hu1em, hu1fr, _, hu1k⟩ :=
        emitBit_spec hW rONE (by decide) u hur (by show u.regs 2 < 2 ^ W; rw [huo]; omega)
          (by rw [huext]; omega)
      have hu1_112 : u1.regs 112 = k + 1 := by rw [hu1fr 112 (by decide), hucc]
      have hu1_2 : u1.regs 2 = 1 := by rw [hu1fr 2 (by decide), huo]
      let u2 := execPrim (Prim.arithmetic .sub rCC rCC rONE) u1
      have g2 := exec_arithmetic u1 .sub rCC rCC rONE
      have u2r : u2.regs = put u1.regs 112 k := by
        simp only [u2, g2, Arithmetic.eval]
        rw [show ((rCC : Operand) : Nat) = 112 from rfl, show ((rONE : Operand) : Nat) = 2 from rfl,
          hu1_112, hu1_2]; rfl
      have u2s : u2.status = .running := by simp [u2, g2, hu1r]
      have hsafe2 : Action.Safe W u1 (.arithmetic .sub rCC rCC rONE) :=
        safe_sub hW u1 _ _ _ (by show u1.regs 2 ≤ u1.regs 112; rw [hu1_2, hu1_112]; omega)
          (by show u1.regs 112 < 2 ^ W; rw [hu1_112]; omega)
      refine ⟨u2, 2 + 1, EvalG.seq e1 (EvalG.action _ u1 hu1r hsafe2), by omega, u2s,
        by rw [u2r, put_same], by omega, ?_, ?_, ?_, ?_, ?_⟩
      · rw [u2r, put_ne _ _ (by decide), hu1_2]
      · rw [u2r, put_ne _ _ (by decide), hu1fr 0 (by decide), huz]
      · have hone' : u.regs rONE = 1 := huo
        rw [hone'] at hu1em
        have e : c - k = (c - (k + 1)) + 1 := by omega
        rw [e, List.replicate_succ']
        exact (huem.trans hu1em).congr_right (by simp [u2, g2]) (by simp [u2, g2])
      · intro r h10 h112
        rw [u2r, put_ne _ _ h112, hu1fr r h10, hufr r h10 h112]
      · simp [u2, g2, hu1k, huk])
    c w2 hQ
  obtain ⟨u3, j3, e3, hj3, hq3⟩ := hloop
  obtain ⟨hu3r, _, _, hu3o, hu3z, hu3em, hu3fr, hu3k⟩ := hq3
  -- the closing zero
  obtain ⟨u4, e4, hu4r, hu4em, hu4fr, _, hu4k⟩ :=
    emitBit_spec hW rZERO (by decide) u3 hu3r (by show u3.regs 0 < 2 ^ W; rw [hu3z]; omega)
      (by rw [hu3em.1, w2e]; simp; omega)
  have hz3 : u3.regs rZERO = 0 := hu3z
  rw [hz3] at hu4em
  have hw2em : Emits w w2 [] := Emits.of_eq w2e w2m
  refine ⟨u4, 2 + (j3 + 2), EvalG.seq ev1 (EvalG.seq e3 e4), by omega, hu4r, ?_, ?_, ?_⟩
  · have := (hw2em.trans hu3em).trans hu4em
    simpa [unitCells] using this
  · intro r h10 h108 h112
    rw [hu4fr r h10, hu3fr r h10 h112, w2r, put_ne _ _ h112, put_ne _ _ h108]
  · rw [hu4k, hu3k, w2k]

theorem sum_take_succ (C : List Nat) (k : Nat) (hk : k < C.length) :
    (C.take (k + 1)).sum = (C.take k).sum + C.getD k 0 := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, sum_append_nat]
  simp [List.getElem?_eq_getElem hk]

theorem sum_take_le : ∀ (C : List Nat) (k : Nat), (C.take k).sum ≤ C.sum
  | [], _ => by simp
  | c :: C, 0 => by simp
  | c :: C, k + 1 => by
      simp only [List.take_succ_cons, List.sum_cons]
      have := sum_take_le C k
      omega

theorem flatMap_take_succ (C : List Nat) (k : Nat) (hk : k < C.length) :
    (C.take (k + 1)).flatMap unitCells = (C.take k).flatMap unitCells ++ unitCells (C.getD k 0) := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, List.flatMap_append]
  simp [List.getElem?_eq_getElem hk]

/-- **BP emission pass.** -/
theorem bpEmit_spec {W : Nat} (hW : 32 ≤ W) (e0 n : Nat) (C : List Nat) (hC : C.length = n)
    (hCsum : C.sum = n) (M : Nat → Nat) (sB : State) (hrun : sB.status = .running)
    (hzero : sB.regs 0 = 0) (hone : sB.regs 2 = 1) (hn : sB.regs 1 = n)
    (h102 : sB.regs 102 = e0 + 2 * (n + 1)) (hR : Region sB e0 (3 * (n + 1)) M)
    (hext : e0 + 3 * (n + 1) ≤ sB.extent) (hM : ∀ j, j < n → M (2 * (n + 1) + j) = C.getD j 0)
    (hcap : sB.extent + 2 * n + 1 < 2 ^ W) :
    ∃ s' k, SafeEval W bpEmitBlock sB s' k ∧ k ≤ 14 * n + 3 ∧ s'.status = .running ∧
      Emits sB s' (C.flatMap unitCells) ∧
      (∀ r : Nat, r ≠ 10 → r ≠ 108 → r ≠ 112 → r ≠ 113 → r ≠ 114 → s'.regs r = sB.regs r) ∧
      s'.keys = sB.keys := by
  let Inv : Nat → State → Prop := fun j u =>
    Emits sB u ((C.take j).flatMap unitCells) ∧
      (∀ r : Nat, r ≠ 10 → r ≠ 108 → r ≠ 112 → r ≠ 113 → r ≠ 114 → u.regs r = sB.regs r) ∧
      u.keys = sB.keys
  obtain ⟨s', k, e, hk, hr, ⟨hem, hfr, hks⟩, _, _⟩ :=
    forSlots_spec_pot hW rJ rJGO rN bpUnitBlock 0 5 (fun u => sB.extent + 2 * n - u.extent)
      (by decide) (by decide) (by decide) (by decide) (by decide) Inv sB hrun hone
      (by show sB.regs 1 < 2 ^ W; rw [hn]; omega)
      (fun u v _ _ he => by show sB.extent + 2 * n - v.extent = sB.extent + 2 * n - u.extent; rw [he])
      (by
        intro u _ hregs hm he hk _
        refine ⟨?_, fun r h10 h108 h112 h113 h114 => hregs r h113 h114, hk⟩
        simp only [List.take_zero, List.flatMap_nil]
        exact Emits.of_eq he hm)
      (by
        intro kk u hkk ⟨huem, hufr, huk⟩ hur hui hucnt huone
        rw [show ((rN : Operand) : Nat) = 1 from rfl, hn] at hkk hucnt
        have huext : u.extent = sB.extent + ((C.take kk).sum + kk) := by
          rw [huem.1, flatMap_unitCells_length, List.length_take, hC, Nat.min_eq_left (by omega)]
        have hRu : Region u e0 (3 * (n + 1)) M := by
          intro a ha
          rw [huem.memory_below (by omega)]
          exact hR a ha
        have hsum1 := sum_take_succ C kk (by omega)
        have hsum2 := sum_take_le C (kk + 1)
        have hMk := hM kk hkk
        obtain ⟨u', j, eb, hj, hu'r, hu'em, hu'fr, hu'k⟩ :=
          bpUnit_spec hW u hur (by rw [hufr 0 (by decide) (by decide) (by decide) (by decide)
            (by decide), hzero]) huone e0 n M
            (by rw [hufr 102 (by decide) (by decide) (by decide) (by decide) (by decide), h102])
            hRu (by rw [huext]; omega) kk hui (by omega) (by rw [huext, hMk]; omega)
        rw [hMk] at hj hu'em
        have hu'ext : u'.extent = u.extent + (C.getD kk 0 + 1) := by
          rw [hu'em.1, unitCells_length]
        refine ⟨u', j, eb, ?_, hu'r, ?_, ?_, ?_, ?_⟩
        · show j + 5 * (sB.extent + 2 * n - u'.extent) ≤ 0 + 5 * (sB.extent + 2 * n - u.extent)
          rw [hu'ext, huext]
          omega
        · show u'.regs 113 = kk
          rw [hu'fr 113 (by decide) (by decide) (by decide)]
          exact hui
        · show u'.regs 1 = sB.regs 1
          rw [hu'fr 1 (by decide) (by decide) (by decide), hufr 1 (by decide) (by decide)
            (by decide) (by decide) (by decide)]
        · rw [hu'fr 2 (by decide) (by decide) (by decide), huone]
        · intro w _ hwr hwm hwe hwk _
          refine ⟨?_, ?_, ?_⟩
          · rw [flatMap_take_succ C kk (by omega)]
            exact (huem.trans hu'em).congr_right hwm hwe
          · intro r h10 h108 h112 h113 h114
            rw [hwr r h113 h114, hu'fr r h10 h108 h112, hufr r h10 h108 h112 h113 h114]
          · rw [hwk, hu'k, huk])
  rw [show ((rN : Operand) : Nat) = 1 from rfl, hn] at hk hem
  rw [List.take_of_length_le (by omega)] at hem
  refine ⟨s', k, e, by simp at hk; omega, hr, hem, hfr, hks⟩

theorem bitToNat_map_bpUnit (c : Nat) :
    (List.replicate c true ++ [false]).map SuccinctSpace.bitToNat = unitCells c := by
  simp [unitCells, List.map_replicate, SuccinctSpace.bitToNat]

/-- The BP code of the canonical shape as 0/1 cells, through the stack tree. -/
theorem bpCells_eq (xs : List Int) :
    (shape xs).bpCode.map SuccinctSpace.bitToNat =
      (openCounts (StackCartesianTree.buildTree xs).shape).flatMap unitCells := by
  rw [bpCode_shape_eq_openCounts_buildTree, List.map_flatMap]
  congr 1
  funext c
  exact bitToNat_map_bpUnit c

/-- **S3 exit: Cartesian stack pass and BP emission.** From a running state with
the constants, the input length in register 1 and an input predicate that only
reads memory below the current extent, the three blocks allocate the arrays, run
the monotone stack with the given leaf, and append the BP code of
`Cartesian.shape xs` as 0/1 cells right after the arrays. -/
theorem cartesianBP_spec {W : Nat} (hW : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (hleaf : KeySpec W xs Inp leaf) (s : State) (hrun : s.status = .running)
    (hzero : s.regs 0 = 0) (hone : s.regs 2 = 1) (hn : s.regs 1 = xs.length)
    (hinp : Inp s) (hInp : InpBelow Inp s.extent)
    (hcap : s.extent + 3 * (xs.length + 1) + 2 * xs.length + 2 < 2 ^ W) :
    ∃ s' k, SafeEval W (.seq stackArraysBlock (.seq (stackPassBlock leaf) bpEmitBlock)) s s' k ∧
      k ≤ 79 * xs.length + 19 ∧ s'.status = .running ∧
      s'.extent = s.extent + 3 * (xs.length + 1) + 2 * xs.length ∧
      (∀ a, a < s.extent → s'.memory a = s.memory a) ∧
      Region s' (s.extent + 3 * (xs.length + 1)) (2 * xs.length)
        (fun k => ((shape xs).bpCode.map SuccinctSpace.bitToNat).getD k 0) ∧
      (∀ r : Nat, ¬ (4 ≤ r ∧ r ≤ 8) → r ≠ 10 → r ≠ 12 → ¬ (100 ≤ r ∧ r ≤ 114) →
        s'.regs r = s.regs r) ∧
      s'.keys = s.keys := by
  generalize hnv : xs.length = n at hn hcap ⊢
  -- arrays
  obtain ⟨sA, k1, e1, hk1, hAr, hAem, hA100, hA101, hA102, hAfr, _, hAk⟩ :=
    stackArrays_spec hW n s hrun hzero hone hn (by omega)
  have hAext : sA.extent = s.extent + 3 * (n + 1) := by rw [hAem.1]; simp
  have hA : PassStart xs s.extent sA := by
    refine ⟨hA100, by rw [hnv]; exact hA101, by rw [hnv]; exact hA102, ?_, ?_, ?_⟩
    · rw [hAfr 2 (by decide) (by decide) (by decide) (by decide) (by decide), hone]
    · rw [hAfr 1 (by decide) (by decide) (by decide) (by decide) (by decide), hn, hnv]
    · rw [hAext, hnv]; exact Nat.le_refl _
  have hinpA : Inp sA := hInp s sA hinp (fun b hb => hAem.memory_below hb) (by rw [hAext]; exact Nat.le_add_right _ _)
    (by rw [hAk])
  have hzeroA : Region sA s.extent (3 * (xs.length + 1)) (fun _ => 0) := by
    rw [hnv]; exact hAem.region_zero
  -- stack pass
  obtain ⟨sP, k2, e2, hk2, hPr, hinv, hP1, hP2⟩ :=
    stackPass_spec hW xs Inp leaf hleaf s.extent hInp sA hA hinpA hAr hzeroA
      (by rw [hnv]; omega)
  obtain ⟨_, hPext, hPkeys, hPout, hPfr, M, hPR, _, _, hPcnt⟩ := hinv
  rw [hnv] at hk2 hP1 hPR hPcnt hPout
  have hCeq : countsAt xs n = openCounts (StackCartesianTree.buildTree xs).shape := by
    show openCounts (StackCartesianTree.buildTree (xs.take n)).shape = _
    rw [← hnv, List.take_length]
  have hsize : (StackCartesianTree.buildTree xs).shape.size = n := by
    rw [← values_length, StackCartesianTree.buildTree_values, hnv]
  -- BP emission
  obtain ⟨s', k3, e3, hk3, hr', hem, hfr', hks'⟩ :=
    bpEmit_spec hW s.extent n (openCounts (StackCartesianTree.buildTree xs).shape)
      (by rw [openCounts_length, hsize]) (by rw [openCounts_sum, hsize]) M sP hPr
      (by rw [hPfr 0 (by omega) (by omega), hAfr 0 (by decide) (by decide) (by decide) (by decide)
        (by decide), hzero]) hP2 hP1
      (by rw [hPfr 102 (by omega) (by omega), hA102]) hPR (by rw [hPext, hAext]; exact Nat.le_refl _)
      (fun j hj => by rw [hPcnt j (by omega), hCeq])
      (by rw [hPext, hAext]; omega)
  refine ⟨s', k1 + (k2 + k3), EvalG.seq e1 (EvalG.seq e2 e3), by omega, hr', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hem.1, flatMap_unitCells_length, openCounts_sum, openCounts_length, hsize, hPext, hAext]
    omega
  · intro a ha
    rw [hem.memory_below (by rw [hPext, hAext]; omega), hPout a (Or.inl ha),
      hAem.memory_below ha]
  · intro k hk
    have hlen : ((openCounts (StackCartesianTree.buildTree xs).shape).flatMap unitCells).length =
        2 * n := by
      rw [flatMap_unitCells_length, openCounts_sum, openCounts_length, hsize]; omega
    have := hem.memory_at (i := k) (by rw [hlen]; exact hk)
    rw [hPext, hAext] at this
    rw [this, bpCells_eq]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < _ by rw [hlen]; exact hk)]
  · intro r h48 h10 h12 h100
    rw [hfr' r h10 (by omega) (by omega) (by omega) (by omega), hPfr r h48 (by omega),
      hAfr r (by omega) (by omega) (by omega) h10 h12]
  · rw [hks', hPkeys, hAk]

theorem oracleInput_below (xs : List Int) (e0 : Nat) : InpBelow (OracleInput xs) e0 := by
  intro u v hu _ _ hk
  show v.keys = _
  rw [hk]; exact hu

theorem wordInput_below (W : Nat) (xs : List Int) (e0 : Nat) (he : xs.length + 1 ≤ e0) :
    InpBelow (WordInput W xs) e0 := by
  intro u v ⟨hfits, hext, hmem⟩ hm hle _
  refine ⟨hfits, by omega, fun k hk => ?_⟩
  rw [hm (k + 1) (by omega)]
  exact hmem k hk

end RMQ.SuccinctFinal.PackedConstruction.Proof
