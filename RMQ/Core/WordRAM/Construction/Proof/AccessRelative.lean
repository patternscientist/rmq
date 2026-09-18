import RMQ.Core.WordRAM.Construction.Proof.AccessEntries

/-! # PRE-1 builder proofs: relative offset tables (stage S5)

Outside the builder firewall. The two flat-mapped relative tables: per long
super (resp. sparse-exception local slot) the body reads the stored flag and
either emits nothing or emits the reference `relativeOffsetsOrZero` row at the
recorded width. The loops are accounted by a potential on the extent, so the
cost is a constant per slot plus a constant per emitted cell.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose RMQ.GenericSelect SuccinctSpace

/-! ## Reference relative offsets as positions -/

/-- Below the occurrence count, every selected close is its position. -/
theorem relativeOffsetsOrZero_eq_positions (b : List Bool) (base cnt e bpos : Nat)
    (he : e ≤ occurrenceCount b false) :
    relativeOffsetsOrZero false b base cnt e bpos =
      (List.range cnt).map (fun o => if base + o < e then position b false (base + o) - bpos else 0) := by
  unfold relativeOffsetsOrZero
  apply List.map_congr_left
  intro o _
  by_cases h : base + o < e
  · obtain ⟨p, hp⟩ := select_exists_of_lt_occurrenceCount b false (show base + o < occurrenceCount b false by omega)
    simp only [h, if_true, hp, position_eq_of_select b false hp]
  · simp only [h, if_false]

/-- Bits of a flat-mapped table, slot by slot. -/
theorem flatten_map_flatMap (width : Nat) (h : Nat → List Nat) :
    ∀ L : List Nat,
      (flattenPayloadWords ((L.flatMap h).map (natToBitsLE width))).map SuccinctSpace.bitToNat =
        L.flatMap (fun x => (flattenPayloadWords ((h x).map (natToBitsLE width))).map SuccinctSpace.bitToNat)
  | [] => by simp [flattenPayloadWords]
  | x :: rest => by
      rw [List.flatMap_cons, List.flatMap_cons, List.map_append, flattenPayloadWords_append, List.map_append,
        flatten_map_flatMap width h rest]

/-! ## One long super -/

/-- Registers a relative body may write, besides the table scratch. -/
abbrev BodyWrites (r : Nat) : Prop := TableScratch r ∨ AccessWrites r

theorem not_bodyWrites {r : Nat} (h : ¬ BodyWrites r) : ¬ TableScratch r ∧ ¬ AccessWrites r :=
  ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩

/-- **Long relative body.** For a long super, the `S` relative offsets at `ws`
bits; nothing otherwise. -/
theorem longRelativeBody_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1) (htwo : u.regs 9 = 2) (P0 L0 k : Nat)
    (h1 : u.regs 1 = shape.size) (h159 : u.regs 159 = P0) (h161 : u.regs 161 = L0)
    (h173 : u.regs 173 = k) (h39 : u.regs 39 = wordBits shape.bpCode.length)
    (h40 : u.regs 40 = superStride shape.bpCode.length)
    (hk : k < superSlotCount shape.bpCode false)
    (hLF : ∀ k', k' < superSlotCount shape.bpCode false →
      u.memory (L0 + k') = some (flagNat (superIsLong shape.bpCode false k')))
    (hPOS : ∀ q, q ≤ shape.size → u.memory (P0 + q) = some (position shape.bpCode false q))
    (hPL : P0 + shape.size < L0) (hLe : L0 + superSlotCount shape.bpCode false ≤ u.extent)
    (hext : u.extent + (longSuperRelativeEntriesForSlot shape.bpCode false k).length *
      wordBits shape.bpCode.length < 2 ^ W)
    (hcapS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length < 2 ^ W)
    (hlenW : shape.bpCode.length < 2 ^ W) :
    ∃ u' j, SafeEval W longRelativeBodyBlock u u' j ∧
      j ≤ 21 + 34 * ((longSuperRelativeEntriesForSlot shape.bpCode false k).length *
        wordBits shape.bpCode.length) ∧ u'.status = .running ∧
      Emits u u' ((flattenPayloadWords ((longSuperRelativeEntriesForSlot shape.bpCode false k).map
        (natToBitsLE (wordBits shape.bpCode.length)))).map SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ BodyWrites r → u'.regs r = u.regs r) ∧ u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys := by
  have h2W := two_le_two_pow hW
  have hocc := bp_occurrenceCount shape
  have hSpos := superStride_pos shape.bpCode.length
  have hwspos := wordBits_pos shape.bpCode.length
  have hkS : k * superStride shape.bpCode.length < shape.size := by
    have := selectCeilDiv_slot_mul_lt (n := occurrenceCount shape.bpCode false) hSpos hk
    rw [hocc] at this; exact this
  have hsupn : superSlotCount shape.bpCode false ≤ shape.size := by
    rw [RMQ.SuccinctFinal.PackedCellProbe.superSlotCount_eq_packed]
    exact RMQ.SuccinctFinal.PackedCellProbe.packedSuperSlots_le _
  have hSws : superStride shape.bpCode.length ≤ superStride shape.bpCode.length * wordBits shape.bpCode.length :=
    Nat.le_mul_of_pos_right _ hwspos
  have hkS1 : (k + 1) * superStride shape.bpCode.length ≤
      superSlotCount shape.bpCode false * superStride shape.bpCode.length := Nat.mul_le_mul_right _ hk
  have hkS1' : (k + 1) * superStride shape.bpCode.length =
      k * superStride shape.bpCode.length + superStride shape.bpCode.length := Nat.succ_mul _ _
  have hsupS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length =
      superSlotCount shape.bpCode false * superStride shape.bpCode.length + superStride shape.bpCode.length :=
    Nat.succ_mul _ _
  have hlf := flagNat_le (superIsLong shape.bpCode false k)
  -- the flag
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pure hW (.arithmetic .add rADDR rLFB rK) u hrun (by
    simp only [pureOK, Arithmetic.eval, operand_val_161, operand_val_173, h161, h173, reduceCtorEq,
      false_implies, false_or, and_true]
    omega)
  have v1_108 : v1.regs 108 = L0 + k := by
    rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_161, operand_val_173, operand_val_108, h161, h173,
      put_same]
  have v1get : ∀ r, r ≠ 108 → v1.regs r = u.regs r := fun r h => by
    rw [r1]; simp only [pureReg, operand_val_108]; rw [put_ne _ _ h]
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_load hW rFLAG rADDR v1 p1.1
    (x := flagNat (superIsLong shape.bpCode false k))
    (by show v1.regs 108 < v1.extent; rw [v1_108, e1]; omega)
    (by show v1.memory (v1.regs 108) = _; rw [v1_108, m1]; exact hLF k hk) (by omega)
  have v2_184 : v2.regs 184 = flagNat (superIsLong shape.bpCode false k) := by
    rw [r2, operand_val_184, put_same]
  have v2get : ∀ r, r ≠ 108 → r ≠ 184 → v2.regs r = u.regs r := fun r a b => by
    rw [r2, operand_val_184, put_ne _ _ b, v1get r a]
  have e12 := (p1.append p2).close
  cases hlong : superIsLong shape.bpCode false k with
  | false =>
      have hz : v2.regs 184 = 0 := by rw [v2_184, hlong]; rfl
      have hnil : longSuperRelativeEntriesForSlot shape.bpCode false k = [] := by
        unfold longSuperRelativeEntriesForSlot; rw [hlong]; rfl
      refine ⟨v2, _, EvalG.seq e12 (EvalG.ifZeroTaken (c := rFLAG) p2.1 hz (EvalG.skip v2 p2.1)), ?_, p2.1,
        ?_, ?_, by rw [kr2, kr1], by rw [k2, k1]⟩
      · omega
      · rw [hnil]; simp only [List.map_nil, flattenPayloadWords]
        exact Emits.of_eq (by rw [e2, e1]) (by rw [m2, m1])
      · intro r hr
        obtain ⟨_, hr2⟩ := not_bodyWrites hr
        obtain ⟨a1, _, _, a4⟩ := not_accessWrites hr2
        exact v2get r a1 (by omega)
  | true =>
      have hnz : v2.regs 184 ≠ 0 := by rw [v2_184, hlong]; decide
      generalize hS : superStride shape.bpCode.length = S at *
      generalize hws : wordBits shape.bpCode.length = ws at *
      obtain ⟨w1, q1, s1, mm1, x1, kk1, kq1⟩ := prefix_pureList hW
        [.arithmetic .mul rBOCC rK rSS, .arithmetic .add rA4 rBOCC rSS] v2 p2.1 (by
          pre1_reg_simp [v2get 173 (by decide) (by decide), h173, v2get 40 (by decide) (by decide), h40]
          omega)
      have w1_172 : w1.regs 172 = k * S + S := by
        rw [s1]; pre1_reg_simp [v2get 173 (by decide) (by decide), h173, v2get 40 (by decide) (by decide), h40]
      have w1_179 : w1.regs 179 = k * S := by
        rw [s1]; pre1_reg_simp [v2get 173 (by decide) (by decide), h173, v2get 40 (by decide) (by decide), h40]
      have w1get : ∀ r, r ≠ 172 → r ≠ 179 → w1.regs r = v2.regs r := fun r a b => by
        rw [s1]; pre1_reg_simp [a, b]
      obtain ⟨w2, q2, s2, mm2, x2, kk2, kq2⟩ := prefix_pureList hW (minActs rEOCC rA4 rN) w1 q1.1 (by
        simp only [minActs]
        pre1_reg_simp [w1_172, w1get 1 (by decide) (by decide), v2get 1 (by decide) (by decide), h1,
          w1get 2 (by decide) (by decide), v2get 2 (by decide) (by decide), hone]
        repeat' apply And.intro
        all_goals first | omega | (split <;> omega))
      have w2_180 : w2.regs 180 = min (k * S + S) shape.size := by
        rw [s2]; simp only [minActs]
        pre1_reg_simp [w1_172, w1get 1 (by decide) (by decide), v2get 1 (by decide) (by decide), h1,
          w1get 2 (by decide) (by decide), v2get 2 (by decide) (by decide), hone]
        split <;> omega
      have w2get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 180 → w2.regs r = w1.regs r := fun r h a => by
        have e1' : r ≠ 26 := by omega
        have e2' : r ≠ 27 := by omega
        have e3' : r ≠ 28 := by omega
        rw [s2]; simp only [minActs]; pre1_reg_simp [e1', e2', e3', a]
      have wget : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 172 → r ≠ 179 → r ≠ 180 → r ≠ 184 →
          w2.regs r = u.regs r := fun r h a b c d e => by
        rw [w2get r h d, w1get r b c, v2get r a e]
      obtain ⟨w3, q3, s3, fr3, mm3, x3, kk3, kq3⟩ := posActs_prefix hW shape rBPOS rBOCC ⟨by decide, by decide⟩
        w2 q2.1 (by rw [wget 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hone])
        P0 (k * S)
        (by rw [wget 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1])
        (by rw [wget 159 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h159])
        (by show w2.regs 179 = k * S; rw [w2get 179 (by decide) (by decide), w1_179]) (by omega)
        (fun q hq => by rw [mm2, mm1, m2, m1]; exact hPOS q hq) (by rw [x2, x1, e2, e1]; omega) (by omega)
        hlenW
      have hpos := position_le_length shape.bpCode false (k * S)
      have w3get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 172 → r ≠ 179 → r ≠ 180 → r ≠ 181 →
          r ≠ 184 → r ≠ 188 → w3.regs r = u.regs r := fun r h a b c d e i j => by
        rw [fr3 r h a j e, wget r h a b c d i]
      have w3_179 : w3.regs 179 = k * S := by
        rw [fr3 179 (by decide) (by decide) (by decide) (by decide), w2get 179 (by decide) (by decide), w1_179]
      have w3_180 : w3.regs 180 = min (k * S + S) shape.size := by
        rw [fr3 180 (by decide) (by decide) (by decide) (by decide), w2_180]
      have w3_181 : w3.regs 181 = position shape.bpCode false (k * S) := s3
      have w3ext : w3.extent = u.extent := by rw [x3, x2, x1, e2, e1]
      have w3mem : w3.memory = u.memory := by rw [mm3, mm2, mm1, m2, m1]
      have pre := (q1.append q2).append q3
      have hentries : longSuperRelativeEntriesForSlot shape.bpCode false k =
          (List.range S).map (fun slot => if k * S + slot < min (k * S + S) shape.size then
            position shape.bpCode false (k * S + slot) - position shape.bpCode false (k * S) else 0) := by
        unfold longSuperRelativeEntriesForSlot
        rw [hlong]
        simp only [if_true]
        rw [relativeOffsetsOrZero_eq_positions shape.bpCode _ _ _ _ (by
          unfold superEndOccurrence; rw [hocc]; exact Nat.min_le_right _ _)]
        unfold superEndOccurrence superBaseOccurrence
        rw [hocc, hS]
      have hlenE : (longSuperRelativeEntriesForSlot shape.bpCode false k).length = S := by
        rw [hentries, List.length_map, List.length_range]
      rw [hlenE] at hext
      -- the table
      obtain ⟨t, jt, et, hjt, htr, htE, htfr, htkr, htk⟩ :=
        emitTable_spec hW rSS rWS relativeOffsetEntryBlock
          (fun slot => if k * S + slot < min (k * S + S) shape.size then
            position shape.bpCode false (k * S + slot) - position shape.bpCode false (k * S) else 0)
          20 RelWrites (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          w3 q3.1 (by rw [w3get 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide), hone])
          (by rw [w3get 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide), htwo])
          (by show w3.regs 40 + 1 < 2 ^ W
              rw [w3get 40 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide), h40]; omega)
          (by show w3.regs 39 < 2 ^ W
              rw [w3get 39 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide), h39]
              have := Nat.le_mul_of_pos_left ws hSpos; omega)
          (by show w3.extent + w3.regs 40 * w3.regs 39 < 2 ^ W
              rw [w3get 40 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide), h40, w3get 39 (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide), h39, w3ext]; exact hext)
          (by
            intro x hxr hxfr hxmem hxe hxk hxkr hslot
            have xget : ∀ r, ¬ RelWrites r → ¬ TableScratch r → x.regs r = w3.regs r := hxfr
            have hslot' : x.regs 14 < S := by
              have : x.regs 14 < w3.regs 40 := hslot
              rwa [w3get 40 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide), h40] at this
            exact relOffsetEntry_spec hW shape x hxr
              (by rw [xget 2 (by decide) (by decide), w3get 2 (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide), hone])
              P0 (k * S) (min (k * S + S) shape.size) (position shape.bpCode false (k * S)) (x.regs 14)
              (by rw [xget 1 (by decide) (by decide), w3get 1 (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide), h1])
              (by rw [xget 159 (by decide) (by decide), w3get 159 (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide), h159])
              rfl
              (by rw [xget 179 (by decide) (by decide), w3_179])
              (by rw [xget 180 (by decide) (by decide), w3_180])
              (by rw [xget 181 (by decide) (by decide), w3_181])
              (by omega) (by omega)
              (fun q hq => by rw [hxmem _ (by rw [w3ext]; omega), w3mem]; exact hPOS q hq)
              (by rw [w3ext] at hxe; omega) (by omega) hlenW)
      have t40 : w3.regs 40 = S := by
        rw [w3get 40 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h40]
      have t39 : w3.regs 39 = ws := by
        rw [w3get 39 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h39]
      simp only [operand_val_40, operand_val_39, t40, t39] at hjt htE
      refine ⟨t, _, EvalG.seq e12 (EvalG.ifZeroFallthrough (c := rFLAG) (zero := .skip) p2.1 hnz
          (EvalG.seq pre.close et) htr), ?_, htr, ?_, ?_, htkr.trans (by rw [kq3, kq2, kq1, kr2, kr1]),
        htk.trans (by rw [kk3, kk2, kk1, k2, k1])⟩
      · simp only [List.length_cons, List.length_nil, minActs]
        rw [hlenE]
        have h1' : S * (20 + 7 * ws + 7) + 3 ≤ 34 * (S * ws) + 3 := by
          have := Nat.mul_le_mul_left S hwspos
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at *
          have h7 : S * (7 * ws) = 7 * (S * ws) := by
            rw [← Nat.mul_assoc, Nat.mul_comm S 7, Nat.mul_assoc]
          omega
        omega
      · rw [hentries]
        have h := (Emits.of_eq (s := u) (s' := w3) w3ext w3mem).trans htE
        rwa [List.nil_append] at h
      · intro r hr
        obtain ⟨h1', h2'⟩ := not_bodyWrites hr
        obtain ⟨a1, a2, a3, a4⟩ := not_accessWrites h2'
        rw [htfr r (fun h => h2' (by
          rcases h with h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl ⟨h.1, by omega⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))) h1']
        exact w3get r a2 a1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-! ## One sparse-exception local slot -/

/-- **Sparse relative body.** For a sparse-exception local slot, its `ls`
relative offsets (bounded by the super end) at the local field width. -/
theorem sparseRelativeBody_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1) (htwo : u.regs 9 = 2) (P0 F0 g : Nat)
    (h1 : u.regs 1 = shape.size) (h159 : u.regs 159 = P0) (h163 : u.regs 163 = F0)
    (h175 : u.regs 175 = g)
    (h40 : u.regs 40 = superStride shape.bpCode.length)
    (h42 : u.regs 42 = localStride shape.bpCode.length)
    (h43 : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (h49 : u.regs 49 = sparseExceptionRelativeWidth shape.bpCode)
    (hg : g < localSlotCount shape.bpCode false)
    (hSF : ∀ g', g' < localSlotCount shape.bpCode false →
      u.memory (F0 + g') = some (flagNat (localIsSparseException shape.bpCode false g')))
    (hPOS : ∀ q, q ≤ shape.size → u.memory (P0 + q) = some (position shape.bpCode false q))
    (hPF : P0 + shape.size < F0) (hFe : F0 + localSlotCount shape.bpCode false ≤ u.extent)
    (hext : u.extent + (sparseExceptionRelativeEntriesForSlot shape.bpCode false g).length *
      sparseExceptionRelativeWidth shape.bpCode < 2 ^ W)
    (hcapS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W)
    (hlenW : shape.bpCode.length < 2 ^ W) :
    ∃ u' j, SafeEval W sparseRelativeBodyBlock u u' j ∧
      j ≤ 25 + 34 * ((sparseExceptionRelativeEntriesForSlot shape.bpCode false g).length *
        sparseExceptionRelativeWidth shape.bpCode) ∧ u'.status = .running ∧
      Emits u u' ((flattenPayloadWords ((sparseExceptionRelativeEntriesForSlot shape.bpCode false g).map
        (natToBitsLE (sparseExceptionRelativeWidth shape.bpCode)))).map SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ BodyWrites r → u'.regs r = u.regs r) ∧ u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys := by
  have h2W := two_le_two_pow hW
  have hocc := bp_occurrenceCount shape
  have hSpos := superStride_pos shape.bpCode.length
  have hlspos := localStride_pos shape.bpCode.length
  have hLPSpos := localSlotsPerSuper_pos shape.bpCode.length
  have hlwpos := sparseExceptionRelativeWidth_pos shape.bpCode
  have hoff := localOffset_le (superStride shape.bpCode.length) (localStride shape.bpCode.length) g
    hlspos hSpos
  have hLPSdef : localSlotsPerSuper shape.bpCode.length =
      selectLocalSlotsPerSuper (superStride shape.bpCode.length) (localStride shape.bpCode.length) := rfl
  rw [← hLPSdef] at hoff
  obtain ⟨hB1, hsS⟩ := localBase_bound shape hg
  have hgcap := localSlot_lt_cap shape hg
  have hbase := localBaseOccurrence_mod shape.bpCode.length g
  have hls : localStride shape.bpCode.length ≤
      localStride shape.bpCode.length * sparseExceptionRelativeWidth shape.bpCode :=
    Nat.le_mul_of_pos_right _ hlwpos
  have hsupS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length =
      superSlotCount shape.bpCode false * superStride shape.bpCode.length + superStride shape.bpCode.length :=
    Nat.succ_mul _ _
  have hsp := flagNat_le (localIsSparseException shape.bpCode false g)
  -- the flag
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pure hW (.arithmetic .add rADDR rSFB rG) u hrun (by
    simp only [pureOK, Arithmetic.eval, operand_val_163, operand_val_175, h163, h175, reduceCtorEq,
      false_implies, false_or, and_true]
    omega)
  have v1_108 : v1.regs 108 = F0 + g := by
    rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_163, operand_val_175, operand_val_108, h163, h175,
      put_same]
  have v1get : ∀ r, r ≠ 108 → v1.regs r = u.regs r := fun r h => by
    rw [r1]; simp only [pureReg, operand_val_108]; rw [put_ne _ _ h]
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_load hW rFLAG rADDR v1 p1.1
    (x := flagNat (localIsSparseException shape.bpCode false g))
    (by show v1.regs 108 < v1.extent; rw [v1_108, e1]; omega)
    (by show v1.memory (v1.regs 108) = _; rw [v1_108, m1]; exact hSF g hg) (by omega)
  have v2_184 : v2.regs 184 = flagNat (localIsSparseException shape.bpCode false g) := by
    rw [r2, operand_val_184, put_same]
  have v2get : ∀ r, r ≠ 108 → r ≠ 184 → v2.regs r = u.regs r := fun r a b => by
    rw [r2, operand_val_184, put_ne _ _ b, v1get r a]
  have e12 := (p1.append p2).close
  cases hsparse : localIsSparseException shape.bpCode false g with
  | false =>
      have hz : v2.regs 184 = 0 := by rw [v2_184, hsparse]; rfl
      have hnil : sparseExceptionRelativeEntriesForSlot shape.bpCode false g = [] := by
        unfold sparseExceptionRelativeEntriesForSlot; rw [hsparse]; rfl
      refine ⟨v2, _, EvalG.seq e12 (EvalG.ifZeroTaken (c := rFLAG) p2.1 hz (EvalG.skip v2 p2.1)), ?_, p2.1,
        ?_, ?_, by rw [kr2, kr1], by rw [k2, k1]⟩
      · omega
      · rw [hnil]; simp only [List.map_nil, flattenPayloadWords]
        exact Emits.of_eq (by rw [e2, e1]) (by rw [m2, m1])
      · intro r hr
        obtain ⟨_, hr2⟩ := not_bodyWrites hr
        obtain ⟨a1, _, _, a4⟩ := not_accessWrites hr2
        exact v2get r a1 (by omega)
  | true =>
      have hnz : v2.regs 184 ≠ 0 := by rw [v2_184, hsparse]; decide
      have hentries0 : sparseExceptionRelativeEntriesForSlot shape.bpCode false g =
          relativeOffsetsOrZero false shape.bpCode (localBaseOccurrence shape.bpCode.length g)
            (localStride shape.bpCode.length)
            (superEndOccurrence shape.bpCode false (localSuperSlot shape.bpCode.length g))
            (position shape.bpCode false (localBaseOccurrence shape.bpCode.length g)) := by
        unfold sparseExceptionRelativeEntriesForSlot; rw [hsparse]; rfl
      have hend : superEndOccurrence shape.bpCode false (localSuperSlot shape.bpCode.length g) =
          min (localSuperSlot shape.bpCode.length g * superStride shape.bpCode.length +
            superStride shape.bpCode.length) shape.size := by
        unfold superEndOccurrence superBaseOccurrence; rw [hocc]
      rw [hend, relativeOffsetsOrZero_eq_positions shape.bpCode _ _ _ _ (by
        rw [hocc]; exact Nat.min_le_right _ _)] at hentries0
      unfold localSuperSlot at hsS hentries0
      generalize hS : superStride shape.bpCode.length = S at *
      generalize hlsd : localStride shape.bpCode.length = ls at *
      generalize hLPS : localSlotsPerSuper shape.bpCode.length = LPS at *
      generalize hsup : superSlotCount shape.bpCode false = sup at *
      generalize hlw : sparseExceptionRelativeWidth shape.bpCode = lw at *
      generalize hB : localBaseOccurrence shape.bpCode.length g = B at *
      obtain ⟨sS, hsSd⟩ : ∃ x, g / LPS = x := ⟨_, rfl⟩
      obtain ⟨gm, hgm⟩ : ∃ x, g % LPS = x := ⟨_, rfl⟩
      rw [hsSd] at hsS hbase hentries0
      rw [hgm] at hoff hbase
      have hsSS : (sS + 1) * S ≤ sup * S := Nat.mul_le_mul_right S hsS
      have hsS1 : (sS + 1) * S = sS * S + S := Nat.succ_mul sS S
      have hgmle : gm ≤ g := hgm ▸ Nat.mod_le g LPS
      have hsSle : sS ≤ g := hsSd ▸ Nat.div_le_self g LPS
      obtain ⟨w1, q1, s1, mm1, x1, kk1, kq1⟩ := prefix_pureList hW
        [.arithmetic .div rSSL rG rLPS, .arithmetic .mod rA1 rG rLPS, .arithmetic .mul rA1 rA1 rLSTR,
          .arithmetic .mul rBOCC rSSL rSS, .arithmetic .add rA4 rBOCC rSS] v2 p2.1 (by
          pre1_reg_simp [v2get 175 (by decide) (by decide), h175, v2get 43 (by decide) (by decide), h43,
            v2get 42 (by decide) (by decide), h42, v2get 40 (by decide) (by decide), h40, hsSd, hgm]
          repeat' apply And.intro
          all_goals first | omega | (apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _); omega) |
            (apply Nat.lt_of_le_of_lt (Nat.mod_le _ _); omega))
      have w1_169 : w1.regs 169 = gm * ls := by
        rw [s1]; pre1_reg_simp [v2get 175 (by decide) (by decide), h175, v2get 43 (by decide) (by decide), h43,
          v2get 42 (by decide) (by decide), h42, v2get 40 (by decide) (by decide), h40, hsSd, hgm]
      have w1_172 : w1.regs 172 = sS * S + S := by
        rw [s1]; pre1_reg_simp [v2get 175 (by decide) (by decide), h175, v2get 43 (by decide) (by decide), h43,
          v2get 42 (by decide) (by decide), h42, v2get 40 (by decide) (by decide), h40, hsSd, hgm]
      have w1_179 : w1.regs 179 = sS * S := by
        rw [s1]; pre1_reg_simp [v2get 175 (by decide) (by decide), h175, v2get 43 (by decide) (by decide), h43,
          v2get 42 (by decide) (by decide), h42, v2get 40 (by decide) (by decide), h40, hsSd, hgm]
      have w1get : ∀ r, r ≠ 169 → r ≠ 172 → r ≠ 179 → r ≠ 185 → w1.regs r = v2.regs r := fun r a b c d => by
        rw [s1]; pre1_reg_simp [a, b, c, d]
      obtain ⟨w2, q2, s2, mm2, x2, kk2, kq2⟩ := prefix_pureList hW (minActs rEOCC rA4 rN) w1 q1.1 (by
        simp only [minActs]
        pre1_reg_simp [w1_172, w1get 1 (by decide) (by decide) (by decide) (by decide),
          v2get 1 (by decide) (by decide), h1,
          w1get 2 (by decide) (by decide) (by decide) (by decide), v2get 2 (by decide) (by decide), hone]
        repeat' apply And.intro
        all_goals first | omega | (split <;> omega))
      have w2_180 : w2.regs 180 = min (sS * S + S) shape.size := by
        rw [s2]; simp only [minActs]
        pre1_reg_simp [w1_172, w1get 1 (by decide) (by decide) (by decide) (by decide),
          v2get 1 (by decide) (by decide), h1,
          w1get 2 (by decide) (by decide) (by decide) (by decide), v2get 2 (by decide) (by decide), hone]
        split <;> omega
      have w2get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 180 → w2.regs r = w1.regs r := fun r h a => by
        have e1' : r ≠ 26 := by omega
        have e2' : r ≠ 27 := by omega
        have e3' : r ≠ 28 := by omega
        rw [s2]; simp only [minActs]; pre1_reg_simp [e1', e2', e3', a]
      obtain ⟨w3, q3, s3, mm3, x3, kk3, kq3⟩ := prefix_pure hW (.arithmetic .add rBOCC rBOCC rA1) w2 q2.1 (by
        simp only [pureOK, Arithmetic.eval, operand_val_179, operand_val_169,
          w2get 179 (by decide) (by decide), w1_179, w2get 169 (by decide) (by decide), w1_169, reduceCtorEq,
          false_implies, false_or, and_true]
        omega)
      have w3_179 : w3.regs 179 = B := by
        rw [s3]; simp only [pureReg, Arithmetic.eval, operand_val_179, operand_val_169,
          w2get 179 (by decide) (by decide), w1_179, w2get 169 (by decide) (by decide), w1_169, put_same]
        omega
      have w3get : ∀ r, r ≠ 179 → w3.regs r = w2.regs r := fun r h => by
        rw [s3]; simp only [pureReg, operand_val_179]; rw [put_ne _ _ h]
      have wget : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 169 → r ≠ 172 → r ≠ 179 → r ≠ 180 →
          r ≠ 184 → r ≠ 185 → w3.regs r = u.regs r := fun r h a b c d e i j => by
        rw [w3get r d, w2get r h e, w1get r b c d j, v2get r a i]
      obtain ⟨w4, q4, s4, fr4, mm4, x4, kk4, kq4⟩ := posActs_prefix hW shape rBPOS rBOCC ⟨by decide, by decide⟩
        w3 q3.1 (by rw [wget 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), hone]) P0 B
        (by rw [wget 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h1])
        (by rw [wget 159 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h159])
        w3_179 (by omega)
        (fun q hq => by rw [mm3, mm2, mm1, m2, m1]; exact hPOS q hq) (by rw [x3, x2, x1, e2, e1]; omega)
        (by omega) hlenW
      have hpos := position_le_length shape.bpCode false B
      have w4get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 169 → r ≠ 172 → r ≠ 179 → r ≠ 180 →
          r ≠ 181 → r ≠ 184 → r ≠ 185 → r ≠ 188 → w4.regs r = u.regs r := fun r h a b c d e i j l m => by
        rw [fr4 r h a m i, wget r h a b c d e j l]
      have w4_179 : w4.regs 179 = B := by
        rw [fr4 179 (by decide) (by decide) (by decide) (by decide), w3_179]
      have w4_180 : w4.regs 180 = min (sS * S + S) shape.size := by
        rw [fr4 180 (by decide) (by decide) (by decide) (by decide), w3get 180 (by decide), w2_180]
      have w4_181 : w4.regs 181 = position shape.bpCode false B := s4
      have w4ext : w4.extent = u.extent := by rw [x4, x3, x2, x1, e2, e1]
      have w4mem : w4.memory = u.memory := by rw [mm4, mm3, mm2, mm1, m2, m1]
      have pre := ((q1.append q2).append q3).append q4
      have t42 : w4.regs 42 = ls := by
        rw [w4get 42 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), h42]
      have t49 : w4.regs 49 = lw := by
        rw [w4get 49 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), h49]
      have hlenE : (sparseExceptionRelativeEntriesForSlot shape.bpCode false g).length = ls := by
        rw [hentries0, List.length_map, List.length_range]
      rw [hlenE] at hext
      -- the table
      obtain ⟨t, jt, et, hjt, htr, htE, htfr, htkr, htk⟩ :=
        emitTable_spec hW rLSTR rLW relativeOffsetEntryBlock
          (fun slot => if B + slot < min (sS * S + S) shape.size then
            position shape.bpCode false (B + slot) - position shape.bpCode false B else 0)
          20 RelWrites (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          w4 q4.1 (by rw [w4get 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide), hone])
          (by rw [w4get 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide), htwo])
          (by show w4.regs 42 + 1 < 2 ^ W; rw [t42]; omega)
          (by show w4.regs 49 < 2 ^ W
              rw [t49]; have := Nat.le_mul_of_pos_left lw hlspos; omega)
          (by show w4.extent + w4.regs 42 * w4.regs 49 < 2 ^ W
              rw [t42, t49, w4ext]; exact hext)
          (by
            intro x hxr hxfr hxmem hxe hxk hxkr hslot
            have xget : ∀ r, ¬ RelWrites r → ¬ TableScratch r → x.regs r = w4.regs r := hxfr
            have hslot' : x.regs 14 < ls := by
              have : x.regs 14 < w4.regs 42 := hslot
              rwa [t42] at this
            exact relOffsetEntry_spec hW shape x hxr
              (by rw [xget 2 (by decide) (by decide), w4get 2 (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hone])
              P0 B (min (sS * S + S) shape.size) (position shape.bpCode false B) (x.regs 14)
              (by rw [xget 1 (by decide) (by decide), w4get 1 (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1])
              (by rw [xget 159 (by decide) (by decide), w4get 159 (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h159])
              rfl
              (by rw [xget 179 (by decide) (by decide), w4_179])
              (by rw [xget 180 (by decide) (by decide), w4_180])
              (by rw [xget 181 (by decide) (by decide), w4_181])
              (by omega) (by omega)
              (fun q hq => by rw [hxmem _ (by rw [w4ext]; omega), w4mem]; exact hPOS q hq)
              (by rw [w4ext] at hxe; omega) (by omega) hlenW)
      simp only [operand_val_42, operand_val_49, t42, t49] at hjt htE
      refine ⟨t, _, EvalG.seq e12 (EvalG.ifZeroFallthrough (c := rFLAG) (zero := .skip) p2.1 hnz
          (EvalG.seq pre.close et) htr), ?_, htr, ?_, ?_, htkr.trans (by rw [kq4, kq3, kq2, kq1, kr2, kr1]),
        htk.trans (by rw [kk4, kk3, kk2, kk1, k2, k1])⟩
      · simp only [List.length_cons, List.length_nil, minActs]
        rw [hlenE]
        have h1' : ls * (20 + 7 * lw + 7) + 3 ≤ 34 * (ls * lw) + 3 := by
          have := Nat.mul_le_mul_left ls hlwpos
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at *
          have h7 : ls * (7 * lw) = 7 * (ls * lw) := by
            rw [← Nat.mul_assoc, Nat.mul_comm ls 7, Nat.mul_assoc]
          omega
        omega
      · rw [hentries0]
        have h := (Emits.of_eq (s := u) (s' := w4) w4ext w4mem).trans htE
        rwa [List.nil_append] at h
      · intro r hr
        obtain ⟨h1', h2'⟩ := not_bodyWrites hr
        obtain ⟨a1, a2, a3, a4⟩ := not_accessWrites h2'
        rw [htfr r (fun h => h2' (by
          rcases h with h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl ⟨h.1, by omega⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))) h1']
        exact w4get r a2 a1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)

/-! ## Relative flat-map loops -/

theorem entryBits_length (w : Nat) (es : List Nat) :
    ((flattenPayloadWords (es.map (natToBitsLE w))).map SuccinctSpace.bitToNat).length = es.length * w := by
  rw [List.length_map, flatten_bits_length]

theorem flatMap_range_length_mono (E : Nat → List Nat) {m N : Nat} (h : m ≤ N) :
    ((List.range m).flatMap E).length ≤ ((List.range N).flatMap E).length := by
  induction N with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ N ih =>
      by_cases hm : m = N + 1
      · rw [hm]; exact Nat.le_refl _
      · rw [List.range_succ, List.flatMap_append, List.length_append]
        have := ih (by omega)
        omega

/-- **Relative flat-map loop.** A counted loop whose body appends the table bits
of `E k` at width `w` emits the bits of `(range N).flatMap E`; the cost pays a
constant per slot plus 34 per emitted cell (potential `CAP - extent`). -/
theorem relLoop_spec {W : Nat} (hW : 32 ≤ W) (i go cnt : Operand) (body : Block) (J w : Nat)
    (E : Nat → List Nat) (Keep : State → Prop)
    (hig : (i : Nat) ≠ go) (hic : (i : Nat) ≠ cnt) (hgc : (go : Nat) ≠ cnt)
    (hi2 : (i : Nat) ≠ 2) (hg2 : (go : Nat) ≠ 2)
    (s : State) (hrun : s.status = .running) (hone : s.regs 2 = 1) (hN : s.regs cnt < 2 ^ W)
    (hext : s.extent + ((List.range (s.regs cnt)).flatMap E).length * w < 2 ^ W)
    (hKeep0 : ∀ u : State, u.status = .running → (∀ r : Nat, r ≠ i → r ≠ go → u.regs r = s.regs r) →
      u.memory = s.memory → u.extent = s.extent → u.keys = s.keys → u.keyRegs = s.keyRegs → Keep u)
    (hKeep : ∀ u v : State, Keep u → (∀ r : Nat, r ≠ i → r ≠ go → v.regs r = u.regs r) →
      v.memory = u.memory → v.extent = u.extent → v.keys = u.keys → v.keyRegs = u.keyRegs → Keep v)
    (hbody : ∀ k (u : State), k < s.regs cnt → Keep u → u.status = .running →
      u.regs i = k → u.regs cnt = s.regs cnt → u.regs 2 = 1 →
      Emits s u ((List.range k).flatMap
        (fun x => (flattenPayloadWords ((E x).map (natToBitsLE w))).map SuccinctSpace.bitToNat)) →
      u.extent + (E k).length * w < 2 ^ W →
      ∃ u' j, SafeEval W body u u' j ∧ j ≤ J + 34 * ((E k).length * w) ∧ u'.status = .running ∧
        u'.regs i = k ∧ u'.regs cnt = s.regs cnt ∧ u'.regs 2 = 1 ∧
        Emits u u' ((flattenPayloadWords ((E k).map (natToBitsLE w))).map SuccinctSpace.bitToNat) ∧
        Keep u') :
    ∃ s' j, SafeEval W (forSlots i go cnt body) s s' j ∧
      j ≤ s.regs cnt * (J + 4) + 3 + 34 * (((List.range (s.regs cnt)).flatMap E).length * w) ∧
      s'.status = .running ∧
      Emits s s' ((flattenPayloadWords (((List.range (s.regs cnt)).flatMap E).map
        (natToBitsLE w))).map SuccinctSpace.bitToNat) ∧ Keep s' := by
  let G : Nat → List Nat := fun x =>
    (flattenPayloadWords ((E x).map (natToBitsLE w))).map SuccinctSpace.bitToNat
  have hGlen : ∀ m, ((List.range m).flatMap G).length = ((List.range m).flatMap E).length * w := by
    intro m
    show ((List.range m).flatMap
      (fun x => (flattenPayloadWords ((E x).map (natToBitsLE w))).map SuccinctSpace.bitToNat)).length = _
    rw [← flatten_map_flatMap, entryBits_length]
  generalize hCAP : s.extent + ((List.range (s.regs cnt)).flatMap E).length * w = CAP at hext
  obtain ⟨s', k, e, hk, hr, ⟨hem, hkeep⟩, _, _⟩ :=
    forSlots_spec_pot hW i go cnt body J 34 (fun u => CAP - u.extent) hig hic hgc hi2 hg2
      (fun k u => Emits s u ((List.range k).flatMap G) ∧ Keep u) s hrun hone hN
      (fun u v _ _ he => by show CAP - v.extent = CAP - u.extent; rw [he])
      (fun u hu hregs hm he hk hkr => ⟨by
          simp only [List.range_zero, List.flatMap_nil]
          exact Emits.of_eq he hm, hKeep0 u hu hregs hm he hk hkr⟩)
      (by
        intro kk u hkk ⟨hue, huk⟩ hur hui hucnt huone
        have huext : u.extent = s.extent + ((List.range kk).flatMap E).length * w := by
          rw [hue.1, hGlen]
        have hmono := flatMap_range_length_mono E (show kk + 1 ≤ s.regs cnt by omega)
        rw [List.range_succ, List.flatMap_append, List.length_append] at hmono
        have hmono' := Nat.mul_le_mul_right w hmono
        rw [Nat.add_mul] at hmono'
        have hEk : ([kk].flatMap E).length = (E kk).length := by simp
        rw [hEk] at hmono'
        obtain ⟨u', j, eb, hj, hu'r, hu'i, hu'cnt, hu'one, hu'e, hu'k⟩ :=
          hbody kk u hkk huk hur hui hucnt huone hue (by omega)
        have hu'ext : u'.extent = u.extent + (E kk).length * w := by
          rw [hu'e.1, entryBits_length]
        refine ⟨u', j, eb, ?_, hu'r, hu'i, hu'cnt, hu'one, fun v _ hvr hvm hve hvk hvkr => ?_⟩
        · show j + 34 * (CAP - u'.extent) ≤ J + 34 * (CAP - u.extent)
          rw [hu'ext]
          omega
        · refine ⟨?_, hKeep u' v hu'k hvr hvm hve hvk hvkr⟩
          rw [flatMap_range_succ]
          exact (hue.trans hu'e).congr_right hvm hve)
  have hcost : k ≤ s.regs cnt * (J + 4) + 3 + 34 * (((List.range (s.regs cnt)).flatMap E).length * w) := by
    have : CAP - s.extent = ((List.range (s.regs cnt)).flatMap E).length * w := by omega
    omega
  refine ⟨s', k, e, hcost, hr, ?_, hkeep⟩
  rw [flatten_map_flatMap]
  exact hem

/-- **Long relative table.** The loop over all supers emits the reference
`selectLongRelative` source. -/
theorem longRelative_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2) (P0 L0 : Nat)
    (h1 : s.regs 1 = shape.size) (h159 : s.regs 159 = P0) (h161 : s.regs 161 = L0)
    (h39 : s.regs 39 = wordBits shape.bpCode.length)
    (h40 : s.regs 40 = superStride shape.bpCode.length)
    (h45 : s.regs 45 = superSlotCount shape.bpCode false)
    (hLF : ∀ k, k < superSlotCount shape.bpCode false →
      s.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (hPOS : ∀ q, q ≤ shape.size → s.memory (P0 + q) = some (position shape.bpCode false q))
    (hPL : P0 + shape.size < L0) (hLe : L0 + superSlotCount shape.bpCode false ≤ s.extent)
    (hext : s.extent + (tableBits (longSuperRelativeEntries shape.bpCode false)
      (wordBits shape.bpCode.length)).length < 2 ^ W)
    (hcapS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length < 2 ^ W)
    (hlenW : shape.bpCode.length < 2 ^ W) :
    ∃ s' j, SafeEval W (forSlots rK rKGO rSUP longRelativeBodyBlock) s s' j ∧
      j ≤ superSlotCount shape.bpCode false * 25 + 3 +
        34 * (tableBits (longSuperRelativeEntries shape.bpCode false) (wordBits shape.bpCode.length)).length ∧
      s'.status = .running ∧
      Emits s s' ((tableBits (longSuperRelativeEntries shape.bpCode false)
        (wordBits shape.bpCode.length)).map SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ BodyWrites r → r ≠ 173 → r ≠ 174 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  have hsupW : superSlotCount shape.bpCode false < 2 ^ W := by
    have := Nat.le_mul_of_pos_right (superSlotCount shape.bpCode false) (superStride_pos shape.bpCode.length)
    rw [Nat.succ_mul] at hcapS; omega
  have hflat : longSuperRelativeEntries shape.bpCode false =
      (List.range (s.regs 45)).flatMap (longSuperRelativeEntriesForSlot shape.bpCode false) := by
    rw [h45]; rfl
  rw [tableBits_length, hflat] at hext
  let Keep : State → Prop := fun u =>
    (∀ r, ¬ BodyWrites r → r ≠ 173 → r ≠ 174 → u.regs r = s.regs r) ∧ u.keys = s.keys ∧ u.keyRegs = s.keyRegs
  obtain ⟨s', j, e, hj, hr, hE, ⟨K1, K2, K3⟩⟩ :=
    relLoop_spec hW rK rKGO rSUP longRelativeBodyBlock 21 (wordBits shape.bpCode.length)
      (longSuperRelativeEntriesForSlot shape.bpCode false) Keep
      (by decide) (by decide) (by decide) (by decide) (by decide) s hrun hone
      (by show s.regs 45 < 2 ^ W; rw [h45]; exact hsupW) hext
      (fun u _ hregs _ _ hk hkr => ⟨fun r _ a b => hregs r a b, hk, hkr⟩)
      (fun u v ⟨U1, U2, U3⟩ hregs _ _ hk hkr => ⟨fun r h a b => by rw [hregs r a b]; exact U1 r h a b,
        by rw [hk, U2], by rw [hkr, U3]⟩)
      (by
        intro k u hk ⟨U1, U2, U3⟩ hur hui hucnt huone hue hextk
        have hk' : k < superSlotCount shape.bpCode false := by
          have : k < s.regs 45 := hk
          rwa [h45] at this
        have uget : ∀ r, ¬ BodyWrites r → r ≠ 173 → r ≠ 174 → u.regs r = s.regs r := U1
        obtain ⟨u', j, ev, hj, hr', hE', F, Kr, Ks⟩ :=
          longRelativeBody_spec hW shape u hur huone
            (by rw [uget 9 (by decide) (by decide) (by decide), htwo]) P0 L0 k
            (by rw [uget 1 (by decide) (by decide) (by decide), h1])
            (by rw [uget 159 (by decide) (by decide) (by decide), h159])
            (by rw [uget 161 (by decide) (by decide) (by decide), h161]) hui
            (by rw [uget 39 (by decide) (by decide) (by decide), h39])
            (by rw [uget 40 (by decide) (by decide) (by decide), h40]) hk'
            (fun k' hk'' => by rw [hue.memory_below (by omega)]; exact hLF k' hk'')
            (fun q hq => by rw [hue.memory_below (by omega)]; exact hPOS q hq)
            hPL (by rw [hue.1]; omega) hextk hcapS hlenW
        refine ⟨u', j, ev, hj, hr', ?_, ?_, ?_, hE', ?_, ?_, ?_⟩
        · show u'.regs 173 = k; rw [F 173 (by decide)]; exact hui
        · show u'.regs 45 = s.regs 45; rw [F 45 (by decide)]; exact hucnt
        · rw [F 2 (by decide), huone]
        · intro r h a b; rw [F r h]; exact U1 r h a b
        · rw [Ks, U2]
        · rw [Kr, U3])
  simp only [operand_val_45] at hj hE
  rw [← hflat] at hj hE
  rw [h45] at hj
  refine ⟨s', j, e, ?_, hr, hE, K1, K3, K2⟩
  rw [tableBits_length]
  exact hj

/-- **Sparse relative table.** The loop over all local slots emits the reference
`selectSparseRelative` source. -/
theorem sparseRelative_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2) (P0 F0 : Nat)
    (h1 : s.regs 1 = shape.size) (h159 : s.regs 159 = P0) (h163 : s.regs 163 = F0)
    (h40 : s.regs 40 = superStride shape.bpCode.length)
    (h42 : s.regs 42 = localStride shape.bpCode.length)
    (h43 : s.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (h46 : s.regs 46 = localSlotCount shape.bpCode false)
    (h49 : s.regs 49 = sparseExceptionRelativeWidth shape.bpCode)
    (hSF : ∀ g, g < localSlotCount shape.bpCode false →
      s.memory (F0 + g) = some (flagNat (localIsSparseException shape.bpCode false g)))
    (hPOS : ∀ q, q ≤ shape.size → s.memory (P0 + q) = some (position shape.bpCode false q))
    (hPF : P0 + shape.size < F0) (hFe : F0 + localSlotCount shape.bpCode false ≤ s.extent)
    (hext : s.extent + (tableBits (sparseExceptionRelativeEntries shape.bpCode false)
      (sparseExceptionRelativeWidth shape.bpCode)).length < 2 ^ W)
    (hcapS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W)
    (hlenW : shape.bpCode.length < 2 ^ W) :
    ∃ s' j, SafeEval W (forSlots rG rGGO rLOC sparseRelativeBodyBlock) s s' j ∧
      j ≤ localSlotCount shape.bpCode false * 29 + 3 +
        34 * (tableBits (sparseExceptionRelativeEntries shape.bpCode false)
          (sparseExceptionRelativeWidth shape.bpCode)).length ∧
      s'.status = .running ∧
      Emits s s' ((tableBits (sparseExceptionRelativeEntries shape.bpCode false)
        (sparseExceptionRelativeWidth shape.bpCode)).map SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ BodyWrites r → r ≠ 175 → r ≠ 176 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  have hlocW : localSlotCount shape.bpCode false < 2 ^ W := by omega
  have hflat : sparseExceptionRelativeEntries shape.bpCode false =
      (List.range (s.regs 46)).flatMap (sparseExceptionRelativeEntriesForSlot shape.bpCode false) := by
    rw [h46]; rfl
  rw [tableBits_length, hflat] at hext
  let Keep : State → Prop := fun u =>
    (∀ r, ¬ BodyWrites r → r ≠ 175 → r ≠ 176 → u.regs r = s.regs r) ∧ u.keys = s.keys ∧ u.keyRegs = s.keyRegs
  obtain ⟨s', j, e, hj, hr, hE, ⟨K1, K2, K3⟩⟩ :=
    relLoop_spec hW rG rGGO rLOC sparseRelativeBodyBlock 25 (sparseExceptionRelativeWidth shape.bpCode)
      (sparseExceptionRelativeEntriesForSlot shape.bpCode false) Keep
      (by decide) (by decide) (by decide) (by decide) (by decide) s hrun hone
      (by show s.regs 46 < 2 ^ W; rw [h46]; exact hlocW) hext
      (fun u _ hregs _ _ hk hkr => ⟨fun r _ a b => hregs r a b, hk, hkr⟩)
      (fun u v ⟨U1, U2, U3⟩ hregs _ _ hk hkr => ⟨fun r h a b => by rw [hregs r a b]; exact U1 r h a b,
        by rw [hk, U2], by rw [hkr, U3]⟩)
      (by
        intro g u hg ⟨U1, U2, U3⟩ hur hui hucnt huone hue hextg
        have hg' : g < localSlotCount shape.bpCode false := by
          have : g < s.regs 46 := hg
          rwa [h46] at this
        have uget : ∀ r, ¬ BodyWrites r → r ≠ 175 → r ≠ 176 → u.regs r = s.regs r := U1
        obtain ⟨u', j, ev, hj, hr', hE', F, Kr, Ks⟩ :=
          sparseRelativeBody_spec hW shape u hur huone
            (by rw [uget 9 (by decide) (by decide) (by decide), htwo]) P0 F0 g
            (by rw [uget 1 (by decide) (by decide) (by decide), h1])
            (by rw [uget 159 (by decide) (by decide) (by decide), h159])
            (by rw [uget 163 (by decide) (by decide) (by decide), h163]) hui
            (by rw [uget 40 (by decide) (by decide) (by decide), h40])
            (by rw [uget 42 (by decide) (by decide) (by decide), h42])
            (by rw [uget 43 (by decide) (by decide) (by decide), h43])
            (by rw [uget 49 (by decide) (by decide) (by decide), h49]) hg'
            (fun g' hg'' => by rw [hue.memory_below (by omega)]; exact hSF g' hg'')
            (fun q hq => by rw [hue.memory_below (by omega)]; exact hPOS q hq)
            hPF (by rw [hue.1]; omega) hextg hcapS hlenW
        refine ⟨u', j, ev, hj, hr', ?_, ?_, ?_, hE', ?_, ?_, ?_⟩
        · show u'.regs 175 = g; rw [F 175 (by decide)]; exact hui
        · show u'.regs 46 = s.regs 46; rw [F 46 (by decide)]; exact hucnt
        · rw [F 2 (by decide), huone]
        · intro r h a b; rw [F r h]; exact U1 r h a b
        · rw [Ks, U2]
        · rw [Kr, U3])
  simp only [operand_val_46] at hj hE
  rw [← hflat] at hj hE
  rw [h46] at hj
  refine ⟨s', j, e, ?_, hr, hE, K1, K3, K2⟩
  rw [tableBits_length]
  exact hj

end RMQ.SuccinctFinal.PackedConstruction.Proof
