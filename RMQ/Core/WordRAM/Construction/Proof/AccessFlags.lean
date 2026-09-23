import RMQ.Core.WordRAM.Construction.Proof.PosPass

/-! # PRE-1 builder proofs: long and sparse-exception flags (stage S5)

Outside the builder firewall. From the close positions, `longFlagsBlock`
stores `superIsLong` for every super slot with its prefix counts, and
`sparseFlagsBlock` stores `localIsSparseException` for every local slot with
its prefix counts, both exactly as the reference defines them, including the
clamped positions and the truncating subtractions.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose RMQ.GenericSelect

/-! ## Register-only action lists as prefixes -/

theorem ActsPrefix.nil' {W : Nat} (u : State) (hrun : u.status = .running) :
    ActsPrefix W [] u u 0 :=
  ⟨hrun, fun rest t' k' e => by rw [List.nil_append, Nat.zero_add]; exact e⟩

theorem prefix_pureList {W : Nat} (hW : 32 ≤ W) :
    ∀ (ops : List Action) (u : State), u.status = .running → pureOKs W ops u.regs →
      ∃ u', ActsPrefix W ops u u' ops.length ∧ u'.regs = pureRegs ops u.regs ∧
        u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs
  | [], u, hrun, _ => ⟨u, ActsPrefix.nil' u hrun, rfl, rfl, rfl, rfl, rfl⟩
  | a :: rest, u, hrun, ⟨ha, hrest⟩ => by
      obtain ⟨v, pv, rv, mv, ev, kv, krv⟩ := prefix_pure hW a u hrun ha
      obtain ⟨w, pw, rw', mw, ew, kw, krw⟩ :=
        prefix_pureList hW rest v pv.1 (by rw [rv]; exact hrest)
      have pa := pv.append pw
      rw [show 1 + rest.length = (a :: rest).length by simp [Nat.add_comm]] at pa
      refine ⟨w, pa, ?_, by rw [mw, mv], by rw [ew, ev], by rw [kw, kv], by rw [krw, krv]⟩
      rw [rw', rv]; rfl

/-- **Clamped position load.** -/
theorem posActs_prefix {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (dst occ : Operand)
    (hocc : (occ : Nat) ≠ 26 ∧ (occ : Nat) ≠ 27)
    (u : State) (hrun : u.status = .running) (hone : u.regs 2 = 1) (P0 K : Nat)
    (h1 : u.regs 1 = shape.size) (h159 : u.regs 159 = P0) (hK : u.regs occ = K)
    (hKW : K < 2 ^ W)
    (hPOS : ∀ k, k ≤ shape.size → u.memory (P0 + k) = some (position shape.bpCode false k))
    (hPe : P0 + shape.size < u.extent) (hPW : P0 + shape.size < 2 ^ W)
    (hlenW : shape.bpCode.length < 2 ^ W) :
    ∃ u', ActsPrefix W (posActs dst occ) u u' 7 ∧
      u'.regs dst = position shape.bpCode false K ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 188 → r ≠ dst → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs := by
  have hsW : shape.size < 2 ^ W := by omega
  have h2W := two_le_two_pow hW
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pureList hW (minActs rA5 occ rN) u hrun (by
    simp only [minActs]
    pre1_reg_simp [hK, h1, hone, hocc.1, hocc.2]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega))
  have v1_188 : v1.regs 188 = min K shape.size := by
    rw [r1]; simp only [minActs]; pre1_reg_simp [hK, h1, hone, hocc.1, hocc.2]
    split <;> omega
  have v1get : ∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 188 → v1.regs r = u.regs r := by
    intro r h h188
    have e1' : r ≠ 26 := by omega
    have e2' : r ≠ 27 := by omega
    have e3' : r ≠ 28 := by omega
    rw [r1]; simp only [minActs]; pre1_reg_simp [e1', e2', e3', h188]
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_pure hW (.arithmetic .add rADDR rPOSB rA5) v1 p1.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_159, operand_val_188, v1_188,
      v1get 159 (by decide) (by decide), h159, reduceCtorEq, false_implies, false_or, and_true]
    have := Nat.min_le_right K shape.size
    omega)
  have v2_108 : v2.regs 108 = P0 + min K shape.size := by
    rw [r2]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_159, operand_val_188,
      v1_188, v1get 159 (by decide) (by decide), h159, put_same]
  have v2get : ∀ r : Nat, r ≠ 108 → v2.regs r = v1.regs r := fun r h => by
    rw [r2]; simp only [pureReg, operand_val_108]; rw [put_ne _ _ h]
  have hpos := position_le_length shape.bpCode false K
  obtain ⟨v3, p3, r3, m3, e3, k3, kr3⟩ := prefix_load hW dst rADDR v2 p2.1
    (x := position shape.bpCode false K)
    (by show v2.regs 108 < v2.extent
        rw [v2_108, e2, e1]; have := Nat.min_le_right K shape.size; omega)
    (by show v2.memory (v2.regs 108) = _
        rw [v2_108, m2, m1, hPOS _ (Nat.min_le_right _ _), position_min_size])
    (by omega)
  have pre := p1.append (p2.append p3)
  refine ⟨v3, pre, by rw [r3, put_same], ?_, by rw [m3, m2, m1], by rw [e3, e2, e1],
    by rw [k3, k2, k1], by rw [kr3, kr2, kr1]⟩
  intro r h h108 h188 hdst
  rw [r3, put_ne _ _ hdst, v2get r h108, v1get r h h188]

/-- **Truncating subtraction.** -/
theorem monusActs_prefix {W : Nat} (hW : 32 ≤ W) (dst a b : Operand)
    (ha : (a : Nat) ≠ 26 ∧ (a : Nat) ≠ 27 ∧ (a : Nat) ≠ 28)
    (hb : (b : Nat) ≠ 26 ∧ (b : Nat) ≠ 27 ∧ (b : Nat) ≠ 28 ∧ (b : Nat) ≠ 189)
    (u : State) (hrun : u.status = .running) (hone : u.regs 2 = 1) (A Bv : Nat)
    (hA : u.regs a = A) (hB : u.regs b = Bv) (hAW : A < 2 ^ W) (hBW : Bv < 2 ^ W) :
    ∃ u', ActsPrefix W (monusActs dst a b) u u' 6 ∧ u'.regs dst = A - Bv ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 189 → r ≠ dst → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs := by
  have h2W := two_le_two_pow hW
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pureList hW (maxActs rA6 a b) u hrun (by
    simp only [maxActs]
    pre1_reg_simp [hA, hB, hone, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2.1]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega))
  have v1_189 : v1.regs 189 = max A Bv := by
    rw [r1]; simp only [maxActs]; pre1_reg_simp [hA, hB, hone, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2.1]
    split <;> omega
  have v1get : ∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 189 → v1.regs r = u.regs r := by
    intro r h h189
    have e1' : r ≠ 26 := by omega
    have e2' : r ≠ 27 := by omega
    have e3' : r ≠ 28 := by omega
    rw [r1]; simp only [maxActs]; pre1_reg_simp [e1', e2', e3', h189]
  have v1b : v1.regs b = Bv := by
    rw [v1get b (by omega) hb.2.2.2, hB]
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_pure hW (.arithmetic .sub dst rA6 b) v1 p1.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_189, v1_189, v1b, reduceCtorEq,
      false_implies, false_or, and_true, forall_const]
    refine ⟨?_, ?_⟩
    · have := Nat.max_le.2 ⟨Nat.le_of_lt hAW, Nat.le_of_lt hBW⟩; omega
    · exact Nat.le_max_right _ _)
  refine ⟨v2, p1.append p2, ?_, ?_, by rw [m2, m1], by rw [e2, e1], by rw [k2, k1], by rw [kr2, kr1]⟩
  · rw [r2]; simp only [pureReg, Arithmetic.eval, operand_val_189, v1_189, v1b, put_same]
    rw [Nat.max_def]; split <;> omega
  · intro r h h189 hdst
    rw [r2]; simp only [pureReg]; rw [put_ne _ _ hdst, v1get r h h189]

/-! ## Long flags -/

/-- The value the builder stores for a flag. -/
def flagNat (b : Bool) : Nat := if b then 1 else 0

theorem flagNat_le (b : Bool) : flagNat b ≤ 1 := by unfold flagNat; split <;> omega

/-- **One long flag.** -/
theorem longFlag_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1)
    (P0 L0 C0 k cnt : Nat) (h1 : u.regs 1 = shape.size) (h159 : u.regs 159 = P0)
    (h161 : u.regs 161 = L0) (h162 : u.regs 162 = C0) (h173 : u.regs 173 = k)
    (h40 : u.regs 40 = superStride shape.bpCode.length)
    (h44 : u.regs 44 = superLongSpan shape.bpCode.length) (h177 : u.regs 177 = cnt)
    (hk : k < superSlotCount shape.bpCode false) (hcnt : cnt ≤ k)
    (hPOS : ∀ q, q ≤ shape.size → u.memory (P0 + q) = some (position shape.bpCode false q))
    (hPL : P0 + shape.size < L0) (hLC : L0 + superSlotCount shape.bpCode false ≤ C0)
    (hCe : C0 + superSlotCount shape.bpCode false < u.extent) (hextW : u.extent < 2 ^ W)
    (hlenW1 : shape.bpCode.length + 1 < 2 ^ W)
    (hkW : (k + 1) * superStride shape.bpCode.length < 2 ^ W) :
    ∃ u' j, SafeEval W longFlagBlock u u' j ∧ j ≤ 35 ∧ u'.status = .running ∧
      u'.memory = put (put u.memory (L0 + k) (some (flagNat (superIsLong shape.bpCode false k))))
        (C0 + k) (some cnt) ∧
      u'.regs 177 = cnt + flagNat (superIsLong shape.bpCode false k) ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 169 → ¬ (177 ≤ r ∧ r ≤ 184) → r ≠ 188 →
        r ≠ 189 → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs := by
  have h2W := two_le_two_pow hW
  have hlenW : shape.bpCode.length < 2 ^ W := by omega
  have hSpos := superStride_pos shape.bpCode.length
  have hocc := bp_occurrenceCount shape
  have hkS : k * superStride shape.bpCode.length < shape.size := by
    have := selectCeilDiv_slot_mul_lt (n := occurrenceCount shape.bpCode false) hSpos hk
    rw [hocc] at this; exact this
  have hsupn : superSlotCount shape.bpCode false ≤ shape.size := by
    rw [RMQ.SuccinctFinal.PackedCellProbe.superSlotCount_eq_packed]
    exact RMQ.SuccinctFinal.PackedCellProbe.packedSuperSlots_le _
  generalize hS : superStride shape.bpCode.length = S at *
  generalize hLSP : superLongSpan shape.bpCode.length = LSP at *
  generalize hsup : superSlotCount shape.bpCode false = sup at *
  have hkS1 : (k + 1) * S = k * S + S := Nat.succ_mul k S
  -- base and end occurrences
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pureList hW
    [.arithmetic .mul rBOCC rK rSS, .arithmetic .add rA1 rBOCC rSS] u hrun (by
      pre1_reg_simp [h173, h40]; omega)
  have v1_179 : v1.regs 179 = k * S := by rw [r1]; pre1_reg_simp [h173, h40]
  have v1_169 : v1.regs 169 = k * S + S := by rw [r1]; pre1_reg_simp [h173, h40]
  have v1get : ∀ r, r ≠ 169 → r ≠ 179 → v1.regs r = u.regs r := fun r a b => by
    rw [r1]; pre1_reg_simp [a, b]
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_pureList hW (minActs rEOCC rA1 rN) v1 p1.1 (by
    simp only [minActs]
    pre1_reg_simp [v1_169, v1get 1 (by decide) (by decide), h1, v1get 2 (by decide) (by decide), hone]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega))
  have v2_180 : v2.regs 180 = min (k * S + S) shape.size := by
    rw [r2]; simp only [minActs]
    pre1_reg_simp [v1_169, v1get 1 (by decide) (by decide), h1, v1get 2 (by decide) (by decide), hone]
    split <;> omega
  have v2get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 180 → v2.regs r = v1.regs r := fun r h a => by
    have e1' : r ≠ 26 := by omega
    have e2' : r ≠ 27 := by omega
    have e3' : r ≠ 28 := by omega
    rw [r2]; simp only [minActs]; pre1_reg_simp [e1', e2', e3', a]
  have hend1 : 1 ≤ min (k * S + S) shape.size := by
    simp only [Nat.min_def]; split <;> omega
  obtain ⟨v3, p3, r3, m3, e3, k3, kr3⟩ := prefix_pure hW (.arithmetic .sub rA1 rEOCC rONE) v2 p2.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_180, operand_val_2, v2_180,
      v2get 2 (by decide) (by decide), v1get 2 (by decide) (by decide), hone, reduceCtorEq,
      false_implies, false_or, and_true, forall_const]
    refine ⟨?_, hend1⟩
    have := Nat.min_le_right (k * S + S) shape.size; omega)
  have v3_169 : v3.regs 169 = min (k * S + S) shape.size - 1 := by
    rw [r3]; simp only [pureReg, Arithmetic.eval, operand_val_169, operand_val_180, operand_val_2,
      v2_180, v2get 2 (by decide) (by decide), v1get 2 (by decide) (by decide), hone, put_same]
  have v3get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 169 → r ≠ 179 → r ≠ 180 → v3.regs r = u.regs r :=
    fun r h a b c => by
      rw [r3]; simp only [pureReg, operand_val_169]; rw [put_ne _ _ a, v2get r h c, v1get r a b]
  have v3_179 : v3.regs 179 = k * S := by
    rw [r3]; simp only [pureReg, operand_val_169]; rw [put_ne _ _ (by decide),
      v2get 179 (by decide) (by decide), v1_179]
  have v3_180 : v3.regs 180 = min (k * S + S) shape.size := by
    rw [r3]; simp only [pureReg, operand_val_169]; rw [put_ne _ _ (by decide), v2_180]
  -- the two positions
  have hPOS3 : ∀ q, q ≤ shape.size → v3.memory (P0 + q) = some (position shape.bpCode false q) :=
    fun q hq => by rw [m3, m2, m1]; exact hPOS q hq
  obtain ⟨v4, p4, r4, fr4, m4, e4, k4, kr4⟩ := posActs_prefix hW shape rEPOS rA1 ⟨by decide, by decide⟩
    v3 p3.1 (by rw [v3get 2 (by decide) (by decide) (by decide) (by decide), hone]) P0
    (min (k * S + S) shape.size - 1)
    (by rw [v3get 1 (by decide) (by decide) (by decide) (by decide), h1])
    (by rw [v3get 159 (by decide) (by decide) (by decide) (by decide), h159]) v3_169
    (by omega) hPOS3 (by rw [e3, e2, e1]; omega) (by omega) hlenW
  have hPOS4 : ∀ q, q ≤ shape.size → v4.memory (P0 + q) = some (position shape.bpCode false q) :=
    fun q hq => by rw [m4]; exact hPOS3 q hq
  obtain ⟨v5, p5, r5, fr5, m5, e5, k5, kr5⟩ := posActs_prefix hW shape rBPOS rBOCC ⟨by decide, by decide⟩
    v4 p4.1 (by rw [fr4 2 (by decide) (by decide) (by decide) (by decide),
      v3get 2 (by decide) (by decide) (by decide) (by decide), hone]) P0 (k * S)
    (by rw [fr4 1 (by decide) (by decide) (by decide) (by decide),
      v3get 1 (by decide) (by decide) (by decide) (by decide), h1])
    (by rw [fr4 159 (by decide) (by decide) (by decide) (by decide),
      v3get 159 (by decide) (by decide) (by decide) (by decide), h159])
    (by show v4.regs 179 = k * S; rw [fr4 179 (by decide) (by decide) (by decide) (by decide), v3_179])
    (by omega) hPOS4 (by rw [e4, e3, e2, e1]; omega) (by omega) hlenW
  have hposE := position_le_length shape.bpCode false (min (k * S + S) shape.size - 1)
  have hposB := position_le_length shape.bpCode false (k * S)
  have v5_182 : v5.regs 182 = position shape.bpCode false (min (k * S + S) shape.size - 1) := by
    rw [fr5 182 (by decide) (by decide) (by decide) (by decide)]; exact r4
  have v5get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 169 → r ≠ 179 → r ≠ 180 → r ≠ 181 →
      r ≠ 182 → r ≠ 188 → v5.regs r = u.regs r := fun r h a b c d e f g => by
    rw [fr5 r h a g e, fr4 r h a g f, v3get r h b c d]
  -- span and flag
  obtain ⟨v6, p6, r6, m6, e6, k6, kr6⟩ := prefix_pure hW (.arithmetic .add rEPOS rEPOS rONE) v5 p5.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_182, operand_val_2, v5_182,
      v5get 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hone, reduceCtorEq, false_implies, false_or, and_true]; omega)
  have v6_182 : v6.regs 182 = position shape.bpCode false (min (k * S + S) shape.size - 1) + 1 := by
    rw [r6]; simp only [pureReg, Arithmetic.eval, operand_val_182, operand_val_2, v5_182,
      v5get 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hone, put_same]
  have v6get : ∀ r, r ≠ 182 → v6.regs r = v5.regs r := fun r h => by
    rw [r6]; simp only [pureReg, operand_val_182]; rw [put_ne _ _ h]
  obtain ⟨v7, p7, r7, fr7, m7, e7, k7, kr7⟩ := monusActs_prefix hW rSPANA rEPOS rBPOS
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide⟩ v6 p6.1
    (by rw [v6get 2 (by decide), v5get 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hone])
    _ _ v6_182 ((v6get 181 (by decide)).trans r5) (by omega) (by omega)
  have v7_183 : v7.regs 183 = superSpan shape.bpCode false k := by
    rw [show v7.regs 183 = _ from r7]; unfold superSpan superEndOccurrence superBaseOccurrence
    rw [hocc, hS]
    try rfl
  have v7get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 183 → r ≠ 189 → v7.regs r = v6.regs r := fun r h a b => by
    rw [fr7 r h b a]
  obtain ⟨v8, p8, r8, m8, e8, k8, kr8⟩ := prefix_pure hW (.comparison .lt rFLAG rLSPAN rSPANA) v7 p7.1 trivial
  have v8_184 : v8.regs 184 = flagNat (superIsLong shape.bpCode false k) := by
    rw [r8]; simp only [pureReg, Comparison.eval, operand_val_184, operand_val_44, operand_val_183,
      v7_183, v7get 44 (by decide) (by decide) (by decide), v6get 44 (by decide),
      v5get 44 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h44, put_same]
    unfold flagNat superIsLong; rw [hLSP]; simp
  have v8get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 169 → ¬ (179 ≤ r ∧ r ≤ 184) → r ≠ 188 →
      r ≠ 189 → v8.regs r = u.regs r := fun r h a b c d e => by
    rw [r8]; simp only [pureReg, operand_val_184]
    rw [put_ne _ _ (by omega), v7get r h (by omega) e, v6get r (by omega),
      v5get r h a b (by omega) (by omega) (by omega) (by omega) d]
  -- stores
  have hflagW : flagNat (superIsLong shape.bpCode false k) < 2 ^ W := by
    have := flagNat_le (superIsLong shape.bpCode false k); omega
  obtain ⟨v9, p9, r9, m9, e9, k9, kr9⟩ := prefix_pure hW (.arithmetic .add rADDR rLFB rK) v8 p8.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_161, operand_val_173,
      v8get 161 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      v8get 173 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h161, h173,
      reduceCtorEq, false_implies, false_or, and_true]; omega)
  have v9_108 : v9.regs 108 = L0 + k := by
    rw [r9]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_161, operand_val_173,
      v8get 161 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      v8get 173 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h161, h173,
      put_same]
  have v9get : ∀ r, r ≠ 108 → v9.regs r = v8.regs r := fun r h => by
    rw [r9]; simp only [pureReg, operand_val_108]; rw [put_ne _ _ h]
  obtain ⟨v10, p10, r10, m10, e10, k10, kr10⟩ := prefix_store hW rADDR rFLAG v9 p9.1
    (by show v9.regs 108 < v9.extent; rw [v9_108, e9, e8, e7, e6, e5, e4, e3, e2, e1]; omega)
    (by show v9.regs 184 < 2 ^ W; rw [v9get 184 (by decide), v8_184]; exact hflagW)
  obtain ⟨v11, p11, r11, m11, e11, k11, kr11⟩ := prefix_pure hW (.arithmetic .add rADDR rLFCB rK) v10 p10.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_162, operand_val_173, r10,
      v9get 162 (by decide), v9get 173 (by decide),
      v8get 162 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      v8get 173 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h162, h173,
      reduceCtorEq, false_implies, false_or, and_true]; omega)
  have v11_108 : v11.regs 108 = C0 + k := by
    rw [r11]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_162, operand_val_173, r10,
      v9get 162 (by decide), v9get 173 (by decide),
      v8get 162 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      v8get 173 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h162, h173,
      put_same]
  have v11get : ∀ r, r ≠ 108 → v11.regs r = v8.regs r := fun r h => by
    rw [r11]; simp only [pureReg, operand_val_108]; rw [put_ne _ _ h, r10, v9get r h]
  have hcntW : cnt < 2 ^ W := by omega
  have v11_177 : v11.regs 177 = cnt := by
    rw [v11get 177 (by decide), v8get 177 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h177]
  obtain ⟨v12, p12, r12, m12, e12, k12, kr12⟩ := prefix_store hW rADDR rLCNT v11 p11.1
    (by show v11.regs 108 < v11.extent; rw [v11_108, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]; omega)
    (by show v11.regs 177 < 2 ^ W; rw [v11_177]; exact hcntW)
  obtain ⟨v13, p13, r13, m13, e13, k13, kr13⟩ := prefix_pure hW (.arithmetic .add rLCNT rLCNT rFLAG) v12 p12.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_177, operand_val_184, r12, v11_177,
      v11get 184 (by decide), v8_184, reduceCtorEq, false_implies, false_or, and_true]
    have := flagNat_le (superIsLong shape.bpCode false k); omega)
  have pre := p1.append (p2.append (p3.append (p4.append (p5.append (p6.append (p7.append
    (p8.append (p9.append (p10.append (p11.append (p12.append p13)))))))))))
  refine ⟨v13, _, pre.close, by simp [minActs], p13.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m13, m12]
    show put v11.memory (v11.regs 108) (some (v11.regs 177)) = _
    rw [v11_108, v11_177, m11, m10]
    show put (put v9.memory (v9.regs 108) (some (v9.regs 184))) (C0 + k) (some cnt) = _
    rw [v9_108, v9get 184 (by decide), v8_184, m9, m8, m7, m6, m5, m4, m3, m2, m1]
  · rw [r13]; simp only [pureReg, Arithmetic.eval, operand_val_177, operand_val_184, r12, v11_177,
      v11get 184 (by decide), v8_184, put_same]
  · intro r h h108 h169 hr h188 h189
    rw [r13]; simp only [pureReg, operand_val_177]
    rw [put_ne _ _ (by omega), r12, v11get r h108, v8get r h h108 h169 (by omega) h188 h189]
  · rw [e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]
  · rw [k13, k12, k11, k10, k9, k8, k7, k6, k5, k4, k3, k2, k1]
  · rw [kr13, kr12, kr11, kr10, kr9, kr8, kr7, kr6, kr5, kr4, kr3, kr2, kr1]

theorem rank_flags_succ {f : Nat → Bool} {N k : Nat} (hk : k < N) :
    RMQ.Succinct.rankPrefix true ((List.range N).map f) (k + 1) =
      RMQ.Succinct.rankPrefix true ((List.range N).map f) k + flagNat (f k) := by
  have hget : ((List.range N).map f)[k]? = some (f k) := by
    simp [List.getElem?_map, List.getElem?_range hk]
  rw [rankPrefix_succ_eq_of_get? (target := true) hget]
  unfold flagNat; cases f k <;> simp

/-- **All long flags.** -/
theorem longFlags_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hone : s.regs 2 = 1)
    (P0 L0 C0 : Nat) (h1 : s.regs 1 = shape.size) (h159 : s.regs 159 = P0)
    (h161 : s.regs 161 = L0) (h162 : s.regs 162 = C0)
    (h40 : s.regs 40 = superStride shape.bpCode.length)
    (h44 : s.regs 44 = superLongSpan shape.bpCode.length)
    (h45 : s.regs 45 = superSlotCount shape.bpCode false)
    (hPOS : ∀ q, q ≤ shape.size → s.memory (P0 + q) = some (position shape.bpCode false q))
    (hPL : P0 + shape.size < L0) (hLC : L0 + superSlotCount shape.bpCode false ≤ C0)
    (hCe : C0 + superSlotCount shape.bpCode false < s.extent) (hextW : s.extent < 2 ^ W)
    (hlenW1 : shape.bpCode.length + 1 < 2 ^ W)
    (hSW : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length < 2 ^ W) :
    ∃ s' j, SafeEval W longFlagsBlock s s' j ∧
      j ≤ superSlotCount shape.bpCode false * 39 + 6 ∧ s'.status = .running ∧
      (∀ k, k < superSlotCount shape.bpCode false →
        s'.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k))) ∧
      (∀ k, k ≤ superSlotCount shape.bpCode false →
        s'.memory (C0 + k) = some (RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false) k)) ∧
      (∀ a, (a < L0 ∨ C0 + superSlotCount shape.bpCode false + 1 ≤ a) → s'.memory a = s.memory a) ∧
      s'.regs 177 = RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false)
        (superSlotCount shape.bpCode false) ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 169 → ¬ (173 ≤ r ∧ r ≤ 184) → r ≠ 188 →
        r ≠ 189 → s'.regs r = s.regs r) ∧
      s'.extent = s.extent ∧ s'.keys = s.keys := by
  have hsupn : superSlotCount shape.bpCode false ≤ shape.size := by
    rw [RMQ.SuccinctFinal.PackedCellProbe.superSlotCount_eq_packed]
    exact RMQ.SuccinctFinal.PackedCellProbe.packedSuperSlots_le _
  generalize hsup : superSlotCount shape.bpCode false = sup at *
  have hlb : longSuperFlagBits shape.bpCode false = (List.range sup).map (superIsLong shape.bpCode false) := by
    rw [← hsup]; rfl
  -- init
  obtain ⟨t, jt, et, hjt, htr, htR, htm, hte, htk, _⟩ :=
    RegSpec.pure hW [.constant rLCNT 0] s hrun (by pre1_reg_simp [])
  have t177 : t.regs 177 = 0 := by rw [htR]; pre1_reg_simp []
  have tfr : ∀ r, r ≠ 177 → t.regs r = s.regs r := fun r a => by rw [htR]; pre1_reg_simp [a]
  let Inv : Nat → State → Prop := fun k u =>
    (∀ a, (a < L0 ∨ C0 + sup + 1 ≤ a) → u.memory a = s.memory a) ∧
      (∀ k', k' < k → u.memory (L0 + k') = some (flagNat (superIsLong shape.bpCode false k'))) ∧
      (∀ k', k' < k → u.memory (C0 + k') =
        some (RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false) k')) ∧
      u.regs 177 = RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false) k ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 169 → ¬ (173 ≤ r ∧ r ≤ 184) → r ≠ 188 →
        r ≠ 189 → u.regs r = s.regs r) ∧
      u.extent = s.extent ∧ u.keys = s.keys
  obtain ⟨s1, k1, e1, hk1, hr1, ⟨I1, I2, I3, I4, I5, I6, I7⟩, _, _⟩ :=
    forSlots_spec hW rK rKGO rSUP longFlagBlock 35 (by decide) (by decide) (by decide) (by decide)
      (by decide) Inv t htr (by rw [tfr 2 (by decide), hone])
      (by show t.regs 45 < 2 ^ W; rw [tfr 45 (by decide), h45]; omega)
      (by
        intro u _ hur hum hue huk _
        have ufr : ∀ r, r ≠ 173 → r ≠ 174 → u.regs r = t.regs r := hur
        refine ⟨fun a _ => by rw [hum, htm], fun k' hk => absurd hk (Nat.not_lt_zero _),
          fun k' hk => absurd hk (Nat.not_lt_zero _), ?_, ?_, by rw [hue, hte], by rw [huk, htk]⟩
        · rw [ufr 177 (by decide) (by decide), t177, RMQ.Succinct.rankPrefix_zero]
        · intro r h a b c d e
          rw [ufr r (by omega) (by omega), tfr r (by omega)])
      (by
        intro k u hk ⟨U1, U2, U3, U4, U5, U6, U7⟩ hur hui hucnt huone
        have hk' : k < sup := by
          have : k < t.regs 45 := hk
          rwa [tfr 45 (by decide), h45] at this
        have hrank := RMQ.Succinct.rankPrefix_le_limit true (longSuperFlagBits shape.bpCode false) k
        have hkS : (k + 1) * superStride shape.bpCode.length ≤ (sup + 1) * superStride shape.bpCode.length :=
          Nat.mul_le_mul_right _ (by omega)
        obtain ⟨u', j, ev, hj, hr', M, R177, F, Ex, Ks, _⟩ :=
          longFlag_spec hW shape u hur huone P0 L0 C0 k _
            (by rw [U5 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1])
            (by rw [U5 159 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h159])
            (by rw [U5 161 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h161])
            (by rw [U5 162 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h162])
            hui
            (by rw [U5 40 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h40])
            (by rw [U5 44 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h44])
            U4 (by rw [hsup]; exact hk') hrank
            (fun q hq => by rw [U1 _ (Or.inl (by omega))]; exact hPOS q hq)
            hPL (by rw [hsup]; exact hLC) (by rw [hsup, U6]; exact hCe) (by rw [U6]; exact hextW)
            hlenW1 (by omega)
        refine ⟨u', j, ev, hj, hr', ?_, ?_, ?_, ?_⟩
        · show u'.regs 173 = k
          rw [F 173 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hui
        · show u'.regs 45 = t.regs 45
          rw [F 45 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hucnt
        · rw [F 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), huone]
        · intro v _ hvr hvm hve hvk _
          have vfr : ∀ r, r ≠ 173 → r ≠ 174 → v.regs r = u'.regs r := hvr
          refine ⟨?_, ?_, ?_, ?_, ?_, by rw [hve, Ex, U6], by rw [hvk, Ks, U7]⟩
          · intro a ha
            rw [hvm, M, put_ne _ _ (by omega), put_ne _ _ (by omega)]; exact U1 a ha
          · intro k' hk''
            rw [hvm, M]
            by_cases hkk : k' = k
            · rw [hkk, put_ne _ _ (by omega), put_same]
            · rw [put_ne _ _ (by omega), put_ne _ _ (by omega)]; exact U2 k' (by omega)
          · intro k' hk''
            rw [hvm, M]
            by_cases hkk : k' = k
            · rw [hkk, put_same]
            · rw [put_ne _ _ (by omega), put_ne _ _ (by omega)]; exact U3 k' (by omega)
          · rw [vfr 177 (by decide) (by decide), R177, hlb, rank_flags_succ hk']
          · intro r h a b c d e
            rw [vfr r (by omega) (by omega), F r h a b (by omega) d e]
            exact U5 r h a b c d e)
  rw [show ((rSUP : Operand) : Nat) = 45 from rfl, tfr 45 (by decide), h45] at hk1 I2 I3 I4
  have e2 := addStore_pair hW rLFCB rSUP rLCNT (by decide) s1 hr1
    (by show s1.regs 162 + s1.regs 45 < s1.extent
        rw [I5 162 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h162,
          I5 45 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h45, I6]; omega)
    (by rw [I6]; exact hextW)
    (by show s1.regs 177 < 2 ^ W
        rw [I4]; have := RMQ.Succinct.rankPrefix_le_limit true (longSuperFlagBits shape.bpCode false) sup
        omega)
  have fm : (addStoreState s1 rLFCB rSUP rLCNT).memory =
      put s1.memory (C0 + sup) (some (RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false) sup)) := by
    show put s1.memory (s1.regs 162 + s1.regs 45) (some (s1.regs 177)) = _
    rw [I5 162 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h162,
      I5 45 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h45, I4]
  refine ⟨addStoreState s1 rLFCB rSUP rLCNT, jt + (k1 + 2), EvalG.seq et (EvalG.seq e1 e2), ?_, hr1,
    ?_, ?_, ?_, ?_, ?_, I6, I7⟩
  · simp at hjt; omega
  · intro k hk; rw [fm, put_ne _ _ (by omega)]; exact I2 k hk
  · intro k hk
    rw [fm]
    by_cases hks : k = sup
    · rw [hks, put_same]
    · rw [put_ne _ _ (by omega)]; exact I3 k (by omega)
  · intro a ha; rw [fm, put_ne _ _ (by omega)]; exact I1 a ha
  · show put s1.regs 108 (s1.regs 162 + s1.regs 45) 177 = _
    rw [put_ne _ _ (by decide)]; exact I4
  · intro r h a b c d e
    show put s1.regs 108 _ r = _
    rw [put_ne _ _ a]; exact I5 r h a b c d e

/-! ## Sparse-exception flags -/

theorem localOffset_le (S ls g : Nat) (hls : 1 ≤ ls) (hS : 1 ≤ S) :
    (g % selectLocalSlotsPerSuper S ls) * ls + 1 ≤ S := by
  have hLPS : 0 < selectLocalSlotsPerSuper S ls := Nat.div_pos (by omega) (by omega)
  have h1 : g % selectLocalSlotsPerSuper S ls + 1 ≤ selectLocalSlotsPerSuper S ls :=
    Nat.mod_lt _ hLPS
  have h2 := Nat.mul_le_mul_right ls h1
  rw [Nat.succ_mul] at h2
  have h3 : selectLocalSlotsPerSuper S ls * ls ≤ S + ls - 1 := Nat.div_mul_le_self _ _
  omega

/-- **One sparse-exception flag.** -/
theorem sparseFlag_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1)
    (P0 L0 F0 G0 g cnt : Nat) (h1 : u.regs 1 = shape.size) (h159 : u.regs 159 = P0)
    (h161 : u.regs 161 = L0) (h163 : u.regs 163 = F0) (h164 : u.regs 164 = G0)
    (h175 : u.regs 175 = g) (h178 : u.regs 178 = cnt)
    (h39 : u.regs 39 = wordBits shape.bpCode.length)
    (h40 : u.regs 40 = superStride shape.bpCode.length)
    (h42 : u.regs 42 = localStride shape.bpCode.length)
    (h43 : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (hg : g < localSlotCount shape.bpCode false) (hcnt : cnt ≤ g)
    (hPOS : ∀ q, q ≤ shape.size → u.memory (P0 + q) = some (position shape.bpCode false q))
    (hLF : ∀ k, k < superSlotCount shape.bpCode false →
      u.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (hPL : P0 + shape.size < L0) (hLF0 : L0 + superSlotCount shape.bpCode false ≤ F0)
    (hFG : F0 + localSlotCount shape.bpCode false ≤ G0)
    (hGe : G0 + localSlotCount shape.bpCode false < u.extent) (hextW : u.extent < 2 ^ W)
    (hlenW1 : shape.bpCode.length + 1 < 2 ^ W)
    (hcapS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W) :
    ∃ u' j, SafeEval W sparseFlagBlock u u' j ∧ j ≤ 60 ∧ u'.status = .running ∧
      u'.memory = put (put u.memory (F0 + g) (some (flagNat (localIsSparseException shape.bpCode false g))))
        (G0 + g) (some cnt) ∧
      u'.regs 178 = cnt + flagNat (localIsSparseException shape.bpCode false g) ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → ¬ (169 ≤ r ∧ r ≤ 172) → ¬ (178 ≤ r ∧ r ≤ 189) →
        u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs := by
  have h2W := two_le_two_pow hW
  have hlenW : shape.bpCode.length < 2 ^ W := by omega
  have hocc := bp_occurrenceCount shape
  have hSpos := superStride_pos shape.bpCode.length
  have hlspos := localStride_pos shape.bpCode.length
  have hLPSpos := localSlotsPerSuper_pos shape.bpCode.length
  have hsupn : superSlotCount shape.bpCode false ≤ shape.size := by
    rw [RMQ.SuccinctFinal.PackedCellProbe.superSlotCount_eq_packed]
    exact RMQ.SuccinctFinal.PackedCellProbe.packedSuperSlots_le _
  have hoff := localOffset_le (superStride shape.bpCode.length) (localStride shape.bpCode.length) g
    hlspos hSpos
  have hLPSdef : localSlotsPerSuper shape.bpCode.length =
      selectLocalSlotsPerSuper (superStride shape.bpCode.length) (localStride shape.bpCode.length) := rfl
  have hsS : g / localSlotsPerSuper shape.bpCode.length < superSlotCount shape.bpCode false := by
    have : g < superSlotCount shape.bpCode false * localSlotsPerSuper shape.bpCode.length := hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact this)
  have hbase := localBaseOccurrence_mod shape.bpCode.length g
  have hws : wordBits shape.bpCode.length ≤ shape.bpCode.length + 1 := by
    show Nat.log2 _ + 1 ≤ _; have := Nat.log2_le_self shape.bpCode.length; omega
  rw [← hLPSdef] at hoff
  generalize hS : superStride shape.bpCode.length = S at *
  generalize hls : localStride shape.bpCode.length = ls at *
  generalize hLPS : localSlotsPerSuper shape.bpCode.length = LPS at *
  generalize hsup : superSlotCount shape.bpCode false = sup at *
  generalize hloc : localSlotCount shape.bpCode false = loc at *
  generalize hws' : wordBits shape.bpCode.length = ws at *
  obtain ⟨sS, hsSd⟩ : ∃ x, g / LPS = x := ⟨_, rfl⟩
  obtain ⟨gm, hgm⟩ : ∃ x, g % LPS = x := ⟨_, rfl⟩
  have hgmle : gm ≤ g := hgm ▸ Nat.mod_le g LPS
  have hsSle : sS ≤ g := hsSd ▸ Nat.div_le_self g LPS
  rw [hsSd] at hsS
  rw [hgm] at hoff
  rw [hsSd, hgm] at hbase
  have hsSS : (sS + 1) * S ≤ sup * S := Nat.mul_le_mul_right S hsS
  have hsS1 : (sS + 1) * S = sS * S + S := Nat.succ_mul sS S
  have hsupS : (sup + 1) * S = sup * S + S := Nat.succ_mul sup S
  -- decode
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pureList hW
    [.arithmetic .div rSSL rG rLPS, .arithmetic .mod rA1 rG rLPS, .arithmetic .mul rA1 rA1 rLSTR,
      .arithmetic .mul rBOCC rSSL rSS, .arithmetic .add rA2 rBOCC rSS] u hrun (by
      pre1_reg_simp [h175, h43, h42, h40, hsSd, hgm]
      repeat' apply And.intro
      all_goals first | omega | (apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _); omega) |
        (apply Nat.lt_of_le_of_lt (Nat.mod_le _ _); omega))
  have v1_185 : v1.regs 185 = sS := by rw [r1]; pre1_reg_simp [h175, h43, h42, h40, hsSd, hgm]
  have v1_169 : v1.regs 169 = gm * ls := by rw [r1]; pre1_reg_simp [h175, h43, h42, h40, hsSd, hgm]
  have v1_179 : v1.regs 179 = sS * S := by rw [r1]; pre1_reg_simp [h175, h43, h42, h40, hsSd, hgm]
  have v1_170 : v1.regs 170 = sS * S + S := by rw [r1]; pre1_reg_simp [h175, h43, h42, h40, hsSd, hgm]
  have v1get : ∀ r, r ≠ 169 → r ≠ 170 → r ≠ 179 → r ≠ 185 → v1.regs r = u.regs r := fun r a b c d => by
    rw [r1]; pre1_reg_simp [a, b, c, d]
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_pureList hW (minActs rSEND rA2 rN) v1 p1.1 (by
    simp only [minActs]
    pre1_reg_simp [v1_170, v1get 1 (by decide) (by decide) (by decide) (by decide), h1,
      v1get 2 (by decide) (by decide) (by decide) (by decide), hone]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega))
  have v2_186 : v2.regs 186 = min (sS * S + S) shape.size := by
    rw [r2]; simp only [minActs]
    pre1_reg_simp [v1_170, v1get 1 (by decide) (by decide) (by decide) (by decide), h1,
      v1get 2 (by decide) (by decide) (by decide) (by decide), hone]
    split <;> omega
  have v2get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 186 → v2.regs r = v1.regs r := fun r h a => by
    have e1' : r ≠ 26 := by omega
    have e2' : r ≠ 27 := by omega
    have e3' : r ≠ 28 := by omega
    rw [r2]; simp only [minActs]; pre1_reg_simp [e1', e2', e3', a]
  obtain ⟨v3, p3, r3, m3, e3, k3, kr3⟩ := prefix_pureList hW
    [.arithmetic .add rBOCC rBOCC rA1, .arithmetic .add rA2 rBOCC rLSTR] v2 p2.1 (by
      pre1_reg_simp [v2get 179 (by decide) (by decide), v2get 169 (by decide) (by decide),
        v2get 42 (by decide) (by decide), v1_179, v1_169,
        v1get 42 (by decide) (by decide) (by decide) (by decide), h42]
      omega)
  have v3_179 : v3.regs 179 = sS * S + gm * ls := by
    rw [r3]; pre1_reg_simp [v2get 179 (by decide) (by decide), v2get 169 (by decide) (by decide),
      v2get 42 (by decide) (by decide), v1_179, v1_169,
      v1get 42 (by decide) (by decide) (by decide) (by decide), h42]
  have v3_170 : v3.regs 170 = sS * S + gm * ls + ls := by
    rw [r3]; pre1_reg_simp [v2get 179 (by decide) (by decide), v2get 169 (by decide) (by decide),
      v2get 42 (by decide) (by decide), v1_179, v1_169,
      v1get 42 (by decide) (by decide) (by decide) (by decide), h42]
  have v3get : ∀ r, r ≠ 170 → r ≠ 179 → v3.regs r = v2.regs r := fun r a b => by
    rw [r3]; pre1_reg_simp [a, b]
  obtain ⟨v4, p4, r4, m4, e4, k4, kr4⟩ := prefix_pureList hW (minActs rEOCC rA2 rSEND) v3 p3.1 (by
    simp only [minActs]
    pre1_reg_simp [v3_170, v3get 186 (by decide) (by decide), v2_186,
      v3get 2 (by decide) (by decide), v2get 2 (by decide) (by decide),
      v1get 2 (by decide) (by decide) (by decide) (by decide), hone]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega) | (simp only [Nat.min_def]; split <;> omega))
  have v4_180 : v4.regs 180 = min (sS * S + gm * ls + ls) (min (sS * S + S) shape.size) := by
    rw [r4]; simp only [minActs]
    pre1_reg_simp [v3_170, v3get 186 (by decide) (by decide), v2_186,
      v3get 2 (by decide) (by decide), v2get 2 (by decide) (by decide),
      v1get 2 (by decide) (by decide) (by decide) (by decide), hone]
    split <;> omega
  have v4get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 180 → v4.regs r = v3.regs r := fun r h a => by
    have e1' : r ≠ 26 := by omega
    have e2' : r ≠ 27 := by omega
    have e3' : r ≠ 28 := by omega
    rw [r4]; simp only [minActs]; pre1_reg_simp [e1', e2', e3', a]
  have ugetA : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 169 → r ≠ 170 → r ≠ 179 → r ≠ 180 → r ≠ 185 →
      r ≠ 186 → v4.regs r = u.regs r := fun r h a b c d e f => by
    rw [v4get r h d, v3get r b c, v2get r h f, v1get r a b c e]
  have hEOCCW : min (sS * S + gm * ls + ls) (min (sS * S + S) shape.size) < 2 ^ W := by
    have := Nat.min_le_right (sS * S + gm * ls + ls) (min (sS * S + S) shape.size)
    have := Nat.min_le_right (sS * S + S) shape.size
    omega
  -- end occurrence minus one, positions, span
  obtain ⟨v5, p5, r5, fr5, m5, e5, k5, kr5⟩ := monusActs_prefix hW rA1 rEOCC rONE
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide⟩ v4 p4.1
    (by rw [ugetA 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hone])
    _ 1 v4_180 (by show v4.regs 2 = 1; rw [ugetA 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hone])
    hEOCCW (by omega)
  have hPOS5 : ∀ q, q ≤ shape.size → v5.memory (P0 + q) = some (position shape.bpCode false q) :=
    fun q hq => by rw [m5, m4, m3, m2, m1]; exact hPOS q hq
  have hext5 : v5.extent = u.extent := by rw [e5, e4, e3, e2, e1]
  have v5get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 169 → r ≠ 170 → r ≠ 179 → r ≠ 180 → r ≠ 185 →
      r ≠ 186 → r ≠ 189 → v5.regs r = u.regs r := fun r h a b c d e f g' => by
    rw [fr5 r h g' a, ugetA r h a b c d e f]
  obtain ⟨v6, p6, r6, fr6, m6, e6, k6, kr6⟩ := posActs_prefix hW shape rEPOS rA1 ⟨by decide, by decide⟩
    v5 p5.1 (by rw [v5get 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hone]) P0 _
    (by rw [v5get 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h1])
    (by rw [v5get 159 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h159]) r5 (by omega) hPOS5 (by rw [hext5]; omega) (by omega) hlenW
  have v5_179 : v5.regs 179 = sS * S + gm * ls := by
    rw [fr5 179 (by decide) (by decide) (by decide), v4get 179 (by decide) (by decide), v3_179]
  obtain ⟨v7, p7, r7, fr7, m7, e7, k7, kr7⟩ := posActs_prefix hW shape rBPOS rBOCC ⟨by decide, by decide⟩
    v6 p6.1 (by rw [fr6 2 (by decide) (by decide) (by decide) (by decide),
      v5get 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hone]) P0 (sS * S + gm * ls)
    (by rw [fr6 1 (by decide) (by decide) (by decide) (by decide),
      v5get 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h1])
    (by rw [fr6 159 (by decide) (by decide) (by decide) (by decide),
      v5get 159 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h159])
    (by show v6.regs 179 = _; rw [fr6 179 (by decide) (by decide) (by decide) (by decide), v5_179])
    (by omega) (fun q hq => by rw [m6]; exact hPOS5 q hq) (by rw [e6, hext5]; omega)
    (by omega) hlenW
  have hposE := position_le_length shape.bpCode false
    (min (sS * S + gm * ls + ls) (min (sS * S + S) shape.size) - 1)
  have hposB := position_le_length shape.bpCode false (sS * S + gm * ls)
  have v7_182 : v7.regs 182 = position shape.bpCode false
      (min (sS * S + gm * ls + ls) (min (sS * S + S) shape.size) - 1) := by
    rw [fr7 182 (by decide) (by decide) (by decide) (by decide)]; exact r6
  have v7get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 169 → r ≠ 170 → r ≠ 179 → r ≠ 180 →
      r ≠ 181 → r ≠ 182 → r ≠ 185 → r ≠ 186 → r ≠ 188 → r ≠ 189 → v7.regs r = u.regs r :=
    fun r h a b c d e f g' i j k l => by
      rw [fr7 r h a k f, fr6 r h a k g', v5get r h b c d e i j l]
  obtain ⟨v8, p8, r8, m8, e8, k8, kr8⟩ := prefix_pure hW (.arithmetic .add rEPOS rEPOS rONE) v7 p7.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_182, operand_val_2, v7_182,
      v7get 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide),
      hone, reduceCtorEq, false_implies, false_or, and_true]; omega)
  have v8_182 : v8.regs 182 = position shape.bpCode false
      (min (sS * S + gm * ls + ls) (min (sS * S + S) shape.size) - 1) + 1 := by
    rw [r8]; simp only [pureReg, Arithmetic.eval, operand_val_182, operand_val_2, v7_182,
      v7get 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), hone, put_same]
  have v8get : ∀ r, r ≠ 182 → v8.regs r = v7.regs r := fun r h => by
    rw [r8]; simp only [pureReg, operand_val_182]; rw [put_ne _ _ h]
  obtain ⟨v9, p9, r9, fr9, m9, e9, k9, kr9⟩ := monusActs_prefix hW rSPANA rEPOS rBPOS
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide⟩ v8 p8.1
    (by rw [v8get 2 (by decide), v7get 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hone])
    _ _ v8_182 ((v8get 181 (by decide)).trans r7) (by omega) (by omega)
  have hspan : v9.regs 183 = shortSuperLocalSpan shape.bpCode false g := by
    rw [show v9.regs 183 = _ from r9]
    unfold shortSuperLocalSpan shortSuperLocalEndOccurrence superEndOccurrence superBaseOccurrence
      localSuperSlot
    rw [hbase, hocc, hS, hls, hLPS, hsSd]
    try rfl
  have v9get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 183 → r ≠ 189 → v9.regs r = v8.regs r :=
    fun r h a b => fr9 r h b a
  -- flag
  have c9 : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → ¬ (169 ≤ r ∧ r ≤ 170) → ¬ (179 ≤ r ∧ r ≤ 189) →
      v9.regs r = u.regs r := fun r h a b c => by
    rw [v9get r h (by omega) (by omega), v8get r (by omega)]
    exact v7get r h a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have v9_185 : v9.regs 185 = sS := by
    rw [v9get 185 (by decide) (by decide) (by decide), v8get 185 (by decide),
      fr7 185 (by decide) (by decide) (by decide) (by decide), fr6 185 (by decide) (by decide) (by decide) (by decide),
      fr5 185 (by decide) (by decide) (by decide), v4get 185 (by decide) (by decide),
      v3get 185 (by decide) (by decide), v2get 185 (by decide) (by decide), v1_185]
  have hext9 : v9.extent = u.extent := by rw [e9, e8, e7, e6, hext5]
  have hmem9 : v9.memory = u.memory := by rw [m9, m8, m7, m6, m5, m4, m3, m2, m1]
  obtain ⟨v10, p10, r10, m10, e10, k10, kr10⟩ := prefix_pureList hW
    [.comparison .lt rA3 rWS rSPANA, .arithmetic .add rADDR rLFB rSSL] v9 p9.1 (by
      pre1_reg_simp [hspan, v9_185, c9 161 (by decide) (by decide) (by decide) (by decide), h161]
      omega)
  have v10_171 : v10.regs 171 = flagNat (decide (ws < shortSuperLocalSpan shape.bpCode false g)) := by
    rw [r10]; pre1_reg_simp [hspan, c9 39 (by decide) (by decide) (by decide) (by decide), h39]
    unfold flagNat; simp
  have v10_108 : v10.regs 108 = L0 + sS := by
    rw [r10]; pre1_reg_simp [v9_185, c9 161 (by decide) (by decide) (by decide) (by decide), h161]
  have c10 : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → ¬ (169 ≤ r ∧ r ≤ 171) → ¬ (179 ≤ r ∧ r ≤ 189) →
      v10.regs r = u.regs r := fun r h a b c => by
    have b1 : r ≠ 171 := by omega
    rw [r10]; pre1_reg_simp [a, b1]; exact c9 r h a (by omega) c
  have hlf := flagNat_le (superIsLong shape.bpCode false sS)
  obtain ⟨v11, p11, r11, m11, e11, k11, kr11⟩ := prefix_load hW rA4 rADDR v10 p10.1
    (x := flagNat (superIsLong shape.bpCode false sS))
    (by show v10.regs 108 < v10.extent
        rw [v10_108, e10, hext9]; omega)
    (by show v10.memory (v10.regs 108) = _
        rw [v10_108, m10, hmem9]; exact hLF sS hsS)
    (by omega)
  have v11_172 : v11.regs 172 = flagNat (superIsLong shape.bpCode false sS) := by
    rw [r11, operand_val_172, put_same]
  have v11get : ∀ r, r ≠ 172 → v11.regs r = v10.regs r := fun r h => by
    rw [r11, operand_val_172, put_ne _ _ h]
  have hc1 := flagNat_le (decide (ws < shortSuperLocalSpan shape.bpCode false g))
  have hprod : flagNat (decide (ws < shortSuperLocalSpan shape.bpCode false g)) *
      (1 - flagNat (superIsLong shape.bpCode false sS)) ≤ 1 := by
    unfold flagNat; split <;> split <;> simp
  have hflag : flagNat (localIsSparseException shape.bpCode false g) =
      flagNat (decide (ws < shortSuperLocalSpan shape.bpCode false g)) *
        (1 - flagNat (superIsLong shape.bpCode false sS)) := by
    unfold localIsSparseException localSuperSlot
    rw [hLPS, hsSd, hws']
    unfold flagNat
    cases superIsLong shape.bpCode false sS <;>
      cases decide (ws < shortSuperLocalSpan shape.bpCode false g) <;> rfl
  obtain ⟨v12, p12, r12, m12, e12, k12, kr12⟩ := prefix_pureList hW
    [.arithmetic .sub rA4 rONE rA4, .arithmetic .mul rFLAG rA3 rA4, .arithmetic .add rADDR rSFB rG]
    v11 p11.1 (by
      pre1_reg_simp [v11_172, v11get 171 (by decide), v10_171, v11get 2 (by decide),
        c10 2 (by decide) (by decide) (by decide) (by decide), hone,
        v11get 163 (by decide), c10 163 (by decide) (by decide) (by decide) (by decide), h163,
        v11get 175 (by decide), c10 175 (by decide) (by decide) (by decide) (by decide), h175]
      repeat' apply And.intro
      all_goals omega)
  have v12_184 : v12.regs 184 = flagNat (localIsSparseException shape.bpCode false g) := by
    rw [r12, hflag]
    pre1_reg_simp [v11_172, v11get 171 (by decide), v10_171, v11get 2 (by decide),
      c10 2 (by decide) (by decide) (by decide) (by decide), hone]
  have v12_108 : v12.regs 108 = F0 + g := by
    rw [r12]
    pre1_reg_simp [v11get 163 (by decide), c10 163 (by decide) (by decide) (by decide) (by decide), h163,
      v11get 175 (by decide), c10 175 (by decide) (by decide) (by decide) (by decide), h175]
  have c12 : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → ¬ (169 ≤ r ∧ r ≤ 172) → ¬ (179 ≤ r ∧ r ≤ 189) →
      v12.regs r = u.regs r := fun r h a b c => by
    have b1 : r ≠ 172 := by omega
    have b2 : r ≠ 184 := by omega
    rw [r12]; pre1_reg_simp [a, b1, b2]
    rw [v11get r b1]; exact c10 r h a (by omega) c
  have hfl1 := flagNat_le (localIsSparseException shape.bpCode false g)
  obtain ⟨v13, p13, r13, m13, e13, k13, kr13⟩ := prefix_store hW rADDR rFLAG v12 p12.1
    (by show v12.regs 108 < v12.extent
        rw [v12_108, e12, e11, e10, hext9]; omega)
    (by show v12.regs 184 < 2 ^ W
        rw [v12_184]; omega)
  obtain ⟨v14, p14, r14, m14, e14, k14, kr14⟩ := prefix_pure hW (.arithmetic .add rADDR rSFCB rG) v13
    p13.1 (by
      pre1_reg_simp [r13, c12 164 (by decide) (by decide) (by decide) (by decide), h164,
        c12 175 (by decide) (by decide) (by decide) (by decide), h175]
      omega)
  have v14_108 : v14.regs 108 = G0 + g := by
    rw [r14]; pre1_reg_simp [r13, c12 164 (by decide) (by decide) (by decide) (by decide), h164,
      c12 175 (by decide) (by decide) (by decide) (by decide), h175]
  have v14get : ∀ r, r ≠ 108 → v14.regs r = v12.regs r := fun r h => by
    rw [r14]; pre1_reg_simp [h, r13]
  obtain ⟨v15, p15, r15, m15, e15, k15, kr15⟩ := prefix_store hW rADDR rSCNT v14 p14.1
    (by show v14.regs 108 < v14.extent
        rw [v14_108, e14, e13, e12, e11, e10, hext9]; omega)
    (by show v14.regs 178 < 2 ^ W
        rw [v14get 178 (by decide), c12 178 (by decide) (by decide) (by decide) (by decide), h178]; omega)
  obtain ⟨v16, p16, r16, m16, e16, k16, kr16⟩ := prefix_pure hW (.arithmetic .add rSCNT rSCNT rFLAG) v15
    p15.1 (by
      pre1_reg_simp [r15, v14get 178 (by decide), c12 178 (by decide) (by decide) (by decide) (by decide),
        h178, v14get 184 (by decide), v12_184]
      omega)
  have pall := ((((((((((((((p1.append p2).append p3).append p4).append p5).append p6).append
    p7).append p8).append p9).append p10).append p11).append p12).append p13).append p14).append
    p15).append p16
  refine ⟨v16, _, pall.close, ?_, p16.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil, minActs]; omega
  · rw [m16, m15, m14, m13]
    simp only [operand_val_108, operand_val_178, operand_val_184]
    rw [v14_108, v14get 178 (by decide), c12 178 (by decide) (by decide) (by decide) (by decide), h178,
      v12_108, v12_184, m12, m11, m10, hmem9]
  · rw [r16]
    pre1_reg_simp [r15, v14get 178 (by decide), c12 178 (by decide) (by decide) (by decide) (by decide),
      h178, v14get 184 (by decide), v12_184]
  · intro r h a b c
    have c1 : r ≠ 178 := by omega
    rw [r16]; pre1_reg_simp [c1]
    rw [r15, v14get r a]; exact c12 r h a b (by omega)
  · rw [e16, e15, e14, e13, e12, e11, e10, hext9]
  · rw [k16, k15, k14, k13, k12, k11, k10, k9, k8, k7, k6, k5, k4, k3, k2, k1]
  · rw [kr16, kr15, kr14, kr13, kr12, kr11, kr10, kr9, kr8, kr7, kr6, kr5, kr4, kr3, kr2, kr1]

/-- **All sparse-exception flags.** -/
theorem sparseFlags_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hone : s.regs 2 = 1)
    (P0 L0 F0 G0 : Nat) (h1 : s.regs 1 = shape.size) (h159 : s.regs 159 = P0)
    (h161 : s.regs 161 = L0) (h163 : s.regs 163 = F0) (h164 : s.regs 164 = G0)
    (h39 : s.regs 39 = wordBits shape.bpCode.length)
    (h40 : s.regs 40 = superStride shape.bpCode.length)
    (h42 : s.regs 42 = localStride shape.bpCode.length)
    (h43 : s.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (h46 : s.regs 46 = localSlotCount shape.bpCode false)
    (hPOS : ∀ q, q ≤ shape.size → s.memory (P0 + q) = some (position shape.bpCode false q))
    (hLF : ∀ k, k < superSlotCount shape.bpCode false →
      s.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (hPL : P0 + shape.size < L0) (hLF0 : L0 + superSlotCount shape.bpCode false ≤ F0)
    (hFG : F0 + localSlotCount shape.bpCode false ≤ G0)
    (hGe : G0 + localSlotCount shape.bpCode false < s.extent) (hextW : s.extent < 2 ^ W)
    (hlenW1 : shape.bpCode.length + 1 < 2 ^ W)
    (hcapS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W) :
    ∃ s' j, SafeEval W sparseFlagsBlock s s' j ∧
      j ≤ localSlotCount shape.bpCode false * 64 + 6 ∧ s'.status = .running ∧
      (∀ g, g < localSlotCount shape.bpCode false →
        s'.memory (F0 + g) = some (flagNat (localIsSparseException shape.bpCode false g))) ∧
      (∀ g, g ≤ localSlotCount shape.bpCode false →
        s'.memory (G0 + g) = some (RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false) g)) ∧
      (∀ a, (a < F0 ∨ G0 + localSlotCount shape.bpCode false + 1 ≤ a) → s'.memory a = s.memory a) ∧
      s'.regs 178 = RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false)
        (localSlotCount shape.bpCode false) ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → ¬ (169 ≤ r ∧ r ≤ 172) → r ≠ 175 → r ≠ 176 →
        ¬ (178 ≤ r ∧ r ≤ 189) → s'.regs r = s.regs r) ∧
      s'.extent = s.extent ∧ s'.keys = s.keys := by
  have hlocW : localSlotCount shape.bpCode false < 2 ^ W := by omega
  generalize hloc : localSlotCount shape.bpCode false = loc at *
  have hsb : sparseExceptionFlagBits shape.bpCode false =
      (List.range loc).map (localIsSparseException shape.bpCode false) := by
    rw [← hloc]; rfl
  -- init
  obtain ⟨t, jt, et, hjt, htr, htR, htm, hte, htk, _⟩ :=
    RegSpec.pure hW [.constant rSCNT 0] s hrun (by pre1_reg_simp [])
  have t178 : t.regs 178 = 0 := by rw [htR]; pre1_reg_simp []
  have tfr : ∀ r, r ≠ 178 → t.regs r = s.regs r := fun r a => by rw [htR]; pre1_reg_simp [a]
  let Inv : Nat → State → Prop := fun k u =>
    (∀ a, (a < F0 ∨ G0 + loc + 1 ≤ a) → u.memory a = s.memory a) ∧
      (∀ k', k' < k → u.memory (F0 + k') = some (flagNat (localIsSparseException shape.bpCode false k'))) ∧
      (∀ k', k' < k → u.memory (G0 + k') =
        some (RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false) k')) ∧
      u.regs 178 = RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false) k ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → ¬ (169 ≤ r ∧ r ≤ 172) → r ≠ 175 → r ≠ 176 →
        ¬ (178 ≤ r ∧ r ≤ 189) → u.regs r = s.regs r) ∧
      u.extent = s.extent ∧ u.keys = s.keys
  obtain ⟨s1, k1, e1, hk1, hr1, ⟨I1, I2, I3, I4, I5, I6, I7⟩, _, _⟩ :=
    forSlots_spec hW rG rGGO rLOC sparseFlagBlock 60 (by decide) (by decide) (by decide) (by decide)
      (by decide) Inv t htr (by rw [tfr 2 (by decide), hone])
      (by show t.regs 46 < 2 ^ W; rw [tfr 46 (by decide), h46]; exact hlocW)
      (by
        intro u _ hur hum hue huk _
        have ufr : ∀ r, r ≠ 175 → r ≠ 176 → u.regs r = t.regs r := hur
        refine ⟨fun a _ => by rw [hum, htm], fun k' hk => absurd hk (Nat.not_lt_zero _),
          fun k' hk => absurd hk (Nat.not_lt_zero _), ?_, ?_, by rw [hue, hte], by rw [huk, htk]⟩
        · rw [ufr 178 (by decide) (by decide), t178, RMQ.Succinct.rankPrefix_zero]
        · intro r h a b c d e
          rw [ufr r c d, tfr r (by omega)])
      (by
        intro k u hk ⟨U1, U2, U3, U4, U5, U6, U7⟩ hur hui hucnt huone
        have hk' : k < loc := by
          have : k < t.regs 46 := hk
          rwa [tfr 46 (by decide), h46] at this
        have hrank := RMQ.Succinct.rankPrefix_le_limit true (sparseExceptionFlagBits shape.bpCode false) k
        obtain ⟨u', j, ev, hj, hr', M, R178, F, Ex, Ks, _⟩ :=
          sparseFlag_spec hW shape u hur huone P0 L0 F0 G0 k _
            (by rw [U5 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1])
            (by rw [U5 159 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h159])
            (by rw [U5 161 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h161])
            (by rw [U5 163 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h163])
            (by rw [U5 164 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h164])
            hui U4
            (by rw [U5 39 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h39])
            (by rw [U5 40 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h40])
            (by rw [U5 42 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h42])
            (by rw [U5 43 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h43])
            (by rw [hloc]; exact hk') hrank
            (fun q hq => by rw [U1 _ (Or.inl (by omega))]; exact hPOS q hq)
            (fun q hq => by rw [U1 _ (Or.inl (by omega))]; exact hLF q hq)
            hPL hLF0 (by rw [hloc]; exact hFG) (by rw [hloc, U6]; exact hGe) (by rw [U6]; exact hextW)
            hlenW1 hcapS
        refine ⟨u', j, ev, hj, hr', ?_, ?_, ?_, ?_⟩
        · show u'.regs 175 = k
          rw [F 175 (by decide) (by decide) (by decide) (by decide)]; exact hui
        · show u'.regs 46 = t.regs 46
          rw [F 46 (by decide) (by decide) (by decide) (by decide)]; exact hucnt
        · rw [F 2 (by decide) (by decide) (by decide) (by decide), huone]
        · intro v _ hvr hvm hve hvk _
          have vfr : ∀ r, r ≠ 175 → r ≠ 176 → v.regs r = u'.regs r := hvr
          refine ⟨?_, ?_, ?_, ?_, ?_, by rw [hve, Ex, U6], by rw [hvk, Ks, U7]⟩
          · intro a ha
            rw [hvm, M, put_ne _ _ (by omega), put_ne _ _ (by omega)]; exact U1 a ha
          · intro k' hk''
            rw [hvm, M]
            by_cases hkk : k' = k
            · rw [hkk, put_ne _ _ (by omega), put_same]
            · rw [put_ne _ _ (by omega), put_ne _ _ (by omega)]; exact U2 k' (by omega)
          · intro k' hk''
            rw [hvm, M]
            by_cases hkk : k' = k
            · rw [hkk, put_same]
            · rw [put_ne _ _ (by omega), put_ne _ _ (by omega)]; exact U3 k' (by omega)
          · rw [vfr 178 (by decide) (by decide), R178, hsb, rank_flags_succ hk']
          · intro r h a b c d e
            rw [vfr r c d, F r h a b e]
            exact U5 r h a b c d e)
  rw [show ((rLOC : Operand) : Nat) = 46 from rfl, tfr 46 (by decide), h46] at hk1 I2 I3 I4
  have e2 := addStore_pair hW rSFCB rLOC rSCNT (by decide) s1 hr1
    (by show s1.regs 164 + s1.regs 46 < s1.extent
        rw [I5 164 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h164,
          I5 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h46, I6]; omega)
    (by rw [I6]; exact hextW)
    (by show s1.regs 178 < 2 ^ W
        rw [I4]; have := RMQ.Succinct.rankPrefix_le_limit true (sparseExceptionFlagBits shape.bpCode false) loc
        omega)
  have fm : (addStoreState s1 rSFCB rLOC rSCNT).memory =
      put s1.memory (G0 + loc)
        (some (RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false) loc)) := by
    show put s1.memory (s1.regs 164 + s1.regs 46) (some (s1.regs 178)) = _
    rw [I5 164 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h164,
      I5 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h46, I4]
  refine ⟨addStoreState s1 rSFCB rLOC rSCNT, jt + (k1 + 2), EvalG.seq et (EvalG.seq e1 e2), ?_, hr1,
    ?_, ?_, ?_, ?_, ?_, I6, I7⟩
  · simp at hjt; omega
  · intro k hk; rw [fm, put_ne _ _ (by omega)]; exact I2 k hk
  · intro k hk
    rw [fm]
    by_cases hks : k = loc
    · rw [hks, put_same]
    · rw [put_ne _ _ (by omega)]; exact I3 k (by omega)
  · intro a ha; rw [fm, put_ne _ _ (by omega)]; exact I1 a ha
  · show put s1.regs 108 (s1.regs 164 + s1.regs 46) 178 = _
    rw [put_ne _ _ (by decide)]; exact I4
  · intro r h a b c d e
    show put s1.regs 108 _ r = _
    rw [put_ne _ _ a]; exact I5 r h a b c d e

end RMQ.SuccinctFinal.PackedConstruction.Proof
