import RMQ.Core.WordRAM.Construction.Proof.AccessFlags

/-! # PRE-1 builder proofs: access table entries (stage S5)

Outside the builder firewall. Each entry block of the eighteen access tables,
run at a table slot, leaves in `regs 16` exactly the reference entry: rank
samples read from the word-boundary counts, super and local entry fields
computed from the close positions and the two flag arrays (with the reference
liveness zeros), flag-rank samples, zeros, raw flags, and relative offsets.
Every entry is packaged as the obligation `emitTable_spec` asks for.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose RMQ.GenericSelect

/-! ## The entry obligation of `emitTable_spec` -/

/-- What `emitTable_spec` asks of one entry block run: `regs 16` holds the
entry value, fits the word, and only `writes` registers besides 16 change. -/
def EntryOK (W : Nat) (entry : Block) (writes : Nat → Prop) (u : State) (v J : Nat) : Prop :=
  ∃ u' j, SafeEval W entry u u' j ∧ j ≤ J ∧ u'.status = .running ∧
    u'.regs 16 = v ∧ u'.regs 16 < 2 ^ W ∧ u'.memory = u.memory ∧
    u'.extent = u.extent ∧ (∀ r, ¬ writes r → r ≠ 16 → u'.regs r = u.regs r) ∧
    u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys

/-- Registers the sixteen non-relative access entry blocks may write. -/
abbrev AccessWrites (r : Nat) : Prop :=
  r = 108 ∨ (26 ≤ r ∧ r ≤ 28) ∨ (169 ≤ r ∧ r ≤ 172) ∨ (179 ≤ r ∧ r ≤ 189)

/-- Registers the relative offset entry block may write. -/
abbrev RelWrites (r : Nat) : Prop :=
  r = 108 ∨ (26 ≤ r ∧ r ≤ 28) ∨ (169 ≤ r ∧ r ≤ 171) ∨ r = 188 ∨ r = 189

/-! ## Array reads -/

/-- **Raw array entry** `F[slot]`. -/
theorem flagEntry_spec {W : Nat} (hW : 32 ≤ W) (base : Operand) (u : State)
    (hrun : u.status = .running) (F0 N slot : Nat) (val : Nat → Nat)
    (h14 : u.regs 14 = slot) (hb : u.regs base = F0) (hslot : slot < N)
    (hF : ∀ k, k < N → u.memory (F0 + k) = some (val k))
    (hFe : F0 + N ≤ u.extent) (hFW : F0 + N < 2 ^ W) (hvW : ∀ k, k < N → val k < 2 ^ W) :
    EntryOK W (flagEntryBlock base) AccessWrites u (val slot) 2 := by
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pure hW (.arithmetic .add rADDR base rSLOT) u hrun (by
    simp only [pureOK, Arithmetic.eval, operand_val_14, h14, hb, reduceCtorEq, false_implies, false_or,
      and_true]
    omega)
  have v1_108 : v1.regs 108 = F0 + slot := by
    rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_14, operand_val_108, h14, hb, put_same]
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_load hW rENT rADDR v1 p1.1 (x := val slot)
    (by show v1.regs 108 < v1.extent; rw [v1_108, e1]; omega)
    (by show v1.memory (v1.regs 108) = _; rw [v1_108, m1]; exact hF slot hslot) (hvW slot hslot)
  refine ⟨v2, _, (p1.append p2).close, by simp, p2.1, ?_, ?_, by rw [m2, m1], by rw [e2, e1], ?_,
    by rw [kr2, kr1], by rw [k2, k1]⟩
  · rw [r2, operand_val_16, put_same]
  · rw [r2, operand_val_16, put_same]; exact hvW slot hslot
  · intro r hr h16
    rw [r2, operand_val_16, put_ne _ _ h16, r1]
    simp only [pureReg, operand_val_108]
    rw [put_ne _ _ (fun h => hr (Or.inl h))]

/-- **Sampled array entry** `C[slot * ws]` (final rank super samples and the
two flag-rank super tables). -/
theorem flagRankEntry_spec {W : Nat} (hW : 32 ≤ W) (base w : Operand) (hb169 : (base : Nat) ≠ 169)
    (u : State) (hrun : u.status = .running) (C0 N ws slot : Nat) (val : Nat → Nat)
    (h14 : u.regs 14 = slot) (hw : u.regs w = ws) (hb : u.regs base = C0) (hslot : slot * ws ≤ N)
    (hC : ∀ k, k ≤ N → u.memory (C0 + k) = some (val k))
    (hCe : C0 + N < u.extent) (hCW : C0 + N < 2 ^ W) (hvW : ∀ k, k ≤ N → val k < 2 ^ W) :
    EntryOK W (flagRankEntryBlock base w) AccessWrites u (val (slot * ws)) 3 := by
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pureList hW
    [.arithmetic .mul rA1 rSLOT w, .arithmetic .add rADDR base rA1] u hrun (by
      pre1_reg_simp [h14, hw, hb169, hb]
      omega)
  have v1_108 : v1.regs 108 = C0 + slot * ws := by rw [r1]; pre1_reg_simp [h14, hw, hb169, hb]
  have v1get : ∀ r, r ≠ 108 → r ≠ 169 → v1.regs r = u.regs r := fun r a b => by
    rw [r1]; pre1_reg_simp [a, b]
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_load hW rENT rADDR v1 p1.1 (x := val (slot * ws))
    (by show v1.regs 108 < v1.extent; rw [v1_108, e1]; omega)
    (by show v1.memory (v1.regs 108) = _; rw [v1_108, m1]; exact hC _ hslot) (hvW _ hslot)
  refine ⟨v2, _, (p1.append p2).close, by simp, p2.1, ?_, ?_, by rw [m2, m1], by rw [e2, e1], ?_,
    by rw [kr2, kr1], by rw [k2, k1]⟩
  · rw [r2, operand_val_16, put_same]
  · rw [r2, operand_val_16, put_same]; exact hvW _ hslot
  · intro r hr h16
    rw [r2, operand_val_16, put_ne _ _ h16]
    exact v1get r (fun h => hr (Or.inl h)) (fun h => hr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))

/-- **Block sample entry** `C[slot] - C[(slot / ws) * ws]` (final rank block samples). -/
theorem rankBlockEntry_spec {W : Nat} (hW : 32 ≤ W) (u : State) (hrun : u.status = .running)
    (R0 N ws slot : Nat) (val : Nat → Nat)
    (h14 : u.regs 14 = slot) (h39 : u.regs 39 = ws) (h160 : u.regs 160 = R0) (hws : 1 ≤ ws)
    (hslot : slot ≤ N)
    (hC : ∀ k, k ≤ N → u.memory (R0 + k) = some (val k))
    (hmono : ∀ i j, i ≤ j → j ≤ N → val i ≤ val j)
    (hCe : R0 + N < u.extent) (hCW : R0 + N < 2 ^ W) (hvW : ∀ k, k ≤ N → val k < 2 ^ W) :
    EntryOK W rankBlockEntryBlock AccessWrites u (val slot - val (slot / ws * ws)) 7 := by
  have hq : slot / ws * ws ≤ slot := Nat.div_mul_le_self slot ws
  have hvs := hvW slot hslot
  have hmq := hmono (slot / ws * ws) slot hq hslot
  obtain ⟨q, hqd⟩ : ∃ x, slot / ws = x := ⟨_, rfl⟩
  rw [hqd] at hq hmq
  have hqs : q ≤ slot := hqd ▸ Nat.div_le_self slot ws
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pure hW (.arithmetic .add rADDR rRWB rSLOT) u hrun (by
    simp only [pureOK, Arithmetic.eval, operand_val_14, operand_val_160, h14, h160, reduceCtorEq,
      false_implies, false_or, and_true]
    omega)
  have v1_108 : v1.regs 108 = R0 + slot := by
    rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_14, operand_val_108, operand_val_160, h14,
      h160, put_same]
  have v1get : ∀ r, r ≠ 108 → v1.regs r = u.regs r := fun r h => by
    rw [r1]; simp only [pureReg, operand_val_108]; rw [put_ne _ _ h]
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_load hW rENT rADDR v1 p1.1 (x := val slot)
    (by show v1.regs 108 < v1.extent; rw [v1_108, e1]; omega)
    (by show v1.memory (v1.regs 108) = _; rw [v1_108, m1]; exact hC slot hslot) hvs
  have v2get : ∀ r, r ≠ 16 → r ≠ 108 → v2.regs r = u.regs r := fun r a b => by
    rw [r2, operand_val_16, put_ne _ _ a, v1get r b]
  obtain ⟨v3, p3, r3, m3, e3, k3, kr3⟩ := prefix_pureList hW
    [.arithmetic .div rA1 rSLOT rWS, .arithmetic .mul rA1 rA1 rWS, .arithmetic .add rADDR rRWB rA1]
    v2 p2.1 (by
      pre1_reg_simp [v2get 14 (by decide) (by decide), h14, v2get 39 (by decide) (by decide), h39,
        v2get 160 (by decide) (by decide), h160, hqd]
      repeat' apply And.intro
      all_goals first | omega | (apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _); omega))
  have v3_108 : v3.regs 108 = R0 + q * ws := by
    rw [r3]; pre1_reg_simp [v2get 14 (by decide) (by decide), h14, v2get 39 (by decide) (by decide), h39,
      v2get 160 (by decide) (by decide), h160, hqd]
  have v3get : ∀ r, r ≠ 108 → r ≠ 169 → v3.regs r = v2.regs r := fun r a b => by
    rw [r3]; pre1_reg_simp [a, b]
  obtain ⟨v4, p4, r4, m4, e4, k4, kr4⟩ := prefix_load hW rA2 rADDR v3 p3.1 (x := val (q * ws))
    (by show v3.regs 108 < v3.extent; rw [v3_108, e3, e2, e1]; omega)
    (by show v3.memory (v3.regs 108) = _; rw [v3_108, m3, m2, m1]; exact hC _ (by omega))
    (hvW _ (by omega))
  have v4_16 : v4.regs 16 = val slot := by
    rw [r4, operand_val_170, put_ne _ _ (by decide), v3get 16 (by decide) (by decide), r2, operand_val_16,
      put_same]
  have v4_170 : v4.regs 170 = val (q * ws) := by rw [r4, operand_val_170, put_same]
  obtain ⟨v5, p5, r5, m5, e5, k5, kr5⟩ := prefix_pure hW (.arithmetic .sub rENT rENT rA2) v4 p4.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_16, operand_val_170, v4_16, v4_170, reduceCtorEq,
      false_implies, false_or, and_true, forall_const]
    exact ⟨by omega, hmq⟩)
  have pall := (((p1.append p2).append p3).append p4).append p5
  refine ⟨v5, _, pall.close, by simp, p5.1, ?_, ?_, by rw [m5, m4, m3, m2, m1],
    by rw [e5, e4, e3, e2, e1], ?_, by rw [kr5, kr4, kr3, kr2, kr1], by rw [k5, k4, k3, k2, k1]⟩
  · rw [r5]; simp only [pureReg, Arithmetic.eval, operand_val_16, operand_val_170, v4_16, v4_170, put_same,
      hqd]
  · rw [r5]; simp only [pureReg, Arithmetic.eval, operand_val_16, operand_val_170, v4_16, v4_170, put_same]
    omega
  · intro r hr h16
    have a1 : r ≠ 108 := fun h => hr (Or.inl h)
    have a2 : r ≠ 169 := fun h => hr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    have a3 : r ≠ 170 := fun h => hr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    rw [r5]; simp only [pureReg, operand_val_16]
    rw [put_ne _ _ h16, r4, operand_val_170, put_ne _ _ a3, v3get r a1 a2, v2get r h16 a1]

/-- **Constant entries**: zero and `slot * S`. -/
theorem zeroEntry_spec {W : Nat} (hW : 32 ≤ W) (u : State) (hrun : u.status = .running) :
    EntryOK W zeroEntryBlock AccessWrites u 0 1 := by
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pure hW (.constant rENT 0) u hrun trivial
  refine ⟨v1, _, p1.close, by simp, p1.1, ?_, ?_, m1, e1, ?_, kr1, k1⟩
  · rw [r1]; simp only [pureReg, operand_val_16, put_same]; rfl
  · rw [r1]; simp only [pureReg, operand_val_16, put_same]; exact Nat.two_pow_pos W
  · intro r _ h16; rw [r1]; simp only [pureReg, operand_val_16]; rw [put_ne _ _ h16]

theorem superOccEntry_spec {W : Nat} (hW : 32 ≤ W) (u : State) (hrun : u.status = .running)
    (S slot : Nat) (h14 : u.regs 14 = slot) (h40 : u.regs 40 = S) (hW' : slot * S < 2 ^ W) :
    EntryOK W superOccEntryBlock AccessWrites u (slot * S) 1 := by
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pure hW (.arithmetic .mul rENT rSLOT rSS) u hrun (by
    simp only [pureOK, Arithmetic.eval, operand_val_14, operand_val_40, h14, h40, reduceCtorEq,
      false_implies, false_or, and_true]
    exact hW')
  refine ⟨v1, _, p1.close, by simp, p1.1, ?_, ?_, m1, e1, ?_, kr1, k1⟩
  · rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_14, operand_val_40, operand_val_16, h14, h40,
      put_same]
  · rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_14, operand_val_40, operand_val_16, h14, h40,
      put_same]; exact hW'
  · intro r _ h16; rw [r1]; simp only [pureReg, operand_val_16]; rw [put_ne _ _ h16]

/-! ## Relative offsets -/

/-- **Relative offset entry**: `POS[base + slot] - basePos` below the end
occurrence, else `0`. -/
theorem relOffsetEntry_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1) (P0 base e bpos slot : Nat)
    (h1 : u.regs 1 = shape.size) (h159 : u.regs 159 = P0) (h14 : u.regs 14 = slot)
    (h179 : u.regs 179 = base) (h180 : u.regs 180 = e) (h181 : u.regs 181 = bpos)
    (hbW : base + slot < 2 ^ W) (hbpW : bpos < 2 ^ W)
    (hPOS : ∀ k, k ≤ shape.size → u.memory (P0 + k) = some (position shape.bpCode false k))
    (hPe : P0 + shape.size < u.extent) (hPW : P0 + shape.size < 2 ^ W)
    (hlenW : shape.bpCode.length < 2 ^ W) :
    EntryOK W relativeOffsetEntryBlock RelWrites u
      (if base + slot < e then position shape.bpCode false (base + slot) - bpos else 0) 20 := by
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pureList hW
    [.arithmetic .add rA1 rBOCC rSLOT, .comparison .lt rA2 rA1 rEOCC] u hrun (by
      pre1_reg_simp [h14, h179]
      exact hbW)
  have v1_169 : v1.regs 169 = base + slot := by rw [r1]; pre1_reg_simp [h14, h179]
  have v1_170 : v1.regs 170 = if base + slot < e then 1 else 0 := by
    rw [r1]; pre1_reg_simp [h14, h179, h180]
  have v1get : ∀ r, r ≠ 169 → r ≠ 170 → v1.regs r = u.regs r := fun r a b => by
    rw [r1]; pre1_reg_simp [a, b]
  obtain ⟨v2, p2, r2, fr2, m2, e2, k2, kr2⟩ := posActs_prefix hW shape rA3 rA1 ⟨by decide, by decide⟩
    v1 p1.1 (by rw [v1get 2 (by decide) (by decide), hone]) P0 (base + slot)
    (by rw [v1get 1 (by decide) (by decide), h1]) (by rw [v1get 159 (by decide) (by decide), h159])
    v1_169 hbW (fun q hq => by rw [m1]; exact hPOS q hq) (by rw [e1]; exact hPe) hPW hlenW
  have hpos := position_le_length shape.bpCode false (base + slot)
  obtain ⟨v3, p3, r3, fr3, m3, e3, k3, kr3⟩ := monusActs_prefix hW rA3 rA3 rBPOS
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide⟩ v2 p2.1
    (by rw [fr2 2 (by decide) (by decide) (by decide) (by decide), v1get 2 (by decide) (by decide), hone])
    _ bpos r2 (by show v2.regs 181 = bpos; rw [fr2 181 (by decide) (by decide) (by decide) (by decide),
      v1get 181 (by decide) (by decide), h181]) (by omega) hbpW
  have v3_170 : v3.regs 170 = if base + slot < e then 1 else 0 := by
    rw [fr3 170 (by decide) (by decide) (by decide), fr2 170 (by decide) (by decide) (by decide) (by decide),
      v1_170]
  have v3_171 : v3.regs 171 = position shape.bpCode false (base + slot) - bpos := r3
  obtain ⟨v4, p4, r4, m4, e4, k4, kr4⟩ := prefix_pure hW (.arithmetic .mul rENT rA2 rA3) v3 p3.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_170, operand_val_171, v3_170, v3_171, reduceCtorEq,
      false_implies, false_or, and_true]
    split <;> omega)
  have pall := ((p1.append p2).append p3).append p4
  have hval : v4.regs 16 =
      if base + slot < e then position shape.bpCode false (base + slot) - bpos else 0 := by
    rw [r4]; simp only [pureReg, Arithmetic.eval, operand_val_16, operand_val_170, operand_val_171, v3_170,
      put_same, v3_171]
    split <;> omega
  refine ⟨v4, _, pall.close, by simp, p4.1, hval, ?_, by rw [m4, m3, m2, m1],
    by rw [e4, e3, e2, e1], ?_, by rw [kr4, kr3, kr2, kr1], by rw [k4, k3, k2, k1]⟩
  · rw [hval]; split <;> omega
  · intro r hr h16
    have a1 : r ≠ 108 := fun h => hr (Or.inl h)
    have a2 : ¬ (26 ≤ r ∧ r ≤ 28) := fun h => hr (Or.inr (Or.inl h))
    have a3 : r ≠ 169 := fun h => hr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    have a4 : r ≠ 170 := fun h => hr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    have a5 : r ≠ 171 := fun h => hr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    have a6 : r ≠ 188 := fun h => hr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have a7 : r ≠ 189 := fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    rw [r4]; simp only [pureReg, operand_val_16]
    rw [put_ne _ _ h16, fr3 r a2 a7 a5, fr2 r a2 a1 a6 a5, v1get r a3 a4]

/-! ## Super fields -/

/-- The super base position `POS[slot * S]` into `regs 181`. -/
theorem superPos_prefix {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1) (P0 S slot : Nat)
    (h1 : u.regs 1 = shape.size) (h159 : u.regs 159 = P0) (h14 : u.regs 14 = slot)
    (h40 : u.regs 40 = S) (hSW : slot * S < 2 ^ W)
    (hPOS : ∀ k, k ≤ shape.size → u.memory (P0 + k) = some (position shape.bpCode false k))
    (hPe : P0 + shape.size < u.extent) (hPW : P0 + shape.size < 2 ^ W)
    (hlenW : shape.bpCode.length < 2 ^ W) :
    ∃ v, ActsPrefix W ([.arithmetic .mul rBOCC rSLOT rSS] ++ posActs rBPOS rBOCC) u v 8 ∧
      v.regs 181 = position shape.bpCode false (slot * S) ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 179 → r ≠ 181 → r ≠ 188 →
        v.regs r = u.regs r) ∧
      v.memory = u.memory ∧ v.extent = u.extent ∧ v.keys = u.keys ∧ v.keyRegs = u.keyRegs := by
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pure hW (.arithmetic .mul rBOCC rSLOT rSS) u hrun (by
    simp only [pureOK, Arithmetic.eval, operand_val_14, operand_val_40, h14, h40, reduceCtorEq,
      false_implies, false_or, and_true]
    exact hSW)
  have v1_179 : v1.regs 179 = slot * S := by
    rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_14, operand_val_40, operand_val_179, h14, h40,
      put_same]
  have v1get : ∀ r, r ≠ 179 → v1.regs r = u.regs r := fun r h => by
    rw [r1]; simp only [pureReg, operand_val_179]; rw [put_ne _ _ h]
  obtain ⟨v2, p2, r2, fr2, m2, e2, k2, kr2⟩ := posActs_prefix hW shape rBPOS rBOCC ⟨by decide, by decide⟩
    v1 p1.1 (by rw [v1get 2 (by decide), hone]) P0 (slot * S)
    (by rw [v1get 1 (by decide), h1]) (by rw [v1get 159 (by decide), h159]) v1_179 hSW
    (fun q hq => by rw [m1]; exact hPOS q hq) (by rw [e1]; exact hPe) hPW hlenW
  refine ⟨v2, p1.append p2, r2, ?_, by rw [m2, m1], by rw [e2, e1], by rw [k2, k1], by rw [kr2, kr1]⟩
  intro r h a b c d
  rw [fr2 r h a d c, v1get r b]

theorem superWordEntry_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1) (P0 S ws slot : Nat)
    (h1 : u.regs 1 = shape.size) (h159 : u.regs 159 = P0) (h14 : u.regs 14 = slot)
    (h40 : u.regs 40 = S) (h39 : u.regs 39 = ws) (hws : 1 ≤ ws) (hSW : slot * S < 2 ^ W)
    (hPOS : ∀ k, k ≤ shape.size → u.memory (P0 + k) = some (position shape.bpCode false k))
    (hPe : P0 + shape.size < u.extent) (hPW : P0 + shape.size < 2 ^ W)
    (hlenW : shape.bpCode.length < 2 ^ W) :
    EntryOK W superWordEntryBlock AccessWrites u (position shape.bpCode false (slot * S) / ws) 9 := by
  obtain ⟨v1, p1, r1, fr1, m1, e1, k1, kr1⟩ :=
    superPos_prefix hW shape u hrun hone P0 S slot h1 h159 h14 h40 hSW hPOS hPe hPW hlenW
  have hpos := position_le_length shape.bpCode false (slot * S)
  have v1_39 : v1.regs 39 = ws := by
    rw [fr1 39 (by decide) (by decide) (by decide) (by decide) (by decide), h39]
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_pure hW (.arithmetic .div rENT rBPOS rWS) v1 p1.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_181, operand_val_39, r1, v1_39, reduceCtorEq,
      false_implies, true_or, true_implies]
    repeat' apply And.intro
    all_goals first | trivial | omega | (intro h; simp at h) |
      (apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _); omega))
  refine ⟨v2, _, (p1.append p2).close, by simp, p2.1, ?_, ?_, by rw [m2, m1], by rw [e2, e1], ?_,
    by rw [kr2, kr1], by rw [k2, k1]⟩
  · rw [r2]; simp only [pureReg, Arithmetic.eval, operand_val_181, operand_val_39, operand_val_16, r1, v1_39,
      put_same]
  · rw [r2]; simp only [pureReg, Arithmetic.eval, operand_val_181, operand_val_39, operand_val_16, r1, v1_39,
      put_same]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  · intro r hr h16
    rw [r2]; simp only [pureReg, operand_val_16]
    rw [put_ne _ _ h16]
    exact fr1 r (fun h => hr (Or.inr (Or.inl h))) (fun h => hr (Or.inl h))
      (fun h => hr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
      (fun h => hr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
      (fun h => hr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))

theorem superOffsetEntry_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1) (P0 S ws slot : Nat)
    (h1 : u.regs 1 = shape.size) (h159 : u.regs 159 = P0) (h14 : u.regs 14 = slot)
    (h40 : u.regs 40 = S) (h39 : u.regs 39 = ws) (hws : 1 ≤ ws) (hSW : slot * S < 2 ^ W)
    (hPOS : ∀ k, k ≤ shape.size → u.memory (P0 + k) = some (position shape.bpCode false k))
    (hPe : P0 + shape.size < u.extent) (hPW : P0 + shape.size < 2 ^ W)
    (hlenW : shape.bpCode.length < 2 ^ W) :
    EntryOK W superOffsetEntryBlock AccessWrites u (position shape.bpCode false (slot * S) % ws) 9 := by
  obtain ⟨v1, p1, r1, fr1, m1, e1, k1, kr1⟩ :=
    superPos_prefix hW shape u hrun hone P0 S slot h1 h159 h14 h40 hSW hPOS hPe hPW hlenW
  have hpos := position_le_length shape.bpCode false (slot * S)
  have v1_39 : v1.regs 39 = ws := by
    rw [fr1 39 (by decide) (by decide) (by decide) (by decide) (by decide), h39]
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_pure hW (.arithmetic .mod rENT rBPOS rWS) v1 p1.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_181, operand_val_39, r1, v1_39, reduceCtorEq,
      false_implies, or_true, true_implies]
    repeat' apply And.intro
    all_goals first | trivial | omega | (intro h; simp at h) |
      (apply Nat.lt_of_le_of_lt (Nat.mod_le _ _); omega))
  refine ⟨v2, _, (p1.append p2).close, by simp, p2.1, ?_, ?_, by rw [m2, m1], by rw [e2, e1], ?_,
    by rw [kr2, kr1], by rw [k2, k1]⟩
  · rw [r2]; simp only [pureReg, Arithmetic.eval, operand_val_181, operand_val_39, operand_val_16, r1, v1_39,
      put_same]
  · rw [r2]; simp only [pureReg, Arithmetic.eval, operand_val_181, operand_val_39, operand_val_16, r1, v1_39,
      put_same]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  · intro r hr h16
    rw [r2]; simp only [pureReg, operand_val_16]
    rw [put_ne _ _ h16]
    exact fr1 r (fun h => hr (Or.inr (Or.inl h))) (fun h => hr (Or.inl h))
      (fun h => hr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
      (fun h => hr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
      (fun h => hr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))

/-! ## Local fields -/

/-- A local slot's base occurrence stays below its super's end. -/
theorem localBase_bound (shape : CartesianShape) {g : Nat}
    (hg : g < localSlotCount shape.bpCode false) :
    localBaseOccurrence shape.bpCode.length g + 1 ≤
      superSlotCount shape.bpCode false * superStride shape.bpCode.length ∧
    localSuperSlot shape.bpCode.length g < superSlotCount shape.bpCode false := by
  have hSpos := superStride_pos shape.bpCode.length
  have hlspos := localStride_pos shape.bpCode.length
  have hoff := localOffset_le (superStride shape.bpCode.length) (localStride shape.bpCode.length) g
    hlspos hSpos
  have hLPSdef : localSlotsPerSuper shape.bpCode.length =
      selectLocalSlotsPerSuper (superStride shape.bpCode.length) (localStride shape.bpCode.length) := rfl
  rw [← hLPSdef] at hoff
  have hsS : g / localSlotsPerSuper shape.bpCode.length < superSlotCount shape.bpCode false := by
    have : g < superSlotCount shape.bpCode false * localSlotsPerSuper shape.bpCode.length := hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact this)
  have hmul := Nat.mul_le_mul_right (superStride shape.bpCode.length) hsS
  rw [Nat.succ_mul] at hmul
  refine ⟨?_, hsS⟩
  rw [localBaseOccurrence_mod]
  omega

theorem localSlotsPerSuper_le_superStride (n : Nat) : localSlotsPerSuper n ≤ superStride n := by
  have hSpos := superStride_pos n
  have hlspos := localStride_pos n
  show (superStride n + localStride n - 1) / localStride n ≤ _
  apply Nat.div_le_of_le_mul
  obtain ⟨l', hl'⟩ : ∃ l', localStride n = l' + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hlspos).symm⟩
  rw [hl', Nat.succ_mul]
  have := Nat.mul_le_mul_left l' (show 1 ≤ superStride n from hSpos)
  rw [Nat.mul_one] at this
  omega

/-- Local slot indices fit below `superSlotCount * superStride`. -/
theorem localSlot_lt_cap (shape : CartesianShape) {g : Nat}
    (hg : g < localSlotCount shape.bpCode false) :
    g < superSlotCount shape.bpCode false * superStride shape.bpCode.length := by
  have h1 : g < superSlotCount shape.bpCode false * localSlotsPerSuper shape.bpCode.length := hg
  have h2 := Nat.mul_le_mul_left (superSlotCount shape.bpCode false)
    (localSlotsPerSuper_le_superStride shape.bpCode.length)
  omega

theorem flagNat_not_and (a b : Bool) :
    flagNat ((!a) && b) = (1 - flagNat a) * flagNat b := by
  cases a <;> cases b <;> rfl

/-- The shared local decoding: super slot, local offset, base occurrence, liveness. -/
theorem localDecode_prefix {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1) (L0 g : Nat)
    (h1 : u.regs 1 = shape.size) (h161 : u.regs 161 = L0) (h14 : u.regs 14 = g)
    (h40 : u.regs 40 = superStride shape.bpCode.length)
    (h42 : u.regs 42 = localStride shape.bpCode.length)
    (h43 : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (hg : g < localSlotCount shape.bpCode false)
    (hLF : ∀ k, k < superSlotCount shape.bpCode false →
      u.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (hLe : L0 + superSlotCount shape.bpCode false ≤ u.extent)
    (hLW : L0 + superSlotCount shape.bpCode false < 2 ^ W)
    (hcapS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W) :
    ∃ v, ActsPrefix W localDecodeActs u v 10 ∧
      v.regs 170 = localSuperSlot shape.bpCode.length g * superStride shape.bpCode.length ∧
      v.regs 169 = localBaseOccurrence shape.bpCode.length g -
        localSuperSlot shape.bpCode.length g * superStride shape.bpCode.length ∧
      v.regs 179 = localBaseOccurrence shape.bpCode.length g ∧
      v.regs 187 = flagNat (compactLocalEntryIsLive shape.bpCode false g) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (169 ≤ r ∧ r ≤ 172) → r ≠ 179 → r ≠ 185 → r ≠ 187 →
        v.regs r = u.regs r) ∧
      v.memory = u.memory ∧ v.extent = u.extent ∧ v.keys = u.keys ∧ v.keyRegs = u.keyRegs := by
  have hocc := bp_occurrenceCount shape
  have hSpos := superStride_pos shape.bpCode.length
  have hlspos := localStride_pos shape.bpCode.length
  have hLPSpos := localSlotsPerSuper_pos shape.bpCode.length
  have hoff := localOffset_le (superStride shape.bpCode.length) (localStride shape.bpCode.length) g
    hlspos hSpos
  have hLPSdef : localSlotsPerSuper shape.bpCode.length =
      selectLocalSlotsPerSuper (superStride shape.bpCode.length) (localStride shape.bpCode.length) := rfl
  obtain ⟨hB1, hsS⟩ := localBase_bound shape hg
  have hgcap := localSlot_lt_cap shape hg
  have hbase := localBaseOccurrence_mod shape.bpCode.length g
  have hlive : compactLocalEntryIsLive shape.bpCode false g =
      ((!superIsLong shape.bpCode false (localSuperSlot shape.bpCode.length g)) &&
        decide (localBaseOccurrence shape.bpCode.length g < shape.size)) := by
    unfold compactLocalEntryIsLive; rw [hocc]
  unfold localSuperSlot at hsS hlive ⊢
  rw [← hLPSdef] at hoff
  rw [hlive, flagNat_not_and]
  generalize hS : superStride shape.bpCode.length = S at *
  generalize hls : localStride shape.bpCode.length = ls at *
  generalize hLPS : localSlotsPerSuper shape.bpCode.length = LPS at *
  generalize hsup : superSlotCount shape.bpCode false = sup at *
  generalize hB : localBaseOccurrence shape.bpCode.length g = B at *
  obtain ⟨sS, hsSd⟩ : ∃ x, g / LPS = x := ⟨_, rfl⟩
  obtain ⟨gm, hgm⟩ : ∃ x, g % LPS = x := ⟨_, rfl⟩
  rw [hsSd] at hsS hbase ⊢
  rw [hgm] at hoff hbase
  have hsSS : (sS + 1) * S ≤ sup * S := Nat.mul_le_mul_right S hsS
  have hsS1 : (sS + 1) * S = sS * S + S := Nat.succ_mul sS S
  have hsupS : (sup + 1) * S = sup * S + S := Nat.succ_mul sup S
  have hgmle : gm ≤ g := hgm ▸ Nat.mod_le g LPS
  have hsSle : sS ≤ g := hsSd ▸ Nat.div_le_self g LPS
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pureList hW
    [.arithmetic .div rSSL rSLOT rLPS, .arithmetic .mod rA1 rSLOT rLPS, .arithmetic .mul rA1 rA1 rLSTR,
      .arithmetic .mul rA2 rSSL rSS, .arithmetic .add rBOCC rA2 rA1, .arithmetic .add rADDR rLFB rSSL]
    u hrun (by
      pre1_reg_simp [h14, h43, h42, h40, h161, hsSd, hgm]
      repeat' apply And.intro
      all_goals first | omega | (apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _); omega) |
        (apply Nat.lt_of_le_of_lt (Nat.mod_le _ _); omega))
  have v1_108 : v1.regs 108 = L0 + sS := by rw [r1]; pre1_reg_simp [h14, h43, h42, h40, h161, hsSd, hgm]
  have v1_169 : v1.regs 169 = gm * ls := by rw [r1]; pre1_reg_simp [h14, h43, h42, h40, h161, hsSd, hgm]
  have v1_170 : v1.regs 170 = sS * S := by rw [r1]; pre1_reg_simp [h14, h43, h42, h40, h161, hsSd, hgm]
  have v1_179 : v1.regs 179 = B := by
    rw [r1]; pre1_reg_simp [h14, h43, h42, h40, h161, hsSd, hgm]; omega
  have v1get : ∀ r, r ≠ 108 → r ≠ 169 → r ≠ 170 → r ≠ 179 → r ≠ 185 → v1.regs r = u.regs r :=
    fun r a b c d e => by rw [r1]; pre1_reg_simp [a, b, c, d, e]
  have hlf := flagNat_le (superIsLong shape.bpCode false sS)
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_load hW rA3 rADDR v1 p1.1
    (x := flagNat (superIsLong shape.bpCode false sS))
    (by show v1.regs 108 < v1.extent; rw [v1_108, e1]; omega)
    (by show v1.memory (v1.regs 108) = _; rw [v1_108, m1]; exact hLF sS hsS) (by omega)
  have v2_171 : v2.regs 171 = flagNat (superIsLong shape.bpCode false sS) := by
    rw [r2, operand_val_171, put_same]
  have v2get : ∀ r, r ≠ 171 → v2.regs r = v1.regs r := fun r h => by rw [r2, operand_val_171, put_ne _ _ h]
  obtain ⟨v3, p3, r3, m3, e3, k3, kr3⟩ := prefix_pureList hW
    [.arithmetic .sub rA3 rONE rA3, .comparison .lt rA4 rBOCC rN, .arithmetic .mul rLIVE rA3 rA4] v2 p2.1 (by
      pre1_reg_simp [v2_171, v2get 2 (by decide), v1get 2 (by decide) (by decide) (by decide) (by decide)
        (by decide), hone, v2get 179 (by decide), v1_179, v2get 1 (by decide),
        v1get 1 (by decide) (by decide) (by decide) (by decide) (by decide), h1]
      repeat' apply And.intro
      all_goals first | omega | (split <;> omega))
  have v3_187 : v3.regs 187 =
      (1 - flagNat (superIsLong shape.bpCode false sS)) * flagNat (decide (B < shape.size)) := by
    rw [r3]
    pre1_reg_simp [v2_171, v2get 2 (by decide), v1get 2 (by decide) (by decide) (by decide) (by decide)
      (by decide), hone, v2get 179 (by decide), v1_179, v2get 1 (by decide),
      v1get 1 (by decide) (by decide) (by decide) (by decide) (by decide), h1]
    unfold flagNat; simp
  have v3get : ∀ r, r ≠ 171 → r ≠ 172 → r ≠ 187 → v3.regs r = v2.regs r := fun r a b c => by
    rw [r3]; pre1_reg_simp [a, b, c]
  refine ⟨v3, (p1.append p2).append p3, ?_, ?_, ?_, v3_187, ?_, by rw [m3, m2, m1], by rw [e3, e2, e1],
    by rw [k3, k2, k1], by rw [kr3, kr2, kr1]⟩
  · rw [v3get 170 (by decide) (by decide) (by decide), v2get 170 (by decide), v1_170]
  · rw [v3get 169 (by decide) (by decide) (by decide), v2get 169 (by decide), v1_169]; omega
  · rw [v3get 179 (by decide) (by decide) (by decide), v2get 179 (by decide), v1_179]
  · intro r a b c d e
    rw [v3get r (by omega) (by omega) e, v2get r (by omega), v1get r a (by omega) (by omega) c d]

theorem not_accessWrites {r : Nat} (h : ¬ AccessWrites r) :
    r ≠ 108 ∧ ¬ (26 ≤ r ∧ r ≤ 28) ∧ ¬ (169 ≤ r ∧ r ≤ 172) ∧ ¬ (179 ≤ r ∧ r ≤ 189) :=
  ⟨fun e => h (Or.inl e), fun e => h (Or.inr (Or.inl e)), fun e => h (Or.inr (Or.inr (Or.inl e))),
    fun e => h (Or.inr (Or.inr (Or.inr e)))⟩

theorem localEntry_baseOccurrence_eq (b : List Bool) (t : Bool) (g : Nat) :
    (localEntry b t g).baseOccurrence = flagNat (compactLocalEntryIsLive b t g) *
      (localBaseOccurrence b.length g - localSuperSlot b.length g * superStride b.length) := by
  unfold localEntry flagNat; cases compactLocalEntryIsLive b t g <;> simp

theorem localEntry_baseWordIndex_eq (b : List Bool) (t : Bool) (g : Nat) :
    (localEntry b t g).baseWordIndex = flagNat (compactLocalEntryIsLive b t g) *
      (position b t (localBaseOccurrence b.length g) / wordBits b.length -
        position b t (localSuperSlot b.length g * superStride b.length) / wordBits b.length) := by
  unfold localEntry flagNat; cases compactLocalEntryIsLive b t g <;> simp

theorem localEntry_rankBefore_eq (b : List Bool) (t : Bool) (g : Nat) :
    (localEntry b t g).rankBefore = flagNat (compactLocalEntryIsLive b t g) *
      flagNat (localIsSparseException b t g) := by
  unfold localEntry flagNat
  cases compactLocalEntryIsLive b t g <;> cases localIsSparseException b t g <;> simp

theorem localEntry_firstOffset_eq (b : List Bool) (t : Bool) (g : Nat) :
    (localEntry b t g).firstOffset = flagNat (compactLocalEntryIsLive b t g) *
      (position b t (localBaseOccurrence b.length g) % wordBits b.length) := by
  unfold localEntry flagNat
  cases compactLocalEntryIsLive b t g <;> simp [Nat.mod_eq_sub_div_mul]

/-- **Local field 1**: the base occurrence relative to the super base. -/
theorem localOccEntry_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1) (L0 g : Nat)
    (h1 : u.regs 1 = shape.size) (h161 : u.regs 161 = L0) (h14 : u.regs 14 = g)
    (h40 : u.regs 40 = superStride shape.bpCode.length)
    (h42 : u.regs 42 = localStride shape.bpCode.length)
    (h43 : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (hg : g < localSlotCount shape.bpCode false)
    (hLF : ∀ k, k < superSlotCount shape.bpCode false →
      u.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (hLe : L0 + superSlotCount shape.bpCode false ≤ u.extent)
    (hLW : L0 + superSlotCount shape.bpCode false < 2 ^ W)
    (hcapS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W) :
    EntryOK W localOccEntryBlock AccessWrites u (localEntry shape.bpCode false g).baseOccurrence 11 := by
  obtain ⟨v1, p1, v170, v169, v179, v187, fr1, m1, e1, k1, kr1⟩ :=
    localDecode_prefix hW shape u hrun hone L0 g h1 h161 h14 h40 h42 h43 hg hLF hLe hLW hcapS
  obtain ⟨hB1, _⟩ := localBase_bound shape hg
  have hlive := flagNat_le (compactLocalEntryIsLive shape.bpCode false g)
  have hsupS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length =
      superSlotCount shape.bpCode false * superStride shape.bpCode.length + superStride shape.bpCode.length :=
    Nat.succ_mul _ _
  have hval : flagNat (compactLocalEntryIsLive shape.bpCode false g) *
      (localBaseOccurrence shape.bpCode.length g -
        localSuperSlot shape.bpCode.length g * superStride shape.bpCode.length) < 2 ^ W := by
    have := Nat.mul_le_mul_right (localBaseOccurrence shape.bpCode.length g -
        localSuperSlot shape.bpCode.length g * superStride shape.bpCode.length) hlive
    rw [Nat.one_mul] at this
    omega
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_pure hW (.arithmetic .mul rENT rLIVE rA1) v1 p1.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_187, operand_val_169, v187, v169, reduceCtorEq,
      false_implies, false_or, and_true]
    exact hval)
  refine ⟨v2, _, (p1.append p2).close, by simp, p2.1, ?_, ?_, by rw [m2, m1], by rw [e2, e1], ?_,
    by rw [kr2, kr1], by rw [k2, k1]⟩
  · rw [r2, localEntry_baseOccurrence_eq]
    simp only [pureReg, Arithmetic.eval, operand_val_187, operand_val_169, operand_val_16, v187, v169, put_same]
  · rw [r2]; simp only [pureReg, Arithmetic.eval, operand_val_187, operand_val_169, operand_val_16, v187, v169,
      put_same]
    exact hval
  · intro r hr h16
    obtain ⟨a1, _, a3, a4⟩ := not_accessWrites hr
    rw [r2]; simp only [pureReg, operand_val_16]
    rw [put_ne _ _ h16, fr1 r a1 a3 (by omega) (by omega) (by omega)]

/-- **Local field 2**: the base word index relative to the super base word. -/
theorem localWordEntry_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1) (P0 L0 g : Nat)
    (h1 : u.regs 1 = shape.size) (h159 : u.regs 159 = P0) (h161 : u.regs 161 = L0)
    (h14 : u.regs 14 = g) (h39 : u.regs 39 = wordBits shape.bpCode.length)
    (h40 : u.regs 40 = superStride shape.bpCode.length)
    (h42 : u.regs 42 = localStride shape.bpCode.length)
    (h43 : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (hg : g < localSlotCount shape.bpCode false)
    (hLF : ∀ k, k < superSlotCount shape.bpCode false →
      u.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (hLe : L0 + superSlotCount shape.bpCode false ≤ u.extent)
    (hLW : L0 + superSlotCount shape.bpCode false < 2 ^ W)
    (hcapS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W)
    (hPOS : ∀ k, k ≤ shape.size → u.memory (P0 + k) = some (position shape.bpCode false k))
    (hPe : P0 + shape.size < u.extent) (hPW : P0 + shape.size < 2 ^ W)
    (hlenW : shape.bpCode.length < 2 ^ W) :
    EntryOK W localWordEntryBlock AccessWrites u (localEntry shape.bpCode false g).baseWordIndex 28 := by
  obtain ⟨v1, p1, v170, v169, v179, v187, fr1, m1, e1, k1, kr1⟩ :=
    localDecode_prefix hW shape u hrun hone L0 g h1 h161 h14 h40 h42 h43 hg hLF hLe hLW hcapS
  obtain ⟨hB1, _⟩ := localBase_bound shape hg
  have hlive := flagNat_le (compactLocalEntryIsLive shape.bpCode false g)
  have hsupS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length =
      superSlotCount shape.bpCode false * superStride shape.bpCode.length + superStride shape.bpCode.length :=
    Nat.succ_mul _ _
  have hwspos := wordBits_pos shape.bpCode.length
  have hbase := localBaseOccurrence_mod shape.bpCode.length g
  have hle : localSuperSlot shape.bpCode.length g * superStride shape.bpCode.length ≤
      localBaseOccurrence shape.bpCode.length g := by
    unfold localSuperSlot; rw [hbase]; omega
  have hsSW : localSuperSlot shape.bpCode.length g * superStride shape.bpCode.length < 2 ^ W := by omega
  have hmono := Nat.div_le_div_right (c := wordBits shape.bpCode.length)
    (position_mono shape.bpCode false hle)
  have hposB := position_le_length shape.bpCode false (localBaseOccurrence shape.bpCode.length g)
  have hposS := position_le_length shape.bpCode false
    (localSuperSlot shape.bpCode.length g * superStride shape.bpCode.length)
  obtain ⟨v2, p2, r2, fr2, m2, e2, k2, kr2⟩ := posActs_prefix hW shape rBPOS rBOCC ⟨by decide, by decide⟩
    v1 p1.1 (by rw [fr1 2 (by decide) (by decide) (by decide) (by decide) (by decide), hone]) P0 _
    (by rw [fr1 1 (by decide) (by decide) (by decide) (by decide) (by decide), h1])
    (by rw [fr1 159 (by decide) (by decide) (by decide) (by decide) (by decide), h159]) v179 (by omega)
    (fun q hq => by rw [m1]; exact hPOS q hq) (by rw [e1]; exact hPe) hPW hlenW
  obtain ⟨v3, p3, r3, fr3, m3, e3, k3, kr3⟩ := posActs_prefix hW shape rEPOS rA2 ⟨by decide, by decide⟩
    v2 p2.1 (by rw [fr2 2 (by decide) (by decide) (by decide) (by decide),
      fr1 2 (by decide) (by decide) (by decide) (by decide) (by decide), hone]) P0 _
    (by rw [fr2 1 (by decide) (by decide) (by decide) (by decide),
      fr1 1 (by decide) (by decide) (by decide) (by decide) (by decide), h1])
    (by rw [fr2 159 (by decide) (by decide) (by decide) (by decide),
      fr1 159 (by decide) (by decide) (by decide) (by decide) (by decide), h159])
    (by show v2.regs 170 = _; rw [fr2 170 (by decide) (by decide) (by decide) (by decide), v170]) hsSW
    (fun q hq => by rw [m2, m1]; exact hPOS q hq) (by rw [e2, e1]; exact hPe) hPW hlenW
  have v3_181 : v3.regs 181 = position shape.bpCode false (localBaseOccurrence shape.bpCode.length g) := by
    rw [fr3 181 (by decide) (by decide) (by decide) (by decide)]; exact r2
  have v3_182 : v3.regs 182 = position shape.bpCode false
      (localSuperSlot shape.bpCode.length g * superStride shape.bpCode.length) := r3
  have v3get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 181 → r ≠ 182 → r ≠ 188 →
      v3.regs r = v1.regs r := fun r h a b c d => by rw [fr3 r h a d c, fr2 r h a d b]
  have v3_39 : v3.regs 39 = wordBits shape.bpCode.length := by
    rw [v3get 39 (by decide) (by decide) (by decide) (by decide) (by decide),
      fr1 39 (by decide) (by decide) (by decide) (by decide) (by decide), h39]
  have v3_187 : v3.regs 187 = flagNat (compactLocalEntryIsLive shape.bpCode false g) := by
    rw [v3get 187 (by decide) (by decide) (by decide) (by decide) (by decide), v187]
  have hval : flagNat (compactLocalEntryIsLive shape.bpCode false g) *
      (position shape.bpCode false (localBaseOccurrence shape.bpCode.length g) / wordBits shape.bpCode.length -
        position shape.bpCode false (localSuperSlot shape.bpCode.length g * superStride shape.bpCode.length) /
          wordBits shape.bpCode.length) < 2 ^ W := by
    have h1' := Nat.div_le_self (position shape.bpCode false (localBaseOccurrence shape.bpCode.length g))
      (wordBits shape.bpCode.length)
    have := Nat.mul_le_mul_right (position shape.bpCode false (localBaseOccurrence shape.bpCode.length g) /
        wordBits shape.bpCode.length -
        position shape.bpCode false (localSuperSlot shape.bpCode.length g * superStride shape.bpCode.length) /
          wordBits shape.bpCode.length) hlive
    rw [Nat.one_mul] at this
    exact Nat.lt_of_le_of_lt (Nat.le_trans this (Nat.le_trans (Nat.sub_le _ _) h1')) (by omega)
  obtain ⟨v4, p4, r4, m4, e4, k4, kr4⟩ := prefix_pureList hW
    [.arithmetic .div rBPOS rBPOS rWS, .arithmetic .div rEPOS rEPOS rWS, .arithmetic .sub rENT rBPOS rEPOS,
      .arithmetic .mul rENT rLIVE rENT] v3 p3.1 (by
      pre1_reg_simp [v3_181, v3_182, v3_39, v3_187]
      repeat' apply And.intro
      all_goals first | omega | exact hval | (apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _); omega) |
        (exact hmono) |
        (exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))))
  have hv16 : v4.regs 16 = (localEntry shape.bpCode false g).baseWordIndex := by
    rw [r4, localEntry_baseWordIndex_eq]; pre1_reg_simp [v3_181, v3_182, v3_39, v3_187]
  have pall := ((p1.append p2).append p3).append p4
  refine ⟨v4, _, pall.close, by simp, p4.1, hv16, ?_, by rw [m4, m3, m2, m1], by rw [e4, e3, e2, e1], ?_,
    by rw [kr4, kr3, kr2, kr1], by rw [k4, k3, k2, k1]⟩
  · rw [hv16, localEntry_baseWordIndex_eq]; exact hval
  · intro r hr h16
    obtain ⟨a1, a2, a3, a4⟩ := not_accessWrites hr
    have b1 : r ≠ 181 := by omega
    have b2 : r ≠ 182 := by omega
    rw [r4]; pre1_reg_simp [h16, b1, b2]
    rw [v3get r a2 a1 b1 b2 (by omega), fr1 r a1 a3 (by omega) (by omega) (by omega)]

/-- **Local field 3**: the sparse-exception flag. -/
theorem localFlagEntry_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1) (L0 F0 g : Nat)
    (h1 : u.regs 1 = shape.size) (h161 : u.regs 161 = L0) (h163 : u.regs 163 = F0)
    (h14 : u.regs 14 = g)
    (h40 : u.regs 40 = superStride shape.bpCode.length)
    (h42 : u.regs 42 = localStride shape.bpCode.length)
    (h43 : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (hg : g < localSlotCount shape.bpCode false)
    (hLF : ∀ k, k < superSlotCount shape.bpCode false →
      u.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (hLe : L0 + superSlotCount shape.bpCode false ≤ u.extent)
    (hLW : L0 + superSlotCount shape.bpCode false < 2 ^ W)
    (hSF : ∀ k, k < localSlotCount shape.bpCode false →
      u.memory (F0 + k) = some (flagNat (localIsSparseException shape.bpCode false k)))
    (hFe : F0 + localSlotCount shape.bpCode false ≤ u.extent)
    (hFW : F0 + localSlotCount shape.bpCode false < 2 ^ W)
    (hcapS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W) :
    EntryOK W localFlagEntryBlock AccessWrites u (localEntry shape.bpCode false g).rankBefore 13 := by
  obtain ⟨v1, p1, v170, v169, v179, v187, fr1, m1, e1, k1, kr1⟩ :=
    localDecode_prefix hW shape u hrun hone L0 g h1 h161 h14 h40 h42 h43 hg hLF hLe hLW hcapS
  have hlive := flagNat_le (compactLocalEntryIsLive shape.bpCode false g)
  have hsp := flagNat_le (localIsSparseException shape.bpCode false g)
  have h2W := two_le_two_pow hW
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ := prefix_pure hW (.arithmetic .add rADDR rSFB rSLOT) v1 p1.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_163, operand_val_14,
      fr1 163 (by decide) (by decide) (by decide) (by decide) (by decide), h163,
      fr1 14 (by decide) (by decide) (by decide) (by decide) (by decide), h14, reduceCtorEq,
      false_implies, false_or, and_true]
    omega)
  have v2_108 : v2.regs 108 = F0 + g := by
    rw [r2]; simp only [pureReg, Arithmetic.eval, operand_val_163, operand_val_14, operand_val_108,
      fr1 163 (by decide) (by decide) (by decide) (by decide) (by decide), h163,
      fr1 14 (by decide) (by decide) (by decide) (by decide) (by decide), h14, put_same]
  have v2get : ∀ r, r ≠ 108 → v2.regs r = v1.regs r := fun r h => by
    rw [r2]; simp only [pureReg, operand_val_108]; rw [put_ne _ _ h]
  obtain ⟨v3, p3, r3, m3, e3, k3, kr3⟩ := prefix_load hW rENT rADDR v2 p2.1
    (x := flagNat (localIsSparseException shape.bpCode false g))
    (by show v2.regs 108 < v2.extent; rw [v2_108, e2, e1]; omega)
    (by show v2.memory (v2.regs 108) = _; rw [v2_108, m2, m1]; exact hSF g hg) (by omega)
  have v3_16 : v3.regs 16 = flagNat (localIsSparseException shape.bpCode false g) := by
    rw [r3, operand_val_16, put_same]
  have v3_187 : v3.regs 187 = flagNat (compactLocalEntryIsLive shape.bpCode false g) := by
    rw [r3, operand_val_16, put_ne _ _ (by decide), v2get 187 (by decide), v187]
  have hprod : flagNat (compactLocalEntryIsLive shape.bpCode false g) *
      flagNat (localIsSparseException shape.bpCode false g) ≤ 1 := by
    have := Nat.mul_le_mul hlive hsp; omega
  obtain ⟨v4, p4, r4, m4, e4, k4, kr4⟩ := prefix_pure hW (.arithmetic .mul rENT rLIVE rENT) v3 p3.1 (by
    simp only [pureOK, Arithmetic.eval, operand_val_187, operand_val_16, v3_187, v3_16, reduceCtorEq,
      false_implies, false_or, and_true]
    omega)
  have hv16 : v4.regs 16 = (localEntry shape.bpCode false g).rankBefore := by
    rw [r4, localEntry_rankBefore_eq]
    simp only [pureReg, Arithmetic.eval, operand_val_187, operand_val_16, v3_187, v3_16, put_same]
  have pall := ((p1.append p2).append p3).append p4
  refine ⟨v4, _, pall.close, by simp, p4.1, hv16, ?_, by rw [m4, m3, m2, m1], by rw [e4, e3, e2, e1], ?_,
    by rw [kr4, kr3, kr2, kr1], by rw [k4, k3, k2, k1]⟩
  · rw [hv16, localEntry_rankBefore_eq]; omega
  · intro r hr h16
    obtain ⟨a1, _, a3, a4⟩ := not_accessWrites hr
    rw [r4]; simp only [pureReg, operand_val_16]
    rw [put_ne _ _ h16, r3, operand_val_16, put_ne _ _ h16, v2get r a1,
      fr1 r a1 a3 (by omega) (by omega) (by omega)]

/-- **Local field 4**: the first offset inside the base word. -/
theorem localOffsetEntry_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1) (P0 L0 g : Nat)
    (h1 : u.regs 1 = shape.size) (h159 : u.regs 159 = P0) (h161 : u.regs 161 = L0)
    (h14 : u.regs 14 = g) (h39 : u.regs 39 = wordBits shape.bpCode.length)
    (h40 : u.regs 40 = superStride shape.bpCode.length)
    (h42 : u.regs 42 = localStride shape.bpCode.length)
    (h43 : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (hg : g < localSlotCount shape.bpCode false)
    (hLF : ∀ k, k < superSlotCount shape.bpCode false →
      u.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (hLe : L0 + superSlotCount shape.bpCode false ≤ u.extent)
    (hLW : L0 + superSlotCount shape.bpCode false < 2 ^ W)
    (hcapS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W)
    (hPOS : ∀ k, k ≤ shape.size → u.memory (P0 + k) = some (position shape.bpCode false k))
    (hPe : P0 + shape.size < u.extent) (hPW : P0 + shape.size < 2 ^ W)
    (hlenW : shape.bpCode.length < 2 ^ W) :
    EntryOK W localOffsetEntryBlock AccessWrites u (localEntry shape.bpCode false g).firstOffset 19 := by
  obtain ⟨v1, p1, v170, v169, v179, v187, fr1, m1, e1, k1, kr1⟩ :=
    localDecode_prefix hW shape u hrun hone L0 g h1 h161 h14 h40 h42 h43 hg hLF hLe hLW hcapS
  obtain ⟨hB1, _⟩ := localBase_bound shape hg
  have hlive := flagNat_le (compactLocalEntryIsLive shape.bpCode false g)
  have hsupS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length =
      superSlotCount shape.bpCode false * superStride shape.bpCode.length + superStride shape.bpCode.length :=
    Nat.succ_mul _ _
  have hwspos := wordBits_pos shape.bpCode.length
  have hposB := position_le_length shape.bpCode false (localBaseOccurrence shape.bpCode.length g)
  obtain ⟨v2, p2, r2, fr2, m2, e2, k2, kr2⟩ := posActs_prefix hW shape rBPOS rBOCC ⟨by decide, by decide⟩
    v1 p1.1 (by rw [fr1 2 (by decide) (by decide) (by decide) (by decide) (by decide), hone]) P0 _
    (by rw [fr1 1 (by decide) (by decide) (by decide) (by decide) (by decide), h1])
    (by rw [fr1 159 (by decide) (by decide) (by decide) (by decide) (by decide), h159]) v179 (by omega)
    (fun q hq => by rw [m1]; exact hPOS q hq) (by rw [e1]; exact hPe) hPW hlenW
  have v2_181 : v2.regs 181 = position shape.bpCode false (localBaseOccurrence shape.bpCode.length g) := r2
  have v2_39 : v2.regs 39 = wordBits shape.bpCode.length := by
    rw [fr2 39 (by decide) (by decide) (by decide) (by decide),
      fr1 39 (by decide) (by decide) (by decide) (by decide) (by decide), h39]
  have v2_187 : v2.regs 187 = flagNat (compactLocalEntryIsLive shape.bpCode false g) := by
    rw [fr2 187 (by decide) (by decide) (by decide) (by decide), v187]
  have hval : flagNat (compactLocalEntryIsLive shape.bpCode false g) *
      (position shape.bpCode false (localBaseOccurrence shape.bpCode.length g) %
        wordBits shape.bpCode.length) < 2 ^ W := by
    have h1' := Nat.mod_le (position shape.bpCode false (localBaseOccurrence shape.bpCode.length g))
      (wordBits shape.bpCode.length)
    have := Nat.mul_le_mul_right (position shape.bpCode false (localBaseOccurrence shape.bpCode.length g) %
        wordBits shape.bpCode.length) hlive
    rw [Nat.one_mul] at this
    exact Nat.lt_of_le_of_lt (Nat.le_trans this h1') (by omega)
  obtain ⟨v3, p3, r3, m3, e3, k3, kr3⟩ := prefix_pureList hW
    [.arithmetic .mod rENT rBPOS rWS, .arithmetic .mul rENT rLIVE rENT] v2 p2.1 (by
      pre1_reg_simp [v2_181, v2_39, v2_187]
      repeat' apply And.intro
      all_goals first | omega | exact hval | (apply Nat.lt_of_le_of_lt (Nat.mod_le _ _); omega))
  have hv16 : v3.regs 16 = (localEntry shape.bpCode false g).firstOffset := by
    rw [r3, localEntry_firstOffset_eq]; pre1_reg_simp [v2_181, v2_39, v2_187]
  have pall := (p1.append p2).append p3
  refine ⟨v3, _, pall.close, by simp, p3.1, hv16, ?_, by rw [m3, m2, m1], by rw [e3, e2, e1], ?_,
    by rw [kr3, kr2, kr1], by rw [k3, k2, k1]⟩
  · rw [hv16, localEntry_firstOffset_eq]; exact hval
  · intro r hr h16
    obtain ⟨a1, a2, a3, a4⟩ := not_accessWrites hr
    rw [r3]; pre1_reg_simp [h16]
    rw [fr2 r a2 a1 (by omega) (show r ≠ 181 by omega), fr1 r a1 a3 (by omega) (by omega) (by omega)]

end RMQ.SuccinctFinal.PackedConstruction.Proof
