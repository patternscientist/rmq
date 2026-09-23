import RMQ.Core.WordRAM.Construction.Proof.SparseMemo

/-! # PRE-1 builder proofs: the local and global sparse tables (stage S4)

Outside the builder firewall. The local sparse entry decodes a slot into macro
index, level and local start, checks the two reference guards and, when both
hold, reads the local memo and subtracts the macro start; the global sparse
entry decodes level and macro start and reads the global memo. Both agree with
`bpLocalSparseCellOffset` and `bpGlobalSparseCellBlock` on every slot, and
`emitTable_spec` turns them into the two reference tables.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose

/-- **Local sparse entry.** -/
theorem localEntry_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1)
    (bs bc Bm M mc LC slot : Nat) (h14 : u.regs 14 = slot) (h58 : u.regs 58 = LC)
    (h31 : u.regs 31 = M) (h32 : u.regs 32 = bc) (h135 : u.regs 135 = Bm)
    (hM1 : 1 ≤ M) (hLC1 : 1 ≤ LC) (hLCW : LC < W) (hslot : slot < mc * (LC * M))
    (hcapE : slot + LC * M + (mc + 1) * M + 2 ^ LC < 2 ^ W)
    (hext : Bm + LC * bc ≤ u.extent) (hBW : Bm + LC * bc < 2 ^ W)
    (hmemo : ∀ l b, l < LC → b + 2 ^ l ≤ bc →
      u.memory (Bm + l * bc + b) = some (bpRangeArgMinBlock shape bs b (2 ^ l))) :
    ∃ u' j, SafeEval W localEntryBlock u u' j ∧ j ≤ 21 ∧ u'.status = .running ∧
      u'.regs 16 = bpLocalSparseCellOffset shape bs bc M (slot / (LC * M))
        ((slot % (LC * M)) % M) ((slot % (LC * M)) / M) ∧
      u'.regs 16 < 2 ^ W ∧ u'.memory = u.memory ∧ u'.extent = u.extent ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 141 → r ≠ 146 → r ≠ 147 → r ≠ 151 → ¬ (155 ≤ r ∧ r ≤ 158) →
        r ≠ 16 → u'.regs r = u.regs r) ∧
      u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys := by
  have hP : 0 < LC * M := Nat.mul_pos (by omega) (by omega)
  obtain ⟨q, hq⟩ : ∃ q, slot / (LC * M) = q := ⟨_, rfl⟩
  obtain ⟨rem, hrem⟩ : ∃ x, slot % (LC * M) = x := ⟨_, rfl⟩
  obtain ⟨lv, hlv⟩ : ∃ x, rem / M = x := ⟨_, rfl⟩
  obtain ⟨ls, hls⟩ : ∃ x, rem % M = x := ⟨_, rfl⟩
  have hqmc : q < mc := by
    rw [← hq]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hslot)
  have hremlt : rem < LC * M := by rw [← hrem]; exact Nat.mod_lt _ hP
  have hlslt : ls < M := by rw [← hls]; exact Nat.mod_lt _ (by omega)
  have hlvlt : lv < LC := by
    rw [← hlv]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hremlt)
  have hqsl : q ≤ slot := by rw [← hq]; exact Nat.div_le_self _ _
  have hremsl : rem ≤ slot := by rw [← hrem]; exact Nat.mod_le _ _
  have hlvsl : lv ≤ rem := by rw [← hlv]; exact Nat.div_le_self _ _
  have hsp : 2 ^ lv ≤ 2 ^ LC := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hlvlt)
  have hqM : q * M + M ≤ (mc + 1) * M := by
    have := Nat.mul_le_mul_right M (show q + 1 ≤ mc + 1 by omega); rw [Nat.succ_mul] at this; exact this
  have hlvbc : lv * bc ≤ LC * bc := Nat.mul_le_mul_right bc (Nat.le_of_lt hlvlt)
  have hLCp : LC < 2 ^ LC := Nat.lt_two_pow_self
  rw [hq, hrem, hlv, hls]
  -- header
  obtain ⟨hd, jh, eh, hjh, hdr, hdR, hdm, hde, hdk, hdkr⟩ :=
    RegSpec.pure hW [.arithmetic .mul rT6 rOW rMACRO,
      .arithmetic .div rMI rSLOT rT6, .arithmetic .mod rT7 rSLOT rT6,
      .arithmetic .div rLV rT7 rMACRO, .arithmetic .mod rLS rT7 rMACRO,
      .arithmetic .shl rSPN rONE rLV,
      .arithmetic .mul rMST rMI rMACRO, .arithmetic .add rSTB rMST rLS,
      .arithmetic .add rT6 rLS rSPN, .comparison .lt rT6 rMACRO rT6,
      .arithmetic .add rT7 rSTB rSPN, .comparison .lt rT7 rBLOCKS rT7,
      .arithmetic .add rT6 rT6 rT7, .constant rENT 0] u hrun (by
        pre1_reg_simp [h14, h58, h31, h32, hone, hq, hrem, hlv, hls, shiftLeft_one]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first | omega | (split <;> split <;> omega) | (split <;> omega))
  have hd146 : hd.regs 146 = (if M < ls + 2 ^ lv then 1 else 0) +
      (if bc < q * M + ls + 2 ^ lv then 1 else 0) := by
    rw [hdR]; pre1_reg_simp [h14, h58, h31, h32, hone, hq, hrem, hlv, hls, shiftLeft_one]
  have hd151 : hd.regs 151 = q * M := by
    rw [hdR]; pre1_reg_simp [h14, h58, h31, h32, hone, hq, hrem, hlv, hls, shiftLeft_one]
  have hd156 : hd.regs 156 = lv := by
    rw [hdR]; pre1_reg_simp [h14, h58, h31, h32, hone, hq, hrem, hlv, hls, shiftLeft_one]
  have hd158 : hd.regs 158 = q * M + ls := by
    rw [hdR]; pre1_reg_simp [h14, h58, h31, h32, hone, hq, hrem, hlv, hls, shiftLeft_one]
  have hd16 : hd.regs 16 = 0 := by
    rw [hdR]; pre1_reg_simp [h14, h58, h31, h32, hone, hq, hrem, hlv, hls, shiftLeft_one]
  have hdfr : ∀ r : Nat, r ≠ 141 → r ≠ 146 → r ≠ 147 → r ≠ 151 → ¬ (155 ≤ r ∧ r ≤ 158) →
      r ≠ 16 → hd.regs r = u.regs r := by
    intro r a b c d e f
    have e1 : r ≠ 155 := by omega
    have e2 : r ≠ 156 := by omega
    have e3 : r ≠ 157 := by omega
    have e4 : r ≠ 158 := by omega
    rw [hdR]; pre1_reg_simp [a, b, c, d, e1, e2, e3, e4, f]
  have hd32 : hd.regs 32 = bc := by
    rw [hdfr 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h32]
  have hd135 : hd.regs 135 = Bm := by
    rw [hdfr 135 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h135]
  unfold bpLocalSparseCellOffset
  simp only []
  by_cases hg : ls + 2 ^ lv ≤ M ∧ q * M + ls + 2 ^ lv ≤ bc
  · have hc : hd.regs rT6 = 0 := by
      show hd.regs 146 = 0; rw [hd146, if_neg (by omega), if_neg (by omega)]
    have hstb : q * M + ls < bc := by have := Nat.two_pow_pos lv; omega
    have hRA := bpRangeArgMinBlock_mem shape bs (q * M + ls) (2 ^ lv) (Nat.two_pow_pos lv)
    -- T7 := lv * bc; T7 += stb; rADDR := Bm + T7; ENT := load; ENT -= mst
    obtain ⟨w1, p1, r1, m1, e1, k1, kr1⟩ :=
      prefix_pure hW (.arithmetic .mul rT7 rLV rBLOCKS) hd hdr (by
        simp only [pureOK, Arithmetic.eval, operand_val_156, operand_val_32, hd156, hd32,
          reduceCtorEq, false_implies, false_or, and_true]; omega)
    have w1r : w1.regs = put hd.regs 147 (lv * bc) := by
      rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_147, operand_val_156, operand_val_32,
        hd156, hd32]
    obtain ⟨w2, p2, r2, m2, e2, k2, kr2⟩ :=
      prefix_pure hW (.arithmetic .add rT7 rT7 rSTB) w1 p1.1 (by
        simp only [pureOK, Arithmetic.eval, operand_val_147, operand_val_158, w1r, put_same,
          put_ne _ _ (show (158 : Nat) ≠ 147 by decide), hd158, reduceCtorEq, false_implies,
          false_or, and_true]
        have := row_lt (L := LC) hstb hlvlt; omega)
    have w2_147 : w2.regs 147 = lv * bc + (q * M + ls) := by
      rw [r2]; simp only [pureReg, Arithmetic.eval, operand_val_147, operand_val_158, w1r, put_same,
        put_ne _ _ (show (158 : Nat) ≠ 147 by decide), hd158]
    have w2fr : ∀ r, r ≠ 147 → w2.regs r = hd.regs r := fun r h => by
      rw [r2]; simp only [pureReg, operand_val_147]; rw [put_ne _ _ h, w1r, put_ne _ _ h]
    obtain ⟨w3, p3, r3, m3, e3, k3, kr3⟩ :=
      prefix_pure hW (.arithmetic .add rADDR rAMB rT7) w2 p2.1 (by
        simp only [pureOK, Arithmetic.eval, operand_val_135, operand_val_147, w2_147,
          w2fr 135 (by decide), hd135, reduceCtorEq, false_implies, false_or, and_true]
        have := row_lt (L := LC) hstb hlvlt; omega)
    have w3_108 : w3.regs 108 = Bm + (lv * bc + (q * M + ls)) := by
      rw [r3]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_135, operand_val_147,
        w2_147, w2fr 135 (by decide), hd135, put_same]
    have w3fr : ∀ r, r ≠ 108 → r ≠ 147 → w3.regs r = hd.regs r := fun r a b => by
      rw [r3]; simp only [pureReg, operand_val_108]; rw [put_ne _ _ a, w2fr r b]
    obtain ⟨w4, p4, r4, m4, e4, k4, kr4⟩ :=
      prefix_load hW rENT rADDR w3 p3.1 (x := bpRangeArgMinBlock shape bs (q * M + ls) (2 ^ lv))
        (by show w3.regs 108 < w3.extent
            rw [w3_108, e3, e2, e1, hde]; have := row_lt (L := LC) hstb hlvlt; omega)
        (by show w3.memory (w3.regs 108) = _
            rw [w3_108, m3, m2, m1, hdm, ← Nat.add_assoc]; exact hmemo lv _ hlvlt hg.2)
        (by omega)
    have w4_16 : w4.regs 16 = bpRangeArgMinBlock shape bs (q * M + ls) (2 ^ lv) := by
      rw [r4]; simp only [operand_val_16, put_same]
    have w4_151 : w4.regs 151 = q * M := by
      rw [r4, operand_val_16, put_ne _ _ (by decide), w3fr 151 (by decide) (by decide), hd151]
    obtain ⟨w5, p5, r5, m5, e5, k5, kr5⟩ :=
      prefix_pure hW (.arithmetic .sub rENT rENT rMST) w4 p4.1 (by
        simp only [pureOK, Arithmetic.eval, operand_val_16, operand_val_151, w4_16, w4_151,
          reduceCtorEq, false_implies, false_or, and_true, forall_const]; omega)
    have w5_16 : w5.regs 16 = bpRangeArgMinBlock shape bs (q * M + ls) (2 ^ lv) - q * M := by
      rw [r5]; simp only [pureReg, Arithmetic.eval, operand_val_16, operand_val_151, w4_16, w4_151,
        put_same]
    have pre := p1.append (p2.append (p3.append (p4.append p5)))
    refine ⟨w5, jh + (1 + (1 + (1 + (1 + 1))) + 1),
      EvalG.seq eh (EvalG.ifZeroTaken hdr hc pre.close), by simp at hjh; omega, p5.1, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · rw [w5_16, if_pos ⟨hg.1, by omega⟩]
    · rw [w5_16]; omega
    · rw [m5, m4, m3, m2, m1, hdm]
    · rw [e5, e4, e3, e2, e1, hde]
    · intro r h108 h141 h146 h147 h151 h155 h16
      rw [r5]; simp only [pureReg, operand_val_16]
      rw [put_ne _ _ h16, r4, operand_val_16, put_ne _ _ h16, w3fr r h108 h147,
        hdfr r h141 h146 h147 h151 h155 h16]
    · rw [kr5, kr4, kr3, kr2, kr1, hdkr]
    · rw [k5, k4, k3, k2, k1, hdk]
  · have hc : hd.regs rT6 ≠ 0 := by
      show hd.regs 146 ≠ 0; rw [hd146]
      by_cases h1 : M < ls + 2 ^ lv
      · rw [if_pos h1]; omega
      · rw [if_neg h1, if_pos (by omega)]; omega
    refine ⟨hd, jh + (0 + 2), EvalG.seq eh (EvalG.ifZeroFallthrough hdr hc (EvalG.skip hd hdr) hdr),
      by simp at hjh; omega, hdr, ?_, ?_, hdm, hde, ?_, hdkr, hdk⟩
    · rw [hd16, if_neg (by omega)]
    · rw [hd16]; omega
    · intro r _ h141 h146 h147 h151 h155 h16
      exact hdfr r h141 h146 h147 h151 h155 h16

/-- **Global sparse entry.** -/
theorem globalEntry_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1)
    (bs bc Gb M mc GLC slot : Nat) (h14 : u.regs 14 = slot) (h33 : u.regs 33 = mc)
    (h31 : u.regs 31 = M) (h32 : u.regs 32 = bc) (h136 : u.regs 136 = Gb)
    (hmc1 : 1 ≤ mc) (hM1 : 1 ≤ M) (hGLCW : GLC < W) (hslot : slot < GLC * mc)
    (hcapE : slot + (mc + 2 ^ GLC) * M < 2 ^ W) (hbcW : bc < 2 ^ W)
    (hext : Gb + GLC * mc ≤ u.extent) (hGW : Gb + GLC * mc < 2 ^ W)
    (hmemo : ∀ l m, l < GLC → (m + 2 ^ l) * M ≤ bc →
      u.memory (Gb + l * mc + m) = some (bpRangeArgMinBlock shape bs (m * M) (2 ^ l * M))) :
    ∃ u' j, SafeEval W globalEntryBlock u u' j ∧ j ≤ 17 ∧ u'.status = .running ∧
      u'.regs 16 = bpGlobalSparseCellBlock shape bs bc M mc (slot % mc) (slot / mc) ∧
      u'.regs 16 < 2 ^ W ∧ u'.memory = u.memory ∧ u'.extent = u.extent ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 141 → r ≠ 146 → r ≠ 147 → r ≠ 155 → r ≠ 156 → r ≠ 158 →
        r ≠ 16 → u'.regs r = u.regs r) ∧
      u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys := by
  obtain ⟨lv, hlv⟩ : ∃ x, slot / mc = x := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ x, slot % mc = x := ⟨_, rfl⟩
  have hlvlt : lv < GLC := by
    rw [← hlv]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hslot)
  have hmlt : m < mc := by rw [← hm]; exact Nat.mod_lt _ (by omega)
  have hlvsl : lv ≤ slot := by rw [← hlv]; exact Nat.div_le_self _ _
  have hsp : 2 ^ lv ≤ 2 ^ GLC := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hlvlt)
  have hmM : m * M ≤ mc * M := Nat.mul_le_mul_right M (Nat.le_of_lt hmlt)
  have hspM : 2 ^ lv * M ≤ 2 ^ GLC * M := Nat.mul_le_mul_right M hsp
  have hsum : (mc + 2 ^ GLC) * M = mc * M + 2 ^ GLC * M := Nat.add_mul _ _ _
  have hGp : GLC < 2 ^ GLC := Nat.lt_two_pow_self
  have hle1 : mc + 2 ^ GLC ≤ (mc + 2 ^ GLC) * M := Nat.le_mul_of_pos_right _ hM1
  rw [hlv, hm]
  obtain ⟨hd, jh, eh, hjh, hdr, hdR, hdm, hde, hdk, hdkr⟩ :=
    RegSpec.pure hW [.arithmetic .div rLV rSLOT rMACROS, .arithmetic .mod rMI rSLOT rMACROS,
      .arithmetic .shl rSPN rONE rLV,
      .arithmetic .add rT6 rMI rSPN, .comparison .lt rT6 rMACROS rT6,
      .arithmetic .mul rSTB rMI rMACRO, .arithmetic .mul rT7 rSPN rMACRO,
      .arithmetic .add rT7 rSTB rT7, .comparison .lt rT7 rBLOCKS rT7,
      .arithmetic .add rT6 rT6 rT7, .constant rENT 0] u hrun (by
        pre1_reg_simp [h14, h33, h31, h32, hone, hlv, hm, shiftLeft_one]
        repeat' apply And.intro
        all_goals first | omega | (split <;> split <;> omega) | (split <;> omega))
  have hd146 : hd.regs 146 = (if mc < m + 2 ^ lv then 1 else 0) +
      (if bc < m * M + 2 ^ lv * M then 1 else 0) := by
    rw [hdR]; pre1_reg_simp [h14, h33, h31, h32, hone, hlv, hm, shiftLeft_one]
  have hd155 : hd.regs 155 = m := by
    rw [hdR]; pre1_reg_simp [h14, h33, h31, h32, hone, hlv, hm, shiftLeft_one]
  have hd156 : hd.regs 156 = lv := by
    rw [hdR]; pre1_reg_simp [h14, h33, h31, h32, hone, hlv, hm, shiftLeft_one]
  have hd16 : hd.regs 16 = 0 := by
    rw [hdR]; pre1_reg_simp [h14, h33, h31, h32, hone, hlv, hm, shiftLeft_one]
  have hdfr : ∀ r : Nat, r ≠ 141 → r ≠ 146 → r ≠ 147 → r ≠ 155 → r ≠ 156 → r ≠ 158 →
      r ≠ 16 → hd.regs r = u.regs r := by
    intro r a b c d e f g
    rw [hdR]; pre1_reg_simp [a, b, c, d, e, f, g]
  have hd33 : hd.regs 33 = mc := by
    rw [hdfr 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h33]
  have hd136 : hd.regs 136 = Gb := by
    rw [hdfr 136 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h136]
  unfold bpGlobalSparseCellBlock
  simp only []
  by_cases hg : m + 2 ^ lv ≤ mc ∧ m * M + 2 ^ lv * M ≤ bc
  · have hc : hd.regs rT6 = 0 := by
      show hd.regs 146 = 0; rw [hd146, if_neg (by omega), if_neg (by omega)]
    have hrow := row_lt (L := GLC) hmlt hlvlt
    obtain ⟨w1, p1, r1, m1, e1, k1, kr1⟩ :=
      prefix_pure hW (.arithmetic .mul rT7 rLV rMACROS) hd hdr (by
        simp only [pureOK, Arithmetic.eval, operand_val_156, operand_val_33, hd156, hd33,
          reduceCtorEq, false_implies, false_or, and_true]; omega)
    have w1r : w1.regs = put hd.regs 147 (lv * mc) := by
      rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_147, operand_val_156, operand_val_33,
        hd156, hd33]
    obtain ⟨w2, p2, r2, m2, e2, k2, kr2⟩ :=
      prefix_pure hW (.arithmetic .add rT7 rT7 rMI) w1 p1.1 (by
        simp only [pureOK, Arithmetic.eval, operand_val_147, operand_val_155, w1r, put_same,
          put_ne _ _ (show (155 : Nat) ≠ 147 by decide), hd155, reduceCtorEq, false_implies,
          false_or, and_true]; omega)
    have w2_147 : w2.regs 147 = lv * mc + m := by
      rw [r2]; simp only [pureReg, Arithmetic.eval, operand_val_147, operand_val_155, w1r, put_same,
        put_ne _ _ (show (155 : Nat) ≠ 147 by decide), hd155]
    have w2fr : ∀ r, r ≠ 147 → w2.regs r = hd.regs r := fun r h => by
      rw [r2]; simp only [pureReg, operand_val_147]; rw [put_ne _ _ h, w1r, put_ne _ _ h]
    obtain ⟨w3, p3, r3, m3, e3, k3, kr3⟩ :=
      prefix_pure hW (.arithmetic .add rADDR rGMB rT7) w2 p2.1 (by
        simp only [pureOK, Arithmetic.eval, operand_val_136, operand_val_147, w2_147,
          w2fr 136 (by decide), hd136, reduceCtorEq, false_implies, false_or, and_true]; omega)
    have w3_108 : w3.regs 108 = Gb + (lv * mc + m) := by
      rw [r3]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_136, operand_val_147,
        w2_147, w2fr 136 (by decide), hd136, put_same]
    have w3fr : ∀ r, r ≠ 108 → r ≠ 147 → w3.regs r = hd.regs r := fun r a b => by
      rw [r3]; simp only [pureReg, operand_val_108]; rw [put_ne _ _ a, w2fr r b]
    have hvalid : (m + 2 ^ lv) * M ≤ bc := by rw [Nat.add_mul]; exact hg.2
    have hpos : 0 < 2 ^ lv * M := Nat.mul_pos (Nat.two_pow_pos lv) (by omega)
    have hRA := (bpRangeArgMinBlock_mem shape bs (m * M) (2 ^ lv * M) hpos).2
    obtain ⟨w4, p4, r4, m4, e4, k4, kr4⟩ :=
      prefix_load hW rENT rADDR w3 p3.1 (x := bpRangeArgMinBlock shape bs (m * M) (2 ^ lv * M))
        (by show w3.regs 108 < w3.extent; rw [w3_108, e3, e2, e1, hde]; omega)
        (by show w3.memory (w3.regs 108) = _
            rw [w3_108, m3, m2, m1, hdm, ← Nat.add_assoc]; exact hmemo lv m hlvlt hvalid)
        (by omega)
    have pre := p1.append (p2.append (p3.append p4))
    refine ⟨w4, jh + (1 + (1 + (1 + 1)) + 1),
      EvalG.seq eh (EvalG.ifZeroTaken hdr hc pre.close), by simp at hjh; omega, p4.1, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · rw [r4, operand_val_16, put_same, if_pos hg]
    · rw [r4, operand_val_16, put_same]; omega
    · rw [m4, m3, m2, m1, hdm]
    · rw [e4, e3, e2, e1, hde]
    · intro r h108 h141 h146 h147 h155 h156 h158 h16
      rw [r4, operand_val_16, put_ne _ _ h16, w3fr r h108 h147,
        hdfr r h141 h146 h147 h155 h156 h158 h16]
    · rw [kr4, kr3, kr2, kr1, hdkr]
    · rw [k4, k3, k2, k1, hdk]
  · have hc : hd.regs rT6 ≠ 0 := by
      show hd.regs 146 ≠ 0; rw [hd146]
      by_cases h1 : mc < m + 2 ^ lv
      · rw [if_pos h1]; omega
      · rw [if_neg h1, if_pos (by omega)]; omega
    refine ⟨hd, jh + (0 + 2), EvalG.seq eh (EvalG.ifZeroFallthrough hdr hc (EvalG.skip hd hdr) hdr),
      by simp at hjh; omega, hdr, ?_, ?_, hdm, hde, ?_, hdkr, hdk⟩
    · rw [hd16, if_neg hg]
    · rw [hd16]; omega
    · intro r _ h141 h146 h147 h155 h156 h158 h16
      exact hdfr r h141 h146 h147 h155 h156 h158 h16

/-! ## The two sparse tables -/

/-- Scratch writes of the local sparse entry. -/
abbrev LocalEntryWrites (r : Nat) : Prop :=
  r = 108 ∨ r = 141 ∨ r = 146 ∨ r = 147 ∨ r = 151 ∨ (155 ≤ r ∧ r ≤ 158)

/-- Scratch writes of the global sparse entry. -/
abbrev GlobalEntryWrites (r : Nat) : Prop :=
  r = 108 ∨ r = 141 ∨ r = 146 ∨ r = 147 ∨ r = 155 ∨ r = 156 ∨ r = 158

/-- **Local sparse table.** -/
theorem localSparseTable_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2)
    (bs bc Bm M mc LC : Nat) (h58 : s.regs 58 = LC) (h31 : s.regs 31 = M)
    (h32 : s.regs 32 = bc) (h135 : s.regs 135 = Bm) (h62 : s.regs 62 = mc * (LC * M))
    (hM1 : 1 ≤ M) (hLC1 : 1 ≤ LC) (hLCW : LC < W)
    (hcapE : mc * (LC * M) + LC * M + (mc + 1) * M + 2 ^ LC < 2 ^ W)
    (hextT : s.extent + mc * (LC * M) * LC < 2 ^ W)
    (hext : Bm + LC * bc ≤ s.extent) (hBW : Bm + LC * bc < 2 ^ W)
    (hmemo : ∀ l b, l < LC → b + 2 ^ l ≤ bc →
      s.memory (Bm + l * bc + b) = some (bpRangeArgMinBlock shape bs b (2 ^ l))) :
    ∃ s' k, SafeEval W (emitTable rLSCNT rOW localEntryBlock) s s' k ∧
      k ≤ mc * (LC * M) * (21 + 7 * LC + 7) + 3 ∧ s'.status = .running ∧
      Emits s s' ((tableBits (bpLocalSparseOffsetEntries shape bs bc M mc LC) LC).map
        SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ LocalEntryWrites r → ¬ (10 ≤ r ∧ r ≤ 16) → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  have hLp : LC < 2 ^ LC := Nat.lt_two_pow_self
  obtain ⟨s', k, e, hk, hr, hem, hfr, hkr, hks⟩ :=
    emitTable_spec hW rLSCNT rOW localEntryBlock
      (fun slot => bpLocalSparseCellOffset shape bs bc M (slot / (LC * M))
        ((slot % (LC * M)) % M) ((slot % (LC * M)) / M)) 21 LocalEntryWrites
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s hrun hone htwo
      (by show s.regs 62 + 1 < 2 ^ W; rw [h62]; omega)
      (by show s.regs 58 < 2 ^ W; rw [h58]; omega)
      (by show s.extent + s.regs 62 * s.regs 58 < 2 ^ W; rw [h62, h58]; exact hextT)
      (by
        intro u hur hufr humem hue huk hukr hslot
        have hslot' : u.regs 14 < mc * (LC * M) := by
          have : u.regs 14 < s.regs 62 := hslot; rwa [h62] at this
        have ufr : ∀ r, ¬ LocalEntryWrites r → ¬ (10 ≤ r ∧ r ≤ 16) → u.regs r = s.regs r := hufr
        obtain ⟨u', j, ev, hj, hur', h16, h16W, hm', he', hfr', hkr', hk'⟩ :=
          localEntry_spec hW shape u hur (by rw [ufr 2 (by decide) (by decide), hone])
            bs bc Bm M mc LC (u.regs 14) rfl
            (by rw [ufr 58 (by decide) (by decide), h58]) (by rw [ufr 31 (by decide) (by decide), h31])
            (by rw [ufr 32 (by decide) (by decide), h32]) (by rw [ufr 135 (by decide) (by decide), h135])
            hM1 hLC1 hLCW hslot' (by omega) (by omega) hBW
            (fun l b hl hb => by
              have hb' : b < bc := by have := Nat.two_pow_pos l; omega
              have hrow := row_lt (L := LC) hb' hl
              rw [humem _ (by omega)]
              exact hmemo l b hl hb)
        refine ⟨u', j, ev, hj, hur', h16, h16W, hm', he', fun r hr h16r => ?_, hkr', hk'⟩
        exact hfr' r (fun h => hr (Or.inl h)) (fun h => hr (Or.inr (Or.inl h)))
          (fun h => hr (Or.inr (Or.inr (Or.inl h)))) (fun h => hr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
          (fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
          (fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))) h16r)
  rw [show ((rLSCNT : Operand) : Nat) = 62 from rfl, show ((rOW : Operand) : Nat) = 58 from rfl,
    h62, h58] at hk hem
  exact ⟨s', k, e, hk, hr, hem, hfr, hkr, hks⟩

/-- **Global sparse table.** -/
theorem globalSparseTable_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2)
    (bs bc Gb M mc GLC BAW : Nat) (h33 : s.regs 33 = mc) (h31 : s.regs 31 = M)
    (h32 : s.regs 32 = bc) (h136 : s.regs 136 = Gb) (h63 : s.regs 63 = GLC * mc)
    (h60 : s.regs 60 = BAW)
    (hmc : mc = bc / M + 1) (hmc1 : 1 ≤ mc) (hM1 : 1 ≤ M) (hGLCW : GLC < W)
    (hcapE : GLC * mc + (mc + 2 ^ GLC) * M < 2 ^ W) (hbcW : bc < 2 ^ W) (hBAWW : BAW < 2 ^ W)
    (hextT : s.extent + GLC * mc * BAW < 2 ^ W)
    (hext : Gb + GLC * mc ≤ s.extent) (hGW : Gb + GLC * mc < 2 ^ W)
    (hmemo : ∀ l m, l < GLC → (m + 2 ^ l) * M ≤ bc →
      s.memory (Gb + l * mc + m) = some (bpRangeArgMinBlock shape bs (m * M) (2 ^ l * M))) :
    ∃ s' k, SafeEval W (emitTable rGSCNT rBAW globalEntryBlock) s s' k ∧
      k ≤ GLC * mc * (17 + 7 * BAW + 7) + 3 ∧ s'.status = .running ∧
      Emits s s' ((tableBits (bpGlobalSparseBlockEntries shape bs bc M mc GLC) BAW).map
        SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ GlobalEntryWrites r → ¬ (10 ≤ r ∧ r ≤ 16) → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  obtain ⟨s', k, e, hk, hr, hem, hfr, hkr, hks⟩ :=
    emitTable_spec hW rGSCNT rBAW globalEntryBlock
      (fun slot => bpGlobalSparseCellBlock shape bs bc M mc (slot % mc) (slot / mc)) 17
      GlobalEntryWrites
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s hrun hone htwo
      (by
        show s.regs 63 + 1 < 2 ^ W
        rw [h63]
        have h1 : 1 ≤ (mc + 2 ^ GLC) * M :=
          Nat.le_trans (Nat.le_trans hmc1 (Nat.le_add_right _ _))
            (Nat.le_mul_of_pos_right (mc + 2 ^ GLC) hM1)
        omega)
      (by show s.regs 60 < 2 ^ W; rw [h60]; exact hBAWW)
      (by show s.extent + s.regs 63 * s.regs 60 < 2 ^ W; rw [h63, h60]; exact hextT)
      (by
        intro u hur hufr humem hue huk hukr hslot
        have hslot' : u.regs 14 < GLC * mc := by
          have : u.regs 14 < s.regs 63 := hslot; rwa [h63] at this
        have ufr : ∀ r, ¬ GlobalEntryWrites r → ¬ (10 ≤ r ∧ r ≤ 16) → u.regs r = s.regs r := hufr
        obtain ⟨u', j, ev, hj, hur', h16, h16W, hm', he', hfr', hkr', hk'⟩ :=
          globalEntry_spec hW shape u hur (by rw [ufr 2 (by decide) (by decide), hone])
            bs bc Gb M mc GLC (u.regs 14) rfl
            (by rw [ufr 33 (by decide) (by decide), h33]) (by rw [ufr 31 (by decide) (by decide), h31])
            (by rw [ufr 32 (by decide) (by decide), h32]) (by rw [ufr 136 (by decide) (by decide), h136])
            hmc1 hM1 hGLCW hslot' (by omega) hbcW (by omega) hGW
            (fun l m hl hm => by
              have hmlt : m < mc := by
                have h1 : (m + 1) * M ≤ bc :=
                  Nat.le_trans (Nat.mul_le_mul_right M (by have := Nat.two_pow_pos l; omega)) hm
                have h2 : m + 1 ≤ bc / M := (Nat.le_div_iff_mul_le (by omega)).2 h1
                omega
              rw [humem _ (by have := row_lt (L := GLC) hmlt hl; omega)]
              exact hmemo l m hl hm)
        refine ⟨u', j, ev, hj, hur', h16, h16W, hm', he', fun r hr h16r => ?_, hkr', hk'⟩
        exact hfr' r (fun h => hr (Or.inl h)) (fun h => hr (Or.inr (Or.inl h)))
          (fun h => hr (Or.inr (Or.inr (Or.inl h)))) (fun h => hr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
          (fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
          (fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
          (fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))) h16r)
  rw [show ((rGSCNT : Operand) : Nat) = 63 from rfl, show ((rBAW : Operand) : Nat) = 60 from rfl,
    h63, h60] at hk hem
  exact ⟨s', k, e, hk, hr, hem, hfr, hkr, hks⟩

end RMQ.SuccinctFinal.PackedConstruction.Proof
