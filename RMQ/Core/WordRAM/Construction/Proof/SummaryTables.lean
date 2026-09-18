import RMQ.Core.WordRAM.Construction.Proof.BlockStats

/-! # PRE-1 builder proofs: the four summary tables (stage S4, first part)

Outside the builder firewall. From the block-statistics arrays that
`blockStatsBlock` leaves in memory, `summaryTablesBlock` emits the superblock
baseline table, the relative minimum and maximum tables and the argmin local
offset table, entry for entry equal to `bpSuperblockBaselineEntries`,
`bpBlockRelativeMinExcessEntries`, `bpBlockRelativeMaxExcessEntries` and
`bpBlockArgMinLocalOffsetEntries`. The two subtractions never underflow, by
`bpBlockMinExcess_baseline_le_add_span`, `bpBlockMaxExcess_baseline_le_add_span`
and `argAcc_ge`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose

/-! ## Single steps -/

/-- One register-only action as a state step. -/
theorem step_pure {W : Nat} (hW : 32 ≤ W) (a : Action) (v : State) (hrun : v.status = .running)
    (h : pureOK W a v.regs) :
    ∃ v', SafeEval W (.action a) v v' 1 ∧ v'.status = .running ∧ v'.regs = pureReg a v.regs ∧
      v'.memory = v.memory ∧ v'.extent = v.extent ∧ v'.keys = v.keys ∧
      v'.keyRegs = v.keyRegs := by
  refine ⟨_, EvalG.action a v hrun (pure_safe hW a v h), ?_⟩
  rw [pure_exec a v h]
  exact ⟨hrun, rfl, rfl, rfl, rfl, rfl⟩

/-- One load of an initialized cell below the extent as a state step. -/
theorem step_load {W : Nat} (hW : 32 ≤ W) (d addr : Operand) (v : State)
    (hrun : v.status = .running) {x : Nat} (ha : v.regs addr < v.extent)
    (hm : v.memory (v.regs addr) = some x) (hx : x < 2 ^ W) :
    ∃ v', SafeEval W (.action (.load d addr)) v v' 1 ∧ v'.status = .running ∧
      v'.regs = put v.regs d x ∧ v'.memory = v.memory ∧ v'.extent = v.extent ∧
      v'.keys = v.keys ∧ v'.keyRegs = v.keyRegs := by
  refine ⟨_, EvalG.action (P := Action.Safe W) (.load d addr) v hrun
    ⟨Prim.operandsFit_of_width _ hW, ha, x, hm, hx⟩, ?_⟩
  rw [show execPrim (Action.load d addr).prim v = _ from exec_load v d addr ha hm]
  exact ⟨hrun, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Entry blocks -/

/-- **Baseline entry.** `regs 16 := excess at the start of superblock slot`. -/
theorem baselineEntry_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (bps bs A0 bc slot : Nat)
    (h14 : u.regs 14 = slot) (h30 : u.regs 30 = bps) (h115 : u.regs 115 = A0)
    (hslot : slot * bps ≤ bc) (hA : A0 + bc < u.extent) (hAW : A0 + bc < 2 ^ W)
    (hlenW : shape.bpCode.length < 2 ^ W)
    (hmem : u.memory (A0 + slot * bps) = some (bpExcessAt shape (slot * bps * bs))) :
    ∃ u' j, SafeEval W baselineEntryBlock u u' j ∧ j ≤ 3 ∧ u'.status = .running ∧
      u'.regs 16 = bpExcessAt shape (blockStartOf bs (slot * bps)) ∧ u'.regs 16 < 2 ^ W ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 131 → r ≠ 16 → u'.regs r = u.regs r) ∧
      u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys := by
  obtain ⟨v1, e1, s1, r1, m1, x1, k1, kr1⟩ :=
    step_pure hW (.arithmetic .mul rT4 rSLOT rBASE) u hrun (by
      pre1_reg_simp [h14, h30]; omega)
  have v1r : v1.regs = put u.regs 131 (slot * bps) := by
    rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_131, operand_val_14, operand_val_30,
      h14, h30]
  obtain ⟨v2, e2, s2, r2, m2, x2, k2, kr2⟩ :=
    step_pure hW (.arithmetic .add rADDR rESB rT4) v1 s1 (by
      simp only [pureOK, Arithmetic.eval, operand_val_115, operand_val_131, v1r, put, reduceCtorEq,
        false_implies, false_or, and_true, if_true, if_false, Nat.reduceEqDiff, h115]
      omega)
  have v2r : v2.regs = put (put u.regs 131 (slot * bps)) 108 (A0 + slot * bps) := by
    rw [r2, v1r]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_115,
      operand_val_131, put_same, put_ne _ _ (show (115 : Nat) ≠ 131 by decide), h115]
  have hx := bpExcessAt_le_length shape (slot * bps * bs)
  obtain ⟨v3, e3, s3, r3, m3, x3, k3, kr3⟩ :=
    step_load hW rENT rADDR v2 s2
      (by show v2.regs 108 < v2.extent; rw [v2r, put_same, x2, x1]; omega)
      (by show v2.memory (v2.regs 108) = _; rw [v2r, put_same, m2, m1]; exact hmem)
      (by omega)
  refine ⟨v3, 1 + (1 + 1), EvalG.seq e1 (EvalG.seq e2 e3), by omega, s3, ?_, ?_, ?_, ?_, ?_,
    by rw [kr3, kr2, kr1], by rw [k3, k2, k1]⟩
  · show v3.regs 16 = _; rw [r3, operand_val_16, put_same]; rfl
  · show v3.regs 16 < _; rw [r3, operand_val_16, put_same]; omega
  · rw [m3, m2, m1]
  · rw [x3, x2, x1]
  · intro r h108 h131 h16
    rw [r3, operand_val_16, put_ne _ _ h16, v2r, put_ne _ _ h108, put_ne _ _ h131]

/-- **Relative entry.** `regs 16 := value + span - baseline` for the stat array
at register `statBase`. -/
theorem relativeEntry_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (statBase : Operand)
    (hsb131 : (statBase : Nat) ≠ 131) (hsb132 : (statBase : Nat) ≠ 132)
    (hsb108 : (statBase : Nat) ≠ 108) (u : State) (hrun : u.status = .running)
    (bps bs A0 S bc slot value : Nat)
    (h14 : u.regs 14 = slot) (h30 : u.regs 30 = bps) (h115 : u.regs 115 = A0)
    (hS : u.regs statBase = S) (h133 : u.regs 133 = bps * bs) (hbps : 0 < bps)
    (hslot : slot < bc) (hA : A0 + bc < u.extent) (hSe : S + bc ≤ u.extent)
    (hAW : A0 + bc < 2 ^ W) (hSW : S + bc < 2 ^ W)
    (hsum : shape.bpCode.length + bps * bs < 2 ^ W)
    (hvalue : value ≤ shape.bpCode.length)
    (hm0 : u.memory (A0 + slot / bps * bps) = some (bpExcessAt shape (slot / bps * bps * bs)))
    (hm1 : u.memory (S + slot) = some value)
    (hle : bpExcessAt shape (bpSuperblockStartPos bs bps slot) ≤
      value + bpSuperblockSpan bs bps) :
    ∃ u' j, SafeEval W (relativeEntryBlock statBase) u u' j ∧ j ≤ 8 ∧ u'.status = .running ∧
      u'.regs 16 = bpRelativeExcessEntry shape bs bps slot value ∧ u'.regs 16 < 2 ^ W ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 131 → r ≠ 132 → r ≠ 16 → u'.regs r = u.regs r) ∧
      u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys := by
  have hq : slot / bps * bps ≤ slot := Nat.div_mul_le_self slot bps
  have hql : slot / bps ≤ slot := Nat.div_le_self slot bps
  have hbase := bpExcessAt_le_length shape (slot / bps * bps * bs)
  generalize hqdef : slot / bps = q at hq hql hm0 hbase
  have hle' : bpExcessAt shape (q * bps * bs) ≤ value + bps * bs := by
    have := hle
    simp only [bpSuperblockStartPos, bpSuperblockStartBlock, blockStartOf, bpSuperblockSpan,
      hqdef] at this
    exact this
  -- div, mul
  obtain ⟨v1, e1, s1, r1, m1, x1, k1, kr1⟩ :=
    step_pure hW (.arithmetic .div rT4 rSLOT rBASE) u hrun (by
      pre1_reg_simp [h14, h30, hqdef]; omega)
  have v1r : v1.regs = put u.regs 131 q := by
    rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_131, operand_val_14, operand_val_30,
      h14, h30, hqdef]
  obtain ⟨v2, e2, s2, r2, m2, x2, k2, kr2⟩ :=
    step_pure hW (.arithmetic .mul rT4 rT4 rBASE) v1 s1 (by
      simp only [pureOK, Arithmetic.eval, operand_val_131, operand_val_30, v1r, put_same,
        put_ne _ _ (show (30 : Nat) ≠ 131 by decide), h30, reduceCtorEq, false_implies, false_or,
        and_true]
      omega)
  have v2r : v2.regs = put u.regs 131 (q * bps) := by
    rw [r2, v1r]; simp only [pureReg, Arithmetic.eval, operand_val_131, operand_val_30, put_same,
      put_ne _ _ (show (30 : Nat) ≠ 131 by decide), h30]
    funext r; simp only [put]; split <;> rfl
  -- baseline load
  obtain ⟨v3, e3, s3, r3, m3, x3, k3, kr3⟩ :=
    step_pure hW (.arithmetic .add rADDR rESB rT4) v2 s2 (by
      simp only [pureOK, Arithmetic.eval, operand_val_115, operand_val_131, v2r, put_same,
        put_ne _ _ (show (115 : Nat) ≠ 131 by decide), h115, reduceCtorEq, false_implies, false_or,
        and_true]
      omega)
  have v3r : v3.regs = put (put u.regs 131 (q * bps)) 108 (A0 + q * bps) := by
    rw [r3, v2r]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_115,
      operand_val_131, put_same, put_ne _ _ (show (115 : Nat) ≠ 131 by decide), h115]
  obtain ⟨v4, e4, s4, r4, m4, x4, k4, kr4⟩ :=
    step_load hW rT5 rADDR v3 s3
      (by show v3.regs 108 < v3.extent; rw [v3r, put_same, x3, x2, x1]; omega)
      (by show v3.memory (v3.regs 108) = _; rw [v3r, put_same, m3, m2, m1]; exact hm0)
      (by omega)
  have v4r : v4.regs = put (put (put u.regs 131 (q * bps)) 108 (A0 + q * bps)) 132
      (bpExcessAt shape (q * bps * bs)) := by
    rw [r4, v3r]; rfl
  -- stat load
  have v4S : v4.regs statBase = S := by
    rw [v4r, put_ne _ _ hsb132, put_ne _ _ hsb108, put_ne _ _ hsb131, hS]
  have v414 : v4.regs 14 = slot := by
    rw [v4r, put_ne _ _ (by decide), put_ne _ _ (by decide), put_ne _ _ (by decide), h14]
  obtain ⟨v5, e5, s5, r5, m5, x5, k5, kr5⟩ :=
    step_pure hW (.arithmetic .add rADDR statBase rSLOT) v4 s4 (by
      simp only [pureOK, Arithmetic.eval, operand_val_14, v4S, v414, reduceCtorEq, false_implies,
        false_or, and_true]
      omega)
  have v5r : v5.regs = put v4.regs 108 (S + slot) := by
    rw [r5]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_14, v4S, v414]
  obtain ⟨v6, e6, s6, r6, m6, x6, k6, kr6⟩ :=
    step_load hW rENT rADDR v5 s5
      (by show v5.regs 108 < v5.extent; rw [v5r, put_same, x5, x4, x3, x2, x1]; omega)
      (by show v5.memory (v5.regs 108) = _; rw [v5r, put_same, m5, m4, m3, m2, m1]; exact hm1)
      (by omega)
  have v6r : v6.regs = put (put v4.regs 108 (S + slot)) 16 value := by rw [r6, v5r]; rfl
  have v6_133 : v6.regs 133 = bps * bs := by
    rw [v6r, put_ne _ _ (by decide), put_ne _ _ (by decide), v4r, put_ne _ _ (by decide),
      put_ne _ _ (by decide), put_ne _ _ (by decide), h133]
  have v6_16 : v6.regs 16 = value := by rw [v6r, put_same]
  -- add span, subtract baseline
  obtain ⟨v7, e7, s7, r7, m7, x7, k7, kr7⟩ :=
    step_pure hW (.arithmetic .add rENT rENT rSPAN) v6 s6 (by
      simp only [pureOK, Arithmetic.eval, operand_val_16, operand_val_133, v6_16, v6_133,
        reduceCtorEq, false_implies, false_or, and_true]
      omega)
  have v7r : v7.regs = put v6.regs 16 (value + bps * bs) := by
    rw [r7]; simp only [pureReg, Arithmetic.eval, operand_val_16, operand_val_133, v6_16, v6_133]
  have v7_132 : v7.regs 132 = bpExcessAt shape (q * bps * bs) := by
    rw [v7r, put_ne _ _ (by decide), v6r, put_ne _ _ (by decide), put_ne _ _ (by decide), v4r,
      put_same]
  have v7_16 : v7.regs 16 = value + bps * bs := by rw [v7r, put_same]
  obtain ⟨v8, e8, s8, r8, m8, x8, k8, kr8⟩ :=
    step_pure hW (.arithmetic .sub rENT rENT rT5) v7 s7 (by
      simp only [pureOK, Arithmetic.eval, operand_val_16, operand_val_132, v7_16, v7_132,
        false_or, and_true, reduceCtorEq, false_implies]
      omega)
  have v8_16 : v8.regs 16 = value + bps * bs - bpExcessAt shape (q * bps * bs) := by
    rw [r8]; simp only [pureReg, Arithmetic.eval, operand_val_16, operand_val_132, v7_16, v7_132,
      put_same]
  refine ⟨v8, 1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))),
    EvalG.seq e1 (EvalG.seq e2 (EvalG.seq e3 (EvalG.seq e4 (EvalG.seq e5 (EvalG.seq e6
      (EvalG.seq e7 e8)))))), by omega, s8, ?_, ?_, ?_, ?_, ?_,
    by rw [kr8, kr7, kr6, kr5, kr4, kr3, kr2, kr1], by rw [k8, k7, k6, k5, k4, k3, k2, k1]⟩
  · rw [v8_16]
    show _ = value + bpSuperblockSpan bs bps - bpExcessAt shape (bpSuperblockStartPos bs bps slot)
    simp only [bpSuperblockStartPos, bpSuperblockStartBlock, blockStartOf, bpSuperblockSpan, hqdef]
  · rw [v8_16]; omega
  · rw [m8, m7, m6, m5, m4, m3, m2, m1]
  · rw [x8, x7, x6, x5, x4, x3, x2, x1]
  · intro r h108 h131 h132 h16
    rw [r8]
    simp only [pureReg, operand_val_16]
    rw [put_ne _ _ h16, v7r, put_ne _ _ h16, v6r, put_ne _ _ h16, put_ne _ _ h108, v4r,
      put_ne _ _ h132, put_ne _ _ h108, put_ne _ _ h131]

/-- **Argmin offset entry.** `regs 16 := argPos[slot] - slot * blockSize`. -/
theorem argOffsetEntry_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (bs A3 bc slot : Nat)
    (h14 : u.regs 14 = slot) (h56 : u.regs 56 = bs) (h118 : u.regs 118 = A3)
    (hslot : slot < bc) (hA : A3 + bc ≤ u.extent) (hAW : A3 + bc < 2 ^ W)
    (hcover : bc * bs ≤ shape.bpCode.length) (hlenW : shape.bpCode.length < 2 ^ W)
    (hmem : u.memory (A3 + slot) = some (bpBlockArgMinPrefixPos shape bs slot)) :
    ∃ u' j, SafeEval W argOffsetEntryBlock u u' j ∧ j ≤ 4 ∧ u'.status = .running ∧
      u'.regs 16 = bpBlockArgMinLocalOffset shape bs slot ∧ u'.regs 16 < 2 ^ W ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 131 → r ≠ 16 → u'.regs r = u.regs r) ∧
      u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys := by
  have hsb : slot * bs ≤ bc * bs := Nat.mul_le_mul_right bs (Nat.le_of_lt hslot)
  have harg := bpBlockArgMinPrefixPos_le_length shape bs slot
  have hge : slot * bs ≤ bpBlockArgMinPrefixPos shape bs slot := by
    have h := argAcc_ge shape (slot * bs) (by omega) (bs + 1)
    have hmin : Nat.min (slot * bs) shape.bpCode.length = slot * bs := Nat.min_eq_left (by omega)
    show slot * bs ≤ bpBlockArgMinPrefixPosFrom shape (blockStartOf bs slot) (bs + 1)
      (Nat.min (blockStartOf bs slot) shape.bpCode.length)
    rw [show blockStartOf bs slot = slot * bs from rfl, hmin, bpBlockArgMinPrefixPosFrom_eq_argAcc]
    exact h
  obtain ⟨v1, e1, s1, r1, m1, x1, k1, kr1⟩ :=
    step_pure hW (.arithmetic .add rADDR rARGB rSLOT) u hrun (by
      pre1_reg_simp [h14, h118]; omega)
  have v1r : v1.regs = put u.regs 108 (A3 + slot) := by
    rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_118, operand_val_14,
      h14, h118]
  obtain ⟨v2, e2, s2, r2, m2, x2, k2, kr2⟩ :=
    step_load hW rENT rADDR v1 s1
      (by show v1.regs 108 < v1.extent; rw [v1r, put_same, x1]; omega)
      (by show v1.memory (v1.regs 108) = _; rw [v1r, put_same, m1]; exact hmem)
      (by omega)
  have v2r : v2.regs = put (put u.regs 108 (A3 + slot)) 16 (bpBlockArgMinPrefixPos shape bs slot) := by
    rw [r2, v1r]; rfl
  have v2_14 : v2.regs 14 = slot := by
    rw [v2r, put_ne _ _ (by decide), put_ne _ _ (by decide), h14]
  have v2_56 : v2.regs 56 = bs := by
    rw [v2r, put_ne _ _ (by decide), put_ne _ _ (by decide), h56]
  obtain ⟨v3, e3, s3, r3, m3, x3, k3, kr3⟩ :=
    step_pure hW (.arithmetic .mul rT4 rSLOT rBS2) v2 s2 (by
      simp only [pureOK, Arithmetic.eval, operand_val_14, operand_val_56, v2_14, v2_56,
        reduceCtorEq, false_implies, false_or, and_true]
      omega)
  have v3r : v3.regs = put v2.regs 131 (slot * bs) := by
    rw [r3]; simp only [pureReg, Arithmetic.eval, operand_val_131, operand_val_14, operand_val_56,
      v2_14, v2_56]
  have v3_16 : v3.regs 16 = bpBlockArgMinPrefixPos shape bs slot := by
    rw [v3r, put_ne _ _ (by decide), v2r, put_same]
  have v3_131 : v3.regs 131 = slot * bs := by rw [v3r, put_same]
  obtain ⟨v4, e4, s4, r4, m4, x4, k4, kr4⟩ :=
    step_pure hW (.arithmetic .sub rENT rENT rT4) v3 s3 (by
      simp only [pureOK, Arithmetic.eval, operand_val_16, operand_val_131, v3_16, v3_131,
        reduceCtorEq, false_implies, false_or, and_true]
      omega)
  have v4_16 : v4.regs 16 = bpBlockArgMinPrefixPos shape bs slot - slot * bs := by
    rw [r4]; simp only [pureReg, Arithmetic.eval, operand_val_16, operand_val_131, v3_16, v3_131,
      put_same]
  refine ⟨v4, 1 + (1 + (1 + 1)), EvalG.seq e1 (EvalG.seq e2 (EvalG.seq e3 e4)), by omega, s4,
    ?_, ?_, ?_, ?_, ?_, by rw [kr4, kr3, kr2, kr1], by rw [k4, k3, k2, k1]⟩
  · rw [v4_16]; rfl
  · rw [v4_16]; omega
  · rw [m4, m3, m2, m1]
  · rw [x4, x3, x2, x1]
  · intro r h108 h131 h16
    rw [r4]
    simp only [pureReg, operand_val_16]
    rw [put_ne _ _ h16, v3r, put_ne _ _ h131, v2r, put_ne _ _ h16, put_ne _ _ h108]

/-! ## The four tables -/

/-- Scratch writes of the baseline and argmin-offset entries. -/
abbrev BaselineWrites (r : Nat) : Prop := r = 108 ∨ r = 131

/-- Scratch writes of the relative entries. -/
abbrev RelativeWrites (r : Nat) : Prop := r = 108 ∨ r = 131 ∨ r = 132

/-- Registers the summary tables leave unchanged. -/
def SummaryFrame (r : Nat) : Prop :=
  ¬ (10 ≤ r ∧ r ≤ 16) ∧ r ≠ 108 ∧ r ≠ 131 ∧ r ≠ 132 ∧ r ≠ 133

/-- **Summary tables.** From the four statistics arrays, `summaryTablesBlock`
emits the baseline, relative minimum, relative maximum and argmin-offset tables
exactly as the reference entry lists define them. -/
theorem summaryTables_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2)
    (A0 A1 A2 A3 bps bs bc ssc sw rw : Nat)
    (h115 : s.regs 115 = A0) (h116 : s.regs 116 = A1) (h117 : s.regs 117 = A2)
    (h118 : s.regs 118 = A3) (h30 : s.regs 30 = bps) (h56 : s.regs 56 = bs)
    (h32 : s.regs 32 = bc) (h57 : s.regs 57 = ssc) (h39 : s.regs 39 = sw) (h61 : s.regs 61 = rw)
    (hbps : 0 < bps) (hssc : ssc = bc / bps + 1) (hcover : bc * bs ≤ shape.bpCode.length)
    (hA01 : A0 + bc + 1 ≤ A1) (hA12 : A1 + bc ≤ A2) (hA23 : A2 + bc ≤ A3)
    (hA3 : A3 + bc ≤ s.extent) (hcntW : bc + 2 < 2 ^ W)
    (hsum : shape.bpCode.length + bps * bs < 2 ^ W)
    (hcapT : s.extent + ssc * sw + bc * rw + bc * rw + bc * rw < 2 ^ W)
    (hswW : sw < 2 ^ W) (hrwW : rw < 2 ^ W)
    (hESB : ∀ b, b ≤ bc → s.memory (A0 + b) = some (bpExcessAt shape (b * bs)))
    (hMIN : ∀ b, b < bc → s.memory (A1 + b) = some (bpBlockMinExcess shape bs b))
    (hMAX : ∀ b, b < bc → s.memory (A2 + b) = some (bpBlockMaxExcess shape bs b))
    (hARG : ∀ b, b < bc → s.memory (A3 + b) = some (bpBlockArgMinPrefixPos shape bs b)) :
    ∃ s' j, SafeEval W summaryTablesBlock s s' j ∧
      j ≤ ssc * (7 * sw + 10) + bc * (21 * rw + 41) + 13 ∧ s'.status = .running ∧
      Emits s s' ((tableBits (bpSuperblockBaselineEntries shape bs bps ssc) sw ++
        tableBits (bpBlockRelativeMinExcessEntries shape bs bps bc) rw ++
        tableBits (bpBlockRelativeMaxExcessEntries shape bs bps bc) rw ++
        tableBits (bpBlockArgMinLocalOffsetEntries shape bs bc) rw).map SuccinctSpace.bitToNat) ∧
      (∀ r : Nat, SummaryFrame r → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  have hlenW : shape.bpCode.length < 2 ^ W := by omega
  -- span
  obtain ⟨s1, e1, s1r, r1, m1, x1, k1, kr1⟩ :=
    step_pure hW (.arithmetic .mul rSPAN rBASE rBS2) s hrun (by
      pre1_reg_simp [h30, h56]; omega)
  have s1R : ∀ r : Nat, s1.regs r = if r = 133 then bps * bs else s.regs r := by
    intro r; rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_133, operand_val_30,
      operand_val_56, h30, h56, put]
  have s1fr : ∀ r : Nat, r ≠ 133 → s1.regs r = s.regs r := fun r h => by rw [s1R, if_neg h]
  have s1_133 : s1.regs 133 = bps * bs := by rw [s1R, if_pos rfl]
  -- baseline table
  obtain ⟨s2, k2, E2ev, hk2, s2r, E2, s2fr, s2kr, s2k⟩ :=
    emitTable_spec hW rSSC rWS baselineEntryBlock
      (fun slot => bpExcessAt shape (blockStartOf bs (slot * bps))) 3 BaselineWrites
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s1 s1r (by rw [s1fr 2 (by decide), hone]) (by rw [s1fr 9 (by decide), htwo])
      (by show s1.regs 57 + 1 < 2 ^ W
          rw [s1fr 57 (by decide), h57, hssc]; have := Nat.div_le_self bc bps; omega)
      (by show s1.regs 39 < 2 ^ W; rw [s1fr 39 (by decide), h39]; exact hswW)
      (by show s1.extent + s1.regs 57 * s1.regs 39 < 2 ^ W
          rw [x1, s1fr 57 (by decide), s1fr 39 (by decide), h57, h39]; omega)
      (by
        intro u hur hufr humem hue huk hukr hslot
        have u30 : u.regs 30 = bps := by rw [hufr 30 (by decide) (by decide), s1fr 30 (by decide), h30]
        have u115 : u.regs 115 = A0 := by
          rw [hufr 115 (by decide) (by decide), s1fr 115 (by decide), h115]
        have hslot' : u.regs 14 < bc / bps + 1 := by
          have : u.regs 14 < s1.regs 57 := hslot
          rw [s1fr 57 (by decide), h57, hssc] at this; exact this
        have hmul : u.regs 14 * bps ≤ bc :=
          Nat.le_trans (Nat.mul_le_mul_right bps (show u.regs 14 ≤ bc / bps by omega))
            (Nat.div_mul_le_self bc bps)
        obtain ⟨u', j, ev, hj, hur', h16, h16W, hm', he', hfr', hkr', hk'⟩ :=
          baselineEntry_spec hW shape u hur bps bs A0 bc (u.regs 14) rfl u30 u115 hmul
            (by rw [x1] at hue; omega) (by omega) hlenW
            (by rw [humem _ (by rw [x1]; omega), m1]; exact hESB _ hmul)
        exact ⟨u', j, ev, hj, hur', h16, h16W, hm', he',
          fun r hr h16r => hfr' r (fun h => hr (Or.inl h)) (fun h => hr (Or.inr h)) h16r, hkr', hk'⟩)
  have c57 : s1.regs 57 = ssc := by rw [s1fr 57 (by decide), h57]
  have c39 : s1.regs 39 = sw := by rw [s1fr 39 (by decide), h39]
  simp only [operand_val_57, operand_val_39, c57, c39] at hk2 E2
  have s2fr' : ∀ r : Nat, ¬ BaselineWrites r → ¬ (10 ≤ r ∧ r ≤ 16) → r ≠ 133 →
      s2.regs r = s.regs r := fun r h1 h2 h3 => by rw [s2fr r h1 h2, s1fr r h3]
  have s2ext : s2.extent = s.extent + ssc * sw := by
    rw [E2.1, List.length_map, flatten_bits_length, List.length_map, List.length_range, x1]
  have s2mem : ∀ a, a < s.extent → s2.memory a = s.memory a := fun a ha => by
    rw [E2.memory_below (by rw [x1]; exact ha), m1]
  have s2_133 : s2.regs 133 = bps * bs := by rw [s2fr 133 (by decide) (by decide), s1_133]
  have s2_32 : s2.regs 32 = bc := by rw [s2fr' 32 (by decide) (by decide) (by decide), h32]
  have s2_61 : s2.regs 61 = rw := by rw [s2fr' 61 (by decide) (by decide) (by decide), h61]
  -- relative minimum table
  obtain ⟨s3, k3, E3ev, hk3, s3r, E3, s3fr, s3kr, s3k⟩ :=
    emitTable_spec hW rBLOCKS rRW (relativeEntryBlock rMINB)
      (fun slot => bpBlockRelativeMinExcess shape bs bps slot) 8 RelativeWrites
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s2 s2r (by rw [s2fr' 2 (by decide) (by decide) (by decide), hone])
      (by rw [s2fr' 9 (by decide) (by decide) (by decide), htwo])
      (by show s2.regs 32 + 1 < 2 ^ W; rw [s2_32]; omega)
      (by show s2.regs 61 < 2 ^ W; rw [s2_61]; exact hrwW)
      (by show s2.extent + s2.regs 32 * s2.regs 61 < 2 ^ W; rw [s2ext, s2_32, s2_61]; omega)
      (by
        intro u hur hufr humem hue huk hukr hslot
        have hsl : u.regs 14 < bc := by have : u.regs 14 < s2.regs 32 := hslot; rwa [s2_32] at this
        have ufr : ∀ r : Nat, ¬ RelativeWrites r → ¬ (10 ≤ r ∧ r ≤ 16) → r ≠ 133 →
            ¬ BaselineWrites r → u.regs r = s.regs r := fun r h1 h2 h3 h4 => by
          rw [hufr r h1 h2, s2fr' r h4 h2 h3]
        have hq : u.regs 14 / bps * bps ≤ u.regs 14 := Nat.div_mul_le_self _ _
        obtain ⟨u', j, ev, hj, hur', h16, h16W, hm', he', hfr', hkr', hk'⟩ :=
          relativeEntry_spec hW shape rMINB (by decide) (by decide) (by decide) u hur bps bs A0 A1 bc
            (u.regs 14) (bpBlockMinExcess shape bs (u.regs 14)) rfl
            (by rw [ufr 30 (by decide) (by decide) (by decide) (by decide), h30])
            (by rw [ufr 115 (by decide) (by decide) (by decide) (by decide), h115])
            (by show u.regs 116 = A1; rw [ufr 116 (by decide) (by decide) (by decide) (by decide), h116])
            (by rw [hufr 133 (by decide) (by decide), s2_133]) hbps hsl
            (by rw [s2ext] at hue; omega) (by rw [s2ext] at hue; omega) (by omega) (by omega) hsum
            (bpBlockMinExcess_le_length shape bs _)
            (by rw [humem _ (by rw [s2ext]; omega), s2mem _ (by omega)]; exact hESB _ (by omega))
            (by rw [humem _ (by rw [s2ext]; omega), s2mem _ (by omega)]; exact hMIN _ hsl)
            (bpBlockMinExcess_baseline_le_add_span shape hbps hsl hcover)
        exact ⟨u', j, ev, hj, hur', h16, h16W, hm', he',
          fun r hr h16r => hfr' r (fun h => hr (Or.inl h)) (fun h => hr (Or.inr (Or.inl h)))
            (fun h => hr (Or.inr (Or.inr h))) h16r, hkr', hk'⟩)
  simp only [operand_val_32, operand_val_61, s2_32, s2_61] at hk3 E3
  have s3fr' : ∀ r : Nat, ¬ RelativeWrites r → ¬ (10 ≤ r ∧ r ≤ 16) → r ≠ 133 →
      s3.regs r = s.regs r := fun r h1 h2 h3 => by
    rw [s3fr r h1 h2, s2fr' r (fun h => h1 (h.elim Or.inl (fun h => Or.inr (Or.inl h)))) h2 h3]
  have s3ext : s3.extent = s.extent + ssc * sw + bc * rw := by
    rw [E3.1, List.length_map, flatten_bits_length, List.length_map, List.length_range, s2ext]
  have s3mem : ∀ a, a < s.extent → s3.memory a = s.memory a := fun a ha => by
    rw [E3.memory_below (by rw [s2ext]; omega), s2mem a ha]
  have s3_133 : s3.regs 133 = bps * bs := by rw [s3fr 133 (by decide) (by decide), s2_133]
  have s3_32 : s3.regs 32 = bc := by rw [s3fr' 32 (by decide) (by decide) (by decide), h32]
  have s3_61 : s3.regs 61 = rw := by rw [s3fr' 61 (by decide) (by decide) (by decide), h61]
  -- relative maximum table
  obtain ⟨s4, k4, E4ev, hk4, s4r, E4, s4fr, s4kr, s4k⟩ :=
    emitTable_spec hW rBLOCKS rRW (relativeEntryBlock rMAXB)
      (fun slot => bpBlockRelativeMaxExcess shape bs bps slot) 8 RelativeWrites
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s3 s3r (by rw [s3fr' 2 (by decide) (by decide) (by decide), hone])
      (by rw [s3fr' 9 (by decide) (by decide) (by decide), htwo])
      (by show s3.regs 32 + 1 < 2 ^ W; rw [s3_32]; omega)
      (by show s3.regs 61 < 2 ^ W; rw [s3_61]; exact hrwW)
      (by show s3.extent + s3.regs 32 * s3.regs 61 < 2 ^ W; rw [s3ext, s3_32, s3_61]; omega)
      (by
        intro u hur hufr humem hue huk hukr hslot
        have hsl : u.regs 14 < bc := by have : u.regs 14 < s3.regs 32 := hslot; rwa [s3_32] at this
        have ufr : ∀ r : Nat, ¬ RelativeWrites r → ¬ (10 ≤ r ∧ r ≤ 16) → r ≠ 133 →
            u.regs r = s.regs r := fun r h1 h2 h3 => by
          rw [hufr r h1 h2, s3fr' r h1 h2 h3]
        have hq : u.regs 14 / bps * bps ≤ u.regs 14 := Nat.div_mul_le_self _ _
        obtain ⟨u', j, ev, hj, hur', h16, h16W, hm', he', hfr', hkr', hk'⟩ :=
          relativeEntry_spec hW shape rMAXB (by decide) (by decide) (by decide) u hur bps bs A0 A2 bc
            (u.regs 14) (bpBlockMaxExcess shape bs (u.regs 14)) rfl
            (by rw [ufr 30 (by decide) (by decide) (by decide), h30])
            (by rw [ufr 115 (by decide) (by decide) (by decide), h115])
            (by show u.regs 117 = A2; rw [ufr 117 (by decide) (by decide) (by decide), h117])
            (by rw [hufr 133 (by decide) (by decide), s3_133]) hbps hsl
            (by rw [s3ext] at hue; omega) (by rw [s3ext] at hue; omega) (by omega) (by omega) hsum
            (bpBlockMaxExcess_le_length shape bs _)
            (by rw [humem _ (by rw [s3ext]; omega), s3mem _ (by omega)]; exact hESB _ (by omega))
            (by rw [humem _ (by rw [s3ext]; omega), s3mem _ (by omega)]; exact hMAX _ hsl)
            (bpBlockMaxExcess_baseline_le_add_span shape hbps hsl hcover)
        exact ⟨u', j, ev, hj, hur', h16, h16W, hm', he',
          fun r hr h16r => hfr' r (fun h => hr (Or.inl h)) (fun h => hr (Or.inr (Or.inl h)))
            (fun h => hr (Or.inr (Or.inr h))) h16r, hkr', hk'⟩)
  simp only [operand_val_32, operand_val_61, s3_32, s3_61] at hk4 E4
  have s4fr' : ∀ r : Nat, ¬ RelativeWrites r → ¬ (10 ≤ r ∧ r ≤ 16) → r ≠ 133 →
      s4.regs r = s.regs r := fun r h1 h2 h3 => by rw [s4fr r h1 h2, s3fr' r h1 h2 h3]
  have s4ext : s4.extent = s.extent + ssc * sw + bc * rw + bc * rw := by
    rw [E4.1, List.length_map, flatten_bits_length, List.length_map, List.length_range, s3ext]
  have s4mem : ∀ a, a < s.extent → s4.memory a = s.memory a := fun a ha => by
    rw [E4.memory_below (by rw [s3ext]; omega), s3mem a ha]
  have s4_32 : s4.regs 32 = bc := by rw [s4fr' 32 (by decide) (by decide) (by decide), h32]
  have s4_61 : s4.regs 61 = rw := by rw [s4fr' 61 (by decide) (by decide) (by decide), h61]
  -- argmin offset table
  obtain ⟨s5, k5, E5ev, hk5, s5r, E5, s5fr, s5kr, s5k⟩ :=
    emitTable_spec hW rBLOCKS rRW argOffsetEntryBlock
      (fun slot => bpBlockArgMinLocalOffset shape bs slot) 4 BaselineWrites
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s4 s4r (by rw [s4fr' 2 (by decide) (by decide) (by decide), hone])
      (by rw [s4fr' 9 (by decide) (by decide) (by decide), htwo])
      (by show s4.regs 32 + 1 < 2 ^ W; rw [s4_32]; omega)
      (by show s4.regs 61 < 2 ^ W; rw [s4_61]; exact hrwW)
      (by show s4.extent + s4.regs 32 * s4.regs 61 < 2 ^ W; rw [s4ext, s4_32, s4_61]; omega)
      (by
        intro u hur hufr humem hue huk hukr hslot
        have hsl : u.regs 14 < bc := by have : u.regs 14 < s4.regs 32 := hslot; rwa [s4_32] at this
        have ufr : ∀ r : Nat, ¬ RelativeWrites r → ¬ (10 ≤ r ∧ r ≤ 16) → r ≠ 133 →
            u.regs r = s.regs r := fun r h1 h2 h3 => by
          rw [hufr r (fun h => h1 (h.elim Or.inl (fun h => Or.inr (Or.inl h)))) h2, s4fr' r h1 h2 h3]
        obtain ⟨u', j, ev, hj, hur', h16, h16W, hm', he', hfr', hkr', hk'⟩ :=
          argOffsetEntry_spec hW shape u hur bs A3 bc (u.regs 14) rfl
            (by rw [ufr 56 (by decide) (by decide) (by decide), h56])
            (by rw [ufr 118 (by decide) (by decide) (by decide), h118]) hsl
            (by rw [s4ext] at hue; omega) (by omega) hcover hlenW
            (by rw [humem _ (by rw [s4ext]; omega), s4mem _ (by omega)]; exact hARG _ hsl)
        exact ⟨u', j, ev, hj, hur', h16, h16W, hm', he',
          fun r hr h16r => hfr' r (fun h => hr (Or.inl h)) (fun h => hr (Or.inr h)) h16r, hkr', hk'⟩)
  simp only [operand_val_32, operand_val_61, s4_32, s4_61] at hk5 E5
  refine ⟨s5, 1 + (k2 + (k3 + (k4 + k5))),
    EvalG.seq e1 (EvalG.seq E2ev (EvalG.seq E3ev (EvalG.seq E4ev E5ev))), ?_, s5r, ?_, ?_,
    by rw [s5kr, s4kr, s3kr, s2kr, kr1], by rw [s5k, s4k, s3k, s2k, k1]⟩
  · have c1 : ssc * (3 + 7 * sw + 7) = ssc * (7 * sw + 10) := by congr 1; omega
    have c2 : bc * (8 + 7 * rw + 7) + bc * (8 + 7 * rw + 7) + bc * (4 + 7 * rw + 7) =
        bc * (21 * rw + 41) := by
      rw [← Nat.mul_add, ← Nat.mul_add]; congr 1; omega
    omega
  · have e01 : Emits s s1 [] := Emits.of_eq x1 m1
    have := (((e01.trans E2).trans E3).trans E4).trans E5
    simp only [List.nil_append, List.map_append, List.append_assoc] at this ⊢
    exact this
  · intro r ⟨h1, h2, h3, h4, h5⟩
    have hrw : ¬ RelativeWrites r := by
      intro h; rcases h with h | h | h
      · exact h2 h
      · exact h3 h
      · exact h4 h
    rw [s5fr r (fun h => hrw (h.elim Or.inl (fun h => Or.inr (Or.inl h)))) h1, s4fr' r hrw h1 h5]

end RMQ.SuccinctFinal.PackedConstruction.Proof
