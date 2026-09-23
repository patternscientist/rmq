import RMQ.Core.WordRAM.Construction.Proof.BPEmit
import RMQ.Core.WordRAM.Construction.Spec.BlockStats

/-! # PRE-1 builder proofs: block statistics (stage S4, first part)

Outside the builder firewall. From the BP cells of a shape in a memory region,
`blockStatsBlock` sweeps the prefix excess block by block and stores, for every
block, its start excess, its minimum and maximum sampled excess and its leftmost
argmin sample position, exactly as `bpExcessAt`, `bpBlockMinExcess`,
`bpBlockMaxExcess` and `bpBlockArgMinPrefixPos` define them. The four summary
tables are then emitted from these arrays.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose

/-- Evaluate straight-line register actions at literal registers 0-199. -/
syntax "pre1_reg_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pre1_reg_simp [$hs,*]) => do
    let hs' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar,
      `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] "," := ⟨hs.elemsAndSeps⟩
    `(tactic| simp only [pureOKs, pureOK, pureRegs, pureReg, wordBitsF, log2F, put,
      Arithmetic.eval, Comparison.eval, reduceCtorEq, false_implies, false_or, or_false,
      and_true, true_and, implies_true, ite_true, ite_false, ↓reduceIte, Nat.reduceEqDiff,
      Nat.reduceAdd, List.cons_append, List.nil_append, minActs, maxActs,
      operand_val_0, operand_val_1, operand_val_2, operand_val_3, operand_val_4, operand_val_5, operand_val_6, operand_val_7, operand_val_8, operand_val_9, operand_val_10, operand_val_11, operand_val_12, operand_val_13, operand_val_14, operand_val_15, operand_val_16, operand_val_17, operand_val_18, operand_val_19, operand_val_20, operand_val_21, operand_val_22, operand_val_23, operand_val_24, operand_val_25, operand_val_26, operand_val_27, operand_val_28, operand_val_29, operand_val_30, operand_val_31, operand_val_32, operand_val_33, operand_val_34, operand_val_35, operand_val_36, operand_val_37, operand_val_38, operand_val_39, operand_val_40, operand_val_41, operand_val_42, operand_val_43, operand_val_44, operand_val_45, operand_val_46, operand_val_47, operand_val_48, operand_val_49, operand_val_50, operand_val_51, operand_val_52, operand_val_53, operand_val_54, operand_val_55, operand_val_56, operand_val_57, operand_val_58, operand_val_59, operand_val_60, operand_val_61, operand_val_62, operand_val_63, operand_val_64, operand_val_65, operand_val_66, operand_val_67, operand_val_68, operand_val_69, operand_val_70, operand_val_71, operand_val_72, operand_val_73, operand_val_74, operand_val_75, operand_val_76, operand_val_77, operand_val_78, operand_val_79, operand_val_80, operand_val_81, operand_val_82, operand_val_83, operand_val_84, operand_val_85, operand_val_86, operand_val_87, operand_val_88, operand_val_89, operand_val_90, operand_val_91, operand_val_92, operand_val_93, operand_val_94, operand_val_95, operand_val_96, operand_val_97, operand_val_98, operand_val_99, operand_val_100, operand_val_101, operand_val_102, operand_val_103, operand_val_104, operand_val_105, operand_val_106, operand_val_107, operand_val_108, operand_val_109, operand_val_110, operand_val_111, operand_val_112, operand_val_113, operand_val_114, operand_val_115, operand_val_116, operand_val_117, operand_val_118, operand_val_119, operand_val_120, operand_val_121, operand_val_122, operand_val_123, operand_val_124, operand_val_125, operand_val_126, operand_val_127, operand_val_128, operand_val_129, operand_val_130, operand_val_131, operand_val_132, operand_val_133, operand_val_134, operand_val_135, operand_val_136, operand_val_137, operand_val_138, operand_val_139, operand_val_140, operand_val_141, operand_val_142, operand_val_143, operand_val_144, operand_val_145, operand_val_146, operand_val_147, operand_val_148, operand_val_149, operand_val_150, operand_val_151, operand_val_152, operand_val_153, operand_val_154, operand_val_155, operand_val_156, operand_val_157, operand_val_158, operand_val_159, operand_val_160, operand_val_161, operand_val_162, operand_val_163, operand_val_164, operand_val_165, operand_val_166, operand_val_167, operand_val_168, operand_val_169, operand_val_170, operand_val_171, operand_val_172, operand_val_173, operand_val_174, operand_val_175, operand_val_176, operand_val_177, operand_val_178, operand_val_179, operand_val_180, operand_val_181, operand_val_182, operand_val_183, operand_val_184, operand_val_185, operand_val_186, operand_val_187, operand_val_188, operand_val_189, operand_val_190, operand_val_191, operand_val_192, operand_val_193, operand_val_194, operand_val_195, operand_val_196, operand_val_197, operand_val_198, operand_val_199, $hs',*])

/-- The BP cells of a shape as 0/1 values. -/
def bpCell (shape : CartesianShape) (k : Nat) : Nat :=
  (shape.bpCode.map SuccinctSpace.bitToNat).getD k 0

theorem bpCell_eq (shape : CartesianShape) {k : Nat} (hk : k < shape.bpCode.length) :
    bpCell shape k = if shape.bpCode[k] then 1 else 0 := by
  simp [bpCell, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, SuccinctSpace.bitToNat]

theorem bpCell_excess (shape : CartesianShape) {p : Nat} (hp : p < shape.bpCode.length) :
    bpExcessAt shape p + bpCell shape p + bpCell shape p - 1 = bpExcessAt shape (p + 1) ∧
      1 ≤ bpExcessAt shape p + bpCell shape p + bpCell shape p := by
  obtain ⟨hopen, hclose⟩ := excess_step shape hp
  rw [bpCell_eq shape hp]
  cases h : shape.bpCode[p]
  · obtain ⟨h1, h2⟩ := hclose h
    simp; omega
  · have := hopen h
    simp; omega

/-- **One sample.** -/
theorem sampleBody_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1) (B : Nat) (hB : u.regs 119 = B)
    (hR : Region u B shape.bpCode.length (bpCell shape))
    (hext : B + shape.bpCode.length ≤ u.extent) (hcap : B + 4 * shape.bpCode.length + 4 < 2 ^ W)
    (bs k p : Nat) (hbs : u.regs 56 = bs) (hk : u.regs 123 = k)
    (hp : u.regs 129 = p) (hpk : k < bs → p < shape.bpCode.length) (hple : p ≤ shape.bpCode.length)
    (hex : u.regs 120 = bpExcessAt shape p) (mn mx best : Nat) (hmn : u.regs 125 = mn)
    (hmx : u.regs 126 = mx) (hmxle : mx ≤ shape.bpCode.length) (hmnle : mn ≤ shape.bpCode.length)
    (hbest : u.regs 127 = best) (hbeste : u.regs 128 = bpExcessAt shape best) :
    ∃ u' j, SafeEval W sampleBodyBlock u u' j ∧ j ≤ 24 ∧ u'.status = .running ∧
      u'.regs 125 = Nat.min mn (bpExcessAt shape p) ∧
      u'.regs 126 = Nat.max mx (bpExcessAt shape p) ∧
      u'.regs 127 = argStep shape p best ∧
      u'.regs 128 = bpExcessAt shape (argStep shape p best) ∧
      u'.regs 129 = (if k < bs then p + 1 else p) ∧
      u'.regs 120 = bpExcessAt shape (if k < bs then p + 1 else p) ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 120 → ¬ (125 ≤ r ∧ r ≤ 131) →
        u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys := by
  have hW32 : 2 ^ 32 ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
  have hexle := bpExcessAt_le_length shape p
  have hbestle := bpExcessAt_le_length shape best
  generalize hev : bpExcessAt shape p = e at hex hexle
  generalize hbev : bpExcessAt shape best = be at hbeste hbestle
  -- min, max, compare
  obtain ⟨u1, j1, e1, hj1, hu1r, hu1R, hu1m, hu1e, hu1k, hu1kr⟩ :=
    RegSpec.pure hW (minActs rMN rMN rEX ++ maxActs rMX rMX rEX ++ [.comparison .lt rT4 rEX rBESTE])
      u hrun (by
        pre1_reg_simp [minActs, maxActs, hmn, hex, hmx, hbeste, hone]
        repeat' apply And.intro
        all_goals first | omega | (split <;> omega))
  have hmin : Nat.min mn e = (if mn < e then 1 else 0) * mn + (1 - if mn < e then 1 else 0) * e := by
    simp only [Nat.min_def]; split <;> split <;> omega
  have hmax : Nat.max mx e = (if mx < e then 1 else 0) * e + (1 - if mx < e then 1 else 0) * mx := by
    simp only [Nat.max_def]; split <;> split <;> omega
  have u1_125 : u1.regs 125 = Nat.min mn e := by
    rw [hu1R, hmin]; pre1_reg_simp [minActs, maxActs, hmn, hex, hmx, hbeste, hone]
  have u1_126 : u1.regs 126 = Nat.max mx e := by
    rw [hu1R, hmax]; pre1_reg_simp [minActs, maxActs, hmn, hex, hmx, hbeste, hone]
  have u1_131 : u1.regs 131 = if e < be then 1 else 0 := by
    rw [hu1R]; pre1_reg_simp [minActs, maxActs, hmn, hex, hmx, hbeste, hone]
  have u1fr : ∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 125 → r ≠ 126 → r ≠ 131 → u1.regs r = u.regs r := by
    intro r h1 h2 h3 h4
    rw [hu1R]
    apply pureRegs_frame
    intro a ha hax
    simp [minActs, maxActs] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [pureDst] at hax <;> omega
  -- conditional argmin update
  have hp' : Nat.min p shape.bpCode.length = p := Nat.min_eq_left hple
  have hstep : argStep shape p best = if e < be then p else best := by
    unfold argStep; rw [hp', hev, hbev]
  obtain ⟨u2, j2, e2, hj2, hu2r, hu2_127, hu2_128, hu2fr, hu2m, hu2e, hu2k⟩ :
      ∃ u2 j2, SafeEval W (.ifZero rT4 .skip (acts [.move rBEST rPOS, .move rBESTE rEX])) u1 u2 j2 ∧
        j2 ≤ 4 ∧ u2.status = .running ∧ u2.regs 127 = (if e < be then p else best) ∧
        u2.regs 128 = (if e < be then e else be) ∧
        (∀ r : Nat, r ≠ 127 → r ≠ 128 → u2.regs r = u1.regs r) ∧
        u2.memory = u1.memory ∧ u2.extent = u1.extent ∧ u2.keys = u1.keys := by
    have u1_129 : u1.regs 129 = p := by
      rw [u1fr 129 (by omega) (by omega) (by omega) (by omega), hp]
    have u1_120 : u1.regs 120 = e := by
      rw [u1fr 120 (by omega) (by omega) (by omega) (by omega), hex]
    have u1_127 : u1.regs 127 = best := by
      rw [u1fr 127 (by omega) (by omega) (by omega) (by omega), hbest]
    have u1_128 : u1.regs 128 = be := by
      rw [u1fr 128 (by omega) (by omega) (by omega) (by omega), hbeste]
    by_cases hlt : e < be
    · have hc : u1.regs rT4 ≠ 0 := by show u1.regs 131 ≠ 0; rw [u1_131, if_pos hlt]; decide
      obtain ⟨w, jw, ew, hjw, hwr, hwR, hwm, hwe, hwk, _⟩ :=
        RegSpec.pure hW [.move rBEST rPOS, .move rBESTE rEX] u1 hu1r (by pre1_reg_simp [])
      refine ⟨w, jw + 2, EvalG.ifZeroFallthrough hu1r hc ew hwr, by simp at hjw; omega, hwr, ?_, ?_,
        ?_, hwm, hwe, hwk⟩
      · rw [hwR, if_pos hlt]; pre1_reg_simp [u1_129]
      · rw [hwR, if_pos hlt]; pre1_reg_simp [u1_120]
      · intro r h127 h128; rw [hwR]; pre1_reg_simp [h127, h128]
    · have hc : u1.regs rT4 = 0 := by show u1.regs 131 = 0; rw [u1_131, if_neg hlt]
      refine ⟨u1, 0 + 1, EvalG.ifZeroTaken hu1r hc (EvalG.skip u1 hu1r), by omega, hu1r, ?_, ?_,
        fun _ _ _ => rfl, rfl, rfl, rfl⟩
      · rw [if_neg hlt, u1_127]
      · rw [if_neg hlt, u1_128]
  -- compare offset with block size
  obtain ⟨u3, j3, e3, hj3, hu3r, hu3R, hu3m, hu3e, hu3k, _⟩ :=
    RegSpec.pure hW [.comparison .lt rT4 rOFF rBS2] u2 hu2r (by pre1_reg_simp [])
  have u2_123 : u2.regs 123 = k := by
    rw [hu2fr 123 (by omega) (by omega), u1fr 123 (by omega) (by omega) (by omega) (by omega), hk]
  have u2_56 : u2.regs 56 = bs := by
    rw [hu2fr 56 (by omega) (by omega), u1fr 56 (by omega) (by omega) (by omega) (by omega), hbs]
  have u3_131 : u3.regs 131 = if k < bs then 1 else 0 := by
    rw [hu3R]; pre1_reg_simp [u2_123, u2_56]
  have u3fr : ∀ r : Nat, r ≠ 131 → u3.regs r = u2.regs r := by
    intro r h; rw [hu3R]; pre1_reg_simp [h]
  have u3_129 : u3.regs 129 = p := by
    rw [u3fr 129 (by omega), hu2fr 129 (by omega) (by omega),
      u1fr 129 (by omega) (by omega) (by omega) (by omega), hp]
  have u3_120 : u3.regs 120 = e := by
    rw [u3fr 120 (by omega), hu2fr 120 (by omega) (by omega),
      u1fr 120 (by omega) (by omega) (by omega) (by omega), hex]
  have u3_119 : u3.regs 119 = B := by
    rw [u3fr 119 (by omega), hu2fr 119 (by omega) (by omega),
      u1fr 119 (by omega) (by omega) (by omega) (by omega), hB]
  have u3_2 : u3.regs 2 = 1 := by
    rw [u3fr 2 (by omega), hu2fr 2 (by omega) (by omega),
      u1fr 2 (by omega) (by omega) (by omega) (by omega), hone]
  have hR3 : Region u3 B shape.bpCode.length (bpCell shape) := by
    intro a ha; rw [hu3m, hu2m, hu1m]; exact hR a ha
  have hext3 : B + shape.bpCode.length ≤ u3.extent := by rw [hu3e, hu2e, hu1e]; exact hext
  -- conditional advance
  obtain ⟨u4, j4, e4, hj4, hu4r, hu4_129, hu4_120, hu4fr, hu4m, hu4e, hu4k⟩ :
      ∃ u4 j4, SafeEval W (.ifZero rT4 .skip
          (acts [.arithmetic .add rADDR rBPB rPOS, .load rCELL rADDR,
            .arithmetic .add rEX rEX rCELL, .arithmetic .add rEX rEX rCELL,
            .arithmetic .sub rEX rEX rONE, .arithmetic .add rPOS rPOS rONE])) u3 u4 j4 ∧
        j4 ≤ 8 ∧ u4.status = .running ∧ u4.regs 129 = (if k < bs then p + 1 else p) ∧
        u4.regs 120 = bpExcessAt shape (if k < bs then p + 1 else p) ∧
        (∀ r : Nat, r ≠ 108 → r ≠ 120 → r ≠ 129 → r ≠ 130 → u4.regs r = u3.regs r) ∧
        u4.memory = u3.memory ∧ u4.extent = u3.extent ∧ u4.keys = u3.keys := by
    by_cases hkb : k < bs
    · have hc : u3.regs rT4 ≠ 0 := by show u3.regs 131 ≠ 0; rw [u3_131, if_pos hkb]; decide
      have hpn := hpk hkb
      obtain ⟨hstepE, hstep1⟩ := bpCell_excess shape hpn
      have hcell : bpCell shape p ≤ 1 := by rw [bpCell_eq shape hpn]; split <;> omega
      -- add rADDR rBPB rPOS
      let v1 := execPrim (Prim.arithmetic .add rADDR rBPB rPOS) u3
      have g1 := exec_arithmetic u3 .add rADDR rBPB rPOS
      have v1r : v1.regs = put u3.regs 108 (B + p) := by
        simp only [v1, g1, Arithmetic.eval]
        rw [show ((rBPB : Operand) : Nat) = 119 from rfl, show ((rPOS : Operand) : Nat) = 129 from rfl,
          u3_119, u3_129]; rfl
      have hRv1 : Region v1 B shape.bpCode.length (bpCell shape) := by
        intro a ha; simp only [v1, g1]; exact hR3 a ha
      have v1e : v1.extent = u3.extent := by simp [v1, g1]
      have v1a : v1.regs rADDR = B + p := by show v1.regs 108 = _; rw [v1r, put_same]
      let v2 := execPrim (Prim.load rCELL rADDR) v1
      have g2 := load_region hRv1 (by rw [v1e]; exact hext3) rCELL rADDR (a := p) hpn v1a
      have v2r : v2.regs = put (put u3.regs 108 (B + p)) 130 (bpCell shape p) := by
        simp only [v2, g2, v1r]; rfl
      have v2s : v2.status = .running := by simp only [v2, g2]; simp [v1, g1, hu3r]
      obtain ⟨hok4, hexec4⟩ := pure_acts_exec hW [.arithmetic .add rEX rEX rCELL,
          .arithmetic .add rEX rEX rCELL, .arithmetic .sub rEX rEX rONE,
          .arithmetic .add rPOS rPOS rONE] v2 v2s (by
            pre1_reg_simp [v2r, u3_120, u3_129, u3_2]
            repeat' apply And.intro
            all_goals omega)
      have v1s : v1.status = .running := by simp [v1, g1, hu3r]
      have hsafe : ActsOK (Action.Safe W) [.arithmetic .add rADDR rBPB rPOS, .load rCELL rADDR,
          .arithmetic .add rEX rEX rCELL, .arithmetic .add rEX rEX rCELL,
          .arithmetic .sub rEX rEX rONE, .arithmetic .add rPOS rPOS rONE] u3 := by
        refine ⟨safe_add hW u3 _ _ _ ?_, v1s, ?_⟩
        · show u3.regs 119 + u3.regs 129 < 2 ^ W
          rw [u3_119, u3_129]; omega
        exact ⟨safe_load_region hW hRv1 (by rw [v1e]; exact hext3) _ _ hpn v1a (by omega), v2s, hok4⟩
      have ev := acts_evalG (P := Action.Safe W) _ u3 hu3r hsafe
      have hw : execActs [.arithmetic .add rADDR rBPB rPOS, .load rCELL rADDR,
          .arithmetic .add rEX rEX rCELL, .arithmetic .add rEX rEX rCELL,
          .arithmetic .sub rEX rEX rONE, .arithmetic .add rPOS rPOS rONE] u3 =
          { v2 with regs := pureRegs [.arithmetic .add rEX rEX rCELL,
            .arithmetic .add rEX rEX rCELL, .arithmetic .sub rEX rEX rONE,
            .arithmetic .add rPOS rPOS rONE] v2.regs, pc := v2.pc + 4 } := hexec4
      rw [hw] at ev
      refine ⟨_, _ + 2, EvalG.ifZeroFallthrough hu3r hc ev v2s, by simp, v2s,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [if_pos hkb]; pre1_reg_simp [v2r, u3_129, u3_2]
      · rw [if_pos hkb, ← hstepE, hev]; pre1_reg_simp [v2r, u3_120, u3_2]
      · intro r h108 h120 h129 h130
        pre1_reg_simp [v2r, h108, h120, h129, h130]
      · show v2.memory = u3.memory
        simp only [v2, g2]; simp [v1, g1]
      · show v2.extent = u3.extent
        simp only [v2, g2]; simp [v1, g1]
      · show v2.keys = u3.keys
        simp only [v2, g2]; simp [v1, g1]
    · have hc : u3.regs rT4 = 0 := by show u3.regs 131 = 0; rw [u3_131, if_neg hkb]
      refine ⟨u3, 0 + 1, EvalG.ifZeroTaken hu3r hc (EvalG.skip u3 hu3r), by omega, hu3r, ?_, ?_,
        fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
      · rw [if_neg hkb, u3_129]
      · rw [if_neg hkb, u3_120, hev]
  refine ⟨u4, j1 + (j2 + (j3 + j4)), EvalG.seq e1 (EvalG.seq e2 (EvalG.seq e3 e4)), ?_, hu4r,
    ?_, ?_, ?_, ?_, hu4_129, hu4_120, ?_, ?_, ?_, ?_⟩
  · simp [minActs, maxActs] at hj1 hj3; omega
  · rw [hu4fr 125 (by omega) (by omega) (by omega) (by omega), u3fr 125 (by omega),
      hu2fr 125 (by omega) (by omega), u1_125]
  · rw [hu4fr 126 (by omega) (by omega) (by omega) (by omega), u3fr 126 (by omega),
      hu2fr 126 (by omega) (by omega), u1_126]
  · rw [hu4fr 127 (by omega) (by omega) (by omega) (by omega), u3fr 127 (by omega), hu2_127, hstep]
  · rw [hu4fr 128 (by omega) (by omega) (by omega) (by omega), u3fr 128 (by omega), hu2_128, hstep]
    split <;> simp_all
  · intro r h26 h108 h120 h125
    rw [hu4fr r h108 h120 (by omega) (by omega), u3fr r (by omega), hu2fr r (by omega) (by omega),
      u1fr r h26 (by omega) (by omega) (by omega)]
  · rw [hu4m, hu3m, hu2m, hu1m]
  · rw [hu4e, hu3e, hu2e, hu1e]
  · rw [hu4k, hu3k, hu2k, hu1k]

/-- The frame of the sample loop. -/
def SampleFrame (r : Nat) : Prop :=
  ¬ (26 ≤ r ∧ r ≤ 28) ∧ r ≠ 108 ∧ r ≠ 120 ∧ r ≠ 123 ∧ r ≠ 124 ∧ ¬ (125 ≤ r ∧ r ≤ 131)

/-- **The samples of one block.** From the block start `blk * bs` with the
running excess at that position, the offset loop leaves the block's minimum,
maximum and leftmost-argmin sample in registers 125-127 and the excess at the
block end in register 120, in at most `28 (bs + 1) + 3` steps. -/
theorem sampleLoop_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hone : s.regs 2 = 1) (B : Nat) (hB : s.regs 119 = B)
    (hR : Region s B shape.bpCode.length (bpCell shape))
    (hext : B + shape.bpCode.length ≤ s.extent) (hcap : B + 4 * shape.bpCode.length + 4 < 2 ^ W)
    (bs blk : Nat) (hbs : s.regs 56 = bs) (hbs1 : s.regs 134 = bs + 1)
    (hend : blk * bs + bs ≤ shape.bpCode.length)
    (hp : s.regs 129 = blk * bs) (hex : s.regs 120 = bpExcessAt shape (blk * bs))
    (hmn : s.regs 125 = shape.bpCode.length) (hmx : s.regs 126 = 0)
    (hbest : s.regs 127 = blk * bs) (hbeste : s.regs 128 = bpExcessAt shape (blk * bs)) :
    ∃ s' j, SafeEval W (forSlots rOFF rOGO rBS1 sampleBodyBlock) s s' j ∧
      j ≤ (bs + 1) * 28 + 3 ∧ s'.status = .running ∧
      s'.regs 125 = bpBlockMinExcess shape bs blk ∧
      s'.regs 126 = bpBlockMaxExcess shape bs blk ∧
      s'.regs 127 = bpBlockArgMinPrefixPos shape bs blk ∧
      s'.regs 120 = bpExcessAt shape (blk * bs + bs) ∧
      (∀ r : Nat, SampleFrame r → s'.regs r = s.regs r) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧ s'.keys = s.keys := by
  let len := shape.bpCode.length
  let start := blk * bs
  let f : Nat → Nat := fun off => bpExcessAt shape (start + off)
  let Inv : Nat → State → Prop := fun k u =>
    u.memory = s.memory ∧ u.extent = s.extent ∧ u.keys = s.keys ∧
      (∀ r : Nat, SampleFrame r → u.regs r = s.regs r) ∧
      u.regs 125 = natListMinFrom len ((List.range k).map f) ∧
      u.regs 126 = natListMax ((List.range k).map f) ∧
      u.regs 127 = argAcc shape start k start ∧
      u.regs 128 = bpExcessAt shape (argAcc shape start k start) ∧
      u.regs 129 = start + min k bs ∧
      u.regs 120 = bpExcessAt shape (start + min k bs) ∧
      u.regs 125 ≤ len ∧ u.regs 126 ≤ len
  have hargle : ∀ m, argAcc shape start m start ≤ len := by
    intro m
    induction m with
    | zero => show blk * bs ≤ shape.bpCode.length; omega
    | succ m ih =>
        show argStep shape (start + m) (argAcc shape start m start) ≤ len
        unfold argStep; split
        · exact Nat.min_le_right _ _
        · exact ih
  obtain ⟨s', k, e, hk, hr, hinv, _, _⟩ :=
    forSlots_spec hW rOFF rOGO rBS1 sampleBodyBlock 24
      (by decide) (by decide) (by decide) (by decide) (by decide) Inv s hrun hone
      (by show s.regs 134 < 2 ^ W; rw [hbs1]; omega)
      (by
        intro u _ hregs hm he hk _
        have fr : ∀ r : Nat, r ≠ 123 → r ≠ 124 → u.regs r = s.regs r := hregs
        refine ⟨hm, he, hk, fun r hr => fr r hr.2.2.2.1 hr.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [fr 125 (by decide) (by decide), hmn]; rfl
        · rw [fr 126 (by decide) (by decide), hmx]; rfl
        · rw [fr 127 (by decide) (by decide), hbest]; rfl
        · rw [fr 128 (by decide) (by decide), hbeste]; rfl
        · rw [fr 129 (by decide) (by decide), hp, Nat.min_eq_left (Nat.zero_le _)]; rfl
        · rw [fr 120 (by decide) (by decide), hex, Nat.min_eq_left (Nat.zero_le _)]; rfl
        · rw [fr 125 (by decide) (by decide), hmn]; exact Nat.le_refl _
        · rw [fr 126 (by decide) (by decide), hmx]; exact Nat.zero_le _)
      (by
        intro kk u hkk ⟨hum, hue, huk, hufr, h125, h126, h127, h128, h129, h120, hmnle, hmxle⟩
          hur hui hucnt huone
        have hui' : u.regs 123 = kk := hui
        have hucnt' : u.regs 134 = s.regs 134 := hucnt
        rw [show ((rBS1 : Operand) : Nat) = 134 from rfl, hbs1] at hkk
        have hkle : kk ≤ bs := by omega
        rw [Nat.min_eq_left hkle] at h129 h120
        obtain ⟨u', j, ev, hj, hr', r125, r126, r127, r128, r129, r120, rfr, rm, re, rk⟩ :=
          sampleBody_spec hW shape u hur huone B
            (by rw [hufr 119 (by simp [SampleFrame]), hB])
            (by intro a ha; rw [hum]; exact hR a ha) (by rw [hue]; exact hext) hcap
            bs kk (start + kk) (by rw [hufr 56 (by simp [SampleFrame]), hbs]) hui' h129
            (fun h => by show blk * bs + kk < shape.bpCode.length; omega)
            (by show blk * bs + kk ≤ shape.bpCode.length; omega) h120
            (u.regs 125) (u.regs 126) (u.regs 127) rfl rfl hmxle hmnle rfl (by rw [h128, h127])
        have r123 : u'.regs 123 = kk := by
          rw [rfr 123 (by omega) (by omega) (by omega) (by omega), hui']
        have r134 : u'.regs 134 = s.regs 134 := by
          rw [rfr 134 (by omega) (by omega) (by omega) (by omega), hucnt']
        have r2 : u'.regs 2 = 1 := by
          rw [rfr 2 (by omega) (by omega) (by omega) (by omega), huone]
        refine ⟨u', j, ev, hj, hr', r123, r134, r2, ?_⟩
        intro v _ hvr hvm hve hvk _
        have vfr : ∀ r : Nat, r ≠ 123 → r ≠ 124 → v.regs r = u'.regs r := hvr
        refine ⟨hvm.trans (rm.trans hum), hve.trans (re.trans hue), hvk.trans (rk.trans huk),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro r hr
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
          rw [vfr r h4 h5, rfr r h1 h2 h3 h6, hufr r ⟨h1, h2, h3, h4, h5, h6⟩]
        · rw [vfr 125 (by decide) (by decide), r125, h125, range_map_succ,
            natListMinFrom_append_singleton]
        · rw [vfr 126 (by decide) (by decide), r126, h126, range_map_succ,
            natListMax_append_singleton]
        · rw [vfr 127 (by decide) (by decide), r127, h127]; rfl
        · rw [vfr 128 (by decide) (by decide), r128, h127]; rfl
        · rw [vfr 129 (by decide) (by decide), r129]
          split <;> simp only [Nat.min_def] <;> split <;> omega
        · rw [vfr 120 (by decide) (by decide), r120]
          congr 1
          split <;> simp only [Nat.min_def] <;> split <;> omega
        · rw [vfr 125 (by decide) (by decide), r125]
          exact Nat.le_trans (Nat.min_le_left _ _) hmnle
        · rw [vfr 126 (by decide) (by decide), r126]
          exact Nat.max_le.2 ⟨hmxle, bpExcessAt_le_length shape _⟩)
  rw [show ((rBS1 : Operand) : Nat) = 134 from rfl, hbs1] at hk hinv
  obtain ⟨hm, he, hks, hfr, h125, h126, h127, _, _, h120, _, _⟩ := hinv
  rw [Nat.min_eq_right (Nat.le_succ bs)] at h120
  have hstart : Nat.min start len = start := by
    show Nat.min (blk * bs) shape.bpCode.length = blk * bs
    exact Nat.min_eq_left (by omega)
  refine ⟨s', k, e, hk, hr, ?_, ?_, ?_, h120, hfr, hm, he, hks⟩
  · rw [h125]; rfl
  · rw [h126]; rfl
  · rw [h127]
    show _ = bpBlockArgMinPrefixPosFrom shape start (bs + 1) (Nat.min start len)
    rw [hstart, bpBlockArgMinPrefixPosFrom_eq_argAcc]

/-! ## Array writes -/

/-- The state after `rADDR := base + idx; memory[rADDR] := src`. -/
def addStoreState (v : State) (base idx src : Operand) : State :=
  { v with
    regs := put v.regs 108 (v.regs base + v.regs idx)
    memory := put v.memory (v.regs base + v.regs idx) (some (v.regs src))
    pc := v.pc + 2 }

theorem addStore_exec (v : State) (base idx src : Operand) (hs : (src : Nat) ≠ 108)
    (hb : v.regs base + v.regs idx < v.extent) :
    execPrim (Prim.store rADDR src) (execPrim (Prim.arithmetic .add rADDR base idx) v) =
      addStoreState v base idx src := by
  rw [exec_arithmetic, exec_store _ _ _ (by
    show put v.regs 108 (v.regs base + v.regs idx) 108 < v.extent
    rw [put_same]; exact hb)]
  simp only [addStoreState, put_same, put_ne _ _ hs, Arithmetic.eval, operand_val_108]

theorem addStore_seq {W : Nat} (hW : 32 ≤ W) (base idx src : Operand) (hs : (src : Nat) ≠ 108)
    (b : Block) (v w : State) (k : Nat) (hrun : v.status = .running)
    (hb : v.regs base + v.regs idx < v.extent) (hext : v.extent < 2 ^ W)
    (hsrc : v.regs src < 2 ^ W)
    (hrest : SafeEval W b (addStoreState v base idx src) w k) :
    SafeEval W (.seq (.action (.arithmetic .add rADDR base idx))
      (.seq (.action (.store rADDR src)) b)) v w (1 + (1 + k)) := by
  have e1 := EvalG.action (P := Action.Safe W) (.arithmetic .add rADDR base idx) v hrun
    (safe_add hW v _ _ _ (by omega))
  have e2 := EvalG.action (P := Action.Safe W) (.store rADDR src)
    (execPrim (Action.arithmetic .add rADDR base idx).prim v) hrun
    (safe_store hW _ _ _
      (by show put v.regs 108 (v.regs base + v.regs idx) 108 < v.extent; rw [put_same]; exact hb)
      (by show put v.regs 108 (v.regs base + v.regs idx) src < 2 ^ W; rw [put_ne _ _ hs]; exact hsrc))
  have heq : execPrim (Action.store rADDR src).prim
      (execPrim (Action.arithmetic .add rADDR base idx).prim v) = addStoreState v base idx src :=
    addStore_exec v base idx src hs hb
  rw [heq] at e2
  exact EvalG.seq e1 (EvalG.seq e2 hrest)

theorem addStore_pair {W : Nat} (hW : 32 ≤ W) (base idx src : Operand) (hs : (src : Nat) ≠ 108)
    (v : State) (hrun : v.status = .running)
    (hb : v.regs base + v.regs idx < v.extent) (hext : v.extent < 2 ^ W)
    (hsrc : v.regs src < 2 ^ W) :
    SafeEval W (acts [.arithmetic .add rADDR base idx, .store rADDR src]) v
      (addStoreState v base idx src) 2 := by
  have e1 := EvalG.action (P := Action.Safe W) (.arithmetic .add rADDR base idx) v hrun
    (safe_add hW v _ _ _ (by omega))
  have e2 := EvalG.action (P := Action.Safe W) (.store rADDR src)
    (execPrim (Action.arithmetic .add rADDR base idx).prim v) hrun
    (safe_store hW _ _ _
      (by show put v.regs 108 (v.regs base + v.regs idx) 108 < v.extent; rw [put_same]; exact hb)
      (by show put v.regs 108 (v.regs base + v.regs idx) src < 2 ^ W; rw [put_ne _ _ hs]; exact hsrc))
  have heq : execPrim (Action.store rADDR src).prim
      (execPrim (Action.arithmetic .add rADDR base idx).prim v) = addStoreState v base idx src :=
    addStore_exec v base idx src hs hb
  rw [heq] at e2
  exact EvalG.seq e1 e2

/-! ## One block -/

/-- **One block.** Stores the block's start excess, minimum, maximum and
leftmost-argmin sample into the four statistics arrays at index `blk`, and
leaves the excess at the next block start in register 120. -/
theorem blockBody_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1)
    (A0 A1 A2 A3 B bs bc blk : Nat) (h115 : u.regs 115 = A0) (h116 : u.regs 116 = A1)
    (h117 : u.regs 117 = A2) (h118 : u.regs 118 = A3) (hB : u.regs 119 = B)
    (h121 : u.regs 121 = blk) (hbs : u.regs 56 = bs) (hbs1 : u.regs 134 = bs + 1)
    (hlen : u.regs 38 = shape.bpCode.length) (hex : u.regs 120 = bpExcessAt shape (blk * bs))
    (hR : Region u B shape.bpCode.length (bpCell shape))
    (hext : B + shape.bpCode.length ≤ u.extent) (hcap : B + 4 * shape.bpCode.length + 4 < 2 ^ W)
    (hextW : u.extent < 2 ^ W) (hblk : blk < bc) (hcover : bc * bs ≤ shape.bpCode.length)
    (hA01 : A0 + bc + 1 ≤ A1) (hA12 : A1 + bc ≤ A2) (hA23 : A2 + bc ≤ A3) (hA3B : A3 + bc ≤ B) :
    ∃ u' j, SafeEval W blockBodyBlock u u' j ∧ j ≤ (bs + 1) * 28 + 16 ∧ u'.status = .running ∧
      u'.memory = put (put (put (put u.memory (A0 + blk) (some (bpExcessAt shape (blk * bs))))
        (A1 + blk) (some (bpBlockMinExcess shape bs blk)))
        (A2 + blk) (some (bpBlockMaxExcess shape bs blk)))
        (A3 + blk) (some (bpBlockArgMinPrefixPos shape bs blk)) ∧
      u'.regs 120 = bpExcessAt shape (blk * bs + bs) ∧
      (∀ r : Nat, SampleFrame r → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys := by
  have hmul1 : blk * bs + bs ≤ bc * bs := by
    have := Nat.mul_le_mul_right bs (show blk + 1 ≤ bc from hblk)
    rw [Nat.succ_mul] at this; exact this
  have hexle := bpExcessAt_le_length shape (blk * bs)
  -- start excess
  let v2 := addStoreState u rESB rBLK rEX
  have v2s : v2.status = .running := hrun
  have v2r : v2.regs = put u.regs 108 (A0 + blk) := by
    show put u.regs 108 (u.regs 115 + u.regs 121) = _; rw [h115, h121]
  have v2m : v2.memory = put u.memory (A0 + blk) (some (bpExcessAt shape (blk * bs))) := by
    show put u.memory (u.regs 115 + u.regs 121) (some (u.regs 120)) = _; rw [h115, h121, hex]
  obtain ⟨t3, j3, e3, hj3, ht3r, ht3R, ht3m, ht3e, ht3k, _⟩ :=
    RegSpec.pure hW [.arithmetic .mul rPOS rBLK rBS2, .move rMN rM2, .constant rMX 0,
      .move rBEST rPOS, .move rBESTE rEX] v2 v2s (by
        pre1_reg_simp [v2r, h121, hbs]
        omega)
  have t3reg : ∀ r : Nat, t3.regs r = if r = 128 then bpExcessAt shape (blk * bs) else
      if r = 127 then blk * bs else if r = 126 then 0 else if r = 125 then shape.bpCode.length else
      if r = 129 then blk * bs else put u.regs 108 (A0 + blk) r := by
    intro r
    rw [ht3R]; pre1_reg_simp [v2r, h121, hbs, hlen, hex]
  have t3fr : ∀ r : Nat, SampleFrame r → t3.regs r = u.regs r := by
    intro r ⟨h1, h2, h3, h4, h5, h6⟩
    rw [t3reg r, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), put_ne _ _ h2]
  have hRt3 : Region t3 B shape.bpCode.length (bpCell shape) := by
    intro a ha
    rw [ht3m, v2m, put_ne _ _ (by omega)]
    exact hR a ha
  obtain ⟨t4, j4, e4, hj4, ht4r, h4_125, h4_126, h4_127, h4_120, ht4fr, ht4m, ht4e, ht4k⟩ :=
    sampleLoop_spec hW shape t3 ht3r
      (by rw [t3fr 2 (by simp [SampleFrame]), hone]) B
      (by rw [t3fr 119 (by simp [SampleFrame]), hB]) hRt3 (by rw [ht3e]; exact hext) hcap bs blk
      (by rw [t3fr 56 (by simp [SampleFrame]), hbs]) (by rw [t3fr 134 (by simp [SampleFrame]), hbs1])
      (by omega) (by rw [t3reg 129]; rfl) (by rw [t3reg 120]; simp [put, hex])
      (by rw [t3reg 125]; rfl) (by rw [t3reg 126]; rfl) (by rw [t3reg 127]; rfl)
      (by rw [t3reg 128]; rfl)
  have t4fr : ∀ r : Nat, SampleFrame r → t4.regs r = u.regs r := fun r hr => by
    rw [ht4fr r hr, t3fr r hr]
  have t4s : t4.status = .running := ht4r
  have t4ext : t4.extent = u.extent := by rw [ht4e, ht3e]; rfl
  have hmin := bpBlockMinExcess_le_length shape bs blk
  have hmax := bpBlockMaxExcess_le_length shape bs blk
  have harg := bpBlockArgMinPrefixPos_le_length shape bs blk
  -- the three statistics
  let w1 := addStoreState t4 rMINB rBLK rMN
  let w2 := addStoreState w1 rMAXB rBLK rMX
  let w3 := addStoreState w2 rARGB rBLK rBEST
  have w1r : w1.regs = put t4.regs 108 (A1 + blk) := by
    show put t4.regs 108 (t4.regs 116 + t4.regs 121) = _
    rw [t4fr 116 (by simp [SampleFrame]), t4fr 121 (by simp [SampleFrame]), h116, h121]
  have w2r : w2.regs = put (put t4.regs 108 (A1 + blk)) 108 (A2 + blk) := by
    show put w1.regs 108 (w1.regs 117 + w1.regs 121) = _
    rw [w1r, put_ne _ _ (by decide), put_ne _ _ (by decide), t4fr 117 (by simp [SampleFrame]),
      t4fr 121 (by simp [SampleFrame]), h117, h121]
  have ev3 : SafeEval W (acts [.arithmetic .add rADDR rARGB rBLK, .store rADDR rBEST]) w2 w3 2 := by
    refine addStore_pair hW _ _ _ (by decide) w2 t4s ?_ (by show t4.extent < 2 ^ W; rw [t4ext]; exact hextW) ?_
    · show w2.regs 118 + w2.regs 121 < t4.extent
      rw [w2r, put_ne _ _ (by decide), put_ne _ _ (by decide), put_ne _ _ (by decide),
        put_ne _ _ (by decide), t4fr 118 (by simp [SampleFrame]), t4fr 121 (by simp [SampleFrame]),
        h118, h121]; omega
    · show w2.regs 127 < 2 ^ W
      rw [w2r, put_ne _ _ (by decide), put_ne _ _ (by decide), h4_127]; omega
  have ev2 := addStore_seq hW rMAXB rBLK rMX (by decide) _ w1 w3 2 t4s
    (by show w1.regs 117 + w1.regs 121 < t4.extent
        rw [w1r, put_ne _ _ (by decide), put_ne _ _ (by decide), t4fr 117 (by simp [SampleFrame]),
          t4fr 121 (by simp [SampleFrame]), h117, h121]; omega)
    (by show t4.extent < 2 ^ W; rw [t4ext]; exact hextW)
    (by show w1.regs 126 < 2 ^ W; rw [w1r, put_ne _ _ (by decide), h4_126]; omega) ev3
  have ev1 := addStore_seq hW rMINB rBLK rMN (by decide) _ t4 w3 (1 + (1 + 2)) t4s
    (by show t4.regs 116 + t4.regs 121 < t4.extent
        rw [t4fr 116 (by simp [SampleFrame]), t4fr 121 (by simp [SampleFrame]), h116, h121]; omega)
    (by rw [t4ext]; exact hextW) (by show t4.regs 125 < 2 ^ W; rw [h4_125]; omega) ev2
  have ev0 := addStore_seq hW rESB rBLK rEX (by decide) _ u t3 j3 hrun
    (by show u.regs 115 + u.regs 121 < u.extent; rw [h115, h121]; omega) hextW
    (by show u.regs 120 < 2 ^ W; rw [hex]; omega) e3
  refine ⟨w3, _, EvalG.seq ev0 (EvalG.seq e4 ev1), by simp at hj3; omega, t4s, ?_, ?_, ?_,
    by show t4.extent = u.extent; exact t4ext, by show t4.keys = u.keys; rw [ht4k, ht3k]; rfl⟩
  · show put (put (put t4.memory (t4.regs 116 + t4.regs 121) (some (t4.regs 125)))
      (w1.regs 117 + w1.regs 121) (some (w1.regs 126)))
      (w2.regs 118 + w2.regs 121) (some (w2.regs 127)) = _
    rw [w2r, w1r, ht4m, ht3m, v2m]
    simp only [put_ne _ _ (show (118 : Nat) ≠ 108 by decide), put_ne _ _ (show (121 : Nat) ≠ 108 by decide),
      put_ne _ _ (show (117 : Nat) ≠ 108 by decide), put_ne _ _ (show (127 : Nat) ≠ 108 by decide),
      put_ne _ _ (show (126 : Nat) ≠ 108 by decide)]
    rw [t4fr 116 (by simp [SampleFrame]), t4fr 117 (by simp [SampleFrame]),
      t4fr 118 (by simp [SampleFrame]), t4fr 121 (by simp [SampleFrame]), h116, h117, h118, h121,
      h4_125, h4_126, h4_127]
  · show put w2.regs 108 (w2.regs 118 + w2.regs 121) 120 = _
    rw [put_ne _ _ (by decide), w2r, put_ne _ _ (by decide), put_ne _ _ (by decide), h4_120]
  · intro r hr
    show put w2.regs 108 (w2.regs 118 + w2.regs 121) r = _
    rw [put_ne _ _ hr.2.1, w2r, put_ne _ _ hr.2.1, put_ne _ _ hr.2.1, t4fr r hr]

/-! ## All blocks -/

/-- Registers the block-statistics pass leaves unchanged. -/
def StatsFrame (r : Nat) : Prop :=
  SampleFrame r ∧ r ≠ 121 ∧ r ≠ 122 ∧ r ≠ 134

theorem put4_ne {α : Type} (f : Nat → α) (a0 a1 a2 a3 x : Nat) (v0 v1 v2 v3 : α)
    (h0 : x ≠ a0) (h1 : x ≠ a1) (h2 : x ≠ a2) (h3 : x ≠ a3) :
    put (put (put (put f a0 v0) a1 v1) a2 v2) a3 v3 x = f x := by
  rw [put_ne _ _ h3, put_ne _ _ h2, put_ne _ _ h1, put_ne _ _ h0]

theorem bpExcessAt_zero (shape : CartesianShape) : bpExcessAt shape 0 = 0 := by
  simp [bpExcessAt, Succinct.rankPrefix_zero]

/-- **Block statistics.** With the BP cells of `shape` at `B` and four arrays
below them, `blockStatsBlock` stores the start excess of every block and of the
position after the last block, and the minimum, maximum and leftmost-argmin
sample of every block, exactly as the reference functions define them. -/
theorem blockStats_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hone : s.regs 2 = 1)
    (A0 A1 A2 A3 B bs bc : Nat) (h115 : s.regs 115 = A0) (h116 : s.regs 116 = A1)
    (h117 : s.regs 117 = A2) (h118 : s.regs 118 = A3) (hB : s.regs 119 = B)
    (hbs : s.regs 56 = bs) (hbc : s.regs 32 = bc) (hlen : s.regs 38 = shape.bpCode.length)
    (hR : Region s B shape.bpCode.length (bpCell shape))
    (hext : B + shape.bpCode.length ≤ s.extent) (hcap : B + 4 * shape.bpCode.length + 4 < 2 ^ W)
    (hextW : s.extent < 2 ^ W) (hbsW : bs + 1 < 2 ^ W) (hcover : bc * bs ≤ shape.bpCode.length)
    (hA01 : A0 + bc + 1 ≤ A1) (hA12 : A1 + bc ≤ A2) (hA23 : A2 + bc ≤ A3) (hA3B : A3 + bc ≤ B) :
    ∃ s' j, SafeEval W blockStatsBlock s s' j ∧ j ≤ bc * ((bs + 1) * 28 + 20) + 7 ∧
      s'.status = .running ∧
      (∀ b, b ≤ bc → s'.memory (A0 + b) = some (bpExcessAt shape (b * bs))) ∧
      (∀ b, b < bc → s'.memory (A1 + b) = some (bpBlockMinExcess shape bs b)) ∧
      (∀ b, b < bc → s'.memory (A2 + b) = some (bpBlockMaxExcess shape bs b)) ∧
      (∀ b, b < bc → s'.memory (A3 + b) = some (bpBlockArgMinPrefixPos shape bs b)) ∧
      (∀ a, (a < A0 ∨ A3 + bc ≤ a) → s'.memory a = s.memory a) ∧
      (∀ r : Nat, StatsFrame r → r ≠ 108 → s'.regs r = s.regs r) ∧
      s'.extent = s.extent ∧ s'.keys = s.keys := by
  -- initialization
  obtain ⟨t, j0, e0, hj0, ht, htR, htm, hte, htk, _⟩ :=
    RegSpec.pure hW [.constant rEX 0, .arithmetic .add rBS1 rBS2 rONE] s hrun (by
      pre1_reg_simp [hbs, hone]; omega)
  have t134 : t.regs 134 = bs + 1 := by rw [htR]; pre1_reg_simp [hbs, hone]
  have t120 : t.regs 120 = 0 := by rw [htR]; pre1_reg_simp []
  have tfr : ∀ r : Nat, r ≠ 120 → r ≠ 134 → t.regs r = s.regs r := by
    intro r h1 h2; rw [htR]; pre1_reg_simp [h1, h2]
  have t32 : t.regs 32 = bc := by rw [tfr 32 (by decide) (by decide), hbc]
  let Inv : Nat → State → Prop := fun b u =>
    u.extent = s.extent ∧ u.keys = s.keys ∧
      (∀ r : Nat, StatsFrame r → u.regs r = s.regs r) ∧ u.regs 134 = bs + 1 ∧
      u.regs 120 = bpExcessAt shape (b * bs) ∧
      (∀ j, j < b → u.memory (A0 + j) = some (bpExcessAt shape (j * bs)) ∧
        u.memory (A1 + j) = some (bpBlockMinExcess shape bs j) ∧
        u.memory (A2 + j) = some (bpBlockMaxExcess shape bs j) ∧
        u.memory (A3 + j) = some (bpBlockArgMinPrefixPos shape bs j)) ∧
      (∀ a, (a < A0 ∨ A3 + bc ≤ a) → u.memory a = s.memory a)
  obtain ⟨s', k, e, hk, hr, hinv, h121', h32'⟩ :=
    forSlots_spec hW rBLK rBGO rBLOCKS blockBodyBlock ((bs + 1) * 28 + 16)
      (by decide) (by decide) (by decide) (by decide) (by decide) Inv t ht
      (by rw [tfr 2 (by decide) (by decide), hone])
      (by show t.regs 32 < 2 ^ W; rw [t32]; omega)
      (by
        intro u _ hregs hm he hk _
        have fr : ∀ r : Nat, r ≠ 121 → r ≠ 122 → u.regs r = t.regs r := hregs
        refine ⟨he.trans hte, hk.trans htk, ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _), ?_⟩
        · intro r ⟨h1, h2, h3, h4⟩
          rw [fr r h2 h3, tfr r h1.2.2.1 h4]
        · rw [fr 134 (by decide) (by decide), t134]
        · rw [fr 120 (by decide) (by decide), t120, Nat.zero_mul, bpExcessAt_zero]
        · intro a _; rw [hm, htm])
      (by
        intro kk u hkk ⟨hue, huk, hufr, hu134, hu120, hustats, humem⟩ hur hui hucnt huone
        have hui' : u.regs 121 = kk := hui
        have hucnt' : u.regs 32 = t.regs 32 := hucnt
        rw [show ((rBLOCKS : Operand) : Nat) = 32 from rfl, t32] at hkk
        have uA : ∀ r : Nat, StatsFrame r → u.regs r = s.regs r := hufr
        obtain ⟨u', j, ev, hj, hr', hmem, h120', hfr', hext', hkeys'⟩ :=
          blockBody_spec hW shape u hur huone A0 A1 A2 A3 B bs bc kk
            (by rw [uA 115 (by simp [StatsFrame, SampleFrame]), h115])
            (by rw [uA 116 (by simp [StatsFrame, SampleFrame]), h116])
            (by rw [uA 117 (by simp [StatsFrame, SampleFrame]), h117])
            (by rw [uA 118 (by simp [StatsFrame, SampleFrame]), h118])
            (by rw [uA 119 (by simp [StatsFrame, SampleFrame]), hB]) hui'
            (by rw [uA 56 (by simp [StatsFrame, SampleFrame]), hbs]) hu134
            (by rw [uA 38 (by simp [StatsFrame, SampleFrame]), hlen]) hu120
            (by intro a ha; rw [humem (B + a) (Or.inr (by omega))]; exact hR a ha)
            (by rw [hue]; exact hext) hcap (by rw [hue]; exact hextW) hkk hcover
            hA01 hA12 hA23 hA3B
        refine ⟨u', j, ev, hj, hr', ?_, ?_, ?_, ?_⟩
        · show u'.regs 121 = kk
          rw [hfr' 121 (by simp [SampleFrame]), hui']
        · show u'.regs 32 = t.regs 32
          rw [hfr' 32 (by simp [SampleFrame]), hucnt']
        · rw [hfr' 2 (by simp [SampleFrame]), huone]
        · intro v _ hvr hvm hve hvk _
          have vfr : ∀ r : Nat, r ≠ 121 → r ≠ 122 → v.regs r = u'.regs r := hvr
          refine ⟨hve.trans (hext'.trans hue), hvk.trans (hkeys'.trans huk), ?_, ?_, ?_, ?_, ?_⟩
          · intro r hr
            rw [vfr r hr.2.1 hr.2.2.1, hfr' r hr.1, uA r hr]
          · rw [vfr 134 (by decide) (by decide), hfr' 134 (by simp [SampleFrame]), hu134]
          · rw [vfr 120 (by decide) (by decide), h120', Nat.succ_mul]
          · intro jj hjj
            rw [hvm, hmem]
            by_cases hlt : jj < kk
            · obtain ⟨m0, m1, m2, m3⟩ := hustats jj hlt
              refine ⟨?_, ?_, ?_, ?_⟩
              · rw [put4_ne _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega), m0]
              · rw [put4_ne _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega), m1]
              · rw [put4_ne _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega), m2]
              · rw [put4_ne _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega), m3]
            · have hjk : jj = kk := by omega
              subst hjk
              refine ⟨?_, ?_, ?_, ?_⟩
              · rw [put_ne _ _ (by omega), put_ne _ _ (by omega), put_ne _ _ (by omega), put_same]
              · rw [put_ne _ _ (by omega), put_ne _ _ (by omega), put_same]
              · rw [put_ne _ _ (by omega), put_same]
              · rw [put_same]
          · intro a ha
            rw [hvm, hmem, put4_ne _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega),
              humem a ha])
  rw [show ((rBLOCKS : Operand) : Nat) = 32 from rfl, t32] at hk hinv
  obtain ⟨hse, hsk, hsfr, _, hs120, hsstats, hsmem⟩ := hinv
  have hs32 : s'.regs 32 = bc := h32'.trans t32
  have hs115 : s'.regs 115 = A0 := by rw [hsfr 115 (by simp [StatsFrame, SampleFrame]), h115]
  have etail := addStore_pair hW rESB rBLOCKS rEX (by decide) s' hr
    (by show s'.regs 115 + s'.regs 32 < s'.extent; rw [hs115, hs32, hse]; omega)
    (by rw [hse]; exact hextW)
    (by show s'.regs 120 < 2 ^ W; rw [hs120]; have := bpExcessAt_le_length shape (bc * bs); omega)
  have fm : (addStoreState s' rESB rBLOCKS rEX).memory =
      put s'.memory (A0 + bc) (some (bpExcessAt shape (bc * bs))) := by
    show put s'.memory (s'.regs 115 + s'.regs 32) (some (s'.regs 120)) = _
    rw [hs115, hs32, hs120]
  refine ⟨addStoreState s' rESB rBLOCKS rEX, _, EvalG.seq e0 (EvalG.seq e etail), ?_, hr,
    ?_, ?_, ?_, ?_, ?_, ?_, hse, hsk⟩
  · rw [show (bs + 1) * 28 + 16 + 4 = (bs + 1) * 28 + 20 by omega] at hk
    simp at hj0; omega
  · intro b hb
    rw [fm]
    by_cases hlt : b < bc
    · rw [put_ne _ _ (by omega)]; exact (hsstats b hlt).1
    · have hbb : b = bc := by omega
      subst hbb; rw [put_same]
  · intro b hb; rw [fm, put_ne _ _ (by omega)]; exact (hsstats b hb).2.1
  · intro b hb; rw [fm, put_ne _ _ (by omega)]; exact (hsstats b hb).2.2.1
  · intro b hb; rw [fm, put_ne _ _ (by omega)]; exact (hsstats b hb).2.2.2
  · intro a ha; rw [fm, put_ne _ _ (by omega)]; exact hsmem a ha
  · intro r hr h108
    show put s'.regs 108 (s'.regs 115 + s'.regs 32) r = _
    rw [put_ne _ _ h108]; exact hsfr r hr

end RMQ.SuccinctFinal.PackedConstruction.Proof
