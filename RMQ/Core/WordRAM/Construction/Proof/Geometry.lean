import RMQ.Core.WordRAM.Construction.Proof.Interior
import RMQ.Core.WordRAM.Construction.Builder.Geometry

/-! # PRE-1 builder proofs: the size-only geometry prelude (interior subset)

Outside the builder firewall. The prelude computes, from the input length in
register 1 and by charged arithmetic only, the interior layout quantities of
`SuccinctClose.RelativeRmm.canonicalLayout`: base `Nat.log2 n + 1` (the blocks
per superblock), macro size, block count, macro sample count, and the domains
and widths of the two sparse-level tables.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder SuccinctSpace SuccinctClose

/-- **Constants.** -/
theorem constantsBlock_spec {W : Nat} (hW : 32 ≤ W) (s : State) (hrun : s.status = .running) :
    ∃ s', SafeEval W constantsBlock s s' 2 ∧ s'.status = .running ∧
      s'.regs 2 = 1 ∧ s'.regs 9 = 2 ∧ s'.memory = s.memory ∧ s'.extent = s.extent ∧
      (∀ r : Nat, r ≠ 2 → r ≠ 9 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  let t1 := execPrim (Prim.constant rONE 1) s
  have f1 := exec_constant s rONE 1
  let t2 := execPrim (Prim.constant rTWO 2) t1
  have f2 := exec_constant t1 rTWO 2
  have t2r : t2.regs = put (put s.regs 2 1) 9 2 := by simp [t2, f2, t1, f1]
  have t2s : t2.status = .running := by simp [t2, f2, t1, f1, hrun]
  refine ⟨t2, acts_evalG (P := Action.Safe W) _ s hrun
      ⟨safe_constant hW s _ _, by simp [Action.prim, exec_constant, hrun],
        safe_constant hW t1 _ _, t2s, trivial⟩, t2s, by simp [t2r, put], by simp [t2r, put],
    by simp [t2, f2, t1, f1], by simp [t2, f2, t1, f1], ?_, by simp [t2, f2, t1, f1],
    by simp [t2, f2, t1, f1]⟩
  intro r h2 h9
  rw [t2r, put_ne _ _ h9, put_ne _ _ h2]

/-- **Level width.** `levelWidthBlock dst dom` sets `regs dst` to
`bpSparseLevelWidth (regs dom)`, writing only `dst`, 20, 21, 22 and 25. -/
theorem levelWidthBlock_spec {W : Nat} (hW : 32 ≤ W) (dst dom : Operand)
    (hdst2 : (dst : Nat) ≠ 2) (hdst9 : (dst : Nat) ≠ 9) (hdst20 : (dst : Nat) ≠ 20)
    (hdst21 : (dst : Nat) ≠ 21)
    (hdom20 : (dom : Nat) ≠ 20) (hdom21 : (dom : Nat) ≠ 21) (hdom22 : (dom : Nat) ≠ 22)
    (s : State) (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2)
    (hcap : s.regs dom * (Nat.log2 (s.regs dom) + 1) < 2 ^ W) :
    ∃ s' k, SafeEval W (levelWidthBlock dst dom) s s' k ∧ k ≤ 10 * W + 11 ∧
      s'.status = .running ∧ s'.regs dst = bpSparseLevelWidth (s.regs dom) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧
      (∀ r : Nat, r ≠ (dst : Nat) → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 25 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  generalize hdv : s.regs dom = d at hcap ⊢
  have hlogd : Nat.log2 d ≤ d := Nat.log2_le_self d
  have hdW : d < 2 ^ W := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; exact Nat.pow_pos (by decide)
    · exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) hcap
  -- log2 dom into 22
  obtain ⟨u1, j1, h1, hj1, hu1run, hu1ll, hu1mem, hu1ext, hu1fr, hu1kr, hu1k⟩ :=
    log2Block_spec hW rLL dom (by decide) (by decide) (by decide) (by decide)
      s hrun hone htwo (by rw [hdv]; exact hdW)
  simp only [operand_val_22, hdv] at hu1ll
  have hu1one : u1.regs 2 = 1 := by rw [hu1fr 2 (by decide) (by decide) (by decide), hone]
  have hu1two : u1.regs 9 = 2 := by rw [hu1fr 9 (by decide) (by decide) (by decide), htwo]
  have hu1dom : u1.regs dom = d := by rw [hu1fr dom (by simpa using hdom22) hdom20 hdom21, hdv]
  -- ll := ll + 1; t0 := dom * ll
  let v1 := execPrim (Prim.arithmetic .add rLL rLL rONE) u1
  have g1 := exec_arithmetic u1 .add rLL rLL rONE
  let v2 := execPrim (Prim.arithmetic .mul rT0 dom rLL) v1
  have g2 := exec_arithmetic v1 .mul rT0 dom rLL
  have v1r : v1.regs = put u1.regs 22 (Nat.log2 d + 1) := by
    show (execPrim (Prim.arithmetic .add rLL rLL rONE) u1).regs = _
    rw [g1]
    show put u1.regs 22 (u1.regs 22 + u1.regs 2) = _
    rw [hu1ll, hu1one]
  have v1dom : v1.regs dom = d := by rw [v1r, put_ne _ _ hdom22, hu1dom]
  have v2r : v2.regs = put v1.regs 25 (d * (Nat.log2 d + 1)) := by
    show (execPrim (Prim.arithmetic .mul rT0 dom rLL) v1).regs = _
    rw [g2]
    show put v1.regs 25 (v1.regs dom * v1.regs 22) = _
    rw [v1dom, v1r, put_same]
  have v2s : v2.status = .running := by simp [v2, g2, v1, g1, hu1run]
  have hstep : ActsOK (Action.Safe W) [.arithmetic .add rLL rLL rONE,
      .arithmetic .mul rT0 dom rLL] u1 := by
    refine ⟨safe_add hW u1 _ _ _ ?_, by simp [Action.prim, exec_arithmetic, hu1run], ?_⟩
    · show u1.regs 22 + u1.regs 2 < 2 ^ W
      have e22 : u1.regs 22 = Nat.log2 d := hu1ll
      have hl : Nat.log2 d < W := log2_lt_width (by omega) hdW
      have : W < 2 ^ W := Nat.lt_two_pow_self
      omega
    refine ⟨safe_mul hW v1 _ _ _ ?_, v2s, trivial⟩
    · show v1.regs dom * v1.regs 22 < 2 ^ W
      rw [v1dom, v1r, put_same]; exact hcap
  have hacts := acts_evalG (P := Action.Safe W) _ u1 hu1run hstep
  have v2one : v2.regs 2 = 1 := by
    rw [v2r, put_ne _ _ (by decide), v1r, put_ne _ _ (by decide), hu1one]
  have v2two : v2.regs 9 = 2 := by
    rw [v2r, put_ne _ _ (by decide), v1r, put_ne _ _ (by decide), hu1two]
  have v2t0 : v2.regs 25 = d * (Nat.log2 d + 1) := by rw [v2r, put_same]
  -- log2 (dom * (log2 dom + 1)) into dst
  obtain ⟨u3, j3, h3, hj3, hu3run, hu3dst, hu3mem, hu3ext, hu3fr, hu3kr, hu3k⟩ :=
    log2Block_spec hW dst rT0 hdst2 hdst9 hdst20 hdst21 v2 v2s v2one v2two
      (by simp only [operand_val_25]; rw [v2t0]; exact hcap)
  simp only [operand_val_25, v2t0] at hu3dst
  have hu3one : u3.regs 2 = 1 := by
    rw [hu3fr 2 (fun h => hdst2 h.symm) (by decide) (by decide), v2one]
  have hlogW : Nat.log2 (d * (Nat.log2 d + 1)) < W := log2_lt_width (by omega) hcap
  let w1 := execPrim (Prim.arithmetic .add dst dst rONE) u3
  have k1 := exec_arithmetic u3 .add dst dst rONE
  have w1r : w1.regs = put u3.regs dst (Nat.log2 (d * (Nat.log2 d + 1)) + 1) := by
    show (execPrim (Prim.arithmetic .add dst dst rONE) u3).regs = _
    rw [k1]
    show put u3.regs dst (u3.regs dst + u3.regs 2) = _
    rw [hu3dst, hu3one]
  have w1s : w1.status = .running := by simp [w1, k1, hu3run]
  have hadd : u3.regs dst + u3.regs 2 < 2 ^ W := by
    have eD : u3.regs dst = Nat.log2 (d * (Nat.log2 d + 1)) := hu3dst
    have : W < 2 ^ W := Nat.lt_two_pow_self
    omega
  have hlast : ActsOK (Action.Safe W) [.arithmetic .add dst dst rONE] u3 :=
    ⟨safe_add hW u3 _ _ _ hadd, w1s, trivial⟩
  have hfinal := acts_evalG (P := Action.Safe W) _ u3 hu3run hlast
  refine ⟨w1, j1 + (2 + (j3 + 1)), EvalG.seq h1 (EvalG.seq hacts (EvalG.seq h3 hfinal)),
    ?_, w1s, by rw [w1r, put_same]; rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdv] at hj1
    simp only [operand_val_25, v2t0] at hj3
    have := log2_lt_width (W := W) (by omega) hdW
    omega
  · simp [w1, k1, hu3mem, v2, g2, v1, g1, hu1mem]
  · simp [w1, k1, hu3ext, v2, g2, v1, g1, hu1ext]
  · intro r hd h20 h21 h22 h25
    rw [w1r, put_ne _ _ hd, hu3fr r hd h20 h21, v2r, put_ne _ _ h25, v1r, put_ne _ _ h22,
      hu1fr r (by simpa using h22) h20 h21]
  · simp [w1, k1, hu3kr, v2, g2, v1, g1, hu1kr]
  · simp [w1, k1, hu3k, v2, g2, v1, g1, hu1k]

theorem log2_succ_le_self {d : Nat} (hd : 1 ≤ d) : Nat.log2 d + 1 ≤ d := by
  have h := Nat.lt_log2_self (n := d)
  have hself : 2 ^ Nat.log2 d ≤ d := Nat.log2_self_le (by omega)
  have hpow : Nat.log2 d + 1 ≤ 2 ^ Nat.log2 d := Nat.lt_two_pow_self
  omega

theorem level_cap_of_le {d B W : Nat} (hd : 1 ≤ d) (hdB : d ≤ B) (hB : B * B < 2 ^ W) :
    d * (Nat.log2 d + 1) < 2 ^ W := by
  have h1 : d * (Nat.log2 d + 1) ≤ d * d := Nat.mul_le_mul_left _ (log2_succ_le_self hd)
  have h2 : d * d ≤ B * B := Nat.mul_le_mul hdB hdB
  omega

/-- The interior layout quantities the prelude computes, as functions of `n`. -/
def geoBase (n : Nat) : Nat := Nat.log2 n + 1
def geoMacro (n : Nat) : Nat := geoBase n * geoBase n
def geoBlocks (n : Nat) : Nat := n / geoBase n
def geoMacros (n : Nat) : Nat := geoBlocks n / geoMacro n + 1

/-- **Interior geometry prelude.** From a running state with the constants in
place and `regs 1 = n`, `interiorGeometryBlock` safely stores the base, macro
size, block count, macro sample count, both sparse-level domains and both
widths in registers 30-37, writing only 20-25 and 30-37. -/
theorem interiorGeometry_spec {W : Nat} (hW : 32 ≤ W) (s : State) (n : Nat)
    (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2)
    (hn : s.regs 1 = n) (hcap : (n + 2) * (n + 2) * ((n + 2) * (n + 2)) < 2 ^ W) :
    ∃ s' k, SafeEval W interiorGeometryBlock s s' k ∧ k ≤ 25 * W + 40 ∧ s'.status = .running ∧
      s'.regs 30 = geoBase n ∧ s'.regs 31 = geoMacro n ∧ s'.regs 32 = geoBlocks n ∧
      s'.regs 33 = geoMacros n ∧
      s'.regs 34 = bpSparseLevelDomain (geoMacro n) ∧
      s'.regs 35 = bpSparseLevelDomain (geoMacros n) ∧
      s'.regs 36 = bpSparseLevelWidth (bpSparseLevelDomain (geoMacro n)) ∧
      s'.regs 37 = bpSparseLevelWidth (bpSparseLevelDomain (geoMacros n)) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧
      (∀ r : Nat, ¬ (20 ≤ r ∧ r ≤ 25) → ¬ (30 ≤ r ∧ r ≤ 37) → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  have hsq : (n + 2) * (n + 2) ≤ (n + 2) * (n + 2) * ((n + 2) * (n + 2)) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
  have hnle : n ≤ (n + 2) * (n + 2) := by
    have : n + 2 ≤ (n + 2) * (n + 2) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hnW : n < 2 ^ W := by omega
  have hlogn : Nat.log2 n ≤ n := Nat.log2_le_self n
  have hbase1 : 1 ≤ geoBase n := by simp [geoBase]
  have hbase_le : geoBase n ≤ n + 1 := by simp [geoBase]; omega
  have hmacro_le : geoMacro n + 2 ≤ (n + 2) * (n + 2) := by
    have : geoMacro n ≤ (n + 1) * (n + 1) := Nat.mul_le_mul hbase_le hbase_le
    have e : (n + 2) * (n + 2) = (n + 1) * (n + 1) + 2 * n + 3 := by
      simp only [Nat.add_mul, Nat.mul_add]; omega
    omega
  have hblocks_le : geoBlocks n ≤ n := Nat.div_le_self _ _
  have hmacros_le : geoMacros n ≤ n + 1 := by
    have := Nat.div_le_self (geoBlocks n) (geoMacro n)
    simp only [geoMacros]; omega
  -- step 1: log2 n into 30
  obtain ⟨u1, j1, h1, hj1, hu1run, hu1b, hu1mem, hu1ext, hu1fr, hu1kr, hu1k⟩ :=
    log2Block_spec hW rBASE rN (by decide) (by decide) (by decide) (by decide)
      s hrun hone htwo (by simp only [operand_val_1]; rw [hn]; exact hnW)
  have e30 : u1.regs 30 = Nat.log2 n := by
    have := hu1b; simp only [operand_val_30, operand_val_1, hn] at this; exact this
  have e1 : u1.regs 1 = n := by rw [hu1fr 1 (by decide) (by decide) (by decide), hn]
  have e2 : u1.regs 2 = 1 := by rw [hu1fr 2 (by decide) (by decide) (by decide), hone]
  have e9 : u1.regs 9 = 2 := by rw [hu1fr 9 (by decide) (by decide) (by decide), htwo]
  -- step 2: seven arithmetic actions
  let a1 := execPrim (Prim.arithmetic .add rBASE rBASE rONE) u1
  have g1 := exec_arithmetic u1 .add rBASE rBASE rONE
  have a1r : a1.regs = put u1.regs 30 (geoBase n) := by
    show (execPrim (Prim.arithmetic .add rBASE rBASE rONE) u1).regs = _
    rw [g1]; show put u1.regs 30 (u1.regs 30 + u1.regs 2) = _; rw [e30, e2]; rfl
  let a2 := execPrim (Prim.arithmetic .mul rMACRO rBASE rBASE) a1
  have g2 := exec_arithmetic a1 .mul rMACRO rBASE rBASE
  have a1b : a1.regs 30 = geoBase n := by rw [a1r, put_same]
  have a2r : a2.regs = put a1.regs 31 (geoMacro n) := by
    show (execPrim (Prim.arithmetic .mul rMACRO rBASE rBASE) a1).regs = _
    rw [g2]; show put a1.regs 31 (a1.regs 30 * a1.regs 30) = _; rw [a1b]; rfl
  let a3 := execPrim (Prim.arithmetic .div rBLOCKS rN rBASE) a2
  have g3 := exec_arithmetic a2 .div rBLOCKS rN rBASE
  have a2b : a2.regs 30 = geoBase n := by rw [a2r, put_ne _ _ (by decide), a1b]
  have a2n : a2.regs 1 = n := by rw [a2r, put_ne _ _ (by decide), a1r, put_ne _ _ (by decide), e1]
  have a2m : a2.regs 31 = geoMacro n := by rw [a2r, put_same]
  have a3r : a3.regs = put a2.regs 32 (geoBlocks n) := by
    show (execPrim (Prim.arithmetic .div rBLOCKS rN rBASE) a2).regs = _
    rw [g3]; show put a2.regs 32 (a2.regs 1 / a2.regs 30) = _; rw [a2n, a2b]; rfl
  let a4 := execPrim (Prim.arithmetic .div rMACROS rBLOCKS rMACRO) a3
  have g4 := exec_arithmetic a3 .div rMACROS rBLOCKS rMACRO
  have a3k : a3.regs 32 = geoBlocks n := by rw [a3r, put_same]
  have a3m : a3.regs 31 = geoMacro n := by rw [a3r, put_ne _ _ (by decide), a2m]
  have a4r : a4.regs = put a3.regs 33 (geoBlocks n / geoMacro n) := by
    show (execPrim (Prim.arithmetic .div rMACROS rBLOCKS rMACRO) a3).regs = _
    rw [g4]; show put a3.regs 33 (a3.regs 32 / a3.regs 31) = _; rw [a3k, a3m]
  let a5 := execPrim (Prim.arithmetic .add rMACROS rMACROS rONE) a4
  have g5 := exec_arithmetic a4 .add rMACROS rMACROS rONE
  have a4q : a4.regs 33 = geoBlocks n / geoMacro n := by rw [a4r, put_same]
  have a4one : a4.regs 2 = 1 := by
    rw [a4r, put_ne _ _ (by decide), a3r, put_ne _ _ (by decide), a2r, put_ne _ _ (by decide),
      a1r, put_ne _ _ (by decide), e2]
  have a5r : a5.regs = put a4.regs 33 (geoMacros n) := by
    show (execPrim (Prim.arithmetic .add rMACROS rMACROS rONE) a4).regs = _
    rw [g5]; show put a4.regs 33 (a4.regs 33 + a4.regs 2) = _; rw [a4q, a4one]; rfl
  let a6 := execPrim (Prim.arithmetic .add rLDOM rMACRO rTWO) a5
  have g6 := exec_arithmetic a5 .add rLDOM rMACRO rTWO
  have a5m : a5.regs 31 = geoMacro n := by
    rw [a5r, put_ne _ _ (by decide), a4r, put_ne _ _ (by decide), a3m]
  have a5two : a5.regs 9 = 2 := by
    rw [a5r, put_ne _ _ (by decide), a4r, put_ne _ _ (by decide), a3r, put_ne _ _ (by decide),
      a2r, put_ne _ _ (by decide), a1r, put_ne _ _ (by decide), e9]
  have a6r : a6.regs = put a5.regs 34 (bpSparseLevelDomain (geoMacro n)) := by
    show (execPrim (Prim.arithmetic .add rLDOM rMACRO rTWO) a5).regs = _
    rw [g6]; show put a5.regs 34 (a5.regs 31 + a5.regs 9) = _; rw [a5m, a5two]; rfl
  let a7 := execPrim (Prim.arithmetic .add rGDOM rMACROS rTWO) a6
  have g7 := exec_arithmetic a6 .add rGDOM rMACROS rTWO
  have a6q : a6.regs 33 = geoMacros n := by rw [a6r, put_ne _ _ (by decide), a5r, put_same]
  have a6two : a6.regs 9 = 2 := by rw [a6r, put_ne _ _ (by decide), a5two]
  have a7r : a7.regs = put a6.regs 35 (bpSparseLevelDomain (geoMacros n)) := by
    show (execPrim (Prim.arithmetic .add rGDOM rMACROS rTWO) a6).regs = _
    rw [g7]; show put a6.regs 35 (a6.regs 33 + a6.regs 9) = _; rw [a6q, a6two]; rfl
  have a7s : a7.status = .running := by
    simp [a7, g7, a6, g6, a5, g5, a4, g4, a3, g3, a2, g2, a1, g1, hu1run]
  have hn3 : n + 3 ≤ (n + 2) * (n + 2) := by simp only [Nat.add_mul, Nat.mul_add]; omega
  have hbig : (n + 2) * (n + 2) < 2 ^ W := Nat.lt_of_le_of_lt hsq hcap
  have hbaseW : geoBase n < 2 ^ W := by omega
  have hmacro2W : geoMacro n + 2 < 2 ^ W := Nat.lt_of_le_of_lt hmacro_le hbig
  have hmacroW : geoMacro n < 2 ^ W := by omega
  have hsafe : ActsOK (Action.Safe W) [.arithmetic .add rBASE rBASE rONE,
      .arithmetic .mul rMACRO rBASE rBASE, .arithmetic .div rBLOCKS rN rBASE,
      .arithmetic .div rMACROS rBLOCKS rMACRO, .arithmetic .add rMACROS rMACROS rONE,
      .arithmetic .add rLDOM rMACRO rTWO, .arithmetic .add rGDOM rMACROS rTWO] u1 := by
    have s1 : u1.regs 30 + u1.regs 2 < 2 ^ W := by rw [e30, e2]; exact hbaseW
    have s2 : a1.regs 30 * a1.regs 30 < 2 ^ W := by rw [a1b]; exact hmacroW
    have s3a : a2.regs 1 < 2 ^ W := by rw [a2n]; exact hnW
    have s3b : 0 < a2.regs 30 := by rw [a2b]; exact hbase1
    have s4a : a3.regs 32 < 2 ^ W := by rw [a3k]; omega
    have s4b : 0 < a3.regs 31 := by rw [a3m]; exact Nat.mul_pos hbase1 hbase1
    have s5 : a4.regs 33 + a4.regs 2 < 2 ^ W := by
      rw [a4q, a4one]; have := Nat.div_le_self (geoBlocks n) (geoMacro n); omega
    have s6 : a5.regs 31 + a5.regs 9 < 2 ^ W := by rw [a5m, a5two]; exact hmacro2W
    have s7 : a6.regs 33 + a6.regs 9 < 2 ^ W := by
      rw [a6q, a6two]; exact Nat.lt_of_le_of_lt (by omega) hbig
    exact ⟨safe_add hW u1 _ _ _ s1, by simp [Action.prim, exec_arithmetic, hu1run],
      safe_mul hW a1 _ _ _ s2, by simp [Action.prim, exec_arithmetic, hu1run],
      safe_div hW a2 _ _ _ s3a s3b, by simp [Action.prim, exec_arithmetic, hu1run],
      safe_div hW a3 _ _ _ s4a s4b,
      by simp [Action.prim, exec_arithmetic, hu1run],
      safe_add hW a4 _ _ _ s5,
      by simp [Action.prim, exec_arithmetic, hu1run],
      safe_add hW a5 _ _ _ s6,
      by simp [Action.prim, exec_arithmetic, hu1run],
      safe_add hW a6 _ _ _ s7, a7s, trivial⟩
  have hacts := acts_evalG (P := Action.Safe W) _ u1 hu1run hsafe
  -- register values after step 2
  have b30 : a7.regs 30 = geoBase n := by
    rw [a7r, put_ne _ _ (by decide), a6r, put_ne _ _ (by decide), a5r, put_ne _ _ (by decide),
      a4r, put_ne _ _ (by decide), a3r, put_ne _ _ (by decide), a2b]
  have b31 : a7.regs 31 = geoMacro n := by
    rw [a7r, put_ne _ _ (by decide), a6r, put_ne _ _ (by decide), a5m]
  have b32 : a7.regs 32 = geoBlocks n := by
    rw [a7r, put_ne _ _ (by decide), a6r, put_ne _ _ (by decide), a5r, put_ne _ _ (by decide),
      a4r, put_ne _ _ (by decide), a3k]
  have b33 : a7.regs 33 = geoMacros n := by rw [a7r, put_ne _ _ (by decide), a6q]
  have b34 : a7.regs 34 = bpSparseLevelDomain (geoMacro n) := by
    rw [a7r, put_ne _ _ (by decide), a6r, put_same]
  have b35 : a7.regs 35 = bpSparseLevelDomain (geoMacros n) := by rw [a7r, put_same]
  have b2 : a7.regs 2 = 1 := by
    rw [a7r, put_ne _ _ (by decide), a6r, put_ne _ _ (by decide), a5r, put_ne _ _ (by decide), a4one]
  have b9 : a7.regs 9 = 2 := by rw [a7r, put_ne _ _ (by decide), a6two]
  have bfr : ∀ r : Nat, ¬ (20 ≤ r ∧ r ≤ 25) → ¬ (30 ≤ r ∧ r ≤ 37) → a7.regs r = s.regs r := by
    intro r h20 h30
    have n30 : r ≠ 30 := fun h => h30 ⟨by omega, by omega⟩
    have n31 : r ≠ 31 := fun h => h30 ⟨by omega, by omega⟩
    have n32 : r ≠ 32 := fun h => h30 ⟨by omega, by omega⟩
    have n33 : r ≠ 33 := fun h => h30 ⟨by omega, by omega⟩
    have n34 : r ≠ 34 := fun h => h30 ⟨by omega, by omega⟩
    have n35 : r ≠ 35 := fun h => h30 ⟨by omega, by omega⟩
    rw [a7r, put_ne _ _ n35, a6r, put_ne _ _ n34, a5r, put_ne _ _ n33, a4r, put_ne _ _ n33,
      a3r, put_ne _ _ n32, a2r, put_ne _ _ n31, a1r, put_ne _ _ n30,
      hu1fr r (by simpa using n30) (fun h => h20 ⟨by omega, by omega⟩)
        (fun h => h20 ⟨by omega, by omega⟩)]
  have a7mem : a7.memory = s.memory := by
    simp [a7, g7, a6, g6, a5, g5, a4, g4, a3, g3, a2, g2, a1, g1, hu1mem]
  have a7ext : a7.extent = s.extent := by
    simp [a7, g7, a6, g6, a5, g5, a4, g4, a3, g3, a2, g2, a1, g1, hu1ext]
  have a7kr : a7.keyRegs = s.keyRegs ∧ a7.keys = s.keys := by
    simp [a7, g7, a6, g6, a5, g5, a4, g4, a3, g3, a2, g2, a1, g1, hu1kr, hu1k]
  -- step 3: local level width into 36
  have hldom1 : 1 ≤ bpSparseLevelDomain (geoMacro n) := by simp [bpSparseLevelDomain]
  have hldomB : bpSparseLevelDomain (geoMacro n) ≤ (n + 2) * (n + 2) := by
    simp only [bpSparseLevelDomain]; exact hmacro_le
  obtain ⟨w1, k1, hw1, hk1, hw1run, hw1dst, hw1mem, hw1ext, hw1fr, hw1kr, hw1k⟩ :=
    levelWidthBlock_spec hW rLWID rLDOM (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) a7 a7s b2 b9
      (by simp only [operand_val_34]; rw [b34]; exact level_cap_of_le hldom1 hldomB hcap)
  simp only [operand_val_36, operand_val_34, b34] at hw1dst
  have fr1 : ∀ r : Nat, r ≠ 36 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 25 → w1.regs r = a7.regs r :=
    fun r a b c d e => hw1fr r (by simpa using a) b c d e
  have c2 : w1.regs 2 = 1 := by rw [fr1 2 (by decide) (by decide) (by decide) (by decide) (by decide), b2]
  have c9 : w1.regs 9 = 2 := by rw [fr1 9 (by decide) (by decide) (by decide) (by decide) (by decide), b9]
  have c35 : w1.regs 35 = bpSparseLevelDomain (geoMacros n) := by
    rw [fr1 35 (by decide) (by decide) (by decide) (by decide) (by decide), b35]
  -- step 4: global level width into 37
  have hgdom1 : 1 ≤ bpSparseLevelDomain (geoMacros n) := by simp [bpSparseLevelDomain]
  have hgdomB : bpSparseLevelDomain (geoMacros n) ≤ (n + 2) * (n + 2) := by
    simp only [bpSparseLevelDomain]
    have : n + 3 ≤ (n + 2) * (n + 2) := by simp only [Nat.add_mul, Nat.mul_add]; omega
    omega
  obtain ⟨w2, k2, hw2, hk2, hw2run, hw2dst, hw2mem, hw2ext, hw2fr, hw2kr, hw2k⟩ :=
    levelWidthBlock_spec hW rGWID rGDOM (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) w1 hw1run c2 c9
      (by simp only [operand_val_35]; rw [c35]; exact level_cap_of_le hgdom1 hgdomB hcap)
  simp only [operand_val_37, operand_val_35, c35] at hw2dst
  have fr2 : ∀ r : Nat, r ≠ 37 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 25 → w2.regs r = w1.regs r :=
    fun r a b c d e => hw2fr r (by simpa using a) b c d e
  refine ⟨w2, j1 + (7 + (k1 + k2)), EvalG.seq h1 (EvalG.seq hacts (EvalG.seq hw1 hw2)), ?_,
    hw2run, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hw2dst, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [operand_val_1, hn] at hj1
    have := log2_lt_width (W := W) (by omega) hnW
    omega
  · rw [fr2 30 (by decide) (by decide) (by decide) (by decide) (by decide),
      fr1 30 (by decide) (by decide) (by decide) (by decide) (by decide), b30]
  · rw [fr2 31 (by decide) (by decide) (by decide) (by decide) (by decide),
      fr1 31 (by decide) (by decide) (by decide) (by decide) (by decide), b31]
  · rw [fr2 32 (by decide) (by decide) (by decide) (by decide) (by decide),
      fr1 32 (by decide) (by decide) (by decide) (by decide) (by decide), b32]
  · rw [fr2 33 (by decide) (by decide) (by decide) (by decide) (by decide),
      fr1 33 (by decide) (by decide) (by decide) (by decide) (by decide), b33]
  · rw [fr2 34 (by decide) (by decide) (by decide) (by decide) (by decide),
      fr1 34 (by decide) (by decide) (by decide) (by decide) (by decide), b34]
  · rw [fr2 35 (by decide) (by decide) (by decide) (by decide) (by decide), c35]
  · rw [fr2 36 (by decide) (by decide) (by decide) (by decide) (by decide), hw1dst]
  · rw [hw2mem, hw1mem, a7mem]
  · rw [hw2ext, hw1ext, a7ext]
  · intro r h20 h30
    have n36 : r ≠ 36 := fun h => h30 ⟨by omega, by omega⟩
    have n37 : r ≠ 37 := fun h => h30 ⟨by omega, by omega⟩
    have n20 : r ≠ 20 := fun h => h20 ⟨by omega, by omega⟩
    have n21 : r ≠ 21 := fun h => h20 ⟨by omega, by omega⟩
    have n22 : r ≠ 22 := fun h => h20 ⟨by omega, by omega⟩
    have n25 : r ≠ 25 := fun h => h20 ⟨by omega, by omega⟩
    rw [fr2 r n37 n20 n21 n22 n25, fr1 r n36 n20 n21 n22 n25, bfr r h20 h30]
  · rw [hw2kr, hw1kr, a7kr.1]
  · rw [hw2k, hw1k, a7kr.2]

end RMQ.SuccinctFinal.PackedConstruction.Proof
