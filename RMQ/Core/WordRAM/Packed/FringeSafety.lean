import RMQ.Core.WordRAM.Packed.WindowSafety
import RMQ.Core.WordRAM.Packed.FringeProof

/-! Bounds and scalar safety for all thirty-three guarded fringe copies. -/
namespace RMQ.SuccinctFinal.PackedWordRAM
open Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

theorem fringe_chunk_geometry (n : Nat) :
    32 * packedFringeChunkBits n ≤ 4 * packedReviewerCellWidth n + 28 ∧
      32 * packedFringeChunkBits n < wordWidth n := by
  have hbp : packedBpCodeWordWidth n ≤ packedReviewerCellWidth n := by
    apply packedReviewerMachineWordBits_le_cellWidth
    have := packedTwoMul_le_reviewerBound n
    omega
  change Nat.log2 (2 * n) + 1 ≤ packedReviewerCellWidth n at hbp
  have hd := Nat.div_mul_le_self (Nat.log2 (2 * n)) 8
  change 32 * (Nat.log2 (2 * n) / 8 + 1) ≤ _ ∧
    32 * (Nat.log2 (2 * n) / 8 + 1) < _
  unfold wordWidth
  omega

theorem fringe_envelope_bounds (n : Nat) :
    2 ^ packedReviewerCellWidth n ≤ metadataEnvelope n ∧
    packedReviewerCellWidth n ≤ metadataEnvelope n ∧
    36 * metadataEnvelope n + 4 < 2 ^ wordWidth n := by
  have rank := rank_output_envelope n
  have cap := reader_polynomial_fit n
  have pos := metadataEnvelope_pos n
  omega

private theorem fs_eval_arithmetic (memory : Memory) (regs : Registers)
    (op : Arithmetic) (dst lhs rhs : Nat) :
    (Block.action (.arithmetic op dst lhs rhs)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩, []⟩ := rfl

private theorem fs_eval_skip (memory : Memory) (regs : Registers) :
    Block.skip.eval memory ⟨regs, .running⟩ = ⟨⟨regs, .running⟩, []⟩ := rfl

theorem fringeAddressRangeBlock_source (memory : Memory) (regs : Registers)
    (hone : regs 1127 = 1) :
    let actual := fringeAddressRangeBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧
      actual.final.regs 1117 = regs 1116 * regs 34 ∧
      actual.final.regs 1118 = min (regs 1109 - regs 1116 * regs 34) (regs 34) ∧
      actual.final.regs 1120 = min (regs 1110 + 1) ((regs 1116 + 1) * regs 34) - regs 1116 * regs 34 ∧
      (∀ r, r ≠ 1117 → r ≠ 1118 → r ≠ 1119 → r ≠ 1120 → r ≠ 1126 → r ≠ 1132 →
        actual.final.regs r = regs r) := by
  have hsub1 (r : Registers) := natSubBlock_source 1118 1109 1117 1132 memory r (by decide) (by decide)
  have hsub2 (r : Registers) := natSubBlock_source 1120 1119 1117 1132 memory r (by decide) (by decide)
  have hmin1 (r : Registers) := minBlock_source 1118 1118 34 1132 memory r (by decide) (by decide)
  have hmin2 (r : Registers) := minBlock_source 1119 1119 1126 1132 memory r (by decide) (by decide)
  simp [fringeAddressRangeBlock, Block.sequence, Block.eval_seq, Evaluation.bind,
    fs_eval_arithmetic, fs_eval_skip, hsub1, hsub2, hmin1, hmin2, Registers.write, Arithmetic.eval, hone]
  intro r h1 h2 h3 h4 h5 h6
  simp [h1, h2, h3, h4, h5, h6]

theorem fringeAddressRangeBlock_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n) (hj : regs 1116 < 33)
    (hi : regs 1110 ≤ 2 * metadataEnvelope n) (hone : regs 1127 = 1) :
    fringeAddressRangeBlock.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have ce := Nat.le_trans hc (fringe_envelope_bounds n).2.1
  have cap := (fringe_envelope_bounds n).2.2
  have ep := metadataEnvelope_pos n
  have one : 1 < 2 ^ wordWidth n := by omega
  have jc := Nat.mul_le_mul_right (regs 34) (show regs 1116 ≤ 33 by omega)
  have jc1 := Nat.mul_le_mul_right (regs 34) (show regs 1116 + 1 ≤ 33 by omega)
  unfold fringeAddressRangeBlock Block.sequence
  refine window_safe_arithmetic fit (by simp [Action.LocalSafe, Arithmetic.eval]; omega) (fun f1 => ?_)
  refine window_safe_sub f1 one (by decide) (by decide) (fun f2 => ?_)
  refine window_safe_min f2 one (by decide) (by decide) (fun f3 => ?_)
  refine window_safe_arithmetic f3 (by simp [Action.LocalSafe, Arithmetic.eval, Registers.write, hone]; omega) (fun f4 => ?_)
  refine window_safe_arithmetic f4 (by simp [Action.LocalSafe, Arithmetic.eval, Registers.write, hone]; omega) (fun f5 => ?_)
  refine window_safe_arithmetic f5 (by simpa [Action.LocalSafe, Arithmetic.eval, Registers.write, hone] using
    (show (regs 1116 + 1) * regs 34 < 2 ^ wordWidth n by omega)) (fun f6 => ?_)
  refine window_safe_min f6 one (by decide) (by decide) (fun f7 => ?_)
  exact window_safe_sub f7 one (by decide) (by decide) (fun f8 => Block.safe_skip _ _ _ f8)

theorem fringeAddressSlotBlock_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n) (hshift : regs 1117 < wordWidth n)
    (lower : regs 1118 ≤ regs 34) (upper : regs 1120 ≤ regs 34)
    (hone : regs 1127 = 1) (hradix : regs 1128 = regs 34 + 1) :
    fringeAddressSlotBlock.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have childShift : regs 34 < wordWidth n := by
    have := fourOldWidths_lt_wordWidth n
    omega
  have positive := Nat.two_pow_pos (regs 34)
  have maskFit := Nat.pow_lt_pow_right (by decide : 1 < 2) childShift
  have wordFit := fit.1 1064
  dsimp only at wordFit
  have divided := Nat.div_le_self (regs 1064) (2 ^ regs 1117)
  have masked := Nat.mod_lt (regs 1064 / 2 ^ regs 1117) positive
  have slotCap := rank_chunk_slot_fit n (regs 34) hc
  have mul1 := Nat.mul_le_mul_right (regs 34 + 1) (Nat.le_of_lt masked)
  have mul2 := Nat.mul_le_mul_right (regs 34 + 1)
    (show (regs 1064 / 2 ^ regs 1117 % 2 ^ regs 34) * (regs 34 + 1) + regs 1118 ≤
        2 ^ regs 34 * (regs 34 + 1) + regs 34 by omega)
  have bigger := Nat.le_mul_of_pos_right (2 ^ regs 34 * (regs 34 + 1) + regs 34)
    (show 0 < regs 34 + 1 by omega)
  have cap := query_small_fields_fit n
  have shiftLeft_numeric (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b
  have shiftRight_numeric (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b
  apply ScalarChecks_safe memory (wordWidth n) _ _ fit
  simp [ScalarChecks, fringeAddressSlotBlock, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState, Registers.write,
    Arithmetic.eval, hone, hradix, shiftLeft_numeric, shiftRight_numeric] <;> omega

theorem fringeAddressBlock_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 = packedFringeChunkBits n) (hj : regs 1116 < 33)
    (hi : regs 1110 ≤ 2 * metadataEnvelope n) (hone : regs 1127 = 1)
    (hradix : regs 1128 = regs 34 + 1) :
    fringeAddressBlock.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have cw : regs 34 ≤ packedReviewerCellWidth n := hc ▸ rank_chunk_le_oldWidth n
  have shift : regs 1116 * regs 34 < wordWidth n := by
    have h := Nat.mul_le_mul_right (regs 34) (show regs 1116 ≤ 32 by omega)
    have geom := (fringe_chunk_geometry n).2
    rw [← hc] at geom
    omega
  have upper : min (regs 1110 + 1) ((regs 1116 + 1) * regs 34) -
      regs 1116 * regs 34 ≤ regs 34 := by
    have h := Nat.min_le_right (regs 1110 + 1) ((regs 1116 + 1) * regs 34)
    have eq : (regs 1116 + 1) * regs 34 = regs 1116 * regs 34 + regs 34 := by simp [Nat.add_mul]
    rw [eq] at h ⊢
    omega
  have safe := fringeAddressRangeBlock_safe n memory regs fit cw hj hi hone
  have source := fringeAddressRangeBlock_source memory regs hone
  have frame := source.2.2.2.2
  apply window_safe_follow safe
  intro f1
  rw [window_data_running _ source.1] at f1 ⊢
  apply fringeAddressSlotBlock_safe n memory _ f1
  · rw [frame 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact cw
  · rw [source.2.1]; exact shift
  · rw [source.2.2.1, frame 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact Nat.min_le_right _ _
  · rw [source.2.2.2.1, frame 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact upper
  · rw [frame 1127 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hone
  · rw [frame 1128 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      frame 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hradix

theorem fringeConsiderBlock_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n)
    (acc : regs 1112 ≤ metadataEnvelope n + 33 * 2 ^ packedReviewerCellWidth n)
    (position : regs 1117 ≤ 32 * regs 34)
    (radix : regs 1128 = regs 34 + 1) (radix2 : regs 1129 = 2 * regs 34 + 2) :
    fringeConsiderBlock.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have cap := (fringe_envelope_bounds n).2.2
  have q := (fringe_envelope_bounds n).1
  have c := Nat.le_trans hc (fringe_envelope_bounds n).2.1
  have entryFit := fit.1 1123
  dsimp only at entryFit
  have divided := Nat.div_le_self (regs 1123) (regs 34 + 1)
  have decoded := Nat.mod_lt (regs 1123 / (regs 34 + 1)) (show 0 < 2 * regs 34 + 2 by omega)
  have offset := Nat.mod_lt (regs 1123) (show 0 < regs 34 + 1 by omega)
  have one : 1 < 2 ^ wordWidth n := by omega
  unfold fringeConsiderBlock Block.sequence
  refine window_safe_arithmetic fit (by simp [Action.LocalSafe, Arithmetic.eval, radix]; omega) (fun f1 => ?_)
  refine window_safe_arithmetic f1 (by simp [Action.LocalSafe, Arithmetic.eval, Registers.write, radix, radix2]; omega) (fun f2 => ?_)
  refine window_safe_arithmetic f2 (by simp [Action.LocalSafe, Arithmetic.eval, Registers.write, radix, radix2]; omega) (fun f3 => ?_)
  refine window_safe_sub f3 one (by decide) (by decide) (fun f4 => ?_)
  refine window_safe_arithmetic f4 (by simp [Action.LocalSafe, Arithmetic.eval, Registers.write, radix]; omega) (fun f5 => ?_)
  refine window_safe_arithmetic f5 (by simp [Action.LocalSafe, Arithmetic.eval, Registers.write, radix]; omega) (fun f6 => ?_)
  apply SimpleScalar.safe memory (wordWidth n) _ _ _ f6
  simp [SimpleScalar, Block.sequence, fringeKeepBestBlock]
  exact Nat.ne_of_gt (wordWidth_pos n)

theorem fringeAdvanceBlock_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n)
    (acc : regs 1112 ≤ metadataEnvelope n + 33 * 2 ^ packedReviewerCellWidth n)
    (entry : regs 1123 ≤ 2 ^ packedReviewerCellWidth n) (index : regs 1116 ≤ 33)
    (one : regs 1127 = 1) (radix : regs 1128 = regs 34 + 1)
    (radix2 : regs 1129 = 2 * regs 34 + 2) :
    fringeAdvanceBlock.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have cap := reader_polynomial_fit n
  have q := (fringe_envelope_bounds n).1
  have c := Nat.le_trans hc (fringe_envelope_bounds n).2.1
  have epos := metadataEnvelope_pos n
  have product := Nat.mul_le_mul (show regs 34 + 1 ≤ metadataEnvelope n + 1 by omega)
    (show 2 * regs 34 + 2 ≤ 2 * metadataEnvelope n + 2 by omega)
  have denominator : 0 < (regs 34 + 1) * (2 * regs 34 + 2) := Nat.mul_pos (by omega) (by omega)
  have divided := Nat.div_le_self (regs 1123) ((regs 34 + 1) * (2 * regs 34 + 2))
  have productEq : (metadataEnvelope n + 1) * (2 * metadataEnvelope n + 2) =
      2 * (metadataEnvelope n * metadataEnvelope n) + 4 * metadataEnvelope n + 2 := by
    simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
    omega
  rw [productEq] at product
  have hwne : wordWidth n ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe memory (wordWidth n) _ _ fit
  by_cases sub : regs 34 ≤ regs 1112 + regs 1123 / ((regs 34 + 1) * (2 * regs 34 + 2))
  all_goals simp [ScalarChecks, fringeAdvanceBlock, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState, Registers.write,
    Arithmetic.eval, Comparison.eval, natSubBlock, one, radix, radix2, sub, hwne] <;> omega

theorem fringeSeedAddressBlock_safe (shape : CartesianShape) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    fringeSeedAddressBlock.Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have wp : 0 < regs 32 := by
    have hw : regs 32 = packedBpCodeWordWidth shape.size := hm 16 (by decide)
    rw [hw]; exact SuccinctRank.machineWordBits_pos _
  have bp : 0 < regs 33 := by
    have hb : regs 33 = (packedInteriorLayout shape.size).blockSize := hm 17 (by decide)
    rw [hb]; change 0 < 2 * (shape.size.log2 + 1); omega
  have inputFit := fit.1 1104
  dsimp only at inputFit
  have d1 := Nat.div_le_self (regs 1104) (regs 33)
  have m1 := Nat.div_mul_le_self (regs 1104) (regs 33)
  have d2 := Nat.div_le_self (regs 1104 / regs 33 * regs 33) (regs 32)
  have m2 := Nat.div_mul_le_self (regs 1104 / regs 33 * regs 33) (regs 32)
  have cap := query_small_fields_fit shape.size
  have hwne : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe memory (wordWidth shape.size) _ _ fit
  simp [ScalarChecks, fringeSeedAddressBlock, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState, Registers.write,
    Arithmetic.eval, wp, bp, hwne] <;> omega

theorem fringeSeedDecodeBlock_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (rankBound : regs 360 ≤ metadataEnvelope n) (two : regs 1131 = 2) :
    fringeSeedDecodeBlock.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have cap := (fringe_envelope_bounds n).2.2
  have one : 1 < 2 ^ wordWidth n := by omega
  unfold fringeSeedDecodeBlock Block.sequence
  refine window_safe_arithmetic fit (by simp [Action.LocalSafe, Arithmetic.eval, two]; omega) (fun f1 => ?_)
  refine window_safe_sub f1 one (by decide) (by decide) (fun f2 => ?_)
  exact window_safe_move f2 (fun f3 => Block.safe_skip _ _ _ f3)

private theorem fringe_safe_comparison {memory : Memory} {width dst lhs rhs : Nat}
    {op : Comparison} {regs : Registers} {tail : Block}
    (fit : (⟨regs, .running⟩ : Data).Fits width) (one : 1 < 2 ^ width)
    (next : (⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩ : Data).Fits width →
      tail.Safe memory width ⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩) :
    (Block.seq (.action (.comparison op dst lhs rhs)) tail).Safe memory width ⟨regs, .running⟩ := by
  have value : op.eval (regs lhs) (regs rhs) < 2 ^ width := by
    cases op <;> simp only [Comparison.eval] <;> split <;> omega
  exact window_safe_follow (Block.safe_action memory width (.comparison op dst lhs rhs) _ fit value) next

theorem fringeDecodeBlock_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n)
    (acc : regs 1112 ≤ metadataEnvelope n + 33 * 2 ^ packedReviewerCellWidth n)
    (position : regs 1117 ≤ 32 * regs 34)
    (_hone : regs 1127 = 1) (radix : regs 1128 = regs 34 + 1)
    (radix2 : regs 1129 = 2 * regs 34 + 2) :
    fringeDecodeBlock.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have cap := (fringe_envelope_bounds n).2.2
  have one : 1 < 2 ^ wordWidth n := by omega
  unfold fringeDecodeBlock Block.sequence
  refine window_safe_sub fit one (by decide) (by decide) (fun f1 => ?_)
  refine fringe_safe_comparison f1 one (fun f2 => ?_)
  apply window_safe_follow ?_ (fun f3 => Block.safe_skip _ _ _ f3)
  apply Block.safe_ifZero f2
  split
  · exact Block.safe_skip _ _ _ f2
  · apply fringeConsiderBlock_safe n memory _ f2
    · simpa [Registers.write] using hc
    · simpa [Registers.write] using acc
    · simpa [Registers.write] using position
    · simp [Registers.write, radix]
    · simp [Registers.write, radix2]

theorem fringeFoldRangeInit_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n)) (cp : 0 < regs 34)
    (start : regs 1105 ≤ metadataEnvelope n) (span : regs 1106 ≤ metadataEnvelope n)
    (hone : regs 1127 = 1) :
    fringeFoldRangeInit.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have cap := (fringe_envelope_bounds n).2.2
  have ep := metadataEnvelope_pos n
  have one : 1 < 2 ^ wordWidth n := by omega
  have divBound := Nat.div_le_self (regs 1105 + regs 1106 - 1 - regs 1107) (regs 34)
  unfold fringeFoldRangeInit Block.sequence
  refine window_safe_sub fit one (by decide) (by decide) (fun f1 => ?_)
  refine window_safe_arithmetic f1 (by simp [Action.LocalSafe, Arithmetic.eval, Registers.write]; omega) (fun f2 => ?_)
  refine window_safe_sub f2 one (by decide) (by decide) (fun f3 => ?_)
  refine window_safe_sub f3 one (by decide) (by decide) (fun f4 => ?_)
  refine window_safe_arithmetic f4 (by simp [Action.LocalSafe, Arithmetic.eval, Registers.write, hone]; omega) (fun f5 => ?_)
  refine window_safe_arithmetic f5 (by simp [Action.LocalSafe, Arithmetic.eval, Registers.write, hone]; omega) (fun f6 => ?_)
  refine window_safe_constant f6 (by omega) (fun f7 => ?_)
  exact window_safe_min f7 one (by decide) (by decide) (fun f8 => Block.safe_skip _ _ _ f8)

theorem fringeFoldStateInit_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n) (hone : regs 1127 = 1) (htwo : regs 1131 = 2) :
    fringeFoldStateInit.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have cap := (fringe_envelope_bounds n).2.2
  have ce := Nat.le_trans hc (fringe_envelope_bounds n).2.1
  have seedFit := fit.1 1108
  dsimp only at seedFit
  apply ScalarChecks_safe memory (wordWidth n) _ _ fit
  simp [ScalarChecks, fringeFoldStateInit, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState, Registers.write,
    Arithmetic.eval, hone, htwo] <;> omega

theorem fringeFoldRangeInit_running (memory : Memory) (regs : Registers) :
    (fringeFoldRangeInit.eval memory ⟨regs, .running⟩).final.status = .running := by
  have hsub1 (r : Registers) := natSubBlock_source 1109 1105 1107 1132 memory r (by decide) (by decide)
  have hsub2 (r : Registers) := natSubBlock_source 1110 1110 1127 1132 memory r (by decide) (by decide)
  have hsub3 (r : Registers) := natSubBlock_source 1110 1110 1107 1132 memory r (by decide) (by decide)
  have hmin (r : Registers) := minBlock_source 1111 1111 1130 1132 memory r (by decide) (by decide)
  have constant (r : Registers) (dst value : Nat) :
      (Block.action (.constant dst value)).eval memory ⟨r, .running⟩ =
        ⟨⟨r.write dst value, .running⟩, []⟩ := rfl
  simp [fringeFoldRangeInit, Block.sequence, Block.eval_seq, Evaluation.bind,
    fs_eval_arithmetic, constant, fs_eval_skip, hsub1, hsub2, hsub3, hmin]

theorem fringeFoldInit_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n) (cp : 0 < regs 34)
    (start : regs 1105 ≤ metadataEnvelope n) (span : regs 1106 ≤ metadataEnvelope n)
    (hone : regs 1127 = 1) (htwo : regs 1131 = 2) :
    fringeFoldInit.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have safe := fringeFoldRangeInit_safe n memory regs fit cp start span hone
  have writes : fringeFoldRangeInit.WritesOnly
      (fun r => r = 1109 ∨ r = 1110 ∨ r = 1111 ∨ r = 1130 ∨ r = 1132) := by
    simp [fringeFoldRangeInit, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, minBlock]
  have frame (r : Nat) (outside : r ≠ 1109 ∧ r ≠ 1110 ∧ r ≠ 1111 ∧ r ≠ 1130 ∧ r ≠ 1132) :=
    Block.eval_frame memory fringeFoldRangeInit _ writes r (by omega) (⟨regs, .running⟩ : Data)
  apply window_safe_follow safe
  intro f1
  rw [window_data_running _ (fringeFoldRangeInit_running memory regs)] at f1 ⊢
  apply fringeFoldStateInit_safe n memory _ f1
  · rw [frame _ (by omega)]; exact hc
  · rw [frame _ (by omega)]; exact hone
  · rw [frame _ (by omega)]; exact htwo

def FringeCandidatePositionBound (bound : Nat) (candidate : Option (Nat × Nat)) : Prop :=
  ∀ score position, candidate = some (score, position) → position ≤ bound

theorem fringeCandidatePositionBound_merge (bound : Nat) (left right : Option (Nat × Nat))
    (hl : FringeCandidatePositionBound bound left) (hr : FringeCandidatePositionBound bound right) :
    FringeCandidatePositionBound bound (bpFringeMergeCand left right) := by
  cases left with
  | none => simpa [bpFringeMergeCand] using hr
  | some left =>
    cases right with
    | none => simpa [bpFringeMergeCand] using hl
    | some right =>
      change FringeCandidatePositionBound bound (if right.1 < left.1 then some right else some left)
      split
      · exact hr
      · exact hl

theorem fringe_step_numeric_bounds (n c lo hi j acc : Nat)
    (candidate : Option (Nat × Nat)) (entry : Option Nat)
    (ha : acc ≤ metadataEnvelope n + j * 2 ^ packedReviewerCellWidth n)
    (he : entry.getD 0 ≤ 2 ^ packedReviewerCellWidth n)
    (hj : j < 33) (best : FringeCandidatePositionBound (33 * c) candidate) :
    (bpFringeChunkStepDecoded c lo hi j (acc, candidate) entry).1 ≤
      metadataEnvelope n + (j + 1) * 2 ^ packedReviewerCellWidth n ∧
    FringeCandidatePositionBound (33 * c)
      (bpFringeChunkStepDecoded c lo hi j (acc, candidate) entry).2 := by
  constructor
  · have h := Nat.div_le_self (entry.getD 0) ((c + 1) * (2 * c + 2))
    change acc + entry.getD 0 / ((c + 1) * (2 * c + 2)) - c ≤
      metadataEnvelope n + (j + 1) * 2 ^ packedReviewerCellWidth n
    rw [show (j + 1) * 2 ^ packedReviewerCellWidth n =
      j * 2 ^ packedReviewerCellWidth n + 2 ^ packedReviewerCellWidth n by simp [Nat.add_mul]]
    omega
  · apply fringeCandidatePositionBound_merge _ _ _ best
    split
    · have modBound := Nat.mod_lt (entry.getD 0) (show 0 < c + 1 by omega)
      have mulBound := Nat.mul_le_mul_right c (show j + 1 ≤ 33 by omega)
      intro score position equal
      cases equal
      rw [Nat.add_mul, Nat.one_mul] at mulBound
      omega
    · intro score position equal
      cases equal

theorem fringeFinishBlock_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n) (base : regs 1107 ≤ metadataEnvelope n)
    (best : FringeCandidatePositionBound (33 * regs 34) (candidateOfRegs 1113 regs)) :
    fringeFinishBlock.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have cap := (fringe_envelope_bounds n).2.2
  have ce := Nat.le_trans hc (fringe_envelope_bounds n).2.1
  have one : 1 < 2 ^ wordWidth n := by omega
  unfold fringeFinishBlock Block.sequence
  refine window_safe_constant fit one (fun f1 => ?_)
  apply window_safe_follow ?_ (fun f2 => Block.safe_skip _ _ _ f2)
  apply Block.safe_ifZero f1
  split
  · apply SimpleScalar.safe memory (wordWidth n) _ _ _ f1
    trivial
  · rename_i nonzero
    have hne : regs 1113 ≠ 0 := by simpa [Registers.write] using nonzero
    have hb := best (regs 1114) (regs 1115) (by simp [candidateOfRegs, hne])
    refine window_safe_move f1 (fun f2 => ?_)
    exact window_safe_arithmetic f2 (by simp [Action.LocalSafe, Arithmetic.eval, Registers.write]; omega)
      (fun f3 => Block.safe_skip _ _ _ f3)

private theorem fringeActive_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (index : regs 1116 < 33)
    (hi : regs 1110 ≤ 2 * metadataEnvelope shape.size)
    (acc : regs 1112 ≤ metadataEnvelope shape.size + 33 * 2 ^ packedReviewerCellWidth shape.size)
    (one : regs 1127 = 1) (radix : regs 1128 = regs 34 + 1)
    (radix2 : regs 1129 = 2 * regs 34 + 2) :
    (Block.seq fringeAddressBlock (.seq reader (.seq fringeDecodeBlock fringeAdvanceBlock))).Safe
      memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have c := metadata_chunkBits shape regs hm
  have cw : regs 34 ≤ packedReviewerCellWidth shape.size := c ▸ rank_chunk_le_oldWidth shape.size
  have addressSafe := fringeAddressBlock_safe shape.size memory regs fit c index hi one radix
  have addressed := fringeAddressBlock_source memory regs one radix
  have af := fringeAddressBlock_frame memory (⟨regs, .running⟩ : Data)
  apply window_safe_follow addressSafe
  intro f1
  generalize hea : fringeAddressBlock.eval memory ⟨regs, .running⟩ = a at addressed af f1 ⊢
  rcases a with ⟨⟨ar, status⟩, reads⟩
  dsimp only at addressed af f1
  obtain ⟨asrun, _, _, _, aspos, _, _⟩ := addressed
  subst status
  have am : MetadataMatches shape ar := by
    intro i hi
    rw [af _ (by unfold FringeAddressWrites; omega)]
    exact hm i hi
  have readSafe := readerSafe _ f1 am
  have loaded := readerCorrect ar am
  have packetBound := (rank_logicalPacket_bounds shape (ar 8192) (ar 8193)).1
  apply window_safe_follow readSafe
  intro f2
  generalize hel : reader.eval memory ⟨ar, .running⟩ = loadedState at loaded f2 ⊢
  rcases loadedState with ⟨⟨br, status⟩, reads⟩
  dsimp only at loaded f2
  obtain ⟨bsrun, packet, _, _, bf⟩ := loaded
  subst status
  have keep (r : Nat) (small : r < 8194) (outside : ¬ FringeAddressWrites r) : br r = regs r :=
    (bf r (Or.inl small)).trans (af r outside)
  have bc : br 34 = regs 34 := keep _ (by decide) (by simp [FringeAddressWrites])
  have bone : br 1127 = 1 := (keep _ (by decide) (by simp [FringeAddressWrites])).trans one
  have bacc : br 1112 ≤ metadataEnvelope shape.size + 33 * 2 ^ packedReviewerCellWidth shape.size := by
    rw [keep _ (by decide) (by simp [FringeAddressWrites])]; exact acc
  have bindex : br 1116 < 33 := by
    rw [keep _ (by decide) (by simp [FringeAddressWrites])]; exact index
  have bpos : br 1117 ≤ 32 * br 34 := by
    rw [bf _ (Or.inl (by decide)), aspos, bc]
    exact Nat.mul_le_mul_right _ (by omega)
  have bradix : br 1128 = br 34 + 1 := by
    rw [keep _ (by decide) (by simp [FringeAddressWrites]), bc]; exact radix
  have bradix2 : br 1129 = 2 * br 34 + 2 := by
    rw [keep _ (by decide) (by simp [FringeAddressWrites]), bc]; exact radix2
  have decodeSafe := fringeDecodeBlock_safe shape.size memory br f2 (by rw [bc]; exact cw)
    bacc bpos bone bradix bradix2
  have decoded := fringeDecodeBlock_source memory br bone
  have df := fringeDecodeBlock_frame memory (⟨br, .running⟩ : Data)
  apply window_safe_follow decodeSafe
  intro f3
  generalize hed : fringeDecodeBlock.eval memory ⟨br, .running⟩ = decodedState at decoded df f3 ⊢
  rcases decodedState with ⟨⟨dr, status⟩, reads⟩
  dsimp only at decoded df f3
  obtain ⟨dsrun, _, dentry, _⟩ := decoded
  subst status
  apply fringeAdvanceBlock_safe shape.size memory dr f3
  · rw [df _ (by simp [FringeDecodeWrites]), bc]; exact cw
  · rw [df _ (by simp [FringeDecodeWrites])]; exact bacc
  · rw [dentry, packet]; omega
  · rw [df _ (by simp [FringeDecodeWrites])]; omega
  · rw [df _ (by simp [FringeDecodeWrites])]; exact bone
  · rw [df _ (by simp [FringeDecodeWrites]), df _ (by simp [FringeDecodeWrites])]; exact bradix
  · rw [df _ (by simp [FringeDecodeWrites]), df _ (by simp [FringeDecodeWrites])]; exact bradix2

theorem fringeBody_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (total : regs 1111 ≤ 33)
    (hi : regs 1110 ≤ 2 * metadataEnvelope shape.size)
    (acc : regs 1112 ≤ metadataEnvelope shape.size + 33 * 2 ^ packedReviewerCellWidth shape.size)
    (one : regs 1127 = 1) (radix : regs 1128 = regs 34 + 1)
    (radix2 : regs 1129 = 2 * regs 34 + 2) :
    (fringeBody reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have cap := query_small_fields_fit shape.size
  unfold fringeBody
  refine fringe_safe_comparison fit (by omega) (fun f1 => ?_)
  apply Block.safe_ifZero f1
  split
  · exact Block.safe_skip _ _ _ f1
  · rename_i active
    have enter : regs 1116 < regs 1111 := by
      simpa [Registers.write, Comparison.eval] using active
    apply fringeActive_safe shape memory reader readerSafe readerCorrect _ f1
    · intro i hi
      simp only [Registers.write, if_neg (show 16 + i ≠ 1130 by omega)]
      exact hm i hi
    · simp [Registers.write]; omega
    · simpa [Registers.write] using hi
    · simpa [Registers.write] using acc
    · simpa [Registers.write] using one
    · simpa [Registers.write] using radix
    · simpa [Registers.write] using radix2

structure FringeSafetyInvariant (shape : CartesianShape) (window : List Bool) (s : Data) : Prop where
  fits : s.Fits (wordWidth shape.size)
  metadata : MetadataMatches shape s.regs
  running : s.status = .running
  total : s.regs 1111 ≤ 33
  index : s.regs 1116 ≤ 33
  high : s.regs 1110 ≤ 2 * metadataEnvelope shape.size
  base : s.regs 1107 ≤ metadataEnvelope shape.size
  window_eq : s.regs 1064 = bitsToNatLE window
  one : s.regs 1127 = 1
  radix : s.regs 1128 = s.regs 34 + 1
  radix2 : s.regs 1129 = 2 * s.regs 34 + 2
  accumulator : s.regs 1112 ≤ metadataEnvelope shape.size +
    s.regs 1116 * 2 ^ packedReviewerCellWidth shape.size
  best : FringeCandidatePositionBound (33 * s.regs 34) (candidateOfRegs 1113 s.regs)

theorem fringeBody_preserves (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (readerWrites : ReaderWrites reader) (window : List Bool) (s : Data)
    (inv : FringeSafetyInvariant shape window s) :
    (fringeBody reader).Safe memory (wordWidth shape.size) s ∧
      FringeSafetyInvariant shape window ((fringeBody reader).eval memory s).final := by
  have stateEq := window_data_running s inv.running
  rw [stateEq] at inv ⊢
  let regs := s.regs
  have total : regs 1111 ≤ 33 := inv.total
  have index : regs 1116 ≤ 33 := inv.index
  have acc : regs 1112 ≤ metadataEnvelope shape.size + regs 1116 * 2 ^ packedReviewerCellWidth shape.size := inv.accumulator
  have limit := Nat.mul_le_mul_right (2 ^ packedReviewerCellWidth shape.size) index
  have safe := fringeBody_safe shape memory reader readerSafe readerCorrect regs
    inv.fits inv.metadata total inv.high (by omega) inv.one inv.radix inv.radix2
  refine ⟨safe, ?_⟩
  have fit := (fringeBody reader).eval_fits memory (wordWidth shape.size) _ safe
  have hm := fringeBody_metadata shape reader readerWrites memory ⟨regs, .running⟩ inv.metadata
  have frame := fringeBody_frame reader readerWrites memory (⟨regs, .running⟩ : Data)
  by_cases active : regs 1116 < regs 1111
  · have source := fringeBody_active shape memory reader readerCorrect regs window inv.metadata
      inv.window_eq inv.one inv.radix inv.radix2 active
    have entryBound : ((((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21
        (bpFringeChunkSlotAt (regs 34) window (regs 1109) (regs 1110) (regs 1116))).map bitsToNatLE).getD 0) ≤
        2 ^ packedReviewerCellWidth shape.size := by
      rw [← logicalPacket_pred]
      have h := (rank_logicalPacket_bounds shape 21
        (bpFringeChunkSlotAt (regs 34) window (regs 1109) (regs 1110) (regs 1116))).1
      omega
    have numeric := fringe_step_numeric_bounds shape.size (regs 34) (regs 1109) (regs 1110)
      (regs 1116) (regs 1112) (candidateOfRegs 1113 regs) _ acc entryBound (by omega) inv.best
    have valueEq := congrArg Prod.fst source.2.2.2
    have bestEq := congrArg Prod.snd source.2.2.2
    dsimp only at valueEq bestEq
    refine ⟨fit, hm, source.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [frame _ (by simp [FringeBodyWrites])]; exact inv.total
    · rw [source.2.2.1]; omega
    · rw [frame _ (by simp [FringeBodyWrites])]; exact inv.high
    · rw [frame _ (by simp [FringeBodyWrites])]; exact inv.base
    · rw [frame _ (by simp [FringeBodyWrites])]; exact inv.window_eq
    · rw [frame _ (by simp [FringeBodyWrites])]; exact inv.one
    · rw [frame _ (by simp [FringeBodyWrites]), frame _ (by simp [FringeBodyWrites])]; exact inv.radix
    · rw [frame _ (by simp [FringeBodyWrites]), frame _ (by simp [FringeBodyWrites])]; exact inv.radix2
    · rw [source.2.2.1, valueEq]; exact numeric.1
    · rw [frame _ (by simp [FringeBodyWrites]), bestEq]; exact numeric.2
  · have source := fringeBody_inactive reader memory regs (by omega)
    rw [source] at fit hm ⊢
    refine ⟨fit, hm, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [Registers.write] using inv.total
    · simpa [Registers.write] using inv.index
    · simpa [Registers.write] using inv.high
    · simpa [Registers.write] using inv.base
    · simpa [Registers.write] using inv.window_eq
    · simpa [Registers.write] using inv.one
    · simpa [Registers.write] using inv.radix
    · simpa [Registers.write] using inv.radix2
    · simpa [Registers.write] using inv.accumulator
    · simpa [Registers.write, candidateOfRegs] using inv.best

private theorem fringe_iterate_invariant (body : Data → Evaluation) (inv : Data → Prop)
    (step : ∀ s, inv s → inv (body s).final) (copies : Nat) (s : Data) (hs : inv s) :
    inv (iterate body copies s).final := by
  induction copies generalizing s with
  | zero => exact hs
  | succ copies ih => exact ih _ (step s hs)

theorem fringeRepeat_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (readerWrites : ReaderWrites reader) (window : List Bool) (copies : Nat) (s : Data)
    (inv : FringeSafetyInvariant shape window s) :
    (Block.repeat copies (fringeBody reader)).Safe memory (wordWidth shape.size) s ∧
      FringeSafetyInvariant shape window ((Block.repeat copies (fringeBody reader)).eval memory s).final := by
  have step := fringeBody_preserves shape memory reader readerSafe readerCorrect readerWrites window
  have safe := IterationsSafe.of_invariant ((fringeBody reader).Safe memory (wordWidth shape.size))
    (FringeSafetyInvariant shape window) ((fringeBody reader).eval memory) step copies s inv
  refine ⟨Block.safe_repeat inv.fits safe, ?_⟩
  have result := fringe_iterate_invariant ((fringeBody reader).eval memory)
    (FringeSafetyInvariant shape window) (fun s h => (step s h).2) copies s inv
  simpa only [Block.eval, inv.running] using result

private theorem fringe_initialized_finish_safe (shape : CartesianShape) (memory : Memory)
    (reader init program : Block) (copies : Nat)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (readerWrites : ReaderWrites reader) (window : List Bool) (s : Data)
    (initial : init.Safe memory (wordWidth shape.size) s)
    (inv : FringeSafetyInvariant shape window (init.eval memory s).final)
    (programEq : program = .seq init (.seq (.repeat copies (fringeBody reader)) fringeFinishBlock)) :
    program.Safe memory (wordWidth shape.size) s := by
  have repeated := fringeRepeat_safe shape memory reader readerSafe readerCorrect readerWrites
    window copies _ inv
  have finalInv := repeated.2
  have finish : fringeFinishBlock.Safe memory (wordWidth shape.size)
      ((Block.repeat copies (fringeBody reader)).eval memory (init.eval memory s).final).final := by
    have stateEq := window_data_running _ finalInv.running
    rw [stateEq] at finalInv ⊢
    apply fringeFinishBlock_safe shape.size memory _ finalInv.fits
    · rw [metadata_chunkBits shape _ finalInv.metadata]; exact rank_chunk_le_oldWidth _
    · exact finalInv.base
    · exact finalInv.best
  rw [programEq]
  exact Block.safe_seq initial (Block.safe_seq repeated.1 finish)

theorem fringeFoldBlock_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (readerWrites : ReaderWrites reader) (window : List Bool) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (start : regs 1105 ≤ metadataEnvelope shape.size) (span : regs 1106 ≤ metadataEnvelope shape.size)
    (base : regs 1107 ≤ metadataEnvelope shape.size) (seed : regs 1108 ≤ metadataEnvelope shape.size)
    (hwindow : regs 1064 = bitsToNatLE window) (hone : regs 1127 = 1) (htwo : regs 1131 = 2) :
    (fringeFoldBlock reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hc : regs 34 = packedFringeChunkBits shape.size := metadata_chunkBits shape regs hm
  have initSafe := fringeFoldInit_safe shape.size memory regs fit
    (by rw [hc]; exact rank_chunk_le_oldWidth _) (by rw [hc]; exact rank_chunk_pos _)
    start span hone htwo
  have source := fringeFoldInit_source memory regs hone htwo
  have frame (r : Nat) (outside : ¬ ((1109 ≤ r ∧ r < 1117) ∨ r = 1128 ∨ r = 1129 ∨ r = 1130 ∨ r = 1132)) :=
    Block.eval_frame memory fringeFoldInit _ fringeFoldInit_writes r outside (⟨regs, .running⟩ : Data)
  dsimp only at source
  obtain ⟨status, _, _, hiEq, countEq, accEq, bestEq, indexEq, radixEq, radix2Eq⟩ := source
  have inv : FringeSafetyInvariant shape window (fringeFoldInit.eval memory ⟨regs, .running⟩).final := by
    refine ⟨fringeFoldInit.eval_fits memory (wordWidth shape.size) _ initSafe, ?_, status,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [frame _ (by omega)]
      exact hm i hi
    · rw [countEq]; exact Nat.min_le_right _ _
    · rw [indexEq]; omega
    · rw [hiEq]; omega
    · rw [frame _ (by omega)]; exact base
    · rw [frame _ (by omega)]; exact hwindow
    · rw [frame _ (by omega)]; exact hone
    · rw [radixEq, frame _ (by omega)]
    · rw [radix2Eq, frame _ (by omega)]
    · rw [accEq, indexEq]; simpa using seed
    · rw [bestEq]
      intro score position equality
      cases equality
  exact fringe_initialized_finish_safe shape memory reader fringeFoldInit (fringeFoldBlock reader)
    33 readerSafe readerCorrect readerWrites window _ initSafe inv rfl

theorem fringeSeedBlock_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerCorrect : ReaderCorrect shape memory reader) (readerWrites : ReaderWrites reader)
    (rankSafe : ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape regs → (rankCloseBlock reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((rankCloseBlock reader).eval memory ⟨regs, .running⟩).final.regs 360 ≤ metadataEnvelope shape.size)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    (fringeSeedBlock reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have safe := fringeSeedAddressBlock_safe shape memory regs fit hm
  have source := fringeSeedAddressBlock_source memory regs
  have frame (r : Nat) (outside : r ≠ 352 ∧ r ≠ 1107 ∧ r ≠ 1127 ∧ r ≠ 1131) :=
    Block.eval_frame memory fringeSeedAddressBlock _ fringeSeedAddressBlock_writes r (by omega)
      (⟨regs, .running⟩ : Data)
  apply window_safe_follow safe
  intro f1
  generalize hea : fringeSeedAddressBlock.eval memory ⟨regs, .running⟩ = addressed at source frame f1 ⊢
  rcases addressed with ⟨⟨ar, status⟩, reads⟩
  dsimp only at source frame f1
  obtain ⟨running, _, _, _, _, two⟩ := source
  subst status
  have am : MetadataMatches shape ar := by
    intro i hi
    rw [frame _ (by omega)]
    exact hm i hi
  have rank := rankSafe ar f1 am
  have ranked := rankCloseBlock_source shape memory reader readerCorrect readerWrites ar am
  have rankFrame := rankCloseBlock_frame reader readerWrites memory (⟨ar, .running⟩ : Data)
  apply window_safe_follow rank.1
  intro f2
  have stateEq := window_data_running _ ranked.1
  rw [stateEq] at f2 ⊢
  apply fringeSeedDecodeBlock_safe shape.size memory _ f2 rank.2
  rw [rankFrame _ (by simp [RankWrapperWrites])]
  exact two

theorem fringe_seed_value_le (n blockSize close : Nat) (rank : Nat → WordRAM.TraceResult Nat) :
    (packedLocalBPSeed n rank blockSize close).value ≤ packedLocalBPWindowBase n blockSize close := by
  change packedLocalBPWindowBase n blockSize close -
    2 * (rank (packedLocalBPWindowBase n blockSize close)).value ≤ _
  exact Nat.sub_le _ _

theorem fringe_window_base_le (n blockSize close : Nat) :
    packedLocalBPWindowBase n blockSize close ≤ close :=
  Nat.le_trans (Nat.div_mul_le_self _ _) (Nat.div_mul_le_self _ _)

theorem fringeWindowFoldBlock_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (readerWrites : ReaderWrites reader) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (close : regs 1024 ≤ metadataEnvelope shape.size)
    (start : regs 1105 ≤ metadataEnvelope shape.size) (span : regs 1106 ≤ metadataEnvelope shape.size)
    (base : regs 1107 ≤ metadataEnvelope shape.size) (seed : regs 1108 ≤ metadataEnvelope shape.size)
    (hone : regs 1127 = 1) (htwo : regs 1131 = 2) :
    (fringeWindowFoldBlock reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have safe := loadWindowBlock_safe shape memory reader readerSafe readerCorrect readerWrites regs fit hm close
  have source := loadWindowBlock_source shape memory reader readerCorrect readerWrites regs hm
  have metadata := loadWindowBlock_metadata shape reader readerWrites memory (⟨regs, .running⟩ : Data) hm
  have frame := loadWindowBlock_frame reader readerWrites memory (⟨regs, .running⟩ : Data)
  apply window_safe_follow safe
  intro f1
  have stateEq := window_data_running _ source.1
  rw [stateEq] at f1 ⊢
  apply fringeFoldBlock_safe shape memory reader readerSafe readerCorrect readerWrites _ _ f1 metadata
  · rw [frame _ (by simp [WindowWrites])]; exact start
  · rw [frame _ (by simp [WindowWrites])]; exact span
  · rw [frame _ (by simp [WindowWrites])]; exact base
  · rw [frame _ (by simp [WindowWrites])]; exact seed
  · exact source.2.1
  · rw [frame _ (by simp [WindowWrites])]; exact hone
  · rw [frame _ (by simp [WindowWrites])]; exact htwo

private theorem fringe_composed_safe (shape : CartesianShape) (memory : Memory) (reader program : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (readerWrites : ReaderWrites reader)
    (rankSafe : ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape regs → (rankCloseBlock reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((rankCloseBlock reader).eval memory ⟨regs, .running⟩).final.regs 360 ≤ metadataEnvelope shape.size)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (close : regs 1104 ≤ metadataEnvelope shape.size)
    (start : regs 1105 ≤ metadataEnvelope shape.size) (span : regs 1106 ≤ metadataEnvelope shape.size)
    (programEq : program = .seq (fringeSeedBlock reader) (fringeWindowFoldBlock reader)) :
    program.Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have safe := fringeSeedBlock_safe shape memory reader readerCorrect readerWrites rankSafe regs fit hm
  have source := fringeSeedBlock_source shape memory reader readerCorrect readerWrites regs hm
  have frame := fringeSeedBlock_frame reader readerWrites memory (⟨regs, .running⟩ : Data)
  rw [programEq]
  apply window_safe_follow safe
  intro f1
  have stateEq := window_data_running _ source.1
  rw [stateEq] at f1 ⊢
  apply fringeWindowFoldBlock_safe shape memory reader readerSafe readerCorrect readerWrites _ f1
  · intro i hi
    rw [frame _ (by unfold FringeSeedWrites RankWrapperWrites; omega)]
    exact hm i hi
  · rw [source.2.2.2.1]; exact close
  · rw [frame _ (by simp [FringeSeedWrites, RankWrapperWrites])]; exact start
  · rw [frame _ (by simp [FringeSeedWrites, RankWrapperWrites])]; exact span
  · rw [source.2.1]
    exact Nat.le_trans (fringe_window_base_le _ _ _) close
  · rw [source.2.2.1]
    exact Nat.le_trans (fringe_seed_value_le _ _ _ _)
      (Nat.le_trans (fringe_window_base_le _ _ _) close)
  · exact source.2.2.2.2.1
  · exact source.2.2.2.2.2.1

theorem fringeBlock_canonical_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (close : regs 1104 ≤ metadataEnvelope shape.size)
    (start : regs 1105 ≤ metadataEnvelope shape.size) (span : regs 1106 ≤ metadataEnvelope shape.size) :
    (fringeBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ :=
  fringe_composed_safe shape (shapeMemory shape) logicalReadBlock (fringeBlock logicalReadBlock)
    (logicalReadBlock_readerSafe shape) (logicalReadBlock_correct shape) logicalReadBlock_writesOnly
    (rankCloseBlock_safe_bound shape) regs fit hm close start span rfl

set_option maxRecDepth 30000 in
theorem fringeBlock_maxEncodedField : (fringeBlock logicalReadBlock).maxEncodedField = 8270 := by rfl

set_option maxRecDepth 30000 in
theorem fringeBlock_size_fixed : (fringeBlock logicalReadBlock).size = 54297 := by rfl

theorem fringeBlock_fieldsFit (n : Nat) : (fringeBlock logicalReadBlock).FieldsFit (wordWidth n) := by
  apply Block.fieldsFit_of_maxEncodedField
  rw [fringeBlock_maxEncodedField]
  have cap := query_small_fields_fit n
  omega

theorem fringeBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (close : regs 1104 ≤ metadataEnvelope shape.size)
    (start : regs 1105 ≤ metadataEnvelope shape.size) (span : regs 1106 ≤ metadataEnvelope shape.size) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((fringeBlock logicalReadBlock).compileAt 0 ++ [.halt 7001]) 54298 ⟨regs, 0, .running⟩ := by
  have cap := query_small_fields_fit shape.size
  exact rank_compiled_safety (shapeMemory shape) (wordWidth shape.size)
    (fringeBlock logicalReadBlock) 7001 54298 regs (by rw [fringeBlock_size_fixed])
    (by omega) (fringeBlock_fieldsFit _)
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega) fit
    (fringeBlock_canonical_safe shape regs fit hm close start span)

theorem fringeReference_present (store : WordRAM.ReadStore) (n close start span : Nat) :
    (fringeReference store n close start span).value ≠ none := by
  have present (base seed position : Nat) (best : Option (Nat × Nat)) :
      bpFringeCandGlobal base seed position best ≠ none := by
    cases best <;> simp [bpFringeCandGlobal]
  simp only [fringeReference, fringeWindowReference, WordRAM.TraceResult.bind, WordRAM.TraceResult.map]
  exact present _ _ _ _

private theorem fringe_compile_candidate (memory : Memory) (block : Block) (regs : Registers)
    (expected : Option (Nat × Nat)) (receipts : List Receipt) (present : expected ≠ none)
    (status : (block.eval memory ⟨regs, .running⟩).final.status = .running)
    (value : candidateOfRegs 7000 (block.eval memory ⟨regs, .running⟩).final.regs = expected)
    (reads : (block.eval memory ⟨regs, .running⟩).reads = receipts)
    (writes : block.WritesOnly FringeWrites) :
    let actual := run memory (block.compileAt 0 ++ [.halt 7001]) (block.size + 1) ⟨regs, 0, .running⟩
    actual.result = some ((expected.getD (0, 0)).1) ∧
    actual.final.status = .halted ((expected.getD (0, 0)).1) ∧
    candidateOfRegs 7000 actual.final.regs = expected ∧ actual.reads = receipts ∧
    actual.steps ≤ block.size + 1 ∧
    (∀ r, ¬ FringeWrites r → actual.final.regs r = regs r) := by
  have score : (block.eval memory ⟨regs, .running⟩).final.regs 7001 = (expected.getD (0, 0)).1 := by
    rw [← value]
    have hn : (block.eval memory ⟨regs, .running⟩).final.regs 7000 ≠ 0 := by
      intro zero
      apply present
      rw [← value]
      simp [candidateOfRegs, zero]
    simp [candidateOfRegs, hn]
  have compiled := block.compile_with_halt memory 7001 ⟨regs, 0, .running⟩ rfl
  dsimp only [Data.ofState] at compiled
  rw [status] at compiled
  have data := compiled.1
  simp only [Block.eval, status] at data
  have frame (r : Nat) := congrArg (fun s : Data => s.regs r) data
  refine ⟨compiled.2.1.trans (congrArg some score), ?_, ?_, compiled.2.2.1.trans reads, ?_, ?_⟩
  · exact (congrArg Data.status data).trans (congrArg Status.halted score)
  · have regsEq := congrArg Data.regs data
    dsimp only at regsEq
    change candidateOfRegs 7000 _ = expected
    rw [regsEq]
    exact value
  · simpa only [List.length_append, Block.compile_length, List.length_singleton] using compiled.2.2.2
  · intro r outside
    exact (frame r).trans (Block.eval_frame memory block FringeWrites writes r outside ⟨regs, .running⟩)

theorem fringeRun_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (close : regs 1104 ≤ metadataEnvelope shape.size)
    (start : regs 1105 ≤ metadataEnvelope shape.size) (span : regs 1106 ≤ metadataEnvelope shape.size) :
    let expected := fringeReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 1104) (regs 1105) (regs 1106)
    let program := (fringeBlock logicalReadBlock).compileAt 0 ++ [.halt 7001]
    let actual := run (shapeMemory shape) program 54298 ⟨regs, 0, .running⟩
    actual.result = some ((expected.value.getD (0, 0)).1) ∧
    actual.final.status = .halted ((expected.value.getD (0, 0)).1) ∧
    candidateOfRegs 7000 actual.final.regs = expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 54298 ∧ (∀ r, ¬ FringeWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program 54298 ⟨regs, 0, .running⟩ := by
  have source := fringeBlock_source shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm
  have actual := fringe_compile_candidate (shapeMemory shape) (fringeBlock logicalReadBlock) regs
    _ _ (fringeReference_present _ _ _ _ _) source.1 source.2.1 source.2.2.1
    (fringeBlock_writes logicalReadBlock logicalReadBlock_writesOnly)
  rw [fringeBlock_size_fixed] at actual
  exact ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2.1, actual.2.2.2.2.1,
    actual.2.2.2.2.2, source.2.2.2, fringeBlock_execution_safe shape regs fit hm close start span⟩

theorem fringe_sameAllocation_safety (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (close : regs 1104 ≤ metadataEnvelope shape.size)
    (start : regs 1105 ≤ metadataEnvelope shape.size) (span : regs 1106 ≤ metadataEnvelope shape.size) :
    (shapeMemory shape).length * wordWidth shape.size ≤ 2 * shape.size + allocationRho shape.size ∧
    wordWidth shape.size ≤ 192 * (Nat.log2 (shape.size + 2) + 1) ∧
    (∀ value ∈ shapeMemory shape, value < 2 ^ wordWidth shape.size) ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((fringeBlock logicalReadBlock).compileAt 0 ++ [.halt 7001]) 54298 ⟨regs, 0, .running⟩ :=
  ⟨shapeMemory_capacity_le shape, wordWidth_le_log shape.size, shapeMemory_words_fit shape,
    fringeBlock_execution_safe shape regs fit hm close start span⟩

namespace FringeSafetyConsumers

theorem canonical_source (shape : CartesianShape) :
    ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) → MetadataMatches shape regs →
      regs 1104 ≤ metadataEnvelope shape.size → regs 1105 ≤ metadataEnvelope shape.size →
      regs 1106 ≤ metadataEnvelope shape.size →
      (fringeBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ :=
  fringeBlock_canonical_safe shape

theorem zero_inputs (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (close : regs 1104 = 0) (start : regs 1105 = 0) (span : regs 1106 = 0) :
    let program := (fringeBlock logicalReadBlock).compileAt 0 ++ [.halt 7001]
    (∀ k, k ≤ 54298 → (run (shapeMemory shape) program k ⟨regs, 0, .running⟩).final.Fits (wordWidth shape.size)) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      (run (shapeMemory shape) program 54298 ⟨regs, 0, .running⟩).transitions[index]? = some t →
      t.receipt = some receipt → receipt.address < 2 ^ wordWidth shape.size ∧
      receipt.reply = (shapeMemory shape)[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ wordWidth shape.size)) := by
  have safe := fringeBlock_execution_safe shape regs fit hm
    (by rw [close]; exact Nat.zero_le _) (by rw [start]; exact Nat.zero_le _)
    (by rw [span]; exact Nat.zero_le _)
  exact ⟨safe.2.2.2.1, safe.2.2.2.2⟩

theorem empty_shape (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth (SuccinctClassic.cartesianShape []).size))
    (hm : MetadataMatches (SuccinctClassic.cartesianShape []) regs)
    (close : regs 1104 = 0) (start : regs 1105 = 0) (span : regs 1106 = 0) :
    RankExecutionSafety (shapeMemory (SuccinctClassic.cartesianShape []))
      (wordWidth (SuccinctClassic.cartesianShape []).size)
      ((fringeBlock logicalReadBlock).compileAt 0 ++ [.halt 7001]) 54298 ⟨regs, 0, .running⟩ :=
  fringeBlock_execution_safe (SuccinctClassic.cartesianShape []) regs fit hm
    (by rw [close]; exact Nat.zero_le _) (by rw [start]; exact Nat.zero_le _)
    (by rw [span]; exact Nat.zero_le _)

theorem absent_entry_step (n c lo hi j acc : Nat) (candidate : Option (Nat × Nat))
    (ha : acc ≤ metadataEnvelope n + j * 2 ^ packedReviewerCellWidth n)
    (hj : j < 33) (best : FringeCandidatePositionBound (33 * c) candidate) :
    (bpFringeChunkStepDecoded c lo hi j (acc, candidate) none).1 ≤
      metadataEnvelope n + (j + 1) * 2 ^ packedReviewerCellWidth n ∧
    FringeCandidatePositionBound (33 * c)
      (bpFringeChunkStepDecoded c lo hi j (acc, candidate) none).2 :=
  fringe_step_numeric_bounds n c lo hi j acc candidate none ha (Nat.zero_le _) hj best

end FringeSafetyConsumers

end RMQ.SuccinctFinal.PackedWordRAM
