import RMQ.Core.WordRAM.Packed.ReaderSafety
import RMQ.Core.WordRAM.Packed.RankProof

/-! Scalar and primitive-run safety of the fixed rank routines. -/
namespace RMQ.SuccinctFinal.PackedWordRAM
open Cartesian PackedCellProbe Structured SuccinctSpace SuccinctClose

theorem chunkRank_le_chunk (c length entry target : Nat) (hl : length ≤ c) :
    chunkRank c length entry target ≤ c := by
  have hm := Nat.mod_lt (entry / (c + 1)) (show 0 < 2 * (c + 1) by omega)
  unfold chunkRank
  split <;> dsimp only <;> omega

theorem chunkRankBlock_safe (base width : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits width) (length : s.regs (base + 1) ≤ s.regs base)
    (cap : 4 * (s.regs base + 1) < 2 ^ width) :
    (chunkRankBlock base).Safe memory width s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs length cap
      subst status
      apply ScalarChecks_safe memory width _ _ fit
      have hwne : width ≠ 0 := by intro h; simp [h] at cap; omega
      have fe := fit.1 (base + 2)
      dsimp only at fe
      have hd := Nat.div_le_self (regs (base + 2)) (regs base + 1)
      have hm := Nat.mod_lt (regs (base + 2) / (regs base + 1))
        (show 0 < 2 * (regs base + 1) by omega)
      by_cases hsub : regs base ≤ regs (base + 2) / (regs base + 1) %
          (2 * (regs base + 1)) + regs (base + 1)
      · by_cases ht : regs (base + 3) = 0
        · by_cases hn : (regs (base + 2) / (regs base + 1) % (2 * (regs base + 1)) +
              regs (base + 1) - regs base) / 2 ≤ regs (base + 1)
          all_goals simp [ScalarChecks, chunkRankBlock, Block.sequence, Block.eval,
            Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
            Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval,
            natSubBlock, hsub, ht, hn, hwne] <;> omega
        · simp [ScalarChecks, chunkRankBlock, Block.sequence, Block.eval,
            Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
            Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval,
            natSubBlock, hsub, ht, hwne] <;> omega
      · have hz : regs (base + 2) / (regs base + 1) % (2 * (regs base + 1)) +
            regs (base + 1) - regs base = 0 := Nat.sub_eq_zero_of_le (by omega)
        by_cases ht : regs (base + 3) = 0
        all_goals simp [ScalarChecks, chunkRankBlock, Block.sequence, Block.eval,
          Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
          Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval,
          natSubBlock, hsub, ht, hwne] <;> omega
  · exact Block.safe_stopped memory width _ s fit hs

theorem chunkSlotBlock_safe (base width : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits width) (hc : s.regs (base + 1) < width)
    (shift : s.regs (base + 2) * s.regs (base + 1) < width)
    (cap : (2 ^ s.regs (base + 1) * (s.regs (base + 1) + 1) +
      s.regs (base + 1)) * (s.regs (base + 1) + 1) + s.regs (base + 1) < 2 ^ width) :
    (chunkSlotBlock base).Safe memory width s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs hc shift cap
      subst status
      apply ScalarChecks_safe memory width _ _ fit
      have hwne : width ≠ 0 := by omega
      have fw := fit.1 base
      have fe := fit.1 (base + 3)
      dsimp only at fw fe
      have widthfit := Nat.lt_two_pow_self (n := width)
      have mask := Nat.pow_lt_pow_right (by decide : 1 < 2) hc
      have maskpos := Nat.two_pow_pos (regs (base + 1))
      have hd := Nat.div_le_self (regs base) (2 ^ (regs (base + 2) * regs (base + 1)))
      have hm := Nat.mod_lt (regs base / 2 ^ (regs (base + 2) * regs (base + 1))) maskpos
      have hp := Nat.mul_le_mul_right (regs (base + 1) + 1) (Nat.le_of_lt hm)
      have hq := Nat.mul_le_mul_right (regs (base + 1) + 1)
        (show regs base / 2 ^ (regs (base + 2) * regs (base + 1)) %
          2 ^ regs (base + 1) * (regs (base + 1) + 1) + regs (base + 1) ≤
          2 ^ regs (base + 1) * (regs (base + 1) + 1) + regs (base + 1) by omega)
      have hmono := Nat.le_mul_of_pos_right
        (2 ^ regs (base + 1) * (regs (base + 1) + 1) + regs (base + 1))
        (show 0 < regs (base + 1) + 1 by omega)
      have shiftLeft_numeric (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b
      have shiftRight_numeric (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b
      by_cases hsub : regs (base + 2) * regs (base + 1) ≤ regs (base + 3)
      · by_cases hmin : regs (base + 1) ≤ regs (base + 3) - regs (base + 2) * regs (base + 1)
        · simp [ScalarChecks, chunkSlotBlock, Block.sequence, Block.eval, Action.eval,
            Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
            Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, minBlock,
            shiftLeft_numeric, shiftRight_numeric, hsub, hmin, hwne] <;> omega
        · have hsmall := Nat.mul_le_mul_right (regs (base + 1) + 1)
            (show regs base / 2 ^ (regs (base + 2) * regs (base + 1)) %
              2 ^ regs (base + 1) * (regs (base + 1) + 1) +
              (regs (base + 3) - regs (base + 2) * regs (base + 1)) ≤
              2 ^ regs (base + 1) * (regs (base + 1) + 1) + regs (base + 1) by omega)
          simp [ScalarChecks, chunkSlotBlock, Block.sequence, Block.eval, Action.eval,
            Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
            Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, minBlock,
            shiftLeft_numeric, shiftRight_numeric, hsub, hmin, hwne] <;> omega
      · have hsmall := Nat.mul_le_mul_right (regs (base + 1) + 1)
          (show regs base / 2 ^ (regs (base + 2) * regs (base + 1)) %
            2 ^ regs (base + 1) * (regs (base + 1) + 1) ≤
            2 ^ regs (base + 1) * (regs (base + 1) + 1) + regs (base + 1) by omega)
        by_cases hc0 : regs (base + 1) = 0
        all_goals simp [ScalarChecks, chunkSlotBlock, Block.sequence, Block.eval, Action.eval,
          Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
          Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, minBlock,
          shiftLeft_numeric, shiftRight_numeric, hsub, hc0, hwne] <;> omega
  · exact Block.safe_stopped memory width _ s fit hs

theorem rank_chunk_pos (n : Nat) : 0 < packedFringeChunkBits n :=
  bpFringeChunkBits_pos (2 * n)

theorem rank_chunk_le_oldWidth (n : Nat) :
    packedFringeChunkBits n ≤ packedReviewerCellWidth n := by
  have hbp : packedBpCodeWordWidth n ≤ packedReviewerCellWidth n := by
    apply packedReviewerMachineWordBits_le_cellWidth
    have := packedTwoMul_le_reviewerBound n
    omega
  have hc : packedFringeChunkBits n ≤ packedBpCodeWordWidth n := by
    change Nat.log2 (2 * n) / 8 + 1 ≤ Nat.log2 (2 * n) + 1
    have := Nat.div_le_self (Nat.log2 (2 * n)) 8
    omega
  omega

theorem rank_polynomial_fit (n : Nat) :
    32 * (metadataEnvelope n * metadataEnvelope n * metadataEnvelope n) <
      2 ^ wordWidth n := by
  have he : metadataEnvelope n = 2 ^ (6 + packedReviewerCellWidth n * 2) := by
    simp [metadataEnvelope, Nat.pow_add, Nat.pow_mul]
  rw [he]
  change 2 ^ 5 * (2 ^ (6 + packedReviewerCellWidth n * 2) *
    2 ^ (6 + packedReviewerCellWidth n * 2) * 2 ^ (6 + packedReviewerCellWidth n * 2)) < _
  rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
  apply Nat.pow_lt_pow_right (by decide)
  unfold wordWidth
  omega

theorem rank_output_envelope (n : Nat) :
    8 * packedReviewerCellWidth n + 2 * 2 ^ packedReviewerCellWidth n ≤
      metadataEnvelope n := by
  have hw := Nat.lt_two_pow_self (n := packedReviewerCellWidth n)
  have hp := Nat.two_pow_pos (packedReviewerCellWidth n)
  have hq := Nat.le_mul_of_pos_right (2 ^ packedReviewerCellWidth n) hp
  unfold metadataEnvelope
  rw [Nat.pow_two]
  omega

theorem rank_chunk_slot_fit (n c : Nat) (hc : c ≤ packedReviewerCellWidth n) :
    (2 ^ c * (c + 1) + c) * (c + 1) + c < 2 ^ wordWidth n := by
  let e := metadataEnvelope n
  have ep : 0 < e := metadataEnvelope_pos n
  have wo := Nat.lt_two_pow_self (n := packedReviewerCellWidth n)
  have ho := rank_output_envelope n
  have cp : c + 1 ≤ e := by dsimp only [e]; omega
  have pp : 2 ^ c ≤ e := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hc
    dsimp only [e]
    omega
  have square : e ≤ e * e := by
    simpa using Nat.mul_le_mul_left e (show 1 ≤ e by omega)
  have cube : e * e ≤ e * e * e := by
    simpa using Nat.mul_le_mul_left (e * e) (show 1 ≤ e by omega)
  have p := Nat.mul_le_mul pp cp
  have q := Nat.mul_le_mul
    (show 2 ^ c * (c + 1) + c ≤ 2 * (e * e) by omega) cp
  have cap := rank_polynomial_fit n
  change 32 * (e * e * e) < _ at cap
  simp only [Nat.mul_assoc] at q cap cube
  omega

theorem chunkSlotBlock_canonical_safe (base n : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits (wordWidth n))
    (hc : s.regs (base + 1) ≤ packedReviewerCellWidth n)
    (hj : s.regs (base + 2) < 8) :
    (chunkSlotBlock base).Safe memory (wordWidth n) s := by
  apply chunkSlotBlock_safe base (wordWidth n) memory s fit
  · have := oldWidth_lt_wordWidth n; omega
  · have hp := Nat.mul_le_mul (show s.regs (base + 2) ≤ 7 by omega) hc
    unfold wordWidth
    omega
  · exact rank_chunk_slot_fit n _ hc

theorem chunkRankBlock_canonical_safe (base n : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits (wordWidth n)) (hc : s.regs base ≤ packedReviewerCellWidth n)
    (hl : s.regs (base + 1) ≤ s.regs base) :
    (chunkRankBlock base).Safe memory (wordWidth n) s := by
  apply chunkRankBlock_safe base (wordWidth n) memory s fit hl
  have env := rank_output_envelope n
  have pos := Nat.two_pow_pos (packedReviewerCellWidth n)
  have cap := reader_polynomial_fit n
  omega

private theorem rank_data_running (s : Data) (hs : s.status = .running) :
    s = ⟨s.regs, .running⟩ := by cases s; simp_all

private theorem rank_safe_follow {memory : Memory} {width : Nat}
    {first second : Block} {s : Data} (head : first.Safe memory width s)
    (tail : (first.eval memory s).final.Fits width →
      second.Safe memory width (first.eval memory s).final) :
    (Block.seq first second).Safe memory width s :=
  Block.safe_seq head (tail (first.eval_fits memory width s head))

private theorem rank_safe_step {memory : Memory} {width : Nat}
    {op : Action} {rest : Block} {regs : Registers}
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (operation : op.LocalSafe memory width ⟨regs, .running⟩)
    (tail : (op.eval memory ⟨regs, .running⟩).final.Fits width →
      rest.Safe memory width (op.eval memory ⟨regs, .running⟩).final) :
    (Block.seq (.action op) rest).Safe memory width ⟨regs, .running⟩ :=
  rank_safe_follow (Block.safe_action memory width op _ fit operation) tail

private theorem rank_safe_move {memory : Memory} {width dst src : Nat}
    {rest : Block} {regs : Registers} (fit : (⟨regs, .running⟩ : Data).Fits width)
    (tail : (⟨regs.write dst (regs src), .running⟩ : Data).Fits width →
      rest.Safe memory width ⟨regs.write dst (regs src), .running⟩) :
    (Block.seq (.action (.move dst src)) rest).Safe memory width ⟨regs, .running⟩ :=
  rank_safe_step fit (fit.1 src) tail

private theorem rank_safe_constant {memory : Memory} {width dst value : Nat}
    {rest : Block} {regs : Registers} (fit : (⟨regs, .running⟩ : Data).Fits width)
    (valueFit : value < 2 ^ width)
    (tail : (⟨regs.write dst value, .running⟩ : Data).Fits width →
      rest.Safe memory width ⟨regs.write dst value, .running⟩) :
    (Block.seq (.action (.constant dst value)) rest).Safe memory width ⟨regs, .running⟩ :=
  rank_safe_step fit valueFit tail

private theorem rank_safe_arithmetic {memory : Memory} {width dst lhs rhs : Nat}
    {op : Arithmetic} {rest : Block} {regs : Registers}
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (operation : (Action.arithmetic op dst lhs rhs).LocalSafe memory width ⟨regs, .running⟩)
    (tail : (⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩ : Data).Fits width →
      rest.Safe memory width ⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩) :
    (Block.seq (.action (.arithmetic op dst lhs rhs)) rest).Safe memory width ⟨regs, .running⟩ :=
  rank_safe_step fit operation tail

private theorem rank_metadata_frame (shape : CartesianShape) (memory : Memory)
    (block : Block) (allowed : Nat → Prop) (writes : block.WritesOnly allowed)
    (outside : ∀ r, 16 ≤ r → r < 190 → ¬ allowed r)
    (s : Data) (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape (block.eval memory s).final.regs := by
  intro i hi
  rw [Block.eval_frame memory block allowed writes _ (outside _ (by omega) (by omega))]
  exact hm i hi

theorem rankWordAddress_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n) (hj : regs 261 < 8) :
    rankWordAddress.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth n by unfold wordWidth; omega)
  unfold rankWordAddress Block.sequence
  refine rank_safe_move fit (fun f1 => ?_)
  refine rank_safe_move f1 (fun f2 => ?_)
  refine rank_safe_move f2 (fun f3 => ?_)
  refine rank_safe_move f3 (fun f4 => ?_)
  have chunk := chunkSlotBlock_canonical_safe 280 n memory _ f4
    (by simpa [Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write] using hc)
    (by simpa [Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write] using hj)
  refine rank_safe_follow chunk (fun f5 => ?_)
  apply SimpleScalar.safe memory (wordWidth n) _ _ _ f5
  simp [SimpleScalar]
  omega

theorem rankWordDecode_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n) (hl : regs 284 ≤ regs 34)
    (ha : regs 260 ≤ 8 * packedReviewerCellWidth n)
    (hj : regs 261 ≤ 8) (hone : regs 265 = 1) :
    rankWordDecode.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have cap := reader_polynomial_fit n
  have env := rank_output_envelope n
  have pos := Nat.two_pow_pos (packedReviewerCellWidth n)
  have one : 1 < 2 ^ wordWidth n := by omega
  unfold rankWordDecode Block.sequence
  refine rank_safe_move fit (fun f1 => ?_)
  refine rank_safe_move f1 (fun f2 => ?_)
  have sub := natSubBlock_safe memory (wordWidth n) 302 8194 265 303 _ f2 one
    (by decide) (by decide)
  refine rank_safe_follow sub (fun f3 => ?_)
  have srcSub := natSubBlock_source 302 8194 265 303 memory
    ((regs.write 300 (regs 34)).write 301 ((regs.write 300 (regs 34)) 284)) (by decide) (by decide)
  rw [srcSub] at f3 ⊢
  refine rank_safe_move f3 (fun f4 => ?_)
  have chunk := chunkRankBlock_canonical_safe 300 n memory _ f4
    (by simpa [Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write] using hc)
    (by simpa [Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write] using hl)
  refine rank_safe_follow chunk (fun f5 => ?_)
  let prepared := (((((regs.write 300 (regs 34)).write 301 (regs 284)).write
    303 (Comparison.le.eval (regs 265) (regs 8194))).write
    302 (regs 8194 - regs 265)).write 303 (regs 259))
  have hs := chunkRankBlock_source 300 memory prepared
  have hf260 := chunkRankBlock_frame 300 memory ⟨prepared, .running⟩ 260 (by omega)
  have hf261 := chunkRankBlock_frame 300 memory ⟨prepared, .running⟩ 261 (by omega)
  have hf265 := chunkRankBlock_frame 300 memory ⟨prepared, .running⟩ 265 (by omega)
  have hb := chunkRank_le_chunk (regs 34) (regs 284) (regs 8194 - regs 265) (regs 259) hl
  change ((chunkRankBlock 300).eval memory ⟨prepared, .running⟩).final.Fits (wordWidth n) at f5
  change (Block.seq (.action (.arithmetic .add 260 260 304))
    (.seq (.action (.arithmetic .add 261 261 265)) .skip)).Safe memory (wordWidth n)
      ((chunkRankBlock 300).eval memory ⟨prepared, .running⟩).final
  simp [prepared, Registers.write] at hs hf260 hf261 hf265
  generalize he : (chunkRankBlock 300).eval memory ⟨prepared, .running⟩ = decoded
    at hs hf260 hf261 hf265 f5 ⊢
  rcases decoded with ⟨⟨out, status⟩, reads⟩
  dsimp only at hs hf260 hf261 hf265 f5
  obtain ⟨hst, _, hv⟩ := hs
  subst status
  rw [hone] at hb
  apply ScalarChecks_safe memory (wordWidth n) _ _ f5
  simp [ScalarChecks, Block.eval, Action.eval, Action.instruction, Action.LocalSafe,
    execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
    hf260, hf261, hf265, hone, hv]
  omega

theorem rankWordInit_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : 0 < regs 34) (hl : regs 257 ≤ packedReviewerCellWidth n) :
    rankWordInit.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have cap := reader_polynomial_fit n
  have env := rank_output_envelope n
  have pos := Nat.two_pow_pos (packedReviewerCellWidth n)
  have one : 1 < 2 ^ wordWidth n := by omega
  have quotient := Nat.div_le_self (min (regs 258) (regs 257) - 1) (regs 34)
  have effective := Nat.min_le_right (regs 258) (regs 257)
  unfold rankWordInit Block.sequence
  refine rank_safe_constant fit one (fun f1 => ?_)
  refine rank_safe_follow (minBlock_safe memory (wordWidth n) 262 258 257 264 _ f1 one)
    (fun f2 => ?_)
  rw [minBlock_source 262 258 257 264 memory _ (by decide) (by decide)] at f2 ⊢
  refine rank_safe_follow (natSubBlock_safe memory (wordWidth n) 263 262 265 264 _ f2 one
    (by decide) (by decide)) (fun f3 => ?_)
  rw [natSubBlock_source 263 262 265 264 memory _ (by decide) (by decide)] at f3 ⊢
  refine rank_safe_arithmetic f3 ?_ (fun f4 => ?_)
  · simp [Action.LocalSafe, Registers.write, Arithmetic.eval]
    omega
  refine rank_safe_arithmetic f4 ?_ (fun f5 => ?_)
  · simp [Action.LocalSafe, Registers.write, Arithmetic.eval]
    omega
  refine rank_safe_constant f5 (by change 8 < _; omega) (fun f6 => ?_)
  refine rank_safe_follow (minBlock_safe memory (wordWidth n) 263 263 266 264 _ f6 one)
    (fun f7 => ?_)
  apply SimpleScalar.safe memory (wordWidth n) _ _ _ f7
  simp [SimpleScalar]
  exact Nat.two_pow_pos _

theorem rankWordBody_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (htotal : regs 263 ≤ 8) (hj : regs 261 ≤ 8)
    (ha : regs 260 ≤ 8 * packedReviewerCellWidth shape.size) (hone : regs 265 = 1) :
    (rankWordBody reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have one : 1 < 2 ^ wordWidth shape.size := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 1 ≤ wordWidth shape.size by unfold wordWidth; omega)
    omega
  unfold rankWordBody
  refine rank_safe_step fit ?_ (fun comparedFit => ?_)
  · simp only [Action.LocalSafe, Comparison.eval]
    split <;> omega
  by_cases active : regs 261 < regs 263
  · have hcompare : Comparison.lt.eval (regs 261) (regs 263) = 1 := by
      simp [Comparison.eval, active]
    simp only [Action.eval, Action.instruction, execute, State.writeNext, Data.ofState,
      hcompare] at comparedFit ⊢
    apply Block.safe_ifZero comparedFit
    simp only [Registers.write_same, Nat.one_ne_zero, if_false]
    let compared := regs.write 264 1
    have metaCompared := MetadataMatches.write shape regs hm 264 1 (Or.inr (by decide))
    have hc : compared 34 ≤ packedReviewerCellWidth shape.size := by
      rw [metadata_chunkBits shape compared metaCompared]
      exact rank_chunk_le_oldWidth shape.size
    have addressSafe := rankWordAddress_safe shape.size memory compared comparedFit hc
      (by dsimp [compared, Registers.write]; omega)
    refine rank_safe_follow addressSafe (fun addressFit => ?_)
    have addressSource := rankWordAddress_source memory compared
    have addressMeta := rank_metadata_frame shape memory rankWordAddress _ rankWordAddress_writes
      (by intro r hlo hhi; omega) ⟨compared, .running⟩ metaCompared
    have addressFrame (r : Nat) (ho : (r < 280 ∨ 292 ≤ r) ∧ r ≠ 8192 ∧ r ≠ 8193) :=
      rankWordAddress_frame memory ⟨compared, .running⟩ r ho
    generalize heA : rankWordAddress.eval memory ⟨compared, .running⟩ = addressed
      at addressSource addressMeta addressFrame addressFit ⊢
    rcases addressed with ⟨⟨ar, ast⟩, receipts⟩
    dsimp only at addressSource addressMeta addressFrame addressFit
    obtain ⟨hast, _, _, _, hlength⟩ := addressSource
    subst ast
    have rs := readerSafe ⟨ar, .running⟩ addressFit addressMeta
    refine rank_safe_follow rs (fun readFit => ?_)
    have readSource := readerCorrect ar addressMeta
    generalize heR : reader.eval memory ⟨ar, .running⟩ = read
      at readFit readSource ⊢
    rcases read with ⟨⟨rr, rst⟩, rreceipts⟩
    dsimp only at readFit readSource
    obtain ⟨hrst, _, _, _, frame⟩ := readSource
    subst rst
    have hf (r : Nat) (hr : r < 280 ∨ 292 ≤ r) (hr2 : r < 8192)
        (hne : r ≠ 264) : rr r = regs r := by
      rw [frame r (Or.inl (by omega)), addressFrame r ⟨hr, by omega, by omega⟩]
      simp only [compared, Registers.write, if_neg hne]
    have h34 : rr 34 = regs 34 := hf 34 (by omega) (by omega) (by decide)
    apply rankWordDecode_safe shape.size memory rr readFit
    · rw [h34, metadata_chunkBits shape regs hm]
      exact rank_chunk_le_oldWidth shape.size
    · rw [frame 284 (Or.inl (by decide)), hlength, h34]
      simpa only [compared, Registers.write] using
        Nat.min_le_left (compared 34) (compared 262 - compared 261 * compared 34)
    · rw [hf 260 (by omega) (by omega) (by decide)]; exact ha
    · rw [hf 261 (by omega) (by omega) (by decide)]; exact hj
    · rw [hf 265 (by omega) (by omega) (by decide)]; exact hone
  · have hzero : Comparison.lt.eval (regs 261) (regs 263) = 0 := by
      simp [Comparison.eval, active]
    simp only [Action.eval, Action.instruction, execute, State.writeNext, Data.ofState,
      hzero] at comparedFit ⊢
    apply Block.safe_ifZero comparedFit
    simp only [Registers.write_same, if_true]
    exact Block.safe_skip memory _ _ comparedFit

structure RankWordInvariant (shape : CartesianShape) (s : Data) : Prop where
  fits : s.Fits (wordWidth shape.size)
  metadata : MetadataMatches shape s.regs
  running : s.status = .running
  total : s.regs 263 ≤ 8
  index : s.regs 261 ≤ 8
  accumulator : s.regs 260 ≤ s.regs 261 * s.regs 34
  one : s.regs 265 = 1

private theorem rankWordBody_preserves (shape : CartesianShape) (memory : Memory)
    (reader : Block) (readerSafe : ReaderSafe shape memory reader)
    (readerCorrect : ReaderCorrect shape memory reader) (readerWrites : ReaderWrites reader)
    (s : Data) (inv : RankWordInvariant shape s) :
    (rankWordBody reader).Safe memory (wordWidth shape.size) s ∧
      RankWordInvariant shape ((rankWordBody reader).eval memory s).final := by
  have stateEq := rank_data_running s inv.running
  rw [stateEq] at inv ⊢
  let regs := s.regs
  have total : regs 263 ≤ 8 := inv.total
  have index : regs 261 ≤ 8 := inv.index
  have accumulator : regs 260 ≤ regs 261 * regs 34 := inv.accumulator
  have hc : regs 34 ≤ packedReviewerCellWidth shape.size := by
    rw [metadata_chunkBits shape regs inv.metadata]
    exact rank_chunk_le_oldWidth shape.size
  have acc := Nat.mul_le_mul index hc
  have safe := rankWordBody_safe shape memory reader readerSafe readerCorrect regs
    inv.fits inv.metadata total index (by omega) inv.one
  refine ⟨safe, ?_⟩
  have fit := (rankWordBody reader).eval_fits memory (wordWidth shape.size) _ safe
  have metadataAfter := rankWordBody_metadata shape reader readerWrites memory
    ⟨regs, .running⟩ inv.metadata
  have frame (r : Nat) (outside : ¬ RankWordBodyWrites r) :=
    rankWordBody_frame reader readerWrites memory ⟨regs, .running⟩ r outside
  by_cases active : regs 261 < regs 263
  · have source := rankWordBody_active shape memory reader readerCorrect regs
      inv.metadata active inv.one
    refine ⟨fit, metadataAfter, source.1, ?_, ?_, ?_, ?_⟩
    · rw [frame 263 (by simp [RankWordBodyWrites])]; exact inv.total
    · rw [source.2.2.2]
      omega
    · rw [source.2.2.1, source.2.2.2, frame 34 (by simp [RankWordBodyWrites])]
      have contribution := chunkRank_le_chunk (regs 34)
        (min (regs 34) (regs 262 - regs 261 * regs 34))
        ((((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21
          (chunkSlot (regs 256) (regs 34) (regs 261) (regs 262))).map bitsToNatLE).getD 0)
        (regs 259) (Nat.min_le_left _ _)
      rw [Nat.add_mul, Nat.one_mul]
      dsimp only
      omega
    · rw [frame 265 (by simp [RankWordBodyWrites])]; exact inv.one
  · have source := rankWordBody_inactive reader memory regs (by omega)
    rw [source] at fit metadataAfter ⊢
    refine ⟨fit, metadataAfter, rfl, ?_, ?_, ?_, ?_⟩
    · simpa only [Registers.write] using inv.total
    · simpa only [Registers.write] using inv.index
    · simpa only [Registers.write] using inv.accumulator
    · simpa only [Registers.write] using inv.one

private theorem rank_iterate_invariant (body : Data → Evaluation) (invariant : Data → Prop)
    (step : ∀ s, invariant s → invariant (body s).final) (count : Nat) (s : Data)
    (hs : invariant s) : invariant (iterate body count s).final := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih _ (step s hs)

private theorem rankWordRepeat_safe (shape : CartesianShape) (memory : Memory)
    (reader : Block) (readerSafe : ReaderSafe shape memory reader)
    (readerCorrect : ReaderCorrect shape memory reader) (readerWrites : ReaderWrites reader)
    (copies : Nat) (s : Data) (inv : RankWordInvariant shape s) :
    (Block.repeat copies (rankWordBody reader)).Safe memory (wordWidth shape.size) s ∧
      RankWordInvariant shape ((Block.repeat copies (rankWordBody reader)).eval memory s).final := by
  have step := rankWordBody_preserves shape memory reader readerSafe readerCorrect readerWrites
  have iterations := IterationsSafe.of_invariant
    ((rankWordBody reader).Safe memory (wordWidth shape.size)) (RankWordInvariant shape)
    ((rankWordBody reader).eval memory) step copies s inv
  refine ⟨Block.safe_repeat inv.fits iterations, ?_⟩
  have result := rank_iterate_invariant ((rankWordBody reader).eval memory)
    (RankWordInvariant shape) (fun s h => (step s h).2) copies s inv
  simpa only [Block.eval, inv.running] using result

private theorem rankWordInitialized_safe (shape : CartesianShape) (memory : Memory)
    (reader init : Block) (readerSafe : ReaderSafe shape memory reader)
    (readerCorrect : ReaderCorrect shape memory reader) (readerWrites : ReaderWrites reader)
    (copies : Nat) (s : Data) (hs : s.status = .running)
    (hi : init.Safe memory (wordWidth shape.size) s)
    (inv : RankWordInvariant shape (init.eval memory s).final) :
    (Block.seq init (.repeat copies (rankWordBody reader))).Safe memory (wordWidth shape.size) s ∧
      RankWordInvariant shape ((Block.seq init (.repeat copies (rankWordBody reader))).eval memory s).final := by
  have repeated := rankWordRepeat_safe shape memory reader readerSafe readerCorrect readerWrites
    copies (init.eval memory s).final inv
  exact ⟨Block.safe_seq hi repeated.1, by simpa only [Block.eval, hs] using repeated.2⟩

theorem rankWordBlock_safe_invariant (shape : CartesianShape) (memory : Memory)
    (reader : Block) (readerSafe : ReaderSafe shape memory reader)
    (readerCorrect : ReaderCorrect shape memory reader) (readerWrites : ReaderWrites reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hl : regs 257 ≤ packedReviewerCellWidth shape.size) :
    (rankWordBlock reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
      RankWordInvariant shape ((rankWordBlock reader).eval memory ⟨regs, .running⟩).final := by
  have hc : 0 < regs 34 := by
    rw [metadata_chunkBits shape regs hm]
    exact rank_chunk_pos shape.size
  have initSafe := rankWordInit_safe shape.size memory regs fit hc hl
  have source := rankWordInit_source memory regs
  have metadataAfter := rank_metadata_frame shape memory rankWordInit _ rankWordInit_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  have inv : RankWordInvariant shape (rankWordInit.eval memory ⟨regs, .running⟩).final := by
    refine ⟨rankWordInit.eval_fits memory (wordWidth shape.size) _ initSafe,
      metadataAfter, source.1, ?_, ?_, ?_, source.2.2.2.2.2.2⟩
    · rw [source.2.2.2.2.2.1]; exact bpWordChunkCount_le_eight _ _
    · rw [source.2.2.2.1]; omega
    · rw [source.2.2.1]; omega
  exact rankWordInitialized_safe shape memory reader rankWordInit readerSafe readerCorrect
    readerWrites 8 ⟨regs, .running⟩ rfl initSafe inv

theorem rankWordBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs)
    (_word : s.regs 256 ≤ 2 ^ packedReviewerCellWidth shape.size)
    (length : s.regs 257 ≤ packedReviewerCellWidth shape.size)
    (_limit : s.regs 258 ≤ metadataEnvelope shape.size) :
    (rankWordBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · rw [rank_data_running s hs] at fit ⊢
    exact (rankWordBlock_safe_invariant shape (shapeMemory shape) logicalReadBlock
      (logicalReadBlock_readerSafe shape) (logicalReadBlock_correct shape)
      logicalReadBlock_writesOnly s.regs fit hm length).1
  · exact Block.safe_stopped _ _ _ s fit hs

theorem rankWordBlock_output_bound (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (length : regs 257 ≤ packedReviewerCellWidth shape.size) :
    ((rankWordBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 260 ≤
      8 * packedReviewerCellWidth shape.size := by
  have inv := (rankWordBlock_safe_invariant shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_readerSafe shape) (logicalReadBlock_correct shape)
    logicalReadBlock_writesOnly regs fit hm length).2
  have hc : ((rankWordBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 34 ≤
      packedReviewerCellWidth shape.size := by
    rw [metadata_chunkBits shape _ inv.metadata]
    exact rank_chunk_le_oldWidth shape.size
  have hp := Nat.mul_le_mul inv.index hc
  exact Nat.le_trans inv.accumulator hp

theorem rankSeedRead_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (segment index output : Nat)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    (rankSeedRead reader segment index output).Safe memory (wordWidth shape.size)
      ⟨regs, .running⟩ := by
  unfold rankSeedRead Block.sequence
  refine rank_safe_move fit (fun f1 => ?_)
  refine rank_safe_move f1 (fun f2 => ?_)
  have mp := MetadataMatches.write shape _
    (MetadataMatches.write shape regs hm 8192 (regs segment) (Or.inr (by decide)))
    8193 ((regs.write 8192 (regs segment)) index) (Or.inr (by decide))
  refine rank_safe_follow (readerSafe _ f2 mp) (fun f3 => ?_)
  apply SimpleScalar.safe memory _ _ _ _ f3
  simp [SimpleScalar]

theorem rankInit_safe (width : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (one : 1 < 2 ^ width)
    (hw : 0 < regs 354) (hb : 0 < regs 355) :
    rankInit.Safe memory width ⟨regs, .running⟩ := by
  have hwne : width ≠ 0 := by intro h; simp [h] at one
  have fp := fit.1 352
  dsimp only at fp
  have q := Nat.div_le_self (min (regs 352) (regs 353)) (regs 354)
  have r := Nat.div_le_self (min (regs 352) (regs 353) / regs 354) (regs 355)
  have lower := Nat.min_le_left (regs 352) (regs 353)
  apply ScalarChecks_safe memory width _ _ fit
  by_cases hmin : regs 352 ≤ regs 353
  · have q1 := Nat.div_le_self (regs 352) (regs 354)
    have q2 := Nat.div_le_self (regs 352 / regs 354) (regs 355)
    simp [ScalarChecks, rankInit, Block.sequence, Block.eval, Action.eval,
      Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
      Registers.write, Arithmetic.eval, Comparison.eval, minBlock, hmin, hwne]
    omega
  · have q1 := Nat.div_le_self (regs 353) (regs 354)
    have q2 := Nat.div_le_self (regs 353 / regs 354) (regs 355)
    simp [ScalarChecks, rankInit, Block.sequence, Block.eval, Action.eval,
      Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
      Registers.write, Arithmetic.eval, Comparison.eval, minBlock, hmin, hwne]
    omega

theorem rankPrepareWord_safe (width : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (one : 1 < 2 ^ width)
    (product : regs 362 * regs 354 < 2 ^ width) :
    rankPrepareWord.Safe memory width ⟨regs, .running⟩ := by
  unfold rankPrepareWord Block.sequence
  refine rank_safe_follow (natSubBlock_safe memory width 256 366 370 369 _ fit one
    (by decide) (by decide)) (fun f1 => ?_)
  rw [natSubBlock_source 256 366 370 369 memory regs (by decide) (by decide)] at f1 ⊢
  refine rank_safe_move f1 (fun f2 => ?_)
  refine rank_safe_arithmetic f2 ?_ (fun f3 => ?_)
  · simpa [Action.LocalSafe, Registers.write, Arithmetic.eval] using product
  refine rank_safe_follow (natSubBlock_safe memory width 258 361 368 369 _ f3 one
    (by decide) (by decide)) (fun f4 => ?_)
  apply SimpleScalar.safe memory width _ _ _ f4
  simp [SimpleScalar]

theorem rankCombine_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hs : regs 364 ≤ 2 ^ packedReviewerCellWidth n)
    (hd : regs 365 ≤ 2 ^ packedReviewerCellWidth n)
    (hw : regs 260 ≤ 8 * packedReviewerCellWidth n) :
    rankCombine.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have cap := metadataEnvelope_lt_wordCapacity n
  have env := rank_output_envelope n
  have hwne : wordWidth n ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe memory (wordWidth n) _ _ fit
  by_cases hsub1 : regs 370 ≤ regs 364
  all_goals by_cases hsub2 : regs 370 ≤ regs 365
  all_goals simp [ScalarChecks, rankCombine, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hsub1, hsub2, hwne] <;> omega

/-- Proof-side output bounds for a charged reader implementation. -/
def ReaderBounds (shape : CartesianShape) (memory : Memory) (reader : Block) : Prop :=
  ∀ regs, MetadataMatches shape regs →
    let actual := reader.eval memory ⟨regs, .running⟩
    actual.final.regs 8194 ≤ 2 ^ packedReviewerCellWidth shape.size ∧
      actual.final.regs 8195 ≤ packedReviewerCellWidth shape.size

theorem logicalReadBlock_readerBounds (shape : CartesianShape) :
    ReaderBounds shape (shapeMemory shape) logicalReadBlock := logicalReadBlock_output_bounds shape

theorem rank_logicalPacket_bounds (shape : CartesianShape) (segment index : Nat) :
    let word := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index
    logicalPacket word ≤ 2 ^ packedReviewerCellWidth shape.size ∧
      logicalLength word ≤ packedReviewerCellWidth shape.size := by
  cases hr : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index with
  | none => simp [logicalPacket, logicalLength]
  | some bits =>
      have fits := packedReviewerGlobalReadStore_word_fits shape
        ⟨⟨.leftSelect, 0, 0⟩, .entryBaseOccurrence, segment, index⟩ bits hr
      have value := fits.value_lt_two_pow
      exact ⟨by dsimp only [logicalPacket]; omega, fits⟩

theorem rankSeedRead_data_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (segment index output : Nat)
    (s : Data) (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (rankSeedRead reader segment index output).Safe memory (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · rw [rank_data_running s hs] at fit ⊢
    exact rankSeedRead_safe shape memory reader readerSafe segment index output s.regs fit hm
  · exact Block.safe_stopped _ _ _ s fit hs

theorem rankSeeds_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerWrites : ReaderWrites reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hw : 0 < regs 354) (hb : 0 < regs 355) :
    (rankSeeds reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have one : 1 < 2 ^ wordWidth shape.size := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 1 ≤ wordWidth shape.size by unfold wordWidth; omega)
    omega
  unfold rankSeeds Block.sequence
  refine rank_safe_follow (rankInit_safe _ memory regs fit one hw hb) (fun f1 => ?_)
  have m1 := rank_metadata_frame shape memory rankInit _ rankInit_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  refine rank_safe_follow (rankSeedRead_data_safe shape memory reader readerSafe 356 363 364 _ f1 m1)
    (fun f2 => ?_)
  have m2 := rankSeedRead_metadata shape memory reader readerWrites 356 363 364 (by decide) _ m1
  refine rank_safe_follow (rankSeedRead_data_safe shape memory reader readerSafe 357 362 365 _ f2 m2)
    (fun f3 => ?_)
  have m3 := rankSeedRead_metadata shape memory reader readerWrites 357 362 365 (by decide) _ m2
  refine rank_safe_follow (rankSeedRead_data_safe shape memory reader readerSafe 358 362 366 _ f3 m3)
    (fun f4 => ?_)
  apply SimpleScalar.safe memory _ _ _ _ f4
  simp [SimpleScalar]

theorem rankWordBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (rankWordBlock reader).FieldsFit width := by
  have hwne : width ≠ 0 := by intro h; simp [h] at cap
  simp [rankWordBlock, rankWordInit, rankWordBody, rankWordAddress, rankWordDecode,
    chunkSlotBlock, chunkRankBlock, natSubBlock, minBlock, Block.sequence, Block.FieldsFit,
    Action.instruction, Instruction.Fits, Instruction.encoding, Instruction.operands,
    Arithmetic.code, Comparison.code, readerFields, hwne]
  omega

theorem rankBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (rankBlock reader).FieldsFit width := by
  have hwne : width ≠ 0 := by intro h; simp [h] at cap
  have wordFields := rankWordBlock_fieldsFit width reader readerFields cap
  simp [rankBlock, rankSeeds, rankInit, rankSeedRead, rankFinish, rankPrepareWord,
    rankCombine, natSubBlock, minBlock, Block.sequence, Block.FieldsFit,
    Action.instruction, Instruction.Fits, Instruction.encoding, Instruction.operands,
    Arithmetic.code, Comparison.code, wordFields, readerFields, hwne]
  omega

theorem rankCloseBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (rankCloseBlock reader).FieldsFit width := by
  have fields := rankBlock_fieldsFit width reader readerFields cap
  have hwne : width ≠ 0 := by intro h; simp [h] at cap
  simp [rankCloseBlock, Block.sequence, Block.FieldsFit, fields,
    Action.instruction, Instruction.Fits, Instruction.encoding, Instruction.operands,
    Arithmetic.code, hwne]
  omega

theorem rankLongBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (rankLongBlock reader).FieldsFit width := by
  have fields := rankBlock_fieldsFit width reader readerFields cap
  have hwne : width ≠ 0 := by intro h; simp [h] at cap
  simp [rankLongBlock, Block.sequence, Block.FieldsFit, fields,
    Action.instruction, Instruction.Fits, Instruction.encoding, Instruction.operands, hwne]
  omega

theorem rankSparseBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (rankSparseBlock reader).FieldsFit width := by
  have fields := rankBlock_fieldsFit width reader readerFields cap
  have hwne : width ≠ 0 := by intro h; simp [h] at cap
  simp [rankSparseBlock, Block.sequence, Block.FieldsFit, fields,
    Action.instruction, Instruction.Fits, Instruction.encoding, Instruction.operands, hwne]
  omega

private theorem rank_safe_follow_post {memory : Memory} {width : Nat}
    {first second : Block} {s : Data} {post : Data → Prop}
    (head : first.Safe memory width s)
    (tail : (first.eval memory s).final.Fits width →
      second.Safe memory width (first.eval memory s).final ∧
        post (second.eval memory (first.eval memory s).final).final) :
    (Block.seq first second).Safe memory width s ∧
      post ((Block.seq first second).eval memory s).final := by
  have ht := tail (first.eval_fits memory width s head)
  refine ⟨Block.safe_seq head ht.1, ?_⟩
  rw [Block.eval_seq]
  exact ht.2

private theorem rank_transport_bound (memory : Memory) (width : Nat)
    (program target : Block) (regs : Registers) (bound : Nat) (eq : program = target)
    (h : program.Safe memory width ⟨regs, .running⟩ ∧
      (program.eval memory ⟨regs, .running⟩).final.regs 360 ≤ bound) :
    target.Safe memory width ⟨regs, .running⟩ ∧
      (target.eval memory ⟨regs, .running⟩).final.regs 360 ≤ bound := by
  subst target
  exact h

private theorem rank_branch_post {memory : Memory} {width condition : Nat}
    {zero nonzero : Block} {regs : Registers} {post : Data → Prop}
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (hz : zero.Safe memory width ⟨regs, .running⟩ ∧
      post (zero.eval memory ⟨regs, .running⟩).final)
    (hn : nonzero.Safe memory width ⟨regs, .running⟩ ∧
      post (nonzero.eval memory ⟨regs, .running⟩).final) :
    (Block.ifZero condition zero nonzero).Safe memory width ⟨regs, .running⟩ ∧
      post ((Block.ifZero condition zero nonzero).eval memory ⟨regs, .running⟩).final := by
  constructor
  · apply Block.safe_ifZero fit
    split
    · exact hz.1
    · exact hn.1
  · simp only [Block.eval]
    split
    · exact hz.2
    · exact hn.2

theorem rankFinish_safe_bound (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (readerWrites : ReaderWrites reader) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hs : regs 364 ≤ 2 ^ packedReviewerCellWidth shape.size)
    (hd : regs 365 ≤ 2 ^ packedReviewerCellWidth shape.size)
    (_hw : regs 366 ≤ 2 ^ packedReviewerCellWidth shape.size)
    (hl : regs 367 ≤ packedReviewerCellWidth shape.size)
    (position : regs 361 ≤ metadataEnvelope shape.size)
    (product : regs 362 * regs 354 ≤ regs 361) (initial : regs 360 = 0) :
    (rankFinish reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((rankFinish reader).eval memory ⟨regs, .running⟩).final.regs 360 ≤
        metadataEnvelope shape.size := by
  have cap := metadataEnvelope_lt_wordCapacity shape.size
  have env := rank_output_envelope shape.size
  have pos := metadataEnvelope_pos shape.size
  have one : 1 < 2 ^ wordWidth shape.size := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 1 ≤ wordWidth shape.size by unfold wordWidth; omega)
    omega
  have positive : (Block.seq rankPrepareWord (.seq (rankWordBlock reader) rankCombine)).Safe
        memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((Block.seq rankPrepareWord (.seq (rankWordBlock reader) rankCombine)).eval
        memory ⟨regs, .running⟩).final.regs 360 ≤ metadataEnvelope shape.size := by
    have prepareSafe := rankPrepareWord_safe _ memory regs fit one (by omega)
    refine rank_safe_follow_post (second := .seq (rankWordBlock reader) rankCombine)
      (post := fun d => d.regs 360 ≤ metadataEnvelope shape.size) prepareSafe (fun prepareFit => ?_)
    have sourcePrepare := rankPrepareWord_source memory regs
    have metadataPrepare := rank_metadata_frame shape memory rankPrepareWord _ rankPrepareWord_writes
      (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
    have framePrepare (r : Nat) (ho : ¬ ((256 ≤ r ∧ r < 260) ∨ r = 368 ∨ r = 369)) :=
      Block.eval_frame memory rankPrepareWord _ rankPrepareWord_writes r ho ⟨regs, .running⟩
    generalize heP : rankPrepareWord.eval memory ⟨regs, .running⟩ = prepared
      at sourcePrepare metadataPrepare framePrepare prepareFit ⊢
    rcases prepared with ⟨⟨pr, pst⟩, preceipts⟩
    dsimp only at sourcePrepare metadataPrepare framePrepare prepareFit
    obtain ⟨hpst, _, _, hlength, _, _⟩ := sourcePrepare
    subst pst
    have word := rankWordBlock_safe_invariant shape memory reader readerSafe readerCorrect
      readerWrites pr prepareFit metadataPrepare (by rw [hlength]; exact hl)
    refine rank_safe_follow_post (second := rankCombine)
      (post := fun d => d.regs 360 ≤ metadataEnvelope shape.size) word.1 (fun wordFit => ?_)
    have wordInv := word.2
    have frameWord (r : Nat) (ho : ¬ RankWordWrites r) :=
      rankWordBlock_frame reader readerWrites memory ⟨pr, .running⟩ r ho
    generalize heW : (rankWordBlock reader).eval memory ⟨pr, .running⟩ = ranked
      at wordInv frameWord wordFit ⊢
    rcases ranked with ⟨⟨wr, wst⟩, wreceipts⟩
    have hwst : wst = .running := wordInv.running
    subst wst
    dsimp only at wordInv frameWord wordFit ⊢
    have hws : wr 364 ≤ 2 ^ packedReviewerCellWidth shape.size := by
      rw [frameWord 364 (by simp [RankWordWrites]), framePrepare 364 (by omega)]
      exact hs
    have hwd : wr 365 ≤ 2 ^ packedReviewerCellWidth shape.size := by
      rw [frameWord 365 (by simp [RankWordWrites]), framePrepare 365 (by omega)]
      exact hd
    have hwc : wr 34 ≤ packedReviewerCellWidth shape.size := by
      rw [metadata_chunkBits shape wr wordInv.metadata]
      exact rank_chunk_le_oldWidth shape.size
    have hwj : wr 261 ≤ 8 := wordInv.index
    have hwa : wr 260 ≤ wr 261 * wr 34 := wordInv.accumulator
    have hwm := Nat.mul_le_mul hwj hwc
    have hwout : wr 260 ≤ 8 * packedReviewerCellWidth shape.size := by omega
    refine ⟨rankCombine_safe shape.size memory wr wordFit hws hwd hwout, ?_⟩
    have combined := rankCombine_source memory wr
    rw [combined.2.2]
    omega
  have skipSafe := Block.safe_skip memory (wordWidth shape.size) ⟨regs, .running⟩ fit
  have skipBound : (Block.skip.eval memory ⟨regs, .running⟩).final.regs 360 ≤
      metadataEnvelope shape.size := by change regs 360 ≤ _; omega
  exact rank_branch_post (condition := 364)
    (post := fun d => d.regs 360 ≤ metadataEnvelope shape.size) fit ⟨skipSafe, skipBound⟩
    (rank_branch_post (condition := 365)
      (post := fun d => d.regs 360 ≤ metadataEnvelope shape.size) fit ⟨skipSafe, skipBound⟩
      (rank_branch_post (condition := 366)
        (post := fun d => d.regs 360 ≤ metadataEnvelope shape.size) fit ⟨skipSafe, skipBound⟩ positive))

private theorem rankBlock_withFinish_safe_bound (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (readerWrites : ReaderWrites reader) (finish : Block)
    (finishSafe : ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape regs → regs 364 ≤ 2 ^ packedReviewerCellWidth shape.size →
      regs 365 ≤ 2 ^ packedReviewerCellWidth shape.size →
      regs 366 ≤ 2 ^ packedReviewerCellWidth shape.size →
      regs 367 ≤ packedReviewerCellWidth shape.size → regs 361 ≤ metadataEnvelope shape.size →
      regs 362 * regs 354 ≤ regs 361 → regs 360 = 0 →
      finish.Safe memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
        (finish.eval memory ⟨regs, .running⟩).final.regs 360 ≤ metadataEnvelope shape.size)
    (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hw : 0 < regs 354) (hb : 0 < regs 355) (length : regs 353 ≤ metadataEnvelope shape.size) :
    (Block.seq (rankSeeds reader) finish).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((Block.seq (rankSeeds reader) finish).eval memory ⟨regs, .running⟩).final.regs 360 ≤
        metadataEnvelope shape.size := by
  have seedsSafe := rankSeeds_safe shape memory reader readerSafe readerWrites regs fit hm hw hb
  refine rank_safe_follow_post (second := finish)
    (post := fun d => d.regs 360 ≤ metadataEnvelope shape.size) seedsSafe (fun seedsFit => ?_)
  have source := rankSeeds_source shape memory reader readerCorrect readerWrites regs hm
  have metadataSeeds := rank_metadata_frame shape memory (rankSeeds reader) _
    (rankSeeds_writes reader readerWrites) (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  have frameSeeds := Block.eval_frame memory (rankSeeds reader) _
    (rankSeeds_writes reader readerWrites) 354 (by omega) ⟨regs, .running⟩
  generalize heS : (rankSeeds reader).eval memory ⟨regs, .running⟩ = seeded
    at source metadataSeeds frameSeeds seedsFit ⊢
  rcases seeded with ⟨⟨sr, sst⟩, receipts⟩
  dsimp only at source metadataSeeds frameSeeds seedsFit
  obtain ⟨hsst, hzero, he, hblock, _, _, hsuper, hdelta, hword, hlength, _⟩ := source
  subst sst
  apply finishSafe sr seedsFit metadataSeeds
  · rw [hsuper]; exact (rank_logicalPacket_bounds shape _ _).1
  · rw [hdelta]; exact (rank_logicalPacket_bounds shape _ _).1
  · rw [hword]; exact (rank_logicalPacket_bounds shape _ _).1
  · rw [hlength]; exact (rank_logicalPacket_bounds shape _ _).2
  · rw [he]; have := Nat.min_le_right (regs 352) (regs 353); omega
  · rw [hblock, he, frameSeeds]
    exact Nat.div_mul_le_self _ _
  · exact hzero

theorem rankBlock_safe_bound (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (readerWrites : ReaderWrites reader) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hw : 0 < regs 354) (hb : 0 < regs 355) (length : regs 353 ≤ metadataEnvelope shape.size) :
    (rankBlock reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((rankBlock reader).eval memory ⟨regs, .running⟩).final.regs 360 ≤ metadataEnvelope shape.size :=
  rank_transport_bound memory (wordWidth shape.size) (.seq (rankSeeds reader) (rankFinish reader))
    (rankBlock reader) regs (metadataEnvelope shape.size) rfl
    (rankBlock_withFinish_safe_bound shape memory reader readerSafe readerCorrect readerWrites
      (rankFinish reader) (rankFinish_safe_bound shape memory reader readerSafe readerCorrect readerWrites)
      regs fit hm hw hb length)

private theorem rank_move_post {memory : Memory} {width dst src : Nat}
    {rest : Block} {regs : Registers} {post : Data → Prop}
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (tail : (⟨regs.write dst (regs src), .running⟩ : Data).Fits width →
      rest.Safe memory width ⟨regs.write dst (regs src), .running⟩ ∧
        post (rest.eval memory ⟨regs.write dst (regs src), .running⟩).final) :
    (Block.seq (.action (.move dst src)) rest).Safe memory width ⟨regs, .running⟩ ∧
      post ((Block.seq (.action (.move dst src)) rest).eval memory ⟨regs, .running⟩).final :=
  rank_safe_follow_post (post := post)
    (Block.safe_action memory width _ _ fit (fit.1 src)) tail

private theorem rank_constant_post {memory : Memory} {width dst value : Nat}
    {rest : Block} {regs : Registers} {post : Data → Prop}
    (fit : (⟨regs, .running⟩ : Data).Fits width) (valueFit : value < 2 ^ width)
    (tail : (⟨regs.write dst value, .running⟩ : Data).Fits width →
      rest.Safe memory width ⟨regs.write dst value, .running⟩ ∧
        post (rest.eval memory ⟨regs.write dst value, .running⟩).final) :
    (Block.seq (.action (.constant dst value)) rest).Safe memory width ⟨regs, .running⟩ ∧
      post ((Block.seq (.action (.constant dst value)) rest).eval memory ⟨regs, .running⟩).final :=
  rank_safe_follow_post (post := post)
    (Block.safe_action memory width _ _ fit valueFit) tail

private theorem rank_arithmetic_post {memory : Memory} {width dst lhs rhs : Nat}
    {op : Arithmetic} {rest : Block} {regs : Registers} {post : Data → Prop}
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (operation : (Action.arithmetic op dst lhs rhs).LocalSafe memory width ⟨regs, .running⟩)
    (tail : (⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩ : Data).Fits width →
      rest.Safe memory width ⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩ ∧
        post (rest.eval memory ⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩).final) :
    (Block.seq (.action (.arithmetic op dst lhs rhs)) rest).Safe memory width ⟨regs, .running⟩ ∧
      post ((Block.seq (.action (.arithmetic op dst lhs rhs)) rest).eval memory ⟨regs, .running⟩).final :=
  rank_safe_follow_post (post := post)
    (Block.safe_action memory width _ _ fit operation) tail

private theorem rank_skip_post {memory : Memory} {width : Nat} {block : Block}
    {s : Data} {post : Data → Prop}
    (h : block.Safe memory width s ∧ post (block.eval memory s).final) :
    (Block.seq block .skip).Safe memory width s ∧
      post ((Block.seq block .skip).eval memory s).final := by
  refine rank_safe_follow_post (post := post) h.1 (fun fit => ?_)
  refine ⟨Block.safe_skip memory width _ fit, ?_⟩
  have skip (d : Data) : Block.skip.eval memory d = ⟨d, []⟩ := by
    cases hs : d.status <;> simp [Block.eval, hs]
  rw [skip]
  exact h.2

private theorem rankFlagWrapper_safe_bound (shape : CartesianShape) (memory : Memory)
    (body : Block)
    (bodySafe : ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape regs → 0 < regs 354 → 0 < regs 355 →
      regs 353 ≤ metadataEnvelope shape.size →
      body.Safe memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
        (body.eval memory ⟨regs, .running⟩).final.regs 360 ≤ metadataEnvelope shape.size)
    (lengthReg widthReg superSegment blockSegment wordSegment : Nat)
    (widthLow : widthReg < 353) (segments : superSegment < 2 ^ wordWidth shape.size ∧
      blockSegment < 2 ^ wordWidth shape.size ∧ wordSegment < 2 ^ wordWidth shape.size)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (widthPos : 0 < regs widthReg)
    (lengthBound : regs lengthReg ≤ metadataEnvelope shape.size) :
    let block := Block.sequence [.action (.move 353 lengthReg), .action (.move 354 widthReg),
      .action (.constant 355 1), .action (.constant 356 superSegment),
      .action (.constant 357 blockSegment), .action (.constant 358 wordSegment),
      .action (.constant 359 1), body]
    block.Safe memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
      (block.eval memory ⟨regs, .running⟩).final.regs 360 ≤ metadataEnvelope shape.size := by
  let post := fun d : Data => d.regs 360 ≤ metadataEnvelope shape.size
  have one : 1 < 2 ^ wordWidth shape.size := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 1 ≤ wordWidth shape.size by unfold wordWidth; omega)
    omega
  dsimp only
  unfold Block.sequence
  refine rank_move_post (post := post) fit (fun f1 => ?_)
  refine rank_move_post (post := post) f1 (fun f2 => ?_)
  refine rank_constant_post (post := post) f2 one (fun f3 => ?_)
  refine rank_constant_post (post := post) f3 segments.1 (fun f4 => ?_)
  refine rank_constant_post (post := post) f4 segments.2.1 (fun f5 => ?_)
  refine rank_constant_post (post := post) f5 segments.2.2 (fun f6 => ?_)
  refine rank_constant_post (post := post) f6 one (fun f7 => ?_)
  apply rank_skip_post (post := post)
  apply bodySafe _ f7
  · intro i hi
    simp only [Registers.write, if_neg (show 16 + i ≠ 359 by omega),
      if_neg (show 16 + i ≠ 358 by omega), if_neg (show 16 + i ≠ 357 by omega),
      if_neg (show 16 + i ≠ 356 by omega), if_neg (show 16 + i ≠ 355 by omega),
      if_neg (show 16 + i ≠ 354 by omega), if_neg (show 16 + i ≠ 353 by omega)]
    exact hm i hi
  · simpa [Registers.write, show widthReg ≠ 353 by omega] using widthPos
  · simp [Registers.write]
  · simpa [Registers.write] using lengthBound

theorem rankLongBlock_safe_bound (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    (rankLongBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((rankLongBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 360 ≤
        metadataEnvelope shape.size := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth shape.size by unfold wordWidth; omega)
  have hw : regs 30 = packedLongFlagWordSize shape.size := hm 14 (by decide)
  apply rank_transport_bound (shapeMemory shape) (wordWidth shape.size)
    (Block.sequence [.action (.move 353 28), .action (.move 354 30),
      .action (.constant 355 1), .action (.constant 356 9), .action (.constant 357 10),
      .action (.constant 358 11), .action (.constant 359 1), rankBlock logicalReadBlock])
    (rankLongBlock logicalReadBlock) regs (metadataEnvelope shape.size) rfl
  exact rankFlagWrapper_safe_bound shape (shapeMemory shape) (rankBlock logicalReadBlock)
    (rankBlock_safe_bound shape (shapeMemory shape) logicalReadBlock
      (logicalReadBlock_readerSafe shape) (logicalReadBlock_correct shape) logicalReadBlock_writesOnly)
    28 30 9 10 11 (by decide) ⟨by omega, by omega, by omega⟩ regs fit hm
    (by rw [hw]; exact SuccinctRank.machineWordBits_pos _) (hm.envelope shape regs 28 (by decide))

theorem rankSparseBlock_safe_bound (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    (rankSparseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((rankSparseBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 360 ≤
        metadataEnvelope shape.size := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth shape.size by unfold wordWidth; omega)
  have hw : regs 31 = packedSparseWordSize shape.size := hm 15 (by decide)
  apply rank_transport_bound (shapeMemory shape) (wordWidth shape.size)
    (Block.sequence [.action (.move 353 29), .action (.move 354 31),
      .action (.constant 355 1), .action (.constant 356 13), .action (.constant 357 14),
      .action (.constant 358 15), .action (.constant 359 1), rankBlock logicalReadBlock])
    (rankSparseBlock logicalReadBlock) regs (metadataEnvelope shape.size) rfl
  exact rankFlagWrapper_safe_bound shape (shapeMemory shape) (rankBlock logicalReadBlock)
    (rankBlock_safe_bound shape (shapeMemory shape) logicalReadBlock
      (logicalReadBlock_readerSafe shape) (logicalReadBlock_correct shape) logicalReadBlock_writesOnly)
    29 31 13 14 15 (by decide) ⟨by omega, by omega, by omega⟩ regs fit hm
    (by rw [hw]; exact SuccinctRank.machineWordBits_pos _) (hm.envelope shape regs 29 (by decide))

private theorem rankCloseWrapper_safe_bound (shape : CartesianShape) (memory : Memory)
    (body : Block)
    (bodySafe : ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape regs → 0 < regs 354 → 0 < regs 355 →
      regs 353 ≤ metadataEnvelope shape.size →
      body.Safe memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
        (body.eval memory ⟨regs, .running⟩).final.regs 360 ≤ metadataEnvelope shape.size)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    let block := Block.sequence [
      .action (.constant 369 2), .action (.arithmetic .mul 353 16 369),
      .action (.move 354 32), .action (.move 355 32), .action (.constant 356 17),
      .action (.constant 357 18), .action (.constant 358 19), .action (.constant 359 0), body]
    block.Safe memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
      (block.eval memory ⟨regs, .running⟩).final.regs 360 ≤ metadataEnvelope shape.size := by
  let post := fun d : Data => d.regs 360 ≤ metadataEnvelope shape.size
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth shape.size by unfold wordWidth; omega)
  have hn : regs 16 = shape.size := hm 0 (by decide)
  have hwidth : regs 32 = packedBpCodeWordWidth shape.size := hm 16 (by decide)
  have two : regs 16 * 2 ≤ metadataEnvelope shape.size := by
    have ht := packedTwoMul_le_reviewerBound shape.size
    have hq := packedReviewerCellBound_lt_two_pow_width shape.size
    have he := rank_output_envelope shape.size
    rw [hn]
    omega
  have twoFit := Nat.lt_of_le_of_lt two (metadataEnvelope_lt_wordCapacity shape.size)
  dsimp only
  unfold Block.sequence
  refine rank_constant_post (post := post) fit (by omega) (fun f1 => ?_)
  refine rank_arithmetic_post (post := post) f1 ?_ (fun f2 => ?_)
  · simpa [Action.LocalSafe, Registers.write, Arithmetic.eval] using twoFit
  refine rank_move_post (post := post) f2 (fun f3 => ?_)
  refine rank_move_post (post := post) f3 (fun f4 => ?_)
  refine rank_constant_post (post := post) f4 (by omega) (fun f5 => ?_)
  refine rank_constant_post (post := post) f5 (by omega) (fun f6 => ?_)
  refine rank_constant_post (post := post) f6 (by omega) (fun f7 => ?_)
  refine rank_constant_post (post := post) f7 (by omega) (fun f8 => ?_)
  apply rank_skip_post (post := post)
  apply bodySafe _ f8
  · intro i hi
    simp only [Registers.write, if_neg (show 16 + i ≠ 359 by omega),
      if_neg (show 16 + i ≠ 358 by omega), if_neg (show 16 + i ≠ 357 by omega),
      if_neg (show 16 + i ≠ 356 by omega), if_neg (show 16 + i ≠ 355 by omega),
      if_neg (show 16 + i ≠ 354 by omega), if_neg (show 16 + i ≠ 353 by omega),
      if_neg (show 16 + i ≠ 369 by omega)]
    exact hm i hi
  · simpa [Registers.write, hwidth] using packedBpCodeWordWidth_pos shape.size
  · simpa [Registers.write, hwidth] using packedBpCodeWordWidth_pos shape.size
  · simpa [Registers.write, Arithmetic.eval] using two

theorem rankCloseBlock_safe_bound (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    (rankCloseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((rankCloseBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 360 ≤
        metadataEnvelope shape.size :=
  rank_transport_bound (shapeMemory shape) (wordWidth shape.size)
    (Block.sequence [.action (.constant 369 2), .action (.arithmetic .mul 353 16 369),
      .action (.move 354 32), .action (.move 355 32), .action (.constant 356 17),
      .action (.constant 357 18), .action (.constant 358 19), .action (.constant 359 0),
      rankBlock logicalReadBlock])
    (rankCloseBlock logicalReadBlock) regs (metadataEnvelope shape.size) rfl
    (rankCloseWrapper_safe_bound shape (shapeMemory shape) (rankBlock logicalReadBlock)
      (rankBlock_safe_bound shape (shapeMemory shape) logicalReadBlock
        (logicalReadBlock_readerSafe shape) (logicalReadBlock_correct shape) logicalReadBlock_writesOnly) regs fit hm)

theorem rankCloseBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (rankCloseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · rw [rank_data_running s hs] at fit ⊢
    exact (rankCloseBlock_safe_bound shape s.regs fit hm).1
  · exact Block.safe_stopped _ _ _ s fit hs

theorem rankLongBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (rankLongBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · rw [rank_data_running s hs] at fit ⊢
    exact (rankLongBlock_safe_bound shape s.regs fit hm).1
  · exact Block.safe_stopped _ _ _ s fit hs

theorem rankSparseBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (rankSparseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · rw [rank_data_running s hs] at fit ⊢
    exact (rankSparseBlock_safe_bound shape s.regs fit hm).1
  · exact Block.safe_stopped _ _ _ s fit hs

/-- All components name the same primitive program, budget and initial state.
In particular the read clause retains the producing transition occurrence. -/
def RankExecutionSafety (memory : Memory) (width : Nat) (program : Program)
    (budget : Nat) (s : State) : Prop :=
  (∀ instruction ∈ program, instruction.Fits width) ∧
  (run memory program budget s).final.Fits width ∧
  (∀ (index : Nat) (t : Transition), (run memory program budget s).transitions[index]? = some t →
    Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
  (∀ index, index ≤ budget → (run memory program index s).final.Fits width) ∧
  (∀ (index : Nat) (t : Transition) (receipt : Receipt),
    (run memory program budget s).transitions[index]? = some t → t.receipt = some receipt →
    receipt.address < 2 ^ width ∧ receipt.reply = memory[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ width))

theorem rank_compiled_safety (memory : Memory) (width : Nat) (block : Block)
    (output budget : Nat) (regs : Registers) (size : block.size + 1 = budget)
    (bound : budget < 2 ^ width) (fields : block.FieldsFit width)
    (haltFields : (Instruction.halt output).Fits width)
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (safe : block.Safe memory width ⟨regs, .running⟩) :
    RankExecutionSafety memory width (block.compileAt 0 ++ [.halt output]) budget
      ⟨regs, 0, .running⟩ := by
  have actual := block.compile_with_halt_safe memory width output ⟨regs, 0, .running⟩ rfl
    fields haltFields (by omega) ⟨Nat.two_pow_pos _, fit⟩ safe
  rw [size] at actual
  have programFields : ∀ instruction ∈ block.compileAt 0 ++ [.halt output], instruction.Fits width := by
    intro instruction hi
    rcases List.mem_append.mp hi with hi | hi
    · exact block.compile_fits width 0 fields (by omega) instruction hi
    · simp only [List.mem_singleton] at hi
      subst instruction
      exact haltFields
  refine ⟨programFields, actual.2.2.2.2.1, actual.2.2.2.2.2.1, actual.2.2.2.2.2.2, ?_⟩
  intro index t receipt occurrence read
  have operation := actual.2.2.2.2.2.1 index t occurrence
  exact run_read_fits occurrence read operation.1 operation.2

theorem rankWordBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (length : regs 257 ≤ packedReviewerCellWidth shape.size) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankWordBlock logicalReadBlock).compileAt 0 ++ [.halt 260])
      (502 + 8 * logicalReadBlock.size) ⟨regs, 0, .running⟩ := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth shape.size by unfold wordWidth; omega)
  exact rank_compiled_safety (shapeMemory shape) (wordWidth shape.size)
    (rankWordBlock logicalReadBlock) 260 (502 + 8 * logicalReadBlock.size) regs
    (by rw [rankWordBlock_size]; omega) (by simp only [logicalReadBlock_size, locateBlock_size]; omega)
    (rankWordBlock_fieldsFit _ _ (logicalReadBlock_fieldsFit _ (by omega)) (by omega))
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega) fit
    (rankWordBlock_safe_invariant shape (shapeMemory shape) logicalReadBlock
      (logicalReadBlock_readerSafe shape) (logicalReadBlock_correct shape)
      logicalReadBlock_writesOnly regs fit hm length).1

theorem rankCloseBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
      (560 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩ := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth shape.size by unfold wordWidth; omega)
  exact rank_compiled_safety (shapeMemory shape) (wordWidth shape.size)
    (rankCloseBlock logicalReadBlock) 360 (560 + 11 * logicalReadBlock.size) regs
    (by rw [rankCloseBlock_size]; omega) (by simp only [logicalReadBlock_size, locateBlock_size]; omega)
    (rankCloseBlock_fieldsFit _ _ (logicalReadBlock_fieldsFit _ (by omega)) (by omega))
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega) fit
    (rankCloseBlock_safe shape _ fit hm)

theorem rankLongBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankLongBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
      (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩ := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth shape.size by unfold wordWidth; omega)
  exact rank_compiled_safety (shapeMemory shape) (wordWidth shape.size)
    (rankLongBlock logicalReadBlock) 360 (559 + 11 * logicalReadBlock.size) regs
    (by rw [rankLongBlock_size]; omega) (by simp only [logicalReadBlock_size, locateBlock_size]; omega)
    (rankLongBlock_fieldsFit _ _ (logicalReadBlock_fieldsFit _ (by omega)) (by omega))
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega) fit
    (rankLongBlock_safe shape _ fit hm)

theorem rankSparseBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankSparseBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
      (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩ := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth shape.size by unfold wordWidth; omega)
  exact rank_compiled_safety (shapeMemory shape) (wordWidth shape.size)
    (rankSparseBlock logicalReadBlock) 360 (559 + 11 * logicalReadBlock.size) regs
    (by rw [rankSparseBlock_size]; omega) (by simp only [logicalReadBlock_size, locateBlock_size]; omega)
    (rankSparseBlock_fieldsFit _ _ (logicalReadBlock_fieldsFit _ (by omega)) (by omega))
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega) fit
    (rankSparseBlock_safe shape _ fit hm)

theorem rankWordRun_safe (shape : CartesianShape) (word : List Bool) (target : Bool)
    (limit : Nat) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hword : regs 256 = bitsToNatLE word) (hlength : regs 257 = word.length)
    (hlimit : regs 258 = limit) (htarget : regs 259 = if target then 1 else 0)
    (length : word.length ≤ packedReviewerCellWidth shape.size) :
    let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21
      (packedFringeChunkBits shape.size) target word limit
    let program := (rankWordBlock logicalReadBlock).compileAt 0 ++ [.halt 260]
    let actual := run (shapeMemory shape) program (502 + 8 * logicalReadBlock.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 502 + 8 * logicalReadBlock.size ∧
    (∀ r, ¬ RankWordWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace ∧ expected.value ≤ 8 * packedReviewerCellWidth shape.size ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program
      (502 + 8 * logicalReadBlock.size) ⟨regs, 0, .running⟩ := by
  have semantic := rankWordBlock_machine shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly word target limit regs hm
    hword hlength hlimit htarget
  have bound := rankWordBlock_output_bound shape regs fit hm (by rw [hlength]; exact length)
  have source := rankWordBlock_source shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly word target limit regs hm
    hword hlength hlimit htarget
  rw [source.2.1] at bound
  exact ⟨semantic.1, semantic.2.1, semantic.2.2.1, semantic.2.2.2.1,
    semantic.2.2.2.2.1, semantic.2.2.2.2.2, bound,
    rankWordBlock_execution_safe shape regs fit hm (by rw [hlength]; exact length)⟩

theorem rankCloseRun_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    let expected := packedRankCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 352)
    let program := (rankCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 360]
    let actual := run (shapeMemory shape) program (560 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 560 + 11 * logicalReadBlock.size ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace ∧ expected.value ≤ metadataEnvelope shape.size ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program
      (560 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩ := by
  have semantic := rankCloseBlock_sameAllocation shape logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm
  have bound := (rankCloseBlock_safe_bound shape regs fit hm).2
  have source := rankCloseBlock_source shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm
  rw [source.2.1] at bound
  exact ⟨semantic.1, semantic.2.1, semantic.2.2.1, semantic.2.2.2.1,
    semantic.2.2.2.2.1, semantic.2.2.2.2.2, bound, rankCloseBlock_execution_safe shape regs fit hm⟩

theorem rankLongRun_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    let expected := packedRankRead 9 10 11 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSuperSlots shape.size) (packedLongFlagWordSize shape.size) 1 (regs 352)
    let program := (rankLongBlock logicalReadBlock).compileAt 0 ++ [.halt 360]
    let actual := run (shapeMemory shape) program (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 559 + 11 * logicalReadBlock.size ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace ∧ expected.value ≤ metadataEnvelope shape.size ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program
      (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩ := by
  have semantic := rankLongBlock_sameAllocation shape logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm
  have bound := (rankLongBlock_safe_bound shape regs fit hm).2
  have source := rankLongBlock_source shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm
  rw [source.2.1] at bound
  exact ⟨semantic.1, semantic.2.1, semantic.2.2.1, semantic.2.2.2.1,
    semantic.2.2.2.2.1, semantic.2.2.2.2.2, bound, rankLongBlock_execution_safe shape regs fit hm⟩

theorem rankSparseRun_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    let expected := packedRankRead 13 14 15 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSparseSlots shape.size) (packedSparseWordSize shape.size) 1 (regs 352)
    let program := (rankSparseBlock logicalReadBlock).compileAt 0 ++ [.halt 360]
    let actual := run (shapeMemory shape) program (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 559 + 11 * logicalReadBlock.size ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace ∧ expected.value ≤ metadataEnvelope shape.size ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program
      (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩ := by
  have semantic := rankSparseBlock_sameAllocation shape logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm
  have bound := (rankSparseBlock_safe_bound shape regs fit hm).2
  have source := rankSparseBlock_source shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm
  rw [source.2.1] at bound
  exact ⟨semantic.1, semantic.2.1, semantic.2.2.1, semantic.2.2.2.1,
    semantic.2.2.2.2.1, semantic.2.2.2.2.2, bound, rankSparseBlock_execution_safe shape regs fit hm⟩

theorem rankWrappers_sameAllocation_safety (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    (shapeMemory shape).length * wordWidth shape.size ≤ 2 * shape.size + allocationRho shape.size ∧
    wordWidth shape.size ≤ 192 * (Nat.log2 (shape.size + 2) + 1) ∧
    (∀ value ∈ shapeMemory shape, value < 2 ^ wordWidth shape.size) ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
      (560 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩ ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankLongBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
      (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩ ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankSparseBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
      (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩ :=
  ⟨shapeMemory_capacity_le shape, wordWidth_le_log shape.size, shapeMemory_words_fit shape,
    rankCloseBlock_execution_safe shape regs fit hm, rankLongBlock_execution_safe shape regs fit hm,
    rankSparseBlock_execution_safe shape regs fit hm⟩

namespace RankSafetyConsumers

theorem canonical_wrappers (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (rankCloseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s ∧
    (rankLongBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s ∧
    (rankSparseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s :=
  ⟨rankCloseBlock_safe shape s fit hm, rankLongBlock_safe shape s fit hm, rankSparseBlock_safe shape s fit hm⟩

theorem canonical_prefixes (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    (∀ k, k ≤ 12308 →
      (run (shapeMemory shape) ((rankCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
        k ⟨regs, 0, .running⟩).final.Fits (wordWidth shape.size)) ∧
    (∀ k, k ≤ 12307 →
      (run (shapeMemory shape) ((rankLongBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
        k ⟨regs, 0, .running⟩).final.Fits (wordWidth shape.size)) ∧
    (∀ k, k ≤ 12307 →
      (run (shapeMemory shape) ((rankSparseBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
        k ⟨regs, 0, .running⟩).final.Fits (wordWidth shape.size)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    exact (rankCloseBlock_execution_safe shape regs fit hm).2.2.2.1 k
      (by simp only [logicalReadBlock_size, locateBlock_size]; omega)
  · intro k hk
    exact (rankLongBlock_execution_safe shape regs fit hm).2.2.2.1 k
      (by simp only [logicalReadBlock_size, locateBlock_size]; omega)
  · intro k hk
    exact (rankSparseBlock_execution_safe shape regs fit hm).2.2.2.1 k
      (by simp only [logicalReadBlock_size, locateBlock_size]; omega)

theorem empty_word_zero_limit (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hword : regs 256 = 0) (hlength : regs 257 = 0) (hlimit : regs 258 = 0) (htarget : regs 259 = 0) :
    let program := (rankWordBlock logicalReadBlock).compileAt 0 ++ [.halt 260]
    let actual := run (shapeMemory shape) program ((rankWordBlock logicalReadBlock).size + 1)
      ⟨regs, 0, .running⟩
    actual.result = some 0 ∧ actual.reads = readerReceipts shape (shapeMemory shape) 21 0 ∧
      RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program
        ((rankWordBlock logicalReadBlock).size + 1) ⟨regs, 0, .running⟩ := by
  have source := rankWordBlock_empty shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm hword hlength hlimit htarget
  have actual := rank_compile_with_halt (rankWordBlock logicalReadBlock) 260 (shapeMemory shape)
    regs 0 (readerReceipts shape (shapeMemory shape) 21 0) RankWordWrites
    (rankWordBlock_writes logicalReadBlock logicalReadBlock_writesOnly) source.1 source.2.1 source.2.2
  have safe := rankWordBlock_execution_safe shape regs fit hm (by rw [hlength]; omega)
  have size : (rankWordBlock logicalReadBlock).size + 1 = 502 + 8 * logicalReadBlock.size := by
    rw [rankWordBlock_size]
    omega
  rw [← size] at safe
  exact ⟨actual.1, actual.2.2.1, safe⟩

theorem absent_entry_packet (base n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs base ≤ packedReviewerCellWidth n) (hl : regs (base + 1) ≤ regs base)
    (missing : regs (base + 2) = 0) :
    (chunkRankBlock base).Safe memory (wordWidth n) ⟨regs, .running⟩ ∧
    ((chunkRankBlock base).eval memory ⟨regs, .running⟩).final.regs (base + 4) =
      chunkRank (regs base) (regs (base + 1)) 0 (regs (base + 3)) ∧
    ((chunkRankBlock base).eval memory ⟨regs, .running⟩).final.regs (base + 4) ≤ regs base := by
  have source := chunkRankBlock_source base memory regs
  refine ⟨chunkRankBlock_canonical_safe base n memory _ fit hc hl, ?_, ?_⟩
  · exact source.2.2.trans (by rw [missing])
  · rw [source.2.2]
    exact chunkRank_le_chunk _ _ _ _ hl

theorem empty_input_prefixes (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth (SuccinctClassic.cartesianShape []).size))
    (hm : MetadataMatches (SuccinctClassic.cartesianShape []) regs) :
    ∀ k, k ≤ 12308 →
      (run (shapeMemory (SuccinctClassic.cartesianShape []))
        ((rankCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 360]) k
        ⟨regs, 0, .running⟩).final.Fits (wordWidth (SuccinctClassic.cartesianShape []).size) :=
  (canonical_prefixes (SuccinctClassic.cartesianShape []) regs fit hm).1

end RankSafetyConsumers

end RMQ.SuccinctFinal.PackedWordRAM
