import RMQ.Core.WordRAM.Bitvector.GenericRankProof
import RMQ.Core.WordRAM.Bitvector.SafetyInterface
import RMQ.Core.WordRAM.Packed.RankSafety

/-! # Arithmetic safety of the unchanged generic rank controllers -/

namespace RMQ.PackedBitvector.Controller

open SuccinctFinal SuccinctFinal.PackedWordRAM Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

theorem chunkSlotBlock_canonical_safe (base : Nat) (limits : SafetyLimits) (memory : Memory) (s : Data)
    (fit : s.Fits (limits.width))
    (hc : s.regs (base + 1) ≤ limits.rawWidth)
    (hj : s.regs (base + 2) < 8) :
    (chunkSlotBlock base).Safe memory (limits.width) s := by
  apply chunkSlotBlock_safe base (limits.width) memory s fit
  · have := limits.rawShift; omega
  · have hp := Nat.mul_le_mul (show s.regs (base + 2) ≤ 7 by omega) hc
    have h := limits.rawShift
    omega
  · exact limits.chunk_slot_fit _ hc

theorem chunkRankBlock_canonical_safe (base : Nat) (limits : SafetyLimits) (memory : Memory) (s : Data)
    (fit : s.Fits (limits.width)) (hc : s.regs base ≤ limits.rawWidth)
    (hl : s.regs (base + 1) ≤ s.regs base) :
    (chunkRankBlock base).Safe memory (limits.width) s := by
  apply chunkRankBlock_safe base (limits.width) memory s fit hl
  have env := limits.output_bound
  have pos := limits.packet_pos
  have cap := limits.reader_polynomial_fit
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

theorem rankWordAddress_safe (limits : SafetyLimits) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hc : regs 34 ≤ limits.rawWidth) (hj : regs 261 < 8) :
    rankWordAddress.Safe memory (limits.width) ⟨regs, .running⟩ := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ limits.width by have h := limits.width32; omega)
  unfold rankWordAddress Block.sequence
  refine rank_safe_move fit (fun f1 => ?_)
  refine rank_safe_move f1 (fun f2 => ?_)
  refine rank_safe_move f2 (fun f3 => ?_)
  refine rank_safe_move f3 (fun f4 => ?_)
  have chunk := chunkSlotBlock_canonical_safe 280 limits memory _ f4
    (by simpa [Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write] using hc)
    (by simpa [Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write] using hj)
  refine rank_safe_follow chunk (fun f5 => ?_)
  apply SimpleScalar.safe memory (limits.width) _ _ _ f5
  simp [SimpleScalar]
  omega

theorem rankWordDecode_safe (limits : SafetyLimits) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hc : regs 34 ≤ limits.rawWidth) (hl : regs 284 ≤ regs 34)
    (ha : regs 260 ≤ 8 * limits.rawWidth)
    (hj : regs 261 ≤ 8) (hone : regs 265 = 1) :
    rankWordDecode.Safe memory (limits.width) ⟨regs, .running⟩ := by
  have cap := limits.reader_polynomial_fit
  have env := limits.output_bound
  have pos := limits.packet_pos
  have one : 1 < 2 ^ limits.width := by omega
  unfold rankWordDecode Block.sequence
  refine rank_safe_move fit (fun f1 => ?_)
  refine rank_safe_move f1 (fun f2 => ?_)
  have sub := natSubBlock_safe memory (limits.width) 302 8194 265 303 _ f2 one
    (by decide) (by decide)
  refine rank_safe_follow sub (fun f3 => ?_)
  have srcSub := natSubBlock_source 302 8194 265 303 memory
    ((regs.write 300 (regs 34)).write 301 ((regs.write 300 (regs 34)) 284)) (by decide) (by decide)
  rw [srcSub] at f3 ⊢
  refine rank_safe_move f3 (fun f4 => ?_)
  have chunk := chunkRankBlock_canonical_safe 300 limits memory _ f4
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
  change ((chunkRankBlock 300).eval memory ⟨prepared, .running⟩).final.Fits (limits.width) at f5
  change (Block.seq (.action (.arithmetic .add 260 260 304))
    (.seq (.action (.arithmetic .add 261 261 265)) .skip)).Safe memory (limits.width)
      ((chunkRankBlock 300).eval memory ⟨prepared, .running⟩).final
  simp [prepared, Registers.write] at hs hf260 hf261 hf265
  generalize he : (chunkRankBlock 300).eval memory ⟨prepared, .running⟩ = decoded
    at hs hf260 hf261 hf265 f5 ⊢
  rcases decoded with ⟨⟨out, status⟩, reads⟩
  dsimp only at hs hf260 hf261 hf265 f5
  obtain ⟨hst, _, hv⟩ := hs
  subst status
  rw [hone] at hb
  apply ScalarChecks_safe memory (limits.width) _ _ f5
  simp [ScalarChecks, Block.eval, Action.eval, Action.instruction, Action.LocalSafe,
    execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
    hf260, hf261, hf265, hone, hv]
  omega

theorem rankWordInit_safe (limits : SafetyLimits) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hc : 0 < regs 34) (hl : regs 257 ≤ limits.rawWidth) :
    rankWordInit.Safe memory (limits.width) ⟨regs, .running⟩ := by
  have cap := limits.reader_polynomial_fit
  have env := limits.output_bound
  have pos := limits.packet_pos
  have one : 1 < 2 ^ limits.width := by omega
  have quotient := Nat.div_le_self (min (regs 258) (regs 257) - 1) (regs 34)
  have effective := Nat.min_le_right (regs 258) (regs 257)
  unfold rankWordInit Block.sequence
  refine rank_safe_constant fit one (fun f1 => ?_)
  refine rank_safe_follow (minBlock_safe memory (limits.width) 262 258 257 264 _ f1 one)
    (fun f2 => ?_)
  rw [minBlock_source 262 258 257 264 memory _ (by decide) (by decide)] at f2 ⊢
  refine rank_safe_follow (natSubBlock_safe memory (limits.width) 263 262 265 264 _ f2 one
    (by decide) (by decide)) (fun f3 => ?_)
  rw [natSubBlock_source 263 262 265 264 memory _ (by decide) (by decide)] at f3 ⊢
  refine rank_safe_arithmetic f3 ?_ (fun f4 => ?_)
  · simp [Action.LocalSafe, Registers.write, Arithmetic.eval]
    omega
  refine rank_safe_arithmetic f4 ?_ (fun f5 => ?_)
  · simp [Action.LocalSafe, Registers.write, Arithmetic.eval]
    omega
  refine rank_safe_constant f5 (by change 8 < _; omega) (fun f6 => ?_)
  refine rank_safe_follow (minBlock_safe memory (limits.width) 263 263 266 264 _ f6 one)
    (fun f7 => ?_)
  apply SimpleScalar.safe memory (limits.width) _ _ _ f7
  simp [SimpleScalar]
  exact Nat.two_pow_pos _

theorem rankWordBody_safe (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader) (readerCorrect : ReaderSimulation model memory reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hm : MetadataMatches model regs) (htotal : regs 263 ≤ 8) (hj : regs 261 ≤ 8)
    (ha : regs 260 ≤ 8 * limits.rawWidth) (hone : regs 265 = 1) :
    (rankWordBody reader).Safe memory (limits.width) ⟨regs, .running⟩ := by
  have one : 1 < 2 ^ limits.width := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 1 ≤ limits.width by have h := limits.width32; omega)
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
    have metaCompared := MetadataMatches.write model regs hm 264 1 (Or.inr (by decide))
    have hc : compared 34 ≤ limits.rawWidth := by
      rw [metadata_chunkBits model compared metaCompared]
      exact bounds.chunk_le
    have addressSafe := rankWordAddress_safe limits memory compared comparedFit hc
      (by dsimp [compared, Registers.write]; omega)
    refine rank_safe_follow addressSafe (fun addressFit => ?_)
    have addressSource := rankWordAddress_source memory compared
    have addressMeta := writes_metadata model memory rankWordAddress _ rankWordAddress_writes
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
    apply rankWordDecode_safe limits memory rr readFit
    · rw [h34, metadata_chunkBits model regs hm]
      exact bounds.chunk_le
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

structure RankWordInvariant (model : ControllerModel) (limits : SafetyLimits) (s : Data) : Prop where
  fits : s.Fits (limits.width)
  metadata : MetadataMatches model s.regs
  running : s.status = .running
  total : s.regs 263 ≤ 8
  index : s.regs 261 ≤ 8
  accumulator : s.regs 260 ≤ s.regs 261 * s.regs 34
  one : s.regs 265 = 1

private theorem rankWordBody_preserves (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory)
    (reader : Block) (readerSafe : ReaderSafe model limits.width memory reader)
    (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
    (s : Data) (inv : RankWordInvariant model limits s) :
    (rankWordBody reader).Safe memory (limits.width) s ∧
      RankWordInvariant model limits ((rankWordBody reader).eval memory s).final := by
  have stateEq := rank_data_running s inv.running
  rw [stateEq] at inv ⊢
  let regs := s.regs
  have total : regs 263 ≤ 8 := inv.total
  have index : regs 261 ≤ 8 := inv.index
  have accumulator : regs 260 ≤ regs 261 * regs 34 := inv.accumulator
  have hc : regs 34 ≤ limits.rawWidth := by
    rw [metadata_chunkBits model regs inv.metadata]
    exact bounds.chunk_le
  have acc := Nat.mul_le_mul index hc
  have safe := rankWordBody_safe model limits bounds memory reader readerSafe readerCorrect regs
    inv.fits inv.metadata total index (by omega) inv.one
  refine ⟨safe, ?_⟩
  have fit := (rankWordBody reader).eval_fits memory (limits.width) _ safe
  have metadataAfter := rankWordBody_metadata model reader readerWrites memory
    ⟨regs, .running⟩ inv.metadata
  have frame (r : Nat) (outside : ¬ RankWordBodyWrites r) :=
    rankWordBody_frame reader readerWrites memory ⟨regs, .running⟩ r outside
  by_cases active : regs 261 < regs 263
  · have source := rankWordBody_active model memory reader readerCorrect regs
      inv.metadata active inv.one
    refine ⟨fit, metadataAfter, source.1, ?_, ?_, ?_, ?_⟩
    · rw [frame 263 (by simp [RankWordBodyWrites])]; exact inv.total
    · rw [source.2.2.2]
      omega
    · rw [source.2.2.1, source.2.2.2, frame 34 (by simp [RankWordBodyWrites])]
      have contribution := chunkRank_le_chunk (regs 34)
        (min (regs 34) (regs 262 - regs 261 * regs 34))
        ((((model.store).readWord? 21
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

private theorem rankWordRepeat_safe (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory)
    (reader : Block) (readerSafe : ReaderSafe model limits.width memory reader)
    (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
    (copies : Nat) (s : Data) (inv : RankWordInvariant model limits s) :
    (Block.repeat copies (rankWordBody reader)).Safe memory (limits.width) s ∧
      RankWordInvariant model limits ((Block.repeat copies (rankWordBody reader)).eval memory s).final := by
  have step := rankWordBody_preserves model limits bounds memory reader readerSafe readerCorrect readerWrites
  have iterations := IterationsSafe.of_invariant
    ((rankWordBody reader).Safe memory (limits.width)) (RankWordInvariant model limits)
    ((rankWordBody reader).eval memory) step copies s inv
  refine ⟨Block.safe_repeat inv.fits iterations, ?_⟩
  have result := rank_iterate_invariant ((rankWordBody reader).eval memory)
    (RankWordInvariant model limits) (fun s h => (step s h).2) copies s inv
  simpa only [Block.eval, inv.running] using result

private theorem rankWordInitialized_safe (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory)
    (reader init : Block) (readerSafe : ReaderSafe model limits.width memory reader)
    (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
    (copies : Nat) (s : Data) (hs : s.status = .running)
    (hi : init.Safe memory (limits.width) s)
    (inv : RankWordInvariant model limits (init.eval memory s).final) :
    (Block.seq init (.repeat copies (rankWordBody reader))).Safe memory (limits.width) s ∧
      RankWordInvariant model limits ((Block.seq init (.repeat copies (rankWordBody reader))).eval memory s).final := by
  have repeated := rankWordRepeat_safe model limits bounds memory reader readerSafe readerCorrect readerWrites
    copies (init.eval memory s).final inv
  exact ⟨Block.safe_seq hi repeated.1, by simpa only [Block.eval, hs] using repeated.2⟩

theorem rankWordBlock_safe_invariant (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory)
    (reader : Block) (readerSafe : ReaderSafe model limits.width memory reader)
    (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hm : MetadataMatches model regs) (hl : regs 257 ≤ limits.rawWidth) :
    (rankWordBlock reader).Safe memory (limits.width) ⟨regs, .running⟩ ∧
      RankWordInvariant model limits ((rankWordBlock reader).eval memory ⟨regs, .running⟩).final := by
  have hc : 0 < regs 34 := by
    rw [metadata_chunkBits model regs hm]
    exact bounds.chunk_pos
  have initSafe := rankWordInit_safe limits memory regs fit hc hl
  have source := rankWordInit_source memory regs
  have metadataAfter := writes_metadata model memory rankWordInit _ rankWordInit_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  have inv : RankWordInvariant model limits (rankWordInit.eval memory ⟨regs, .running⟩).final := by
    refine ⟨rankWordInit.eval_fits memory (limits.width) _ initSafe,
      metadataAfter, source.1, ?_, ?_, ?_, source.2.2.2.2.2.2⟩
    · rw [source.2.2.2.2.2.1]; exact bpWordChunkCount_le_eight _ _
    · rw [source.2.2.2.1]; omega
    · rw [source.2.2.1]; omega
  exact rankWordInitialized_safe model limits bounds memory reader rankWordInit readerSafe readerCorrect
    readerWrites 8 ⟨regs, .running⟩ rfl initSafe inv

theorem rankWordBlock_safe (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader)
    (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
    (s : Data) (fit : s.Fits limits.width) (hm : MetadataMatches model s.regs)
    (length : s.regs 257 ≤ limits.rawWidth) :
    (rankWordBlock reader).Safe memory limits.width s := by
  by_cases hs : s.status = .running
  · rw [rank_data_running s hs] at fit ⊢
    exact (rankWordBlock_safe_invariant model limits bounds memory reader
      readerSafe readerCorrect readerWrites s.regs fit hm length).1
  · exact Block.safe_stopped _ _ _ s fit hs

theorem rankWordBlock_output_bound (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader)
    (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits limits.width)
    (hm : MetadataMatches model regs) (length : regs 257 ≤ limits.rawWidth) :
    ((rankWordBlock reader).eval memory ⟨regs, .running⟩).final.regs 260 ≤ 8 * limits.rawWidth := by
  have inv := (rankWordBlock_safe_invariant model limits bounds memory reader
    readerSafe readerCorrect readerWrites regs fit hm length).2
  have hc : ((rankWordBlock reader).eval memory ⟨regs, .running⟩).final.regs 34 ≤ limits.rawWidth := by
    rw [metadata_chunkBits model _ inv.metadata]
    exact bounds.chunk_le
  exact Nat.le_trans inv.accumulator (Nat.mul_le_mul inv.index hc)

theorem rankSeedRead_safe (model : ControllerModel) (limits : SafetyLimits)
    (_bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader) (segment index output : Nat)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hm : MetadataMatches model regs) :
    (rankSeedRead reader segment index output).Safe memory (limits.width)
      ⟨regs, .running⟩ := by
  unfold rankSeedRead Block.sequence
  refine rank_safe_move fit (fun f1 => ?_)
  refine rank_safe_move f1 (fun f2 => ?_)
  have mp := MetadataMatches.write model _
    (MetadataMatches.write model regs hm 8192 (regs segment) (Or.inr (by decide)))
    8193 ((regs.write 8192 (regs segment)) index) (Or.inr (by decide))
  refine rank_safe_follow (readerSafe _ f2 mp) (fun f3 => ?_)
  apply SimpleScalar.safe memory _ _ _ _ f3
  simp [SimpleScalar]

theorem rankCombine_safe (limits : SafetyLimits) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hs : regs 364 ≤ limits.packetBound)
    (hd : regs 365 ≤ limits.packetBound)
    (hw : regs 260 ≤ 8 * limits.rawWidth) :
    rankCombine.Safe memory (limits.width) ⟨regs, .running⟩ := by
  have cap := limits.envelope_lt_capacity
  have env := limits.output_bound
  have hwne : limits.width ≠ 0 := by have h := limits.width32; omega
  apply ScalarChecks_safe memory (limits.width) _ _ fit
  by_cases hsub1 : regs 370 ≤ regs 364
  all_goals by_cases hsub2 : regs 370 ≤ regs 365
  all_goals simp [ScalarChecks, rankCombine, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hsub1, hsub2, hwne] <;> omega

theorem rankSeedRead_data_safe (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader) (segment index output : Nat)
    (s : Data) (fit : s.Fits (limits.width)) (hm : MetadataMatches model s.regs) :
    (rankSeedRead reader segment index output).Safe memory (limits.width) s := by
  by_cases hs : s.status = .running
  · rw [rank_data_running s hs] at fit ⊢
    exact rankSeedRead_safe model limits bounds memory reader readerSafe segment index output s.regs fit hm
  · exact Block.safe_stopped _ _ _ s fit hs

theorem rankSeeds_safe (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader) (readerWrites : ReaderWrites reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hm : MetadataMatches model regs) (hw : 0 < regs 354) (hb : 0 < regs 355) :
    (rankSeeds reader).Safe memory (limits.width) ⟨regs, .running⟩ := by
  have one : 1 < 2 ^ limits.width := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 1 ≤ limits.width by have h := limits.width32; omega)
    omega
  unfold rankSeeds Block.sequence
  refine rank_safe_follow (rankInit_safe _ memory regs fit one hw hb) (fun f1 => ?_)
  have m1 := writes_metadata model memory rankInit _ rankInit_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  refine rank_safe_follow (rankSeedRead_data_safe model limits bounds memory reader readerSafe 356 363 364 _ f1 m1)
    (fun f2 => ?_)
  have m2 := rankSeedRead_metadata model memory reader readerWrites 356 363 364 (by decide) _ m1
  refine rank_safe_follow (rankSeedRead_data_safe model limits bounds memory reader readerSafe 357 362 365 _ f2 m2)
    (fun f3 => ?_)
  have m3 := rankSeedRead_metadata model memory reader readerWrites 357 362 365 (by decide) _ m2
  refine rank_safe_follow (rankSeedRead_data_safe model limits bounds memory reader readerSafe 358 362 366 _ f3 m3)
    (fun f4 => ?_)
  apply SimpleScalar.safe memory _ _ _ _ f4
  simp [SimpleScalar]

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

theorem rankFinish_safe_bound (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader) (readerCorrect : ReaderSimulation model memory reader)
    (readerWrites : ReaderWrites reader) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (limits.width)) (hm : MetadataMatches model regs)
    (hs : regs 364 ≤ limits.packetBound)
    (hd : regs 365 ≤ limits.packetBound)
    (_hw : regs 366 ≤ limits.packetBound)
    (hl : regs 367 ≤ limits.rawWidth)
    (position : regs 361 ≤ limits.envelope)
    (product : regs 362 * regs 354 ≤ regs 361) (initial : regs 360 = 0) :
    (rankFinish reader).Safe memory (limits.width) ⟨regs, .running⟩ ∧
      ((rankFinish reader).eval memory ⟨regs, .running⟩).final.regs 360 ≤
        limits.envelope := by
  have cap := limits.envelope_lt_capacity
  have env := limits.output_bound
  have pos := limits.envelope_pos
  have one : 1 < 2 ^ limits.width := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 1 ≤ limits.width by have h := limits.width32; omega)
    omega
  have positive : (Block.seq rankPrepareWord (.seq (rankWordBlock reader) rankCombine)).Safe
        memory (limits.width) ⟨regs, .running⟩ ∧
      ((Block.seq rankPrepareWord (.seq (rankWordBlock reader) rankCombine)).eval
        memory ⟨regs, .running⟩).final.regs 360 ≤ limits.envelope := by
    have prepareSafe := rankPrepareWord_safe _ memory regs fit one (by omega)
    refine rank_safe_follow_post (second := .seq (rankWordBlock reader) rankCombine)
      (post := fun d => d.regs 360 ≤ limits.envelope) prepareSafe (fun prepareFit => ?_)
    have sourcePrepare := rankPrepareWord_source memory regs
    have metadataPrepare := writes_metadata model memory rankPrepareWord _ rankPrepareWord_writes
      (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
    have framePrepare (r : Nat) (ho : ¬ ((256 ≤ r ∧ r < 260) ∨ r = 368 ∨ r = 369)) :=
      Block.eval_frame memory rankPrepareWord _ rankPrepareWord_writes r ho ⟨regs, .running⟩
    generalize heP : rankPrepareWord.eval memory ⟨regs, .running⟩ = prepared
      at sourcePrepare metadataPrepare framePrepare prepareFit ⊢
    rcases prepared with ⟨⟨pr, pst⟩, preceipts⟩
    dsimp only at sourcePrepare metadataPrepare framePrepare prepareFit
    obtain ⟨hpst, _, _, hlength, _, _⟩ := sourcePrepare
    subst pst
    have word := rankWordBlock_safe_invariant model limits bounds memory reader readerSafe readerCorrect
      readerWrites pr prepareFit metadataPrepare (by rw [hlength]; exact hl)
    refine rank_safe_follow_post (second := rankCombine)
      (post := fun d => d.regs 360 ≤ limits.envelope) word.1 (fun wordFit => ?_)
    have wordInv := word.2
    have frameWord (r : Nat) (ho : ¬ RankWordWrites r) :=
      rankWordBlock_frame reader readerWrites memory ⟨pr, .running⟩ r ho
    generalize heW : (rankWordBlock reader).eval memory ⟨pr, .running⟩ = ranked
      at wordInv frameWord wordFit ⊢
    rcases ranked with ⟨⟨wr, wst⟩, wreceipts⟩
    have hwst : wst = .running := wordInv.running
    subst wst
    dsimp only at wordInv frameWord wordFit ⊢
    have hws : wr 364 ≤ limits.packetBound := by
      rw [frameWord 364 (by simp [RankWordWrites]), framePrepare 364 (by omega)]
      exact hs
    have hwd : wr 365 ≤ limits.packetBound := by
      rw [frameWord 365 (by simp [RankWordWrites]), framePrepare 365 (by omega)]
      exact hd
    have hwc : wr 34 ≤ limits.rawWidth := by
      rw [metadata_chunkBits model wr wordInv.metadata]
      exact bounds.chunk_le
    have hwj : wr 261 ≤ 8 := wordInv.index
    have hwa : wr 260 ≤ wr 261 * wr 34 := wordInv.accumulator
    have hwm := Nat.mul_le_mul hwj hwc
    have hwout : wr 260 ≤ 8 * limits.rawWidth := by omega
    refine ⟨rankCombine_safe limits memory wr wordFit hws hwd hwout, ?_⟩
    have combined := rankCombine_source memory wr
    rw [combined.2.2]
    omega
  have skipSafe := Block.safe_skip memory (limits.width) ⟨regs, .running⟩ fit
  have skipBound : (Block.skip.eval memory ⟨regs, .running⟩).final.regs 360 ≤
      limits.envelope := by change regs 360 ≤ _; omega
  exact rank_branch_post (condition := 364)
    (post := fun d => d.regs 360 ≤ limits.envelope) fit ⟨skipSafe, skipBound⟩
    (rank_branch_post (condition := 365)
      (post := fun d => d.regs 360 ≤ limits.envelope) fit ⟨skipSafe, skipBound⟩
      (rank_branch_post (condition := 366)
        (post := fun d => d.regs 360 ≤ limits.envelope) fit ⟨skipSafe, skipBound⟩ positive))

private theorem rankBlock_withFinish_safe_bound (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader) (readerCorrect : ReaderSimulation model memory reader)
    (readerWrites : ReaderWrites reader) (finish : Block)
    (finishSafe : ∀ regs, (⟨regs, .running⟩ : Data).Fits (limits.width) →
      MetadataMatches model regs → regs 364 ≤ limits.packetBound →
      regs 365 ≤ limits.packetBound →
      regs 366 ≤ limits.packetBound →
      regs 367 ≤ limits.rawWidth → regs 361 ≤ limits.envelope →
      regs 362 * regs 354 ≤ regs 361 → regs 360 = 0 →
      finish.Safe memory (limits.width) ⟨regs, .running⟩ ∧
        (finish.eval memory ⟨regs, .running⟩).final.regs 360 ≤ limits.envelope)
    (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (limits.width)) (hm : MetadataMatches model regs)
    (hw : 0 < regs 354) (hb : 0 < regs 355) (length : regs 353 ≤ limits.envelope)
    (rawLength : ∀ index, logicalLength (model.store.readWord? (regs 358) index) ≤ limits.rawWidth) :
    (Block.seq (rankSeeds reader) finish).Safe memory (limits.width) ⟨regs, .running⟩ ∧
      ((Block.seq (rankSeeds reader) finish).eval memory ⟨regs, .running⟩).final.regs 360 ≤
        limits.envelope := by
  have seedsSafe := rankSeeds_safe model limits bounds memory reader readerSafe readerWrites regs fit hm hw hb
  refine rank_safe_follow_post (second := finish)
    (post := fun d => d.regs 360 ≤ limits.envelope) seedsSafe (fun seedsFit => ?_)
  have source := rankSeeds_source model memory reader readerCorrect readerWrites regs hm
  have metadataSeeds := writes_metadata model memory (rankSeeds reader) _
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
  · rw [hsuper]; exact logicalPacket_bound model limits bounds _ _
  · rw [hdelta]; exact logicalPacket_bound model limits bounds _ _
  · rw [hword]; exact logicalPacket_bound model limits bounds _ _
  · rw [hlength]; exact rawLength _
  · rw [he]; have := Nat.min_le_right (regs 352) (regs 353); omega
  · rw [hblock, he, frameSeeds]
    exact Nat.div_mul_le_self _ _
  · exact hzero

theorem rankBlock_safe_bound (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader) (readerCorrect : ReaderSimulation model memory reader)
    (readerWrites : ReaderWrites reader) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (limits.width)) (hm : MetadataMatches model regs)
    (hw : 0 < regs 354) (hb : 0 < regs 355) (length : regs 353 ≤ limits.envelope)
    (rawLength : ∀ index, logicalLength (model.store.readWord? (regs 358) index) ≤ limits.rawWidth) :
    (rankBlock reader).Safe memory (limits.width) ⟨regs, .running⟩ ∧
      ((rankBlock reader).eval memory ⟨regs, .running⟩).final.regs 360 ≤ limits.envelope :=
  rank_transport_bound memory (limits.width) (.seq (rankSeeds reader) (rankFinish reader))
    (rankBlock reader) regs (limits.envelope) rfl
    (rankBlock_withFinish_safe_bound model limits bounds memory reader readerSafe readerCorrect readerWrites
      (rankFinish reader) (rankFinish_safe_bound model limits bounds memory reader readerSafe readerCorrect readerWrites)
      regs fit hm hw hb length rawLength)

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

private theorem rankFlagWrapper_safe_bound (model : ControllerModel) (limits : SafetyLimits)
    (_bounds : ControllerSafetyBounds model limits) (memory : Memory)
    (body : Block)
    (bodySafe : ∀ regs, (⟨regs, .running⟩ : Data).Fits (limits.width) →
      MetadataMatches model regs → 0 < regs 354 → 0 < regs 355 →
      regs 353 ≤ limits.envelope →
      (∀ index, logicalLength (model.store.readWord? (regs 358) index) ≤ limits.rawWidth) →
      body.Safe memory (limits.width) ⟨regs, .running⟩ ∧
        (body.eval memory ⟨regs, .running⟩).final.regs 360 ≤ limits.envelope)
    (lengthReg widthReg superSegment blockSegment wordSegment : Nat)
    (widthLow : widthReg < 353) (segments : superSegment < 2 ^ limits.width ∧
      blockSegment < 2 ^ limits.width ∧ wordSegment < 2 ^ limits.width)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hm : MetadataMatches model regs) (widthPos : 0 < regs widthReg)
    (lengthBound : regs lengthReg ≤ limits.envelope)
    (rawLength : ∀ index, logicalLength (model.store.readWord? wordSegment index) ≤ limits.rawWidth) :
    let block := Block.sequence [.action (.move 353 lengthReg), .action (.move 354 widthReg),
      .action (.constant 355 1), .action (.constant 356 superSegment),
      .action (.constant 357 blockSegment), .action (.constant 358 wordSegment),
      .action (.constant 359 1), body]
    block.Safe memory (limits.width) ⟨regs, .running⟩ ∧
      (block.eval memory ⟨regs, .running⟩).final.regs 360 ≤ limits.envelope := by
  let post := fun d : Data => d.regs 360 ≤ limits.envelope
  have one : 1 < 2 ^ limits.width := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 1 ≤ limits.width by have h := limits.width32; omega)
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
    simp only [Registers.write, if_neg (show i ≠ 359 by omega),
      if_neg (show i ≠ 358 by omega), if_neg (show i ≠ 357 by omega),
      if_neg (show i ≠ 356 by omega), if_neg (show i ≠ 355 by omega),
      if_neg (show i ≠ 354 by omega), if_neg (show i ≠ 353 by omega)]
    exact hm i hi
  · simpa [Registers.write, show widthReg ≠ 353 by omega] using widthPos
  · simp [Registers.write]
  · simpa [Registers.write] using lengthBound
  · simpa [Registers.write] using rawLength

theorem rankLongBlock_safe_bound (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader)
    (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits limits.width)
    (hm : MetadataMatches model regs) :
    (rankLongBlock reader).Safe memory limits.width ⟨regs, .running⟩ ∧
      ((rankLongBlock reader).eval memory ⟨regs, .running⟩).final.regs 360 ≤ limits.envelope := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2) limits.width32
  apply rank_transport_bound memory limits.width
    (Block.sequence [.action (.move 353 28), .action (.move 354 30),
      .action (.constant 355 1), .action (.constant 356 9), .action (.constant 357 10),
      .action (.constant 358 11), .action (.constant 359 1), rankBlock reader])
    (rankLongBlock reader) regs limits.envelope rfl
  exact rankFlagWrapper_safe_bound model limits bounds memory (rankBlock reader)
    (rankBlock_safe_bound model limits bounds memory reader readerSafe readerCorrect readerWrites)
    28 30 9 10 11 (by decide) ⟨by omega, by omega, by omega⟩ regs fit hm
    (by rw [hm 30 (by decide)]; exact bounds.long_word_pos)
    (metadata_envelope model limits bounds regs hm 28 (by decide))
    (fun index => bounds.raw_length 11 index (Or.inr (Or.inl rfl)))

theorem rankSparseBlock_safe_bound (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader)
    (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits limits.width)
    (hm : MetadataMatches model regs) :
    (rankSparseBlock reader).Safe memory limits.width ⟨regs, .running⟩ ∧
      ((rankSparseBlock reader).eval memory ⟨regs, .running⟩).final.regs 360 ≤ limits.envelope := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2) limits.width32
  apply rank_transport_bound memory limits.width
    (Block.sequence [.action (.move 353 29), .action (.move 354 31),
      .action (.constant 355 1), .action (.constant 356 13), .action (.constant 357 14),
      .action (.constant 358 15), .action (.constant 359 1), rankBlock reader])
    (rankSparseBlock reader) regs limits.envelope rfl
  exact rankFlagWrapper_safe_bound model limits bounds memory (rankBlock reader)
    (rankBlock_safe_bound model limits bounds memory reader readerSafe readerCorrect readerWrites)
    29 31 13 14 15 (by decide) ⟨by omega, by omega, by omega⟩ regs fit hm
    (by rw [hm 31 (by decide)]; exact bounds.sparse_word_pos)
    (metadata_envelope model limits bounds regs hm 29 (by decide))
    (fun index => bounds.raw_length 15 index (Or.inr (Or.inr rfl)))

theorem rankBlock_execution_safe (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader)
    (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
    (readerFields : reader.FieldsFit limits.width)
    (budget : 552 + 11 * reader.size < 2 ^ limits.width)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits limits.width)
    (hm : MetadataMatches model regs) (hw : 0 < regs 354) (hb : 0 < regs 355)
    (length : regs 353 ≤ limits.envelope)
    (rawLength : ∀ index, logicalLength (model.store.readWord? (regs 358) index) ≤ limits.rawWidth) :
    RankExecutionSafety memory limits.width ((rankBlock reader).compileAt 0 ++ [.halt 360])
      (552 + 11 * reader.size) ⟨regs, 0, .running⟩ := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2) limits.width32
  exact rank_compiled_safety memory limits.width (rankBlock reader) 360 _ regs
    (by rw [rankBlock_size]; omega) budget
    (rankBlock_fieldsFit _ _ readerFields (by omega))
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega) fit
    (rankBlock_safe_bound model limits bounds memory reader readerSafe readerCorrect readerWrites
      regs fit hm hw hb length rawLength).1

/-- An independently expanded consumer of every compiled safety conjunct. -/
theorem rankBlock_execution_safe_expectedType (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader)
    (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
    (readerFields : reader.FieldsFit limits.width)
    (budget : 552 + 11 * reader.size < 2 ^ limits.width)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits limits.width)
    (hm : MetadataMatches model regs) (hw : 0 < regs 354) (hb : 0 < regs 355)
    (length : regs 353 ≤ limits.envelope)
    (rawLength : ∀ index, logicalLength (model.store.readWord? (regs 358) index) ≤ limits.rawWidth) :
    let program := (rankBlock reader).compileAt 0 ++ [.halt 360]
    let actual := run memory program (552 + 11 * reader.size) ⟨regs, 0, .running⟩
    (∀ instruction ∈ program, instruction.Fits limits.width) ∧
    actual.final.Fits limits.width ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe limits.width t.before t.instruction ∧ t.after.Fits limits.width) ∧
    (∀ index, index ≤ 552 + 11 * reader.size →
      (run memory program index ⟨regs, 0, .running⟩).final.Fits limits.width) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      actual.transitions[index]? = some t → t.receipt = some receipt →
      receipt.address < 2 ^ limits.width ∧ receipt.reply = memory[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ limits.width)) :=
  rankBlock_execution_safe model limits bounds memory reader readerSafe readerCorrect readerWrites
    readerFields budget regs fit hm hw hb length rawLength

end RMQ.PackedBitvector.Controller
