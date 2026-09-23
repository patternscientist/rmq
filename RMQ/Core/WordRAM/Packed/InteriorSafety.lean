import RMQ.Core.WordRAM.Packed.RankSafety
import RMQ.Core.WordRAM.Packed.InteriorCandidateProof
import RMQ.Core.WordRAM.Packed.QueryStatic

/-! # Word safety of the complete fixed interior navigator -/

namespace RMQ.SuccinctFinal.PackedWordRAM
open Cartesian PackedCellProbe Structured SuccinctSpace SuccinctClose

private theorem shiftLeft_numeric (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b :=
  Nat.shiftLeft_eq a b

theorem interior_concat_value_lt (a b la lb : Nat)
    (ha : a < 2 ^ la) (hb : b < 2 ^ lb) :
    a + b * 2 ^ la < 2 ^ (la + lb) := by
  have hm := Nat.mul_le_mul_right (2 ^ la) (show b + 1 ≤ 2 ^ lb by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  rw [Nat.pow_add, Nat.mul_comm (2 ^ la) (2 ^ lb)]
  omega

theorem interior_seven_width_lt (n : Nat) :
    7 * packedReviewerCellWidth n < wordWidth n := by
  unfold wordWidth
  omega

theorem interior_seven_value_fit (n : Nat) :
    2 ^ (7 * packedReviewerCellWidth n) + 1 < 2 ^ wordWidth n := by
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 7 * packedReviewerCellWidth n + 2 ≤ wordWidth n by unfold wordWidth; omega)
  have hp := Nat.two_pow_pos (7 * packedReviewerCellWidth n)
  rw [Nat.pow_add] at hpow
  omega

theorem interior_small_constants_fit (n : Nat) : 8280 < 2 ^ wordWidth n := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth n by unfold wordWidth; omega)
  omega

theorem interior_address_fit (n base index total next : Nat)
    (hb : base ≤ metadataEnvelope n) (hi : index ≤ metadataEnvelope n)
    (ht : total ≤ 7) (hn : next ≤ 7) :
    base + index * total + next < 2 ^ wordWidth n := by
  have hm := Nat.mul_le_mul hi ht
  have hp := reader_polynomial_fit n
  have he := metadataEnvelope_pos n
  omega

theorem interiorReadHead_safe (n : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits (wordWidth n)) :
    interiorReadHead.Safe memory (wordWidth n) s := by
  apply SimpleScalar.safe _ _ _ _ _ fit
  have h := interior_small_constants_fit n
  have hw := wordWidth_pos n
  simp [SimpleScalar, interiorReadHead, Block.sequence]
  omega

theorem interiorReadAddress_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hb : regs 706 ≤ metadataEnvelope n) (hi : regs 707 ≤ metadataEnvelope n)
    (ht : regs 709 ≤ 7) (hj : regs 710 ≤ 7) :
    interiorReadAddress.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have hcap := interior_address_fit n (regs 706) (regs 707) (regs 709) (regs 710) hb hi ht hj
  have hsmall := interior_small_constants_fit n
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, interiorReadAddress, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval]
  omega

theorem interiorReadDecode_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hone : regs 714 = 1) (hj : regs 710 < 7)
    (hlen : regs 712 + regs 8195 ≤ 7 * packedReviewerCellWidth n)
    (ha : regs 711 < 2 ^ regs 712) (hb : regs 8194 ≤ 2 ^ regs 8195) :
    interiorReadDecode.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have hsmall := interior_small_constants_fit n
  have hw := interior_seven_width_lt n
  have hcap := interior_seven_value_fit n
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hlen
  have hwfit := Nat.lt_two_pow_self (n := wordWidth n)
  have hwne : wordWidth n ≠ 0 := by unfold wordWidth; omega
  have hpacketFit := fit.1 8194
  dsimp only at hpacketFit
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hz : regs 8194 = 0
  · simp [ScalarChecks, interiorReadDecode, Block.sequence, Block.eval, Action.eval,
      Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
      Registers.write, Arithmetic.eval, hone, hz]
    omega
  · have hv := interior_concat_value_lt (regs 711) (regs 8194 - 1)
      (regs 712) (regs 8195) ha (by omega)
    have hsub : 1 ≤ regs 8194 := by omega
    simp [ScalarChecks, interiorReadDecode, Block.sequence, Block.eval, Action.eval,
      Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
      Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
      shiftLeft_numeric, hone, hz, hsub, hwne]
    omega

theorem interiorReadInit_safe (shape : CartesianShape) (memory : Memory)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hone : regs 714 = 1)
    (hwidth : regs 705 ≤ 7 * packedReviewerCellWidth shape.size) :
    interiorReadInit.Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hbp : regs 32 = packedBpCodeWordWidth shape.size := hm 16 (by decide)
  have hpos : 0 < regs 32 := by rw [hbp]; exact packedBpCodeWordWidth_pos shape.size
  have hcap := interior_seven_value_fit shape.size
  have hw := interior_seven_width_lt shape.size
  have hwfit := Nat.lt_two_pow_self (n := wordWidth shape.size)
  have hsmall := interior_small_constants_fit shape.size
  have hquot := Nat.div_le_self (regs 705) (regs 32)
  have hmod := Nat.mod_le (regs 705) (regs 32)
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hz : regs 705 % regs 32 = 0
  all_goals simp [ScalarChecks, interiorReadInit, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, hone, hz] <;> omega

theorem interiorReadFinish_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n)) (hone : regs 714 = 1)
    (hlen : regs 712 ≤ 7 * packedReviewerCellWidth n) (ha : regs 711 < 2 ^ regs 712) :
    interiorReadFinish.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hlen
  have hcap := interior_seven_value_fit n
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hz : regs 713 = 0
  all_goals simp [ScalarChecks, interiorReadFinish, Action.LocalSafe,
    Arithmetic.eval, hone, hz] <;> omega

private theorem interior_safe_follow {memory : Memory} {width : Nat}
    {first second : Block} {s : Data} (head : first.Safe memory width s)
    (tail : (first.eval memory s).final.Fits width →
      second.Safe memory width (first.eval memory s).final) :
    (Block.seq first second).Safe memory width s :=
  Block.safe_seq head (tail (first.eval_fits memory width s head))

private theorem interior_data_running (s : Data) (hs : s.status = .running) :
    s = ⟨s.regs, .running⟩ := by cases s; simp_all

theorem logicalPacket_le_two_pow_logicalLength (word : Option (List Bool)) :
    logicalPacket word ≤ 2 ^ logicalLength word := by
  cases word with
  | none => simp [logicalPacket, logicalLength]
  | some bits =>
    have hb := GenericSelect.bitsToNatLE_lt_two_pow_length bits
    dsimp [logicalPacket, logicalLength]
    omega

theorem interiorReadBody_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (rsafe : ReaderSafe shape memory reader) (rcorrect : ReaderCorrect shape memory reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hb : regs 706 ≤ metadataEnvelope shape.size)
    (hi : regs 707 ≤ metadataEnvelope shape.size) (ht : regs 709 ≤ 7)
    (hone : regs 714 = 1)
    (hlen : regs 712 ≤ regs 710 * packedReviewerCellWidth shape.size)
    (hvalue : regs 711 < 2 ^ regs 712) :
    (interiorReadBody reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hsmall := interior_small_constants_fit shape.size
  have hcmp : (Action.comparison .lt 717 710 709).LocalSafe memory
      (wordWidth shape.size) ⟨regs, .running⟩ := by
    simp only [Action.LocalSafe, Comparison.eval]
    split <;> omega
  unfold interiorReadBody
  refine interior_safe_follow (Block.safe_action _ _ _ _ fit hcmp) (fun comparedFit => ?_)
  by_cases active : regs 710 < regs 709
  · have he : Comparison.lt.eval (regs 710) (regs 709) = 1 := by
      simp [Comparison.eval, active]
    simp only [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, he] at comparedFit ⊢
    apply Block.safe_ifZero comparedFit
    simp only [Registers.write_same, Nat.one_ne_zero, if_false]
    let compared := regs.write 717 1
    have hmc := MetadataMatches.write shape regs hm 717 1 (Or.inr (by decide))
    have ha := interiorReadAddress_safe shape.size memory compared comparedFit
      (by simpa [compared, Registers.write] using hb)
      (by simpa [compared, Registers.write] using hi)
      (by simpa [compared, Registers.write] using ht)
      (by dsimp [compared, Registers.write]; omega)
    refine interior_safe_follow ha (fun addressFit => ?_)
    have hs := interiorReadAddress_source memory compared
    generalize hea : interiorReadAddress.eval memory ⟨compared, .running⟩ = addressed
      at hs addressFit ⊢
    rcases addressed with ⟨⟨ar, ast⟩, receipts⟩
    dsimp only at hs addressFit
    obtain ⟨hst, _, hsegment, haddress, hframe⟩ := hs
    subst ast
    have hma : MetadataMatches shape ar := by
      intro i hi
      rw [hframe _ (by omega) (by omega) (by omega)]
      exact hmc i hi
    have hr := rsafe ⟨ar, .running⟩ addressFit hma
    refine interior_safe_follow hr (fun readFit => ?_)
    have hs := rcorrect ar hma
    generalize her : reader.eval memory ⟨ar, .running⟩ = readResult at hs readFit ⊢
    rcases readResult with ⟨⟨rr, rst⟩, reads⟩
    dsimp only at hs readFit
    obtain ⟨hst, hpacket, hlength, _, rframe⟩ := hs
    subst rst
    have hf (r : Nat) (hr : r < 715) : rr r = regs r := by
      rw [rframe r (Or.inl (by omega)), hframe r (by omega) (by omega) (by omega)]
      simp [compared, Registers.write, show r ≠ 717 by omega]
    have hw := (rank_logicalPacket_bounds shape (ar 8192) (ar 8193)).2
    have hv := logicalPacket_le_two_pow_logicalLength
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? (ar 8192) (ar 8193))
    have hmul := Nat.mul_le_mul_right (packedReviewerCellWidth shape.size)
      (show regs 710 + 1 ≤ 7 by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    apply interiorReadDecode_safe shape.size memory rr readFit
    · rw [hf 714 (by decide)]; exact hone
    · rw [hf 710 (by decide)]; omega
    · rw [hf 712 (by decide), hlength]
      omega
    · rw [hf 711 (by decide), hf 712 (by decide)]; exact hvalue
    · rw [hpacket, hlength]; exact hv
  · have he : Comparison.lt.eval (regs 710) (regs 709) = 0 := by
      simp [Comparison.eval, active]
    simp only [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, he] at comparedFit ⊢
    apply Block.safe_ifZero comparedFit
    simp only [Registers.write_same, if_true]
    exact Block.safe_skip _ _ _ comparedFit

structure InteriorWordInvariant (shape : CartesianShape) (s : Data) : Prop where
  fits : s.Fits (wordWidth shape.size)
  metadata : MetadataMatches shape s.regs
  running : s.status = .running
  base : s.regs 706 ≤ metadataEnvelope shape.size
  entry : s.regs 707 ≤ metadataEnvelope shape.size
  total : s.regs 709 ≤ 7
  index : s.regs 710 ≤ s.regs 709
  one : s.regs 714 = 1
  length : s.regs 712 ≤ s.regs 710 * packedReviewerCellWidth shape.size
  value : s.regs 711 < 2 ^ s.regs 712

theorem interiorReadBody_preserves (shape : CartesianShape) (memory : Memory)
    (reader : Block) (rsafe : ReaderSafe shape memory reader)
    (rcorrect : ReaderCorrect shape memory reader) (rwrites : ReaderWrites reader)
    (s : Data) (inv : InteriorWordInvariant shape s) :
    (interiorReadBody reader).Safe memory (wordWidth shape.size) s ∧
      InteriorWordInvariant shape ((interiorReadBody reader).eval memory s).final := by
  have he := interior_data_running s inv.running
  rw [he] at inv ⊢
  let regs := s.regs
  have hs := interiorReadBody_safe shape memory reader rsafe rcorrect regs inv.fits
    inv.metadata inv.base inv.entry inv.total inv.one inv.length inv.value
  refine ⟨hs, ?_⟩
  have fit := (interiorReadBody reader).eval_fits _ _ _ hs
  have hmeta := interiorReadBody_metadata shape reader rwrites memory ⟨regs, .running⟩ inv.metadata
  have hf (r : Nat) (hr : ¬ InteriorBodyWrites r) :=
    interiorReadBody_frame reader rwrites memory ⟨regs, .running⟩ r hr
  by_cases active : regs 710 < regs 709
  · have source := interiorReadBody_active shape memory reader rcorrect regs inv.metadata inv.one active
    let word := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
      (regs 706 + regs 707 * regs 709 + regs 710)
    have hlen : (word.getD []).length ≤ packedReviewerCellWidth shape.size := by
      have he : logicalLength word = (word.getD []).length := by cases word <;> rfl
      rw [← he]
      exact (rank_logicalPacket_bounds shape 20 (regs 706 + regs 707 * regs 709 + regs 710)).2
    have hbits := GenericSelect.bitsToNatLE_lt_two_pow_length (word.getD [])
    refine ⟨fit, hmeta, source.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf 706 (by simp [InteriorBodyWrites])]; exact inv.base
    · rw [hf 707 (by simp [InteriorBodyWrites])]; exact inv.entry
    · rw [hf 709 (by simp [InteriorBodyWrites])]; exact inv.total
    · calc
        _ = regs 710 + 1 := source.2.2.1
        _ ≤ regs 709 := by omega
        _ = _ := (hf 709 (by simp [InteriorBodyWrites])).symm
    · rw [hf 714 (by simp [InteriorBodyWrites])]; exact inv.one
    · calc
        _ = regs 712 + (word.getD []).length := source.2.2.2.2.2
        _ ≤ regs 710 * packedReviewerCellWidth shape.size + packedReviewerCellWidth shape.size :=
          Nat.add_le_add inv.length hlen
        _ = (regs 710 + 1) * packedReviewerCellWidth shape.size := by rw [Nat.add_mul, Nat.one_mul]
        _ = _ := congrArg (fun j => j * packedReviewerCellWidth shape.size) source.2.2.1.symm
    · rw [source.2.2.2.2.1, source.2.2.2.2.2]
      exact interior_concat_value_lt _ _ _ _ inv.value hbits
  · have source := interiorReadBody_inactive reader memory regs (by omega)
    rw [source] at fit hmeta ⊢
    refine ⟨fit, hmeta, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Registers.write] using inv.base
    · simpa only [Registers.write] using inv.entry
    · simpa only [Registers.write] using inv.total
    · simpa only [Registers.write] using inv.index
    · simpa only [Registers.write] using inv.one
    · simpa only [Registers.write] using inv.length
    · simpa only [Registers.write] using inv.value

private theorem interior_iterate_invariant (body : Data → Evaluation) (invariant : Data → Prop)
    (step : ∀ s, invariant s → invariant (body s).final) (count : Nat) (s : Data)
    (hs : invariant s) : invariant (iterate body count s).final := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih _ (step s hs)

theorem interiorReadRepeat_safe (shape : CartesianShape) (memory : Memory)
    (reader : Block) (rsafe : ReaderSafe shape memory reader)
    (rcorrect : ReaderCorrect shape memory reader) (rwrites : ReaderWrites reader)
    (copies : Nat) (s : Data) (inv : InteriorWordInvariant shape s) :
    (Block.repeat copies (interiorReadBody reader)).Safe memory (wordWidth shape.size) s ∧
      InteriorWordInvariant shape ((Block.repeat copies (interiorReadBody reader)).eval memory s).final := by
  have step := interiorReadBody_preserves shape memory reader rsafe rcorrect rwrites
  have loops := IterationsSafe.of_invariant ((interiorReadBody reader).Safe memory (wordWidth shape.size))
    (InteriorWordInvariant shape) ((interiorReadBody reader).eval memory) step copies s inv
  refine ⟨Block.safe_repeat inv.fits loops, ?_⟩
  have hi := interior_iterate_invariant ((interiorReadBody reader).eval memory)
    (InteriorWordInvariant shape) (fun s h => (step s h).2) copies s inv
  simpa only [Block.eval, inv.running] using hi

private theorem interiorReadInitialized_safe (shape : CartesianShape) (memory : Memory)
    (reader init : Block) (rsafe : ReaderSafe shape memory reader)
    (rcorrect : ReaderCorrect shape memory reader) (rwrites : ReaderWrites reader)
    (copies : Nat) (s : Data) (hi : init.Safe memory (wordWidth shape.size) s)
    (inv : InteriorWordInvariant shape (init.eval memory s).final) :
    (Block.seq init (.seq (.repeat copies (interiorReadBody reader)) interiorReadFinish)).Safe
      memory (wordWidth shape.size) s := by
  have repeated := interiorReadRepeat_safe shape memory reader rsafe rcorrect rwrites copies _ inv
  refine Block.safe_seq hi (Block.safe_seq repeated.1 ?_)
  have ir := repeated.2
  generalize he : (Block.repeat copies (interiorReadBody reader)).eval memory (init.eval memory s).final =
    actual at ir ⊢
  rcases actual with ⟨⟨regs, status⟩, reads⟩
  have hr := ir.running
  dsimp only at hr
  subst status
  have hindex : regs 710 ≤ regs 709 := ir.index
  have htotal : regs 709 ≤ 7 := ir.total
  have hm := Nat.mul_le_mul_right (packedReviewerCellWidth shape.size) (Nat.le_trans hindex htotal)
  exact interiorReadFinish_safe shape.size memory regs ir.fits ir.one
    (Nat.le_trans ir.length hm) ir.value

theorem interiorReadValid_safe (shape : CartesianShape) (memory : Memory)
    (reader : Block) (rsafe : ReaderSafe shape memory reader)
    (rcorrect : ReaderCorrect shape memory reader) (rwrites : ReaderWrites reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hone : regs 714 = 1)
    (hb : regs 706 ≤ metadataEnvelope shape.size) (hi : regs 707 ≤ metadataEnvelope shape.size)
    (hwidth : regs 705 ≤ 7 * packedReviewerCellWidth shape.size)
    (hcount : fixedWidthNatTableMachineChunkCount (regs 705) (regs 32) ≤ 7) :
    (interiorReadValid reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hs := interiorReadInit_safe shape memory regs fit hm hone hwidth
  have source := interiorReadInit_source memory regs hone
  have frame (r : Nat) (ho : ¬ (709 ≤ r ∧ r < 714 ∨ r = 715)) :=
    Block.eval_frame memory interiorReadInit _ interiorReadInit_writes r ho ⟨regs, .running⟩
  have hinv : InteriorWordInvariant shape (interiorReadInit.eval memory ⟨regs, .running⟩).final := by
    refine ⟨interiorReadInit.eval_fits _ _ _ hs, ?_, source.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [frame (16 + i) (by omega)]
      exact hm i hi
    · rw [frame 706 (by omega)]; exact hb
    · rw [frame 707 (by omega)]; exact hi
    · rw [source.2.2.1]; exact hcount
    · rw [source.2.2.2.1]; omega
    · rw [frame 714 (by omega)]; exact hone
    · rw [source.2.2.2.2.2.1, source.2.2.2.1]; simp
    · rw [source.2.2.2.2.1, source.2.2.2.2.2.1]; decide
  exact interiorReadInitialized_safe shape memory reader interiorReadInit rsafe rcorrect rwrites
    7 ⟨regs, .running⟩ hs hinv

theorem interiorReadInvalid_safe (shape : CartesianShape) (memory : Memory)
    (reader : Block) (rsafe : ReaderSafe shape memory reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    (interiorReadInvalid reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hsmall := interior_small_constants_fit shape.size
  unfold interiorReadInvalid Block.sequence
  refine interior_safe_follow (Block.safe_action _ _ _ _ fit (by change 20 < _; omega)) (fun f1 => ?_)
  refine interior_safe_follow (Block.safe_action _ _ _ _ f1 (f1.1 57)) (fun f2 => ?_)
  have hmeta : MetadataMatches shape (((regs.write 8192 20).write 8193 (regs 57))) := by
    intro i hi
    simpa [Registers.write, show 16 + i ≠ 8192 by omega, show 16 + i ≠ 8193 by omega] using hm i hi
  have hs := rsafe _ f2 hmeta
  refine interior_safe_follow hs (fun f3 => ?_)
  apply SimpleScalar.safe _ _ _ _ _ f3
  simp [SimpleScalar]

theorem interiorReadBlock_bounded_safe (shape : CartesianShape) (memory : Memory)
    (reader : Block) (rsafe : ReaderSafe shape memory reader)
    (rcorrect : ReaderCorrect shape memory reader) (rwrites : ReaderWrites reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hentries : regs 704 ≤ metadataEnvelope shape.size)
    (hb : regs 706 ≤ metadataEnvelope shape.size)
    (hwidth : regs 705 ≤ 7 * packedReviewerCellWidth shape.size)
    (hcount : fixedWidthNatTableMachineChunkCount (regs 705) (packedBpCodeWordWidth shape.size) ≤ 7) :
    (interiorReadBlock reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have headSafe := interiorReadHead_safe shape.size memory ⟨regs, .running⟩ fit
  unfold interiorReadBlock
  refine interior_safe_follow headSafe (fun headFit => ?_)
  rw [interiorReadHead_source] at headFit ⊢
  let prepared := interiorReadHeadRegs regs
  have hmeta : MetadataMatches shape prepared := by
    intro i hi
    simpa [prepared, interiorReadHeadRegs, Registers.write, show 16 + i ≠ 708 by omega,
      show 16 + i ≠ 714 by omega, show 16 + i ≠ 717 by omega] using hm i hi
  apply Block.safe_ifZero headFit
  by_cases active : regs 707 < regs 704
  · have hone : prepared 714 = 1 := by simp [prepared, interiorReadHeadRegs, Registers.write]
    have hbp : prepared 32 = packedBpCodeWordWidth shape.size := hmeta 16 (by decide)
    have hc : fixedWidthNatTableMachineChunkCount (prepared 705) (prepared 32) ≤ 7 := by
      rw [hbp]
      simpa [prepared, interiorReadHeadRegs, Registers.write] using hcount
    have hs := interiorReadValid_safe shape memory reader rsafe rcorrect rwrites prepared headFit hmeta hone
      (by simpa [prepared, interiorReadHeadRegs, Registers.write] using hb)
      (by dsimp [prepared, interiorReadHeadRegs, Registers.write]; omega)
      (by simpa [prepared, interiorReadHeadRegs, Registers.write] using hwidth) hc
    simpa only [prepared, interiorReadHeadRegs, Registers.write, active, reduceIte] using hs
  · have hs := interiorReadInvalid_safe shape memory reader rsafe prepared headFit hmeta
    simpa only [prepared, interiorReadHeadRegs, Registers.write, active, reduceIte] using hs

theorem interior_bpWidth_le_old (n : Nat) : packedBpCodeWordWidth n ≤ packedReviewerCellWidth n := by
  apply packedReviewerMachineWordBits_le_cellWidth
  have := packedTwoMul_le_reviewerBound n
  omega

theorem interior_canonical_count_bound (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) :
    packedReviewerInteriorEntryCount shape.size component ≤ metadataEnvelope shape.size := by
  have hword := interiorDescriptor_le_envelope shape component
    (word := packedReviewerInteriorComponentWordCount shape.size component)
    (by simp [interiorDescriptor])
  have hwidth := packedReviewerInteriorEntryWidth_pos shape component
  have hbp := packedBpCodeWordWidth_pos shape.size
  have hcover := GenericSelect.selectCeilDiv_mul_ge_of_pos
    (n := packedReviewerInteriorEntryWidth shape.size component) hbp
  have hchunks : 0 < packedChunkCount (packedReviewerInteriorEntryWidth shape.size component)
      (packedBpCodeWordWidth shape.size) := by
    rw [← selectCeilDiv_eq_packedChunkCount _ _ hbp]
    by_cases hz : GenericSelect.selectCeilDiv (packedReviewerInteriorEntryWidth shape.size component)
        (packedBpCodeWordWidth shape.size) = 0
    · rw [hz] at hcover; simp at hcover; omega
    · omega
  have hm := Nat.le_mul_of_pos_right (packedReviewerInteriorEntryCount shape.size component) hchunks
  rw [← packedReviewerInteriorTableWords_eq_chunkCount _ _ _ hbp] at hm
  exact Nat.le_trans hm hword

theorem interior_canonical_base_bound (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) :
    packedReviewerInteriorComponentWordPrefix shape.size component ≤ metadataEnvelope shape.size :=
  interiorDescriptor_le_envelope shape component (by simp [interiorDescriptor])

theorem interiorReadBlock_canonical_safe (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hentries : regs 704 = packedReviewerInteriorEntryCount shape.size component)
    (hwidth : regs 705 = packedReviewerInteriorEntryWidth shape.size component)
    (hbase : regs 706 = packedReviewerInteriorComponentWordPrefix shape.size component) :
    (interiorReadBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  apply interiorReadBlock_bounded_safe shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_readerSafe shape) (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs fit hm
  · rw [hentries]; exact interior_canonical_count_bound shape component
  · rw [hbase]; exact interior_canonical_base_bound shape component
  · rw [hwidth]
    exact Nat.le_trans (interiorEntryWidth_le_seven shape component)
      (Nat.mul_le_mul_left 7 (interior_bpWidth_le_old shape.size))
  · rw [hwidth]; exact canonical_interior_chunks_le_seven shape component

theorem interior_envelope_power (n : Nat) :
    metadataEnvelope n = 2 ^ (6 + 2 * packedReviewerCellWidth n) := by
  rw [Nat.mul_comm 2 (packedReviewerCellWidth n)]
  simp [metadataEnvelope, Nat.pow_add, Nat.pow_mul]

theorem interior_envelope_log_width (n : Nat) :
    SuccinctRank.machineWordBits (metadataEnvelope n) = 7 + 2 * packedReviewerCellWidth n := by
  rw [interior_envelope_power]
  simp [SuccinctRank.machineWordBits, Nat.log2_two_pow]
  omega

theorem interior_envelope_square_log_width (n : Nat) :
    SuccinctRank.machineWordBits (metadataEnvelope n * metadataEnvelope n) =
      13 + 4 * packedReviewerCellWidth n := by
  rw [interior_envelope_power, ← Nat.pow_add]
  simp [SuccinctRank.machineWordBits, Nat.log2_two_pow]
  omega

theorem interior_sparse_width_bound (n domain : Nat) (hd : domain ≤ metadataEnvelope n) :
    bpSparseLevelWidth domain ≤ 13 + 4 * packedReviewerCellWidth n := by
  have hlog := SuccinctRank.machineWordBits_mono_le hd
  rw [interior_envelope_log_width] at hlog
  have he := Nat.lt_two_pow_self (n := 6 + 2 * packedReviewerCellWidth n)
  rw [← interior_envelope_power] at he
  have hfactor : Nat.log2 domain + 1 ≤ metadataEnvelope n := by
    unfold SuccinctRank.machineWordBits at hlog
    omega
  have hm := SuccinctRank.machineWordBits_mono_le (Nat.mul_le_mul hd hfactor)
  rw [interior_envelope_square_log_width] at hm
  exact hm

theorem interior_entry_width_bound (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) :
    packedReviewerInteriorEntryWidth shape.size component ≤
      17 + 4 * packedReviewerCellWidth shape.size := by
  have hlocal := interior_canonical_count_bound shape .localLevel
  have hglobal := interior_canonical_count_bound shape .globalLevel
  have hblock := interior_canonical_count_bound shape .minRel
  have hmacro : (packedInteriorLayout shape.size).macroSize ≤ metadataEnvelope shape.size := by
    change (packedInteriorLayout shape.size).macroSize + 2 ≤ _ at hlocal
    omega
  have hbase : packedSummaryBase shape.size ≤ metadataEnvelope shape.size := by
    have hm := Nat.le_mul_of_pos_right (packedSummaryBase shape.size)
      (show 0 < packedSummaryBase shape.size by unfold packedSummaryBase; omega)
    change packedSummaryBase shape.size * packedSummaryBase shape.size ≤ _ at hmacro
    omega
  have hb := SuccinctRank.machineWordBits_mono_le hbase
  rw [interior_envelope_log_width] at hb
  have hmw := SuccinctRank.machineWordBits_mono_le hmacro
  rw [interior_envelope_log_width] at hmw
  have hbw := SuccinctRank.machineWordBits_mono_le hblock
  rw [interior_envelope_log_width] at hbw
  cases component with
  | baseline =>
    have h := interior_bpWidth_le_old shape.size
    simpa only [packedReviewerInteriorEntryWidth] using (by omega :
      packedBpCodeWordWidth shape.size ≤ 17 + 4 * packedReviewerCellWidth shape.size)
  | minRel | maxRel | argOffset =>
    change 2 * (Nat.log2 (packedSummaryBase shape.size) + 1) + 3 ≤ _
    unfold SuccinctRank.machineWordBits at hb
    omega
  | localOffset =>
    change SuccinctRank.machineWordBits (packedInteriorLayout shape.size).macroSize ≤ _
    omega
  | globalBlock =>
    change SuccinctRank.machineWordBits (packedReviewerInteriorEntryCount shape.size .minRel) ≤ _
    omega
  | localLevel =>
    exact Nat.le_trans (interior_sparse_width_bound shape.size _ hlocal) (by omega)
  | globalLevel =>
    exact Nat.le_trans (interior_sparse_width_bound shape.size _ hglobal) (by omega)

theorem interior_entry_capacity_bound (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) :
    2 ^ packedReviewerInteriorEntryWidth shape.size component ≤
      32 * (metadataEnvelope shape.size * metadataEnvelope shape.size) := by
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) (interior_entry_width_bound shape component)
  have he : 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size) =
      2 ^ (17 + 4 * packedReviewerCellWidth shape.size) := by
    rw [interior_envelope_power]
    change 2 ^ 5 * (2 ^ (6 + 2 * packedReviewerCellWidth shape.size) *
      2 ^ (6 + 2 * packedReviewerCellWidth shape.size)) = _
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  rw [he]
  exact h

theorem interior_polynomial_fit (n : Nat) :
    512 * (metadataEnvelope n * metadataEnvelope n * metadataEnvelope n) < 2 ^ wordWidth n := by
  have he : 512 * (metadataEnvelope n * metadataEnvelope n * metadataEnvelope n) =
      2 ^ (27 + 6 * packedReviewerCellWidth n) := by
    rw [interior_envelope_power]
    change 2 ^ 9 * ((2 ^ (6 + 2 * packedReviewerCellWidth n) *
      2 ^ (6 + 2 * packedReviewerCellWidth n)) * 2 ^ (6 + 2 * packedReviewerCellWidth n)) = _
    rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  rw [he]
  apply Nat.pow_lt_pow_right (by decide)
  unfold wordWidth
  omega

theorem fixedTable_packet_bound {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (index : Nat) :
    (((table.readCosted index).erase).map (· + 1)).getD 0 ≤ 2 ^ width := by
  rw [FixedWidthNatTable.readCosted_erase, ← table.read_exact index]
  cases hw : table.store.words[index]? with
  | none => simp
  | some bits =>
    have hv := GenericSelect.bitsToNatLE_lt_two_pow_length bits
    have hl := table.word_length_of_get? hw
    simp only [Option.map_some, Option.getD_some]
    rw [hl] at hv
    omega

private theorem interior_packet_bound_of_refinement (shape : CartesianShape)
    {entries : List Nat} {width : Nat} (table : FixedWidthNatTable entries width)
    (base index : Nat)
    (href : ((canonicalRelativeRmmMachineReadNatComputation shape table base index).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
        canonicalRelativeRmmMachineReadNatCosted shape table index) :
    ((((packedInteriorReadNatOf shape.size entries.length width base index).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)).value).map (· + 1)).getD 0 ≤
        2 ^ width := by
  have hstore : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20 =
      (canonicalRelativeRmmInteriorComponentStore shape).store.words := by
    funext address
    simpa using concreteBPNativeSuccinctRMQGlobalReadStore_canonicalComponent shape address
  have hv := congrArg Costed.erase href
  simp only [FlatStoreExecution.toCosted_erase, canonicalRelativeRmmMachineReadNatCosted_erase,
    packedInteriorReadNatOf_eq] at hv
  rw [hstore, hv]
  exact fixedTable_packet_bound table index

theorem interior_canonical_packet_width_bound (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) (index : Nat) :
    let execution := (packedInteriorReadNatOf shape.size
      (packedReviewerInteriorEntryCount shape.size component)
      (packedReviewerInteriorEntryWidth shape.size component)
      (packedReviewerInteriorComponentWordPrefix shape.size component) index).run
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    (execution.value.map (· + 1)).getD 0 ≤ 2 ^ packedReviewerInteriorEntryWidth shape.size component := by
  cases component with
  | baseline =>
    have h := interior_packet_bound_of_refinement shape
      (canonicalRelativeRmmSummaryTable shape).baselineTable _ index
      (canonicalRelativeRmmBaselineReadComputation_refines shape index)
    simpa only [packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedReviewerInteriorComponentWordPrefix, bpSuperblockBaselineEntries_length,
      RelativeRmm.Layout.superWidth, packedBpCodeWordWidth, CartesianShape.bpCode_length,
      packedInteriorLayout_eq, packedInteriorOffsets_eq] using h
  | minRel =>
    have h := interior_packet_bound_of_refinement shape
      (canonicalRelativeRmmSummaryTable shape).minRelTable _ index
      (canonicalRelativeRmmMinRelReadComputation_refines shape index)
    simpa only [packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedReviewerInteriorComponentWordPrefix, bpBlockRelativeMinExcessEntries_length,
      packedInteriorLayout_eq, packedInteriorOffsets_eq] using h
  | maxRel =>
    have h := interior_packet_bound_of_refinement shape
      (canonicalRelativeRmmSummaryTable shape).maxRelTable _ index
      (canonicalRelativeRmmMaxRelReadComputation_refines shape index)
    simpa only [packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedReviewerInteriorComponentWordPrefix, bpBlockRelativeMaxExcessEntries_length,
      packedInteriorLayout_eq, packedInteriorOffsets_eq] using h
  | argOffset =>
    have h := interior_packet_bound_of_refinement shape
      (canonicalRelativeRmmSummaryTable shape).argOffsetTable _ index
      (canonicalRelativeRmmArgOffsetReadComputation_refines shape index)
    simpa only [packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedReviewerInteriorComponentWordPrefix, bpBlockArgMinLocalOffsetEntries_length,
      packedInteriorLayout_eq, packedInteriorOffsets_eq] using h
  | localOffset =>
    have h := interior_packet_bound_of_refinement shape
      (canonicalRelativeRmmInteriorLocalTable shape).table _ index
      (canonicalRelativeRmmLocalReadComputation_refines shape index)
    simpa only [packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedReviewerInteriorComponentWordPrefix, bpLocalSparseOffsetEntries_length,
      packedInteriorLayout_eq, packedInteriorOffsets_eq] using h
  | globalBlock =>
    have h := interior_packet_bound_of_refinement shape
      (canonicalRelativeRmmInteriorGlobalTable shape).table _ index
      (canonicalRelativeRmmGlobalReadComputation_refines shape index)
    simpa only [packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedReviewerInteriorComponentWordPrefix, bpGlobalSparseBlockEntries_length,
      packedInteriorLayout_eq, packedInteriorOffsets_eq] using h
  | localLevel =>
    have h := interior_packet_bound_of_refinement shape
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table _ index
      (canonicalRelativeRmmLocalLevelReadComputation_refines shape index)
    simpa only [packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedReviewerInteriorComponentWordPrefix, bpSparseLevelEntries_length,
      packedInteriorLayout_eq, packedInteriorOffsets_eq] using h
  | globalLevel =>
    have h := interior_packet_bound_of_refinement shape
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table _ index
      (canonicalRelativeRmmGlobalLevelReadComputation_refines shape index)
    simpa only [packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedReviewerInteriorComponentWordPrefix, bpSparseLevelEntries_length,
      packedInteriorLayout_eq, packedInteriorOffsets_eq] using h

theorem interiorReadBlock_canonical_packet_bound (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) (regs : Registers)
    (hm : MetadataMatches shape regs)
    (hentries : regs 704 = packedReviewerInteriorEntryCount shape.size component)
    (hwidth : regs 705 = packedReviewerInteriorEntryWidth shape.size component)
    (hbase : regs 706 = packedReviewerInteriorComponentWordPrefix shape.size component) :
    ((interiorReadBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 708 ≤
      32 * (metadataEnvelope shape.size * metadataEnvelope shape.size) := by
  have hs := interiorReadBlock_reference shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm
    (by rw [hwidth]; exact canonical_interior_chunks_le_seven shape component)
  have hb := interior_canonical_packet_width_bound shape component (regs 707)
  have hp := interior_entry_capacity_bound shape component
  dsimp only [flatStoreExecutionTraceResultAtSegment] at hs hb
  rw [hs.2.1]
  simpa only [hentries, hwidth, hbase] using Nat.le_trans hb hp

def InteriorEntrySafety (shape : CartesianShape) (entry : Block) : Prop :=
  ∀ component regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) →
    MetadataMatches shape regs →
    regs 704 = packedReviewerInteriorEntryCount shape.size component →
    regs 705 = packedReviewerInteriorEntryWidth shape.size component →
    regs 706 = packedReviewerInteriorComponentWordPrefix shape.size component →
    entry.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
      (entry.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 708 ≤
        32 * (metadataEnvelope shape.size * metadataEnvelope shape.size)

theorem interiorReadBlock_entrySafety (shape : CartesianShape) :
    InteriorEntrySafety shape (interiorReadBlock logicalReadBlock) := by
  intro component regs fit hm hc hw hb
  exact ⟨interiorReadBlock_canonical_safe shape component regs fit hm hc hw hb,
    interiorReadBlock_canonical_packet_bound shape component regs hm hc hw hb⟩

private theorem interior_follow_result (memory : Memory) (width : Nat)
    (first second : Block) (regs : Registers) (post : Registers → Prop)
    (safe : first.Safe memory width ⟨regs, .running⟩)
    (running : (first.eval memory ⟨regs, .running⟩).final.status = .running)
    (result : post (first.eval memory ⟨regs, .running⟩).final.regs)
    (next : ∀ out, (⟨out, .running⟩ : Data).Fits width → post out →
      second.Safe memory width ⟨out, .running⟩) :
    (Block.seq first second).Safe memory width ⟨regs, .running⟩ := by
  refine Block.safe_seq safe ?_
  have fit := first.eval_fits memory width ⟨regs, .running⟩ safe
  generalize he : first.eval memory ⟨regs, .running⟩ = actual at running result fit ⊢
  rcases actual with ⟨⟨out, status⟩, reads⟩
  dsimp only at running result fit
  subst status
  exact next out fit result

private theorem interior_follow_exact (memory : Memory) (width : Nat)
    (first second : Block) (regs prepared : Registers) (reads : List Receipt)
    (safe : first.Safe memory width ⟨regs, .running⟩)
    (result : first.eval memory ⟨regs, .running⟩ = ⟨⟨prepared, .running⟩, reads⟩)
    (next : (⟨prepared, .running⟩ : Data).Fits width →
      second.Safe memory width ⟨prepared, .running⟩) :
    (Block.seq first second).Safe memory width ⟨regs, .running⟩ := by
  refine Block.safe_seq safe ?_
  have fit := first.eval_fits memory width ⟨regs, .running⟩ safe
  rw [result] at fit ⊢
  exact next fit

private theorem interior_metadata_frame (shape : CartesianShape) (before after : Registers)
    (hm : MetadataMatches shape before)
    (frame : ∀ r, 16 ≤ r → r < 190 → after r = before r) :
    MetadataMatches shape after := by
  intro i hi
  rw [frame (16 + i) (by omega) (by omega)]
  exact hm i hi

theorem interior_geometry_positive (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    0 < regs 35 ∧ 0 < regs 38 ∧ 0 < regs 45 ∧ 0 < regs 46 := by
  have h35 : regs 35 = (packedInteriorLayout shape.size).blocksPerSuper := hm 19 (by decide)
  have h38 : regs 38 = (packedInteriorLayout shape.size).macroSize := hm 22 (by decide)
  have h45 : regs 45 = bpSparseLevelDomain (packedInteriorLayout shape.size).macroSize := hm 29 (by decide)
  have h46 : regs 46 = bpSparseLevelDomain (packedInteriorLayout shape.size).macroSampleCount := hm 30 (by decide)
  rw [h35, h38, h45, h46]
  have hbase : 0 < packedSummaryBase shape.size := by unfold packedSummaryBase; omega
  exact ⟨hbase, Nat.mul_pos hbase hbase, by unfold bpSparseLevelDomain; omega,
    by unfold bpSparseLevelDomain; omega⟩

theorem interior_envelope_powers (n : Nat) :
    metadataEnvelope n ≤ metadataEnvelope n * metadataEnvelope n ∧
    metadataEnvelope n * metadataEnvelope n ≤
      metadataEnvelope n * metadataEnvelope n * metadataEnvelope n := by
  have he := metadataEnvelope_pos n
  exact ⟨Nat.le_mul_of_pos_right _ he, Nat.le_mul_of_pos_right _ he⟩

theorem interiorCandidateNone_safe (n : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits (wordWidth n)) : candidateNoneBlock.Safe memory (wordWidth n) s := by
  apply SimpleScalar.safe _ _ _ _ _ fit
  simp [SimpleScalar, candidateNoneBlock, Block.sequence, Nat.two_pow_pos]

theorem interiorCandidateSave_safe (n base : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits (wordWidth n)) : (candidateSaveBlock base).Safe memory (wordWidth n) s := by
  apply SimpleScalar.safe _ _ _ _ _ fit
  simp [SimpleScalar, candidateSaveBlock, Block.sequence]

theorem interiorCandidateMerge_safe (n base : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits (wordWidth n)) : (candidateMergeLeftBlock base).Safe memory (wordWidth n) s := by
  have h := interior_small_constants_fit n
  have hw := wordWidth_pos n
  apply SimpleScalar.safe _ _ _ _ _ fit
  simp [SimpleScalar, candidateMergeLeftBlock, candidateRestoreBlock, Block.sequence]
  omega

theorem interiorMinBaselinePrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    interiorMinBaselinePrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hpos := (interior_geometry_positive shape regs hm).1
  have hd := Nat.div_le_self (regs 768) (regs 35)
  have hf := fit.1 768
  have hs := interior_small_constants_fit shape.size
  have widthPos := wordWidth_pos shape.size
  have bounded (r : Nat) : regs r < 2 ^ wordWidth shape.size := fit.1 r
  dsimp only at hf
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, interiorMinBaselinePrefix, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, bounded]
  omega

theorem interiorMinRelativePrefix_safe (shape : CartesianShape) (base : Nat) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) :
    (interiorMinRelativePrefix base).Safe (shapeMemory shape) (wordWidth shape.size) s := by
  apply SimpleScalar.safe _ _ _ _ _ fit
  simp [SimpleScalar, interiorMinRelativePrefix, Block.sequence]

theorem interiorLocalSpanPrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hmacro : regs 800 ≤ 3 * metadataEnvelope shape.size)
    (hstart : regs 801 ≤ 3 * metadataEnvelope shape.size)
    (hlevel : regs 802 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    interiorLocalSpanPrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have h38 := MetadataMatches.envelope shape regs hm 38 (by decide)
  have h39 := MetadataMatches.envelope shape regs hm 39 (by decide)
  have h40 := MetadataMatches.envelope shape regs hm 40 (by decide)
  have hm0 := Nat.mul_le_mul h40 h38
  have hm1 := Nat.mul_le_mul hmacro hm0
  have hm2 := Nat.mul_le_mul hlevel h38
  have hm3 := Nat.mul_le_mul h39 hm0
  have he := interior_envelope_powers shape.size
  have cap := interior_polynomial_fit shape.size
  have bounded (r : Nat) : regs r < 2 ^ wordWidth shape.size := fit.1 r
  simp only [Nat.mul_assoc] at hm1 hm2 hm3 cap he
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, interiorLocalSpanPrefix, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, bounded]
  omega

theorem interiorGlobalSpanPrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hstart : regs 816 ≤ 3 * metadataEnvelope shape.size)
    (hlevel : regs 817 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    interiorGlobalSpanPrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have h39 := MetadataMatches.envelope shape regs hm 39 (by decide)
  have h41 := MetadataMatches.envelope shape regs hm 41 (by decide)
  have hm0 := Nat.mul_le_mul h41 h39
  have hm1 := Nat.mul_le_mul hlevel h39
  have he := interior_envelope_powers shape.size
  have cap := interior_polynomial_fit shape.size
  have bounded (r : Nat) : regs r < 2 ^ wordWidth shape.size := fit.1 r
  simp only [Nat.mul_assoc] at hm1 cap he
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, interiorGlobalSpanPrefix, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, bounded]
  omega

private theorem interior_entry_then (shape : CartesianShape) (entry tail : Block)
    (es : InteriorEntrySafety shape entry)
    (ec : InteriorEntrySpec shape (shapeMemory shape) entry)
    (ew : entry.WritesOnly InteriorReadWrites)
    (component : PackedReviewerInteriorComponentTag) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hc : regs 704 = packedReviewerInteriorEntryCount shape.size component)
    (hw : regs 705 = packedReviewerInteriorEntryWidth shape.size component)
    (hb : regs 706 = packedReviewerInteriorComponentWordPrefix shape.size component)
    (next : ∀ out, (⟨out, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape out → out 708 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size) →
      (∀ r, ¬ InteriorReadWrites r → out r = regs r) →
      tail.Safe (shapeMemory shape) (wordWidth shape.size) ⟨out, .running⟩) :
    (Block.seq entry tail).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hs := es component regs fit hm hc hw hb
  obtain ⟨out, he, _⟩ := ec regs hm
    (by rw [hw]; exact canonical_interior_chunks_le_seven shape component)
  have frame := Block.eval_frame (shapeMemory shape) entry InteriorReadWrites ew
  have keep : ∀ r, ¬ InteriorReadWrites r → out r = regs r := by
    intro r hr
    simpa only [he] using frame r hr ⟨regs, .running⟩
  have om := interior_metadata_frame shape regs out hm
    (by intro r hr hl; exact keep r (by unfold InteriorReadWrites; omega))
  have bound : out 708 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size) := by
    simpa only [he] using hs.2
  exact interior_follow_exact (shapeMemory shape) (wordWidth shape.size) entry tail regs out _
    hs.1 he (fun ofit => next out ofit om bound keep)

theorem interiorMinBaselineProgram_safe (shape : CartesianShape) (entry : Block)
    (es : InteriorEntrySafety shape entry)
    (ec : InteriorEntrySpec shape (shapeMemory shape) entry)
    (ew : entry.WritesOnly InteriorReadWrites) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    (interiorMinBaselineProgram entry).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  unfold interiorMinBaselineProgram
  refine interior_follow_exact _ _ _ _ regs _ _
    (interiorMinBaselinePrefix_safe shape regs fit hm)
    (interiorMinBaselinePrefix_source (shapeMemory shape) regs) (fun preparedFit => ?_)
  let pr := ((((regs.write 774 1).write 704 (regs 37)).write 705 (regs 32)).write
    706 (regs 49)).write 707 (regs 768 / regs 35)
  have pm : MetadataMatches shape pr := interior_metadata_frame shape regs pr hm (by
    intro r hr hl
    simp [pr, Registers.write, show r ≠ 774 by omega, show r ≠ 704 by omega,
      show r ≠ 705 by omega, show r ≠ 706 by omega, show r ≠ 707 by omega])
  have hc : regs 37 = packedReviewerInteriorEntryCount shape.size .baseline := hm 21 (by decide)
  have hw : regs 32 = packedReviewerInteriorEntryWidth shape.size .baseline := hm 16 (by decide)
  have hb : regs 49 = packedReviewerInteriorComponentWordPrefix shape.size .baseline := hm 33 (by decide)
  refine interior_entry_then shape entry _ es ec ew .baseline pr preparedFit pm
    (by simpa [pr, Registers.write] using hc) (by simpa [pr, Registers.write] using hw)
    (by simpa [pr, Registers.write] using hb) ?_
  intro out ofit _ _ _
  exact Block.safe_action _ _ _ _ ofit (ofit.1 708)

theorem interiorMinFieldProgram_safe (shape : CartesianShape) (entry : Block)
    (es : InteriorEntrySafety shape entry)
    (ec : InteriorEntrySpec shape (shapeMemory shape) entry)
    (ew : entry.WritesOnly InteriorReadWrites)
    (component : PackedReviewerInteriorComponentTag) (base output : Nat) (hbase : base < 704)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hc : regs 36 = packedReviewerInteriorEntryCount shape.size component)
    (hw : regs 42 = packedReviewerInteriorEntryWidth shape.size component)
    (hb : regs base = packedReviewerInteriorComponentWordPrefix shape.size component) :
    (interiorMinFieldProgram entry base output).Safe (shapeMemory shape) (wordWidth shape.size)
      ⟨regs, .running⟩ := by
  unfold interiorMinFieldProgram
  refine interior_follow_exact _ _ _ _ regs _ _
    (interiorMinRelativePrefix_safe shape base _ fit)
    (interiorMinRelativePrefix_source (shapeMemory shape) regs base hbase) (fun preparedFit => ?_)
  let pr := (((regs.write 704 (regs 36)).write 705 (regs 42)).write 706 (regs base)).write 707 (regs 768)
  have pm : MetadataMatches shape pr := interior_metadata_frame shape regs pr hm (by
    intro r hr hl
    simp [pr, Registers.write, show r ≠ 704 by omega, show r ≠ 705 by omega,
      show r ≠ 706 by omega, show r ≠ 707 by omega])
  refine interior_entry_then shape entry _ es ec ew component pr preparedFit pm
    (by simpa [pr, Registers.write] using hc) (by simpa [pr, Registers.write] using hw)
    (by simpa [pr, Registers.write] using hb) ?_
  intro out ofit _ _ _
  exact Block.safe_action _ _ _ _ ofit (ofit.1 708)

theorem interiorMinFinish_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hblock : regs 768 ≤ 40 * (metadataEnvelope shape.size * metadataEnvelope shape.size))
    (hone : regs 774 = 1)
    (hp0 : regs 769 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size))
    (hp1 : regs 770 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size))
    (hp2 : regs 772 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    interiorMinFinish.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have h33 := MetadataMatches.envelope shape regs hm 33 (by decide)
  have h35 := MetadataMatches.envelope shape regs hm 35 (by decide)
  have hm0 := Nat.mul_le_mul h33 h35
  have hm1 := Nat.mul_le_mul hblock h33
  have he := interior_envelope_powers shape.size
  have cap := interior_polynomial_fit shape.size
  have small := interior_small_constants_fit shape.size
  have hw : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  simp only [Nat.mul_assoc] at hm1 cap he
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases h0 : regs 769 = 0
  · simp [ScalarChecks, interiorMinFinish, candidateNoneBlock, Block.sequence, Block.eval,
      Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
      Registers.write, h0, Nat.two_pow_pos]
  by_cases h1 : regs 770 = 0
  · simp [ScalarChecks, interiorMinFinish, candidateNoneBlock, Block.sequence, Block.eval,
      Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
      Registers.write, h0, h1, Nat.two_pow_pos]
  by_cases h2 : regs 771 = 0
  · simp [ScalarChecks, interiorMinFinish, candidateNoneBlock, Block.sequence, Block.eval,
      Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
      Registers.write, h0, h1, h2, Nat.two_pow_pos]
  by_cases h3 : regs 772 = 0
  · simp [ScalarChecks, interiorMinFinish, candidateNoneBlock, Block.sequence, Block.eval,
      Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
      Registers.write, h0, h1, h2, h3, Nat.two_pow_pos]
  have ha : 1 ≤ regs 769 := by omega
  have hb : 1 ≤ regs 770 := by omega
  have hc : 1 ≤ regs 768 * regs 33 + regs 772 := by omega
  by_cases hd : regs 33 * regs 35 ≤ regs 769 - 1 + (regs 770 - 1)
  all_goals simp [ScalarChecks, interiorMinFinish, candidateNoneBlock, Block.sequence,
    Block.eval, Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
    h0, h1, h2, h3, hone, ha, hb, hc, hd, hw] <;> omega

private theorem interior_min_field_then (shape : CartesianShape) (entry tail : Block)
    (es : InteriorEntrySafety shape entry)
    (ec : InteriorEntrySpec shape (shapeMemory shape) entry)
    (ew : entry.WritesOnly InteriorReadWrites)
    (component : PackedReviewerInteriorComponentTag) (base output : Nat) (hbase : base < 704)
    (hout : 190 ≤ output) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hc : regs 36 = packedReviewerInteriorEntryCount shape.size component)
    (hw : regs 42 = packedReviewerInteriorEntryWidth shape.size component)
    (hb : regs base = packedReviewerInteriorComponentWordPrefix shape.size component)
    (next : ∀ out, (⟨out, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape out → out output ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size) →
      (∀ r, ¬ InteriorFieldWrites output r → out r = regs r) →
      tail.Safe (shapeMemory shape) (wordWidth shape.size) ⟨out, .running⟩) :
    (Block.seq (interiorMinFieldProgram entry base output) tail).Safe
      (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have safe := interiorMinFieldProgram_safe shape entry es ec ew component base output hbase regs fit hm hc hw hb
  obtain ⟨out, he, hp, frame⟩ := interiorMinFieldProgram_source shape (shapeMemory shape) entry ec ew
    base output hbase regs hm
  have om := interior_metadata_frame shape regs out hm
    (by intro r hr hl; exact frame r (by unfold InteriorFieldWrites; omega))
  have hcount : (packedInteriorLayout shape.size).blockCount =
      packedReviewerInteriorEntryCount shape.size component := (hm 20 (by decide)).symm.trans hc
  have hwidth : (packedInteriorLayout shape.size).relativeWidth =
      packedReviewerInteriorEntryWidth shape.size component := (hm 26 (by decide)).symm.trans hw
  have packet := Nat.le_trans (interior_canonical_packet_width_bound shape component (regs 768))
    (interior_entry_capacity_bound shape component)
  have bound : out output ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size) := by
    rw [hp]
    simpa only [hcount, hwidth, hb] using packet
  exact interior_follow_exact _ _ _ _ regs out _ safe he
    (fun ofit => next out ofit om bound frame)

private theorem interior_min_baseline_then (shape : CartesianShape) (entry tail : Block)
    (es : InteriorEntrySafety shape entry)
    (ec : InteriorEntrySpec shape (shapeMemory shape) entry)
    (ew : entry.WritesOnly InteriorReadWrites) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (next : ∀ out, (⟨out, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape out → out 769 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size) →
      out 774 = 1 → (∀ r, ¬ InteriorBaselineWrites r → out r = regs r) →
      tail.Safe (shapeMemory shape) (wordWidth shape.size) ⟨out, .running⟩) :
    (Block.seq (interiorMinBaselineProgram entry) tail).Safe
      (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have safe := interiorMinBaselineProgram_safe shape entry es ec ew regs fit hm
  obtain ⟨out, he, hp, hone, frame⟩ := interiorMinBaselineProgram_source shape (shapeMemory shape) entry ec ew regs hm
  have om := interior_metadata_frame shape regs out hm
    (by intro r hr hl; exact frame r (by unfold InteriorBaselineWrites; omega))
  have packet := Nat.le_trans (interior_canonical_packet_width_bound shape .baseline
    (regs 768 / (packedInteriorLayout shape.size).blocksPerSuper)) (interior_entry_capacity_bound shape .baseline)
  have bound : out 769 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size) := by
    rw [hp]
    exact packet
  exact interior_follow_exact _ _ _ _ regs out _ safe he
    (fun ofit => next out ofit om bound hone frame)

theorem interiorMinProgram_safe (shape : CartesianShape) (entry : Block)
    (es : InteriorEntrySafety shape entry)
    (ec : InteriorEntrySpec shape (shapeMemory shape) entry)
    (ew : entry.WritesOnly InteriorReadWrites) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hblock : regs 768 ≤ 40 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (interiorMinProgram entry).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  unfold interiorMinProgram
  refine interior_min_baseline_then shape entry _ es ec ew regs fit hm ?_
  intro ra fa ma pa onea framea
  refine interior_min_field_then shape entry _ es ec ew .minRel 50 770 (by decide) (by decide)
    ra fa ma (ma 20 (by decide)) (ma 26 (by decide)) (ma 34 (by decide)) ?_
  intro rb fb mb pb frameb
  refine interior_min_field_then shape entry _ es ec ew .maxRel 51 771 (by decide) (by decide)
    rb fb mb (mb 20 (by decide)) (mb 26 (by decide)) (mb 35 (by decide)) ?_
  intro rc fc mc _ framec
  refine interior_min_field_then shape entry _ es ec ew .argOffset 52 772 (by decide) (by decide)
    rc fc mc (mc 20 (by decide)) (mc 26 (by decide)) (mc 36 (by decide)) ?_
  intro rd fd md pd framed
  apply interiorMinFinish_safe shape rd fd md
  · rw [framed 768 (by simp [InteriorFieldWrites]), framec 768 (by simp [InteriorFieldWrites]),
      frameb 768 (by simp [InteriorFieldWrites]), framea 768 (by simp [InteriorBaselineWrites])]
    exact hblock
  · rw [framed 774 (by simp [InteriorFieldWrites]), framec 774 (by simp [InteriorFieldWrites]),
      frameb 774 (by simp [InteriorFieldWrites])]
    exact onea
  · rw [framed 769 (by simp [InteriorFieldWrites]), framec 769 (by simp [InteriorFieldWrites]),
      frameb 769 (by simp [InteriorFieldWrites])]
    exact pa
  · rw [framed 770 (by simp [InteriorFieldWrites]), framec 770 (by simp [InteriorFieldWrites])]
    exact pb
  · exact pd

theorem interiorMinBlock_canonical_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hblock : regs 768 ≤ 40 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (interiorMinBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ :=
  interiorMinProgram_safe shape (interiorReadBlock logicalReadBlock) (interiorReadBlock_entrySafety shape)
    (interiorReadBlock_spec shape (shapeMemory shape) logicalReadBlock (logicalReadBlock_correct shape)
      logicalReadBlock_writesOnly) (interiorReadBlock_writes logicalReadBlock logicalReadBlock_writesOnly)
    regs fit hm hblock

theorem interiorLocalSpanSelectedPrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hmacro : regs 800 ≤ 3 * metadataEnvelope shape.size)
    (hp : regs 708 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    interiorLocalSpanSelectedPrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have h38 := MetadataMatches.envelope shape regs hm 38 (by decide)
  have hm0 := Nat.mul_le_mul hmacro h38
  have he := interior_envelope_powers shape.size
  have cap := interior_polynomial_fit shape.size
  have small := interior_small_constants_fit shape.size
  have hw : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  simp only [Nat.mul_assoc] at hm0 cap he
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : 1 ≤ regs 800 * regs 38 + regs 708
  all_goals simp [ScalarChecks, interiorLocalSpanSelectedPrefix, Block.sequence,
    Block.eval, Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hsub, hw] <;> omega

theorem interiorGlobalSpanSelectedPrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) :
    interiorGlobalSpanSelectedPrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hp := fit.1 708
  have small := interior_small_constants_fit shape.size
  have hw : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  dsimp only at hp
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : 1 ≤ regs 708
  all_goals simp [ScalarChecks, interiorGlobalSpanSelectedPrefix, Block.sequence,
    Block.eval, Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hsub, hw] <;> omega

def InteriorMinimumSafety (shape : CartesianShape) (minimum : Block) : Prop :=
  ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) → MetadataMatches shape regs →
    regs 768 ≤ 40 * (metadataEnvelope shape.size * metadataEnvelope shape.size) →
    minimum.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩

theorem interiorLocalSpanProgram_safe (shape : CartesianShape) (entry minimum : Block)
    (es : InteriorEntrySafety shape entry)
    (ec : InteriorEntrySpec shape (shapeMemory shape) entry)
    (ew : entry.WritesOnly InteriorReadWrites) (ms : InteriorMinimumSafety shape minimum)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hmacro : regs 800 ≤ 3 * metadataEnvelope shape.size)
    (hstart : regs 801 ≤ 3 * metadataEnvelope shape.size)
    (hlevel : regs 802 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (interiorLocalSpanProgram entry minimum).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  unfold interiorLocalSpanProgram
  refine interior_follow_exact _ _ _ _ regs _ _
    (interiorLocalSpanPrefix_safe shape regs fit hm hmacro hstart hlevel)
    (interiorLocalSpanPrefix_source (shapeMemory shape) regs) (fun preparedFit => ?_)
  have pm : MetadataMatches shape (interiorLocalSpanPrepared regs) :=
    interior_metadata_frame shape regs _ hm (by
      intro r hr hl
      simp [interiorLocalSpanPrepared, Registers.write, show r ≠ 704 by omega,
        show r ≠ 707 by omega, show r ≠ 803 by omega, show r ≠ 705 by omega, show r ≠ 706 by omega])
  have h38 : regs 38 = (packedInteriorLayout shape.size).macroSize := hm 22 (by decide)
  have h39 : regs 39 = (packedInteriorLayout shape.size).macroSampleCount := hm 23 (by decide)
  have h40 : regs 40 = (packedInteriorLayout shape.size).levelCount := hm 24 (by decide)
  have h43 : regs 43 = (packedInteriorLayout shape.size).offsetWidth := hm 27 (by decide)
  have h53 : regs 53 = (packedInteriorOffsets shape.size).localOffset := hm 37 (by decide)
  refine interior_entry_then shape entry _ es ec ew .localOffset _ preparedFit pm
    (by simp [interiorLocalSpanPrepared, Registers.write, h38, h39, h40, packedReviewerInteriorEntryCount])
    (by simp [interiorLocalSpanPrepared, Registers.write, h43, packedReviewerInteriorEntryWidth])
    (by simp [interiorLocalSpanPrepared, Registers.write, h53, packedReviewerInteriorComponentWordPrefix]) ?_
  intro out ofit om packet frame
  apply Block.safe_ifZero ofit
  split
  · exact interiorCandidateNone_safe shape.size _ _ ofit
  · have macroBound : out 800 ≤ 3 * metadataEnvelope shape.size := by
      rw [frame 800 (by simp [InteriorReadWrites])]
      simpa [interiorLocalSpanPrepared, Registers.write] using hmacro
    refine interior_follow_exact _ _ _ _ out _ _
      (interiorLocalSpanSelectedPrefix_safe shape out ofit om macroBound packet)
      (interiorLocalSpanSelectedPrefix_source (shapeMemory shape) out) (fun selectedFit => ?_)
    apply ms _ selectedFit
    · exact interior_metadata_frame shape out _ om (by
        intro r hr hl
        simp [interiorLocalSpanSelected, Registers.write, show r ≠ 804 by omega,
          show r ≠ 768 by omega, show r ≠ 803 by omega])
    · have mul := Nat.mul_le_mul macroBound (MetadataMatches.envelope shape out om 38 (by decide))
      simp only [Nat.mul_assoc] at mul
      simp [interiorLocalSpanSelected, Registers.write]
      omega

theorem interiorGlobalSpanProgram_safe (shape : CartesianShape) (entry minimum : Block)
    (es : InteriorEntrySafety shape entry)
    (ec : InteriorEntrySpec shape (shapeMemory shape) entry)
    (ew : entry.WritesOnly InteriorReadWrites) (ms : InteriorMinimumSafety shape minimum)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hstart : regs 816 ≤ 3 * metadataEnvelope shape.size)
    (hlevel : regs 817 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (interiorGlobalSpanProgram entry minimum).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  unfold interiorGlobalSpanProgram
  refine interior_follow_exact _ _ _ _ regs _ _
    (interiorGlobalSpanPrefix_safe shape regs fit hm hstart hlevel)
    (interiorGlobalSpanPrefix_source (shapeMemory shape) regs) (fun preparedFit => ?_)
  have pm : MetadataMatches shape (interiorGlobalSpanPrepared regs) :=
    interior_metadata_frame shape regs _ hm (by
      intro r hr hl
      simp [interiorGlobalSpanPrepared, Registers.write, show r ≠ 704 by omega,
        show r ≠ 707 by omega, show r ≠ 705 by omega, show r ≠ 706 by omega])
  have h39 : regs 39 = (packedInteriorLayout shape.size).macroSampleCount := hm 23 (by decide)
  have h41 : regs 41 = (packedInteriorLayout shape.size).globalLevelCount := hm 25 (by decide)
  have h44 : regs 44 = (packedInteriorLayout shape.size).blockAddressWidth := hm 28 (by decide)
  have h54 : regs 54 = (packedInteriorOffsets shape.size).globalBlock := hm 38 (by decide)
  refine interior_entry_then shape entry _ es ec ew .globalBlock _ preparedFit pm
    (by simp [interiorGlobalSpanPrepared, Registers.write, h39, h41, packedReviewerInteriorEntryCount])
    (by simp [interiorGlobalSpanPrepared, Registers.write, h44, packedReviewerInteriorEntryWidth])
    (by simp [interiorGlobalSpanPrepared, Registers.write, h54, packedReviewerInteriorComponentWordPrefix]) ?_
  intro out ofit om packet _
  apply Block.safe_ifZero ofit
  split
  · exact interiorCandidateNone_safe shape.size _ _ ofit
  · refine interior_follow_exact _ _ _ _ out _ _
      (interiorGlobalSpanSelectedPrefix_safe shape out ofit)
      (interiorGlobalSpanSelectedPrefix_source (shapeMemory shape) out) (fun selectedFit => ?_)
    apply ms _ selectedFit
    · exact interior_metadata_frame shape out _ om (by
        intro r hr hl
        simp [interiorGlobalSpanSelected, Registers.write, show r ≠ 818 by omega,
          show r ≠ 768 by omega, show r ≠ 819 by omega])
    · simp [interiorGlobalSpanSelected, Registers.write]
      omega

theorem interiorLocalSpanBlock_canonical_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hmacro : regs 800 ≤ 3 * metadataEnvelope shape.size)
    (hstart : regs 801 ≤ 3 * metadataEnvelope shape.size)
    (hlevel : regs 802 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (interiorLocalSpanBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ :=
  interiorLocalSpanProgram_safe shape _ _ (interiorReadBlock_entrySafety shape)
    (interiorReadBlock_spec shape _ _ (logicalReadBlock_correct shape) logicalReadBlock_writesOnly)
    (interiorReadBlock_writes _ logicalReadBlock_writesOnly) (interiorMinBlock_canonical_safe shape)
    regs fit hm hmacro hstart hlevel

theorem interiorGlobalSpanBlock_canonical_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hstart : regs 816 ≤ 3 * metadataEnvelope shape.size)
    (hlevel : regs 817 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (interiorGlobalSpanBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ :=
  interiorGlobalSpanProgram_safe shape _ _ (interiorReadBlock_entrySafety shape)
    (interiorReadBlock_spec shape _ _ (logicalReadBlock_correct shape) logicalReadBlock_writesOnly)
    (interiorReadBlock_writes _ logicalReadBlock_writesOnly) (interiorMinBlock_canonical_safe shape)
    regs fit hm hstart hlevel

private theorem interior_call_then (shape : CartesianShape) (first tail : Block)
    (writes : Nat → Prop) (hw : first.WritesOnly writes)
    (outside : ∀ r, 16 ≤ r → r < 190 → ¬ writes r)
    (regs : Registers) (hm : MetadataMatches shape regs)
    (safe : first.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩)
    (running : (first.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running)
    (next : ∀ out, (⟨out, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape out → (∀ r, ¬ writes r → out r = regs r) →
      tail.Safe (shapeMemory shape) (wordWidth shape.size) ⟨out, .running⟩) :
    (Block.seq first tail).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have frame := fun r hr => Block.eval_frame (shapeMemory shape) first writes hw r hr ⟨regs, .running⟩
  have hmeta := interior_metadata_frame shape regs _ hm (fun r hr hl => frame r (outside r hr hl))
  exact interior_follow_result _ _ first tail regs
    (fun out => MetadataMatches shape out ∧ ∀ r, ¬ writes r → out r = regs r)
    safe running ⟨hmeta, frame⟩ (fun out fit h => next out fit h.1 h.2)

private theorem interior_save_then (shape : CartesianShape) (base : Nat) (hbase : 190 ≤ base)
    (tail : Block) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (next : ∀ out, (⟨out, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape out → (∀ r, r < base ∨ base + 3 ≤ r → out r = regs r) →
      tail.Safe (shapeMemory shape) (wordWidth shape.size) ⟨out, .running⟩) :
    (Block.seq (candidateSaveBlock base) tail).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  apply interior_call_then shape _ tail (fun r => base ≤ r ∧ r < base + 3)
    (candidateSaveBlock_writes base) (by intro r hr hl; omega) regs hm
    (interiorCandidateSave_safe shape.size base _ _ fit)
    (by simp [candidateSaveBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
      execute, State.writeNext, Data.ofState])
  intro out ofit om frame
  exact next out ofit om (by intro r hr; exact frame r (by omega))

theorem interiorLocalTwoFirstPrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    interiorLocalTwoFirstPrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have pos := (interior_geometry_positive shape regs hm).2.2.1
  have bound (r : Nat) : regs r < 2 ^ wordWidth shape.size := fit.1 r
  have packetFit := bound 708
  have hd := Nat.div_le_self (regs 708 - 1) (regs 45)
  have hmod := Nat.mod_le (regs 708 - 1) (regs 45)
  have small := interior_small_constants_fit shape.size
  have hw : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : 1 ≤ regs 708
  all_goals simp [ScalarChecks, interiorLocalTwoFirstPrefix, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hsub, bound, hw] <;> omega

theorem interiorGlobalTwoFirstPrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    interiorGlobalTwoFirstPrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have pos := (interior_geometry_positive shape regs hm).2.2.2
  have bound (r : Nat) : regs r < 2 ^ wordWidth shape.size := fit.1 r
  have packetFit := bound 708
  have hd := Nat.div_le_self (regs 708 - 1) (regs 46)
  have hmod := Nat.mod_le (regs 708 - 1) (regs 46)
  have small := interior_small_constants_fit shape.size
  have hw : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : 1 ≤ regs 708
  all_goals simp [ScalarChecks, interiorGlobalTwoFirstPrefix, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hsub, bound, hw] <;> omega

theorem interiorLocalTwoSecondPrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (ha : regs 833 ≤ metadataEnvelope shape.size) (hb : regs 834 ≤ metadataEnvelope shape.size) :
    interiorLocalTwoSecondPrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have bound (r : Nat) : regs r < 2 ^ wordWidth shape.size := fit.1 r
  have he := interior_envelope_powers shape.size
  have cap := interior_polynomial_fit shape.size
  have small := interior_small_constants_fit shape.size
  have hw : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : regs 837 ≤ regs 833 + regs 834
  all_goals simp [ScalarChecks, interiorLocalTwoSecondPrefix, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hsub, bound, hw] <;> omega

theorem interiorGlobalTwoSecondPrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (ha : regs 864 ≤ 2 * metadataEnvelope shape.size) (hb : regs 865 ≤ metadataEnvelope shape.size) :
    interiorGlobalTwoSecondPrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have bound (r : Nat) : regs r < 2 ^ wordWidth shape.size := fit.1 r
  have he := interior_envelope_powers shape.size
  have cap := interior_polynomial_fit shape.size
  have small := interior_small_constants_fit shape.size
  have hw : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : regs 868 ≤ regs 864 + regs 865
  all_goals simp [ScalarChecks, interiorGlobalTwoSecondPrefix, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hsub, bound, hw] <;> omega

def InteriorLocalSpanSafety (shape : CartesianShape) (span : Block) : Prop :=
  ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) → MetadataMatches shape regs →
    regs 800 ≤ 3 * metadataEnvelope shape.size → regs 801 ≤ 3 * metadataEnvelope shape.size →
    regs 802 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size) →
    span.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩

def InteriorGlobalSpanSafety (shape : CartesianShape) (span : Block) : Prop :=
  ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) → MetadataMatches shape regs →
    regs 816 ≤ 3 * metadataEnvelope shape.size →
    regs 817 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size) →
    span.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩

theorem interiorLocalTwoSelectedProgram_safe (shape : CartesianShape) (span : Block)
    (ss : InteriorLocalSpanSafety shape span)
    (sr : ∀ regs, MetadataMatches shape regs →
      (span.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running)
    (sw : span.WritesOnly InteriorLocalSpanWrites)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hmcr : regs 832 ≤ 3 * metadataEnvelope shape.size)
    (hst : regs 833 ≤ metadataEnvelope shape.size) (hcnt : regs 834 ≤ metadataEnvelope shape.size)
    (hp : regs 708 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (interiorLocalTwoSelectedProgram span).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  unfold interiorLocalTwoSelectedProgram
  refine interior_follow_exact _ _ _ _ regs _ _
    (interiorLocalTwoFirstPrefix_safe shape regs fit hm)
    (interiorLocalTwoFirstPrefix_source (shapeMemory shape) regs) (fun firstFit => ?_)
  let first := interiorLocalTwoFirst regs
  have fm : MetadataMatches shape first := interior_metadata_frame shape regs first hm (by
    intro r hr hl
    simp [first, interiorLocalTwoFirst, Registers.write, show r ≠ 843 by omega,
      show r ≠ 844 by omega, show r ≠ 835 by omega, show r ≠ 836 by omega,
      show r ≠ 837 by omega, show r ≠ 800 by omega, show r ≠ 801 by omega, show r ≠ 802 by omega])
  have level : (regs 708 - 1) / regs 45 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size) :=
    Nat.le_trans (Nat.div_le_self _ _) (by omega)
  have fs := ss first firstFit fm (by simpa [first, interiorLocalTwoFirst, Registers.write] using hmcr)
    (by simp [first, interiorLocalTwoFirst, Registers.write]; omega)
    (by simpa [first, interiorLocalTwoFirst, Registers.write] using level)
  refine interior_call_then shape span _ InteriorLocalSpanWrites sw
    (by intro r hr hl; unfold InteriorLocalSpanWrites InteriorMinWrites; omega) first fm fs (sr first fm) ?_
  intro out ofit om frame
  refine interior_save_then shape 840 (by decide) _ out ofit om ?_
  intro saved savedFit sm saveFrame
  have keep (r : Nat) (hr : r = 832 ∨ r = 833 ∨ r = 834 ∨ r = 836) : saved r = first r := by
    rw [saveFrame r (by omega), frame r (by unfold InteriorLocalSpanWrites InteriorMinWrites; omega)]
  have start : saved 833 ≤ metadataEnvelope shape.size := by
    rw [keep 833 (by omega)]; simpa [first, interiorLocalTwoFirst, Registers.write] using hst
  have count : saved 834 ≤ metadataEnvelope shape.size := by
    rw [keep 834 (by omega)]; simpa [first, interiorLocalTwoFirst, Registers.write] using hcnt
  refine interior_follow_exact _ _ _ _ saved _ _
    (interiorLocalTwoSecondPrefix_safe shape saved savedFit start count)
    (interiorLocalTwoSecondPrefix_source (shapeMemory shape) saved) (fun secondFit => ?_)
  have secondMeta : MetadataMatches shape (interiorLocalTwoSecond saved) := interior_metadata_frame shape saved _ sm (by
    intro r hr hl
    simp [interiorLocalTwoSecond, Registers.write, show r ≠ 800 by omega,
      show r ≠ 801 by omega, show r ≠ 802 by omega, show r ≠ 844 by omega])
  have secondSafe := ss (interiorLocalTwoSecond saved) secondFit secondMeta
    (by simp [interiorLocalTwoSecond, Registers.write, keep 832 (by omega), first, interiorLocalTwoFirst]; exact hmcr)
    (by simp [interiorLocalTwoSecond, Registers.write]; omega)
    (by simpa [interiorLocalTwoSecond, Registers.write, keep 836 (by omega), first, interiorLocalTwoFirst] using level)
  exact Block.safe_seq secondSafe (interiorCandidateMerge_safe shape.size 840 _ _
    (span.eval_fits _ _ _ secondSafe))

theorem interiorGlobalTwoSelectedProgram_safe (shape : CartesianShape) (span : Block)
    (ss : InteriorGlobalSpanSafety shape span)
    (sr : ∀ regs, MetadataMatches shape regs →
      (span.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running)
    (sw : span.WritesOnly InteriorGlobalSpanWrites)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hst : regs 864 ≤ 2 * metadataEnvelope shape.size) (hcnt : regs 865 ≤ metadataEnvelope shape.size)
    (hp : regs 708 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (interiorGlobalTwoSelectedProgram span).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  unfold interiorGlobalTwoSelectedProgram
  refine interior_follow_exact _ _ _ _ regs _ _
    (interiorGlobalTwoFirstPrefix_safe shape regs fit hm)
    (interiorGlobalTwoFirstPrefix_source (shapeMemory shape) regs) (fun firstFit => ?_)
  let first := interiorGlobalTwoFirst regs
  have fm : MetadataMatches shape first := interior_metadata_frame shape regs first hm (by
    intro r hr hl
    simp [first, interiorGlobalTwoFirst, Registers.write, show r ≠ 875 by omega,
      show r ≠ 876 by omega, show r ≠ 866 by omega, show r ≠ 867 by omega,
      show r ≠ 868 by omega, show r ≠ 816 by omega, show r ≠ 817 by omega])
  have level : (regs 708 - 1) / regs 46 ≤ 32 * (metadataEnvelope shape.size * metadataEnvelope shape.size) :=
    Nat.le_trans (Nat.div_le_self _ _) (by omega)
  have fs := ss first firstFit fm (by simp [first, interiorGlobalTwoFirst, Registers.write]; omega)
    (by simpa [first, interiorGlobalTwoFirst, Registers.write] using level)
  refine interior_call_then shape span _ InteriorGlobalSpanWrites sw
    (by intro r hr hl; unfold InteriorGlobalSpanWrites InteriorMinWrites; omega) first fm fs (sr first fm) ?_
  intro out ofit om frame
  refine interior_save_then shape 872 (by decide) _ out ofit om ?_
  intro saved savedFit sm saveFrame
  have keep (r : Nat) (hr : r = 864 ∨ r = 865 ∨ r = 867) : saved r = first r := by
    rw [saveFrame r (by omega), frame r (by unfold InteriorGlobalSpanWrites InteriorMinWrites; omega)]
  have start : saved 864 ≤ 2 * metadataEnvelope shape.size := by
    rw [keep 864 (by omega)]; simpa [first, interiorGlobalTwoFirst, Registers.write] using hst
  have count : saved 865 ≤ metadataEnvelope shape.size := by
    rw [keep 865 (by omega)]; simpa [first, interiorGlobalTwoFirst, Registers.write] using hcnt
  refine interior_follow_exact _ _ _ _ saved _ _
    (interiorGlobalTwoSecondPrefix_safe shape saved savedFit start count)
    (interiorGlobalTwoSecondPrefix_source (shapeMemory shape) saved) (fun secondFit => ?_)
  have secondMeta : MetadataMatches shape (interiorGlobalTwoSecond saved) := interior_metadata_frame shape saved _ sm (by
    intro r hr hl
    simp [interiorGlobalTwoSecond, Registers.write, show r ≠ 816 by omega,
      show r ≠ 817 by omega, show r ≠ 876 by omega])
  have secondSafe := ss (interiorGlobalTwoSecond saved) secondFit secondMeta
    (by simp [interiorGlobalTwoSecond, Registers.write]; omega)
    (by simpa [interiorGlobalTwoSecond, Registers.write, keep 867 (by omega), first, interiorGlobalTwoFirst] using level)
  exact Block.safe_seq secondSafe (interiorCandidateMerge_safe shape.size 872 _ _
    (span.eval_fits _ _ _ secondSafe))

theorem interiorLocalTwoProgram_safe (shape : CartesianShape) (entry span : Block)
    (es : InteriorEntrySafety shape entry)
    (ec : InteriorEntrySpec shape (shapeMemory shape) entry)
    (ew : entry.WritesOnly InteriorReadWrites)
    (ss : InteriorLocalSpanSafety shape span)
    (sr : ∀ regs, MetadataMatches shape regs →
      (span.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running)
    (sw : span.WritesOnly InteriorLocalSpanWrites)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hmcr : regs 832 ≤ 3 * metadataEnvelope shape.size)
    (hst : regs 833 ≤ metadataEnvelope shape.size) (hcnt : regs 834 ≤ metadataEnvelope shape.size) :
    (interiorLocalTwoProgram entry span).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have firstSafe : interiorLocalTwoPrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
    apply SimpleScalar.safe _ _ _ _ _ fit
    simp [SimpleScalar, interiorLocalTwoPrefix, Block.sequence]
  unfold interiorLocalTwoProgram
  refine interior_follow_exact _ _ _ _ regs _ _ firstSafe
    (interiorLocalTwoPrefix_source (shapeMemory shape) regs) (fun preparedFit => ?_)
  have pm : MetadataMatches shape (interiorLocalTwoPrepared regs) := interior_metadata_frame shape regs _ hm (by
    intro r hr hl
    simp [interiorLocalTwoPrepared, Registers.write, show r ≠ 704 by omega,
      show r ≠ 705 by omega, show r ≠ 706 by omega, show r ≠ 707 by omega])
  have hc : regs 45 = packedReviewerInteriorEntryCount shape.size .localLevel := hm 29 (by decide)
  have hw : regs 47 = packedReviewerInteriorEntryWidth shape.size .localLevel := hm 31 (by decide)
  have hb : regs 55 = packedReviewerInteriorComponentWordPrefix shape.size .localLevel := hm 39 (by decide)
  refine interior_entry_then shape entry _ es ec ew .localLevel _ preparedFit pm
    (by simpa [interiorLocalTwoPrepared, Registers.write] using hc)
    (by simpa [interiorLocalTwoPrepared, Registers.write] using hw)
    (by simpa [interiorLocalTwoPrepared, Registers.write] using hb) ?_
  intro out ofit om packet frame
  apply Block.safe_ifZero ofit
  split
  · exact interiorCandidateNone_safe shape.size _ _ ofit
  · apply interiorLocalTwoSelectedProgram_safe shape span ss sr sw out ofit om
    · rw [frame 832 (by simp [InteriorReadWrites])]
      simpa [interiorLocalTwoPrepared, Registers.write] using hmcr
    · rw [frame 833 (by simp [InteriorReadWrites])]
      simpa [interiorLocalTwoPrepared, Registers.write] using hst
    · rw [frame 834 (by simp [InteriorReadWrites])]
      simpa [interiorLocalTwoPrepared, Registers.write] using hcnt
    · exact packet

theorem interiorGlobalTwoProgram_safe (shape : CartesianShape) (entry span : Block)
    (es : InteriorEntrySafety shape entry)
    (ec : InteriorEntrySpec shape (shapeMemory shape) entry)
    (ew : entry.WritesOnly InteriorReadWrites)
    (ss : InteriorGlobalSpanSafety shape span)
    (sr : ∀ regs, MetadataMatches shape regs →
      (span.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running)
    (sw : span.WritesOnly InteriorGlobalSpanWrites)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hst : regs 864 ≤ 2 * metadataEnvelope shape.size) (hcnt : regs 865 ≤ metadataEnvelope shape.size) :
    (interiorGlobalTwoProgram entry span).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have firstSafe : interiorGlobalTwoPrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
    apply SimpleScalar.safe _ _ _ _ _ fit
    simp [SimpleScalar, interiorGlobalTwoPrefix, Block.sequence]
  unfold interiorGlobalTwoProgram
  refine interior_follow_exact _ _ _ _ regs _ _ firstSafe
    (interiorGlobalTwoPrefix_source (shapeMemory shape) regs) (fun preparedFit => ?_)
  have pm : MetadataMatches shape (interiorGlobalTwoPrepared regs) := interior_metadata_frame shape regs _ hm (by
    intro r hr hl
    simp [interiorGlobalTwoPrepared, Registers.write, show r ≠ 704 by omega,
      show r ≠ 705 by omega, show r ≠ 706 by omega, show r ≠ 707 by omega])
  have hc : regs 46 = packedReviewerInteriorEntryCount shape.size .globalLevel := hm 30 (by decide)
  have hw : regs 48 = packedReviewerInteriorEntryWidth shape.size .globalLevel := hm 32 (by decide)
  have hb : regs 56 = packedReviewerInteriorComponentWordPrefix shape.size .globalLevel := hm 40 (by decide)
  refine interior_entry_then shape entry _ es ec ew .globalLevel _ preparedFit pm
    (by simpa [interiorGlobalTwoPrepared, Registers.write] using hc)
    (by simpa [interiorGlobalTwoPrepared, Registers.write] using hw)
    (by simpa [interiorGlobalTwoPrepared, Registers.write] using hb) ?_
  intro out ofit om packet frame
  apply Block.safe_ifZero ofit
  split
  · exact interiorCandidateNone_safe shape.size _ _ ofit
  · apply interiorGlobalTwoSelectedProgram_safe shape span ss sr sw out ofit om
    · rw [frame 864 (by simp [InteriorReadWrites])]
      simpa [interiorGlobalTwoPrepared, Registers.write] using hst
    · rw [frame 865 (by simp [InteriorReadWrites])]
      simpa [interiorGlobalTwoPrepared, Registers.write] using hcnt
    · exact packet

theorem interiorLocalTwoBlock_canonical_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hmcr : regs 832 ≤ 3 * metadataEnvelope shape.size)
    (hst : regs 833 ≤ metadataEnvelope shape.size) (hcnt : regs 834 ≤ metadataEnvelope shape.size) :
    (interiorLocalTwoBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ :=
  interiorLocalTwoProgram_safe shape _ _ (interiorReadBlock_entrySafety shape)
    (interiorReadBlock_spec shape _ _ (logicalReadBlock_correct shape) logicalReadBlock_writesOnly)
    (interiorReadBlock_writes _ logicalReadBlock_writesOnly) (interiorLocalSpanBlock_canonical_safe shape)
    (fun regs hm => (interiorLocalSpanBlock_source shape _ _ (logicalReadBlock_correct shape)
      logicalReadBlock_writesOnly regs hm).1)
    (interiorLocalSpanBlock_writes _ logicalReadBlock_writesOnly) regs fit hm hmcr hst hcnt

theorem interiorGlobalTwoBlock_canonical_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hst : regs 864 ≤ 2 * metadataEnvelope shape.size) (hcnt : regs 865 ≤ metadataEnvelope shape.size) :
    (interiorGlobalTwoBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ :=
  interiorGlobalTwoProgram_safe shape _ _ (interiorReadBlock_entrySafety shape)
    (interiorReadBlock_spec shape _ _ (logicalReadBlock_correct shape) logicalReadBlock_writesOnly)
    (interiorReadBlock_writes _ logicalReadBlock_writesOnly) (interiorGlobalSpanBlock_canonical_safe shape)
    (fun regs hm => (interiorGlobalSpanBlock_source shape _ _ (logicalReadBlock_correct shape)
      logicalReadBlock_writesOnly regs hm).1)
    (interiorGlobalSpanBlock_writes _ logicalReadBlock_writesOnly) regs fit hm hst hcnt

theorem interiorRangePrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    interiorRangePrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have pos := (interior_geometry_positive shape regs hm).2.1
  have bound (r : Nat) : regs r < 2 ^ wordWidth shape.size := fit.1 r
  have inputFit := bound 896
  have macroFit := bound 38
  have hd := Nat.div_le_self (regs 896) (regs 38)
  have hmod := Nat.mod_lt (regs 896) pos
  have hsub : regs 896 % regs 38 ≤ regs 38 := by omega
  have small := interior_small_constants_fit shape.size
  have hw : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, interiorRangePrefix, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hsub, hw]
  split <;> omega

theorem interiorRangeCrossPrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    interiorRangeCrossPrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have pos := (interior_geometry_positive shape regs hm).2.1
  have bound (r : Nat) : regs r < 2 ^ wordWidth shape.size := fit.1 r
  have inputFit := bound 897
  have hd := Nat.div_le_self (regs 897 - regs 900) (regs 38)
  have hmod := Nat.mod_le (regs 897 - regs 900) (regs 38)
  have small := interior_small_constants_fit shape.size
  have hw : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : regs 900 ≤ regs 897
  all_goals simp [ScalarChecks, interiorRangeCrossPrefix, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hsub, bound, hw] <;> omega

structure InteriorRangeTailBounds (shape : CartesianShape) (regs : Registers) : Prop where
  first : regs 898 ≤ metadataEnvelope shape.size
  middle : regs 902 ≤ metadataEnvelope shape.size
  trailing : regs 903 ≤ metadataEnvelope shape.size
  one : regs 911 = 1

private theorem InteriorRangeTailBounds.frame (shape : CartesianShape) (before after : Registers)
    (hb : InteriorRangeTailBounds shape before)
    (frame : ∀ r, 898 ≤ r → r ≤ 911 → after r = before r) :
    InteriorRangeTailBounds shape after := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [frame 898 (by decide) (by decide)]; exact hb.first
  · rw [frame 902 (by decide) (by decide)]; exact hb.middle
  · rw [frame 903 (by decide) (by decide)]; exact hb.trailing
  · rw [frame 911 (by decide) (by decide)]; exact hb.one

theorem interiorRangeAdjacentPrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hb : InteriorRangeTailBounds shape regs) :
    interiorRangeAdjacentPrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have bound (r : Nat) : regs r < 2 ^ wordWidth shape.size := fit.1 r
  have he := interior_envelope_powers shape.size
  have cap := interior_polynomial_fit shape.size
  have pos := metadataEnvelope_pos shape.size
  have first := hb.first
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, interiorRangeAdjacentPrefix, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, bound, hb.one]
  omega

theorem interiorRangeMiddlePrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hb : InteriorRangeTailBounds shape regs) :
    interiorRangeMiddlePrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have bound (r : Nat) : regs r < 2 ^ wordWidth shape.size := fit.1 r
  have he := interior_envelope_powers shape.size
  have cap := interior_polynomial_fit shape.size
  have pos := metadataEnvelope_pos shape.size
  have first := hb.first
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, interiorRangeMiddlePrefix, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, bound, hb.one]
  omega

theorem interiorRangeTrailingPrefix_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hb : InteriorRangeTailBounds shape regs) :
    interiorRangeTrailingPrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have bound (r : Nat) : regs r < 2 ^ wordWidth shape.size := fit.1 r
  have he := interior_envelope_powers shape.size
  have cap := interior_polynomial_fit shape.size
  have pos := metadataEnvelope_pos shape.size
  have first := hb.first
  have middle := hb.middle
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, interiorRangeTrailingPrefix, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, bound, hb.one]
  omega

def InteriorLocalTwoSafety (shape : CartesianShape) (localTwo : Block) : Prop :=
  ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) → MetadataMatches shape regs →
    regs 832 ≤ 3 * metadataEnvelope shape.size → regs 833 ≤ metadataEnvelope shape.size →
    regs 834 ≤ metadataEnvelope shape.size →
    localTwo.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩

def InteriorGlobalTwoSafety (shape : CartesianShape) (globalTwo : Block) : Prop :=
  ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) → MetadataMatches shape regs →
    regs 864 ≤ 2 * metadataEnvelope shape.size → regs 865 ≤ metadataEnvelope shape.size →
    globalTwo.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩

private theorem interiorRangeAdjacent_safe (shape : CartesianShape) (localTwo : Block)
    (ls : InteriorLocalTwoSafety shape localTwo) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hb : InteriorRangeTailBounds shape regs) :
    (Block.seq interiorRangeAdjacentPrefix (.seq localTwo (candidateMergeLeftBlock 904))).Safe
      (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  refine interior_follow_exact _ _ _ _ regs _ _ (interiorRangeAdjacentPrefix_safe shape regs fit hb)
    (interiorRangeAdjacentPrefix_source (shapeMemory shape) regs) (fun preparedFit => ?_)
  have pm : MetadataMatches shape (interiorRangeAdjacentPrepared regs) := interior_metadata_frame shape regs _ hm (by
    intro r hr hl
    simp [interiorRangeAdjacentPrepared, Registers.write, show r ≠ 832 by omega,
      show r ≠ 833 by omega, show r ≠ 834 by omega])
  have hfirst := hb.first
  have pos := metadataEnvelope_pos shape.size
  have safe := ls _ preparedFit pm
    (by simp [interiorRangeAdjacentPrepared, Registers.write, hb.one]; omega)
    (by simp [interiorRangeAdjacentPrepared, Registers.write])
    (by simpa [interiorRangeAdjacentPrepared, Registers.write] using hb.trailing)
  exact Block.safe_seq safe (interiorCandidateMerge_safe shape.size 904 _ _ (localTwo.eval_fits _ _ _ safe))

private theorem interiorRangeTrailing_safe (shape : CartesianShape) (localTwo : Block)
    (ls : InteriorLocalTwoSafety shape localTwo) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hb : InteriorRangeTailBounds shape regs) :
    (interiorRangeTrailingProgram localTwo).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  unfold interiorRangeTrailingProgram
  refine interior_save_then shape 907 (by decide) _ regs fit hm ?_
  intro out ofit om frame
  have ob : InteriorRangeTailBounds shape out := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [frame 898 (by omega)]; exact hb.first
    · rw [frame 902 (by omega)]; exact hb.middle
    · rw [frame 903 (by omega)]; exact hb.trailing
    · rw [frame 911 (by omega)]; exact hb.one
  refine interior_follow_exact _ _ _ _ out _ _ (interiorRangeTrailingPrefix_safe shape out ofit ob)
    (interiorRangeTrailingPrefix_source (shapeMemory shape) out) (fun preparedFit => ?_)
  have pm : MetadataMatches shape (interiorRangeTrailingPrepared out) := interior_metadata_frame shape out _ om (by
    intro r hr hl
    simp [interiorRangeTrailingPrepared, Registers.write, show r ≠ 832 by omega,
      show r ≠ 833 by omega, show r ≠ 834 by omega])
  have hfirst := ob.first
  have hmiddle := ob.middle
  have pos := metadataEnvelope_pos shape.size
  have safe := ls _ preparedFit pm
    (by simp [interiorRangeTrailingPrepared, Registers.write, ob.one]; omega)
    (by simp [interiorRangeTrailingPrepared, Registers.write])
    (by simpa [interiorRangeTrailingPrepared, Registers.write] using ob.trailing)
  exact Block.safe_seq safe (interiorCandidateMerge_safe shape.size 907 _ _ (localTwo.eval_fits _ _ _ safe))

private theorem interiorRangeMiddleStage_safe (shape : CartesianShape) (globalTwo : Block)
    (gs : InteriorGlobalTwoSafety shape globalTwo) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hb : InteriorRangeTailBounds shape regs) :
    (interiorRangeMiddleStageProgram globalTwo).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  unfold interiorRangeMiddleStageProgram
  refine interior_follow_exact _ _ _ _ regs _ _ (interiorRangeMiddlePrefix_safe shape regs fit hb)
    (interiorRangeMiddlePrefix_source (shapeMemory shape) regs) (fun preparedFit => ?_)
  have pm : MetadataMatches shape (interiorRangeMiddlePrepared regs) := interior_metadata_frame shape regs _ hm (by
    intro r hr hl
    simp [interiorRangeMiddlePrepared, Registers.write, show r ≠ 864 by omega, show r ≠ 865 by omega])
  have first := hb.first
  have pos := metadataEnvelope_pos shape.size
  have safe := gs _ preparedFit pm
    (by simp [interiorRangeMiddlePrepared, Registers.write, hb.one]; omega)
    (by simpa [interiorRangeMiddlePrepared, Registers.write] using hb.middle)
  exact Block.safe_seq safe (interiorCandidateMerge_safe shape.size 904 _ _ (globalTwo.eval_fits _ _ _ safe))

private theorem interiorRangeMiddleStage_running (shape : CartesianShape) (globalTwo : Block)
    (gr : ∀ regs, MetadataMatches shape regs →
      (globalTwo.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    ((interiorRangeMiddleStageProgram globalTwo).eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running := by
  have pm : MetadataMatches shape (interiorRangeMiddlePrepared regs) := interior_metadata_frame shape regs _ hm (by
    intro r hr hl
    simp [interiorRangeMiddlePrepared, Registers.write, show r ≠ 864 by omega, show r ≠ 865 by omega])
  have running := gr (interiorRangeMiddlePrepared regs) pm
  rw [interiorRangeMiddleStageProgram, Block.eval_seq,
    interiorRangeMiddlePrefix_source, Evaluation.bind]
  simp only [Block.eval_seq, Evaluation.bind]
  generalize he : globalTwo.eval (shapeMemory shape) ⟨interiorRangeMiddlePrepared regs, .running⟩ = actual at running ⊢
  rcases actual with ⟨⟨out, status⟩, receipts⟩
  dsimp only at running
  subst status
  exact (candidateMergeLeftBlock_source 904 (by decide) (shapeMemory shape) out).1

private theorem interiorRangeMiddleStage_writes (globalTwo : Block)
    (gw : globalTwo.WritesOnly InteriorGlobalTwoWrites) :
    (interiorRangeMiddleStageProgram globalTwo).WritesOnly
      (fun r => InteriorGlobalTwoWrites r ∨ r = 864 ∨ r = 865) := by
  have globalWrites : globalTwo.WritesOnly
      (fun r => InteriorGlobalTwoWrites r ∨ r = 864 ∨ r = 865) :=
    Block.WritesOnly.mono globalTwo gw (fun _ h => Or.inl h)
  have mergeWrites := Block.WritesOnly.mono (candidateMergeLeftBlock 904)
    (candidateMergeLeftBlock_writesOnly 904)
    (show ∀ r, 7000 ≤ r ∧ r < 7004 → InteriorGlobalTwoWrites r ∨ r = 864 ∨ r = 865 from by
      intro r hr
      left
      unfold InteriorGlobalTwoWrites InteriorGlobalSpanWrites InteriorMinWrites
      omega)
  simp [interiorRangeMiddleStageProgram, interiorRangeMiddlePrefix, Block.sequence,
    Block.WritesOnly, Action.destination, globalWrites, mergeWrites]

private theorem interiorRangeMiddle_safe (shape : CartesianShape) (localTwo globalTwo : Block)
    (ls : InteriorLocalTwoSafety shape localTwo) (gs : InteriorGlobalTwoSafety shape globalTwo)
    (gr : ∀ regs, MetadataMatches shape regs →
      (globalTwo.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running)
    (gw : globalTwo.WritesOnly InteriorGlobalTwoWrites)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hb : InteriorRangeTailBounds shape regs) :
    (interiorRangeMiddleProgram localTwo globalTwo).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  unfold interiorRangeMiddleProgram
  refine interior_call_then shape _ _ (fun r => InteriorGlobalTwoWrites r ∨ r = 864 ∨ r = 865)
    (interiorRangeMiddleStage_writes globalTwo gw)
    (by intro r hr hl; unfold InteriorGlobalTwoWrites InteriorGlobalSpanWrites InteriorMinWrites; omega)
    regs hm (interiorRangeMiddleStage_safe shape globalTwo gs regs fit hm hb)
    (interiorRangeMiddleStage_running shape globalTwo gr regs hm) ?_
  intro out ofit om frame
  have ob := InteriorRangeTailBounds.frame shape regs out hb (by
    intro r hr hl
    exact frame r (by unfold InteriorGlobalTwoWrites InteriorGlobalSpanWrites InteriorMinWrites; omega))
  apply Block.safe_ifZero ofit
  split
  · exact Block.safe_skip _ _ _ ofit
  · exact interiorRangeTrailing_safe shape localTwo ls out ofit om ob

theorem interiorRangeCrossProgram_safe (shape : CartesianShape) (localTwo globalTwo : Block)
    (ls : InteriorLocalTwoSafety shape localTwo) (gs : InteriorGlobalTwoSafety shape globalTwo)
    (lr : ∀ regs, MetadataMatches shape regs →
      (localTwo.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running)
    (gr : ∀ regs, MetadataMatches shape regs →
      (globalTwo.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running)
    (lw : localTwo.WritesOnly InteriorLocalTwoWrites) (gw : globalTwo.WritesOnly InteriorGlobalTwoWrites)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hcount : regs 897 ≤ metadataEnvelope shape.size)
    (hfirst : regs 898 ≤ metadataEnvelope shape.size) (hstart : regs 899 ≤ metadataEnvelope shape.size)
    (hleft : regs 900 ≤ metadataEnvelope shape.size) (hone : regs 911 = 1) :
    (interiorRangeCrossProgram localTwo globalTwo).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  unfold interiorRangeCrossProgram
  refine interior_follow_exact _ _ _ _ regs _ _ (interiorRangeCrossPrefix_safe shape regs fit hm)
    (interiorRangeCrossPrefix_source (shapeMemory shape) regs) (fun preparedFit => ?_)
  let prepared := interiorRangeCrossPrepared regs
  have pm : MetadataMatches shape prepared := interior_metadata_frame shape regs _ hm (by
    intro r hr hl
    simp [prepared, interiorRangeCrossPrepared, Registers.write, show r ≠ 910 by omega,
      show r ≠ 901 by omega, show r ≠ 902 by omega, show r ≠ 903 by omega,
      show r ≠ 832 by omega, show r ≠ 833 by omega, show r ≠ 834 by omega])
  have pb : InteriorRangeTailBounds shape prepared := by
    have hd := Nat.div_le_self (regs 897 - regs 900) (regs 38)
    have hmod := Nat.mod_le (regs 897 - regs 900) (regs 38)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [prepared, interiorRangeCrossPrepared, Registers.write] using hfirst
    · simp [prepared, interiorRangeCrossPrepared, Registers.write]; omega
    · simp [prepared, interiorRangeCrossPrepared, Registers.write]; omega
    · simpa [prepared, interiorRangeCrossPrepared, Registers.write] using hone
  have localSafe := ls prepared preparedFit pm
    (by simp [prepared, interiorRangeCrossPrepared, Registers.write]; omega)
    (by simpa [prepared, interiorRangeCrossPrepared, Registers.write] using hstart)
    (by simpa [prepared, interiorRangeCrossPrepared, Registers.write] using hleft)
  refine interior_call_then shape localTwo _ InteriorLocalTwoWrites lw
    (by intro r hr hl; unfold InteriorLocalTwoWrites InteriorLocalSpanWrites InteriorMinWrites; omega)
    prepared pm localSafe (lr prepared pm) ?_
  intro out ofit om frame
  have ob := InteriorRangeTailBounds.frame shape prepared out pb (by
    intro r hr hl
    exact frame r (by unfold InteriorLocalTwoWrites InteriorLocalSpanWrites InteriorMinWrites; omega))
  refine interior_save_then shape 904 (by decide) _ out ofit om ?_
  intro saved savedFit sm saveFrame
  have sb : InteriorRangeTailBounds shape saved := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [saveFrame 898 (by omega)]; exact ob.first
    · rw [saveFrame 902 (by omega)]; exact ob.middle
    · rw [saveFrame 903 (by omega)]; exact ob.trailing
    · rw [saveFrame 911 (by omega)]; exact ob.one
  unfold interiorRangeBranchProgram
  apply Block.safe_ifZero savedFit
  split
  · exact interiorRangeAdjacent_safe shape localTwo ls saved savedFit sm sb
  · exact interiorRangeMiddle_safe shape localTwo globalTwo ls gs gr gw saved savedFit sm sb

def InteriorCrossSafety (shape : CartesianShape) (cross : Block) : Prop :=
  ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) → MetadataMatches shape regs →
    regs 897 ≤ metadataEnvelope shape.size → regs 898 ≤ metadataEnvelope shape.size →
    regs 899 ≤ metadataEnvelope shape.size → regs 900 ≤ metadataEnvelope shape.size → regs 911 = 1 →
    cross.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩

theorem interiorRangeProgram_safe (shape : CartesianShape) (localTwo cross : Block)
    (ls : InteriorLocalTwoSafety shape localTwo) (cs : InteriorCrossSafety shape cross)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hstart : regs 896 ≤ metadataEnvelope shape.size)
    (hcount : regs 897 ≤ metadataEnvelope shape.size) :
    (interiorRangeProgram localTwo cross).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  unfold interiorRangeProgram
  apply Block.safe_ifZero fit
  split
  · exact interiorCandidateNone_safe shape.size _ _ fit
  · refine interior_follow_exact _ _ _ _ regs _ _ (interiorRangePrefix_safe shape regs fit hm)
      (interiorRangePrefix_source (shapeMemory shape) regs) (fun preparedFit => ?_)
    let prepared := interiorRangePrepared regs
    have pm : MetadataMatches shape prepared := interior_metadata_frame shape regs _ hm (by
      intro r hr hl
      simp [prepared, interiorRangePrepared, Registers.write, show r ≠ 911 by omega,
        show r ≠ 898 by omega, show r ≠ 899 by omega, show r ≠ 900 by omega, show r ≠ 910 by omega])
    have hd := Nat.div_le_self (regs 896) (regs 38)
    have hmod := Nat.mod_le (regs 896) (regs 38)
    have h38 := MetadataMatches.envelope shape regs hm 38 (by decide)
    apply Block.safe_ifZero preparedFit
    split
    · apply cs prepared preparedFit pm
      · simpa [prepared, interiorRangePrepared, Registers.write] using hcount
      · simp [prepared, interiorRangePrepared, Registers.write]; omega
      · simp [prepared, interiorRangePrepared, Registers.write]; omega
      · simp [prepared, interiorRangePrepared, Registers.write]; omega
      · simp [prepared, interiorRangePrepared, Registers.write]
    · have singleSafe : interiorRangeSinglePrefix.Safe (shapeMemory shape) (wordWidth shape.size) ⟨prepared, .running⟩ := by
        apply SimpleScalar.safe _ _ _ _ _ preparedFit
        simp [SimpleScalar, interiorRangeSinglePrefix, Block.sequence]
      refine interior_follow_exact _ _ _ _ prepared _ _ singleSafe
        (interiorRangeSinglePrefix_source (shapeMemory shape) prepared) (fun singleFit => ?_)
      apply ls _ singleFit
      · exact interior_metadata_frame shape prepared _ pm (by
          intro r hr hl
          simp [interiorRangeSinglePrepared, Registers.write, show r ≠ 832 by omega,
            show r ≠ 833 by omega, show r ≠ 834 by omega])
      · simp [interiorRangeSinglePrepared, prepared, interiorRangePrepared, Registers.write]; omega
      · simp [interiorRangeSinglePrepared, prepared, interiorRangePrepared, Registers.write]; omega
      · simpa [interiorRangeSinglePrepared, prepared, interiorRangePrepared, Registers.write] using hcount

theorem interiorRangeCrossBlock_canonical_safe (shape : CartesianShape) :
    InteriorCrossSafety shape (interiorRangeCrossBlock logicalReadBlock) :=
  interiorRangeCrossProgram_safe shape _ _ (interiorLocalTwoBlock_canonical_safe shape)
    (interiorGlobalTwoBlock_canonical_safe shape)
    (fun regs hm => (interiorLocalTwoBlock_source shape _ _ (logicalReadBlock_correct shape)
      logicalReadBlock_writesOnly regs hm).1)
    (fun regs hm => (interiorGlobalTwoBlock_source shape _ _ (logicalReadBlock_correct shape)
      logicalReadBlock_writesOnly regs hm).1)
    (interiorLocalTwoBlock_writes _ logicalReadBlock_writesOnly)
    (interiorGlobalTwoBlock_writes _ logicalReadBlock_writesOnly)

theorem interiorRangeBlock_canonical_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hstart : regs 896 ≤ metadataEnvelope shape.size)
    (hcount : regs 897 ≤ metadataEnvelope shape.size) :
    (interiorRangeBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ :=
  interiorRangeProgram_safe shape _ _ (interiorLocalTwoBlock_canonical_safe shape)
    (interiorRangeCrossBlock_canonical_safe shape) regs fit hm hstart hcount

private theorem interior_entries_of_refinement (shape : CartesianShape)
    {entries : List Nat} {width : Nat} (table : FixedWidthNatTable entries width)
    (base index : Nat)
    (href : ((canonicalRelativeRmmMachineReadNatComputation shape table base index).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
        canonicalRelativeRmmMachineReadNatCosted shape table index) :
    ((packedInteriorReadNatOf shape.size entries.length width base index).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)).value = entries[index]? := by
  have hstore : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20 =
      (canonicalRelativeRmmInteriorComponentStore shape).store.words := by
    funext address
    simpa using concreteBPNativeSuccinctRMQGlobalReadStore_canonicalComponent shape address
  have hv := congrArg Costed.erase href
  simp only [FlatStoreExecution.toCosted_erase, canonicalRelativeRmmMachineReadNatCosted_erase,
    packedInteriorReadNatOf_eq, FixedWidthNatTable.readCosted_erase] at hv
  rw [hstore, hv]

theorem interior_local_level_read (shape : CartesianShape) (index : Nat) :
    ((packedInteriorReadNatOf shape.size
      (packedReviewerInteriorEntryCount shape.size .localLevel)
      (packedReviewerInteriorEntryWidth shape.size .localLevel)
      (packedReviewerInteriorComponentWordPrefix shape.size .localLevel) index).run
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)).value =
      (bpSparseLevelEntries (bpSparseLevelDomain (packedInteriorLayout shape.size).macroSize))[index]? := by
  have h := interior_entries_of_refinement shape (canonicalRelativeRmmInteriorLocalLevelTable shape).table
    _ index (canonicalRelativeRmmLocalLevelReadComputation_refines shape index)
  simpa only [packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
    packedReviewerInteriorComponentWordPrefix, bpSparseLevelEntries_length,
    packedInteriorLayout_eq, packedInteriorOffsets_eq] using h

theorem interior_global_level_read (shape : CartesianShape) (index : Nat) :
    ((packedInteriorReadNatOf shape.size
      (packedReviewerInteriorEntryCount shape.size .globalLevel)
      (packedReviewerInteriorEntryWidth shape.size .globalLevel)
      (packedReviewerInteriorComponentWordPrefix shape.size .globalLevel) index).run
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)).value =
      (bpSparseLevelEntries (bpSparseLevelDomain (packedInteriorLayout shape.size).macroSampleCount))[index]? := by
  have h := interior_entries_of_refinement shape (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
    _ index (canonicalRelativeRmmGlobalLevelReadComputation_refines shape index)
  simpa only [packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
    packedReviewerInteriorComponentWordPrefix, bpSparseLevelEntries_length,
    packedInteriorLayout_eq, packedInteriorOffsets_eq] using h

theorem interior_level_value_bounds (n domain index value : Nat)
    (hpos : 2 ≤ domain) (hbound : domain ≤ metadataEnvelope n)
    (read : (bpSparseLevelEntries domain)[index]? = some value) :
    index < domain ∧ value / domain = Nat.log2 index ∧
      value % domain = bpSparseLogSpan index ∧ value / domain < wordWidth n := by
  have hi : index < domain := by
    simpa only [bpSparseLevelEntries_length] using (List.getElem?_eq_some_iff.mp read).1
  have hv : bpSparseLevelCell domain index = value := by
    rw [bpSparseLevelEntries_getElem? hi] at read
    exact Option.some.inj read
  subst value
  have hd := bpSparseLevelCell_div hpos hi
  have hm := bpSparseLevelCell_mod hpos hi
  refine ⟨hi, hd, hm, ?_⟩
  rw [hd]
  have hf := Nat.lt_of_le_of_lt hbound (metadataEnvelope_lt_wordCapacity n)
  have hl : Nat.log2 domain < wordWidth n := (Nat.log2_lt (by omega)).mpr hf
  have mono := SuccinctRank.machineWordBits_mono_le (Nat.le_of_lt hi)
  unfold SuccinctRank.machineWordBits at mono
  omega

theorem interior_local_level_exponent (shape : CartesianShape) (index value : Nat)
    (read : ((packedInteriorReadNatOf shape.size
      (packedReviewerInteriorEntryCount shape.size .localLevel)
      (packedReviewerInteriorEntryWidth shape.size .localLevel)
      (packedReviewerInteriorComponentWordPrefix shape.size .localLevel) index).run
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)).value = some value) :
    let domain := bpSparseLevelDomain (packedInteriorLayout shape.size).macroSize
    index < domain ∧ value / domain = Nat.log2 index ∧
      value % domain = bpSparseLogSpan index ∧ value / domain < wordWidth shape.size := by
  rw [interior_local_level_read] at read
  exact interior_level_value_bounds shape.size _ index value
    (by unfold bpSparseLevelDomain; omega) (interior_canonical_count_bound shape .localLevel) read

theorem interior_global_level_exponent (shape : CartesianShape) (index value : Nat)
    (read : ((packedInteriorReadNatOf shape.size
      (packedReviewerInteriorEntryCount shape.size .globalLevel)
      (packedReviewerInteriorEntryWidth shape.size .globalLevel)
      (packedReviewerInteriorComponentWordPrefix shape.size .globalLevel) index).run
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)).value = some value) :
    let domain := bpSparseLevelDomain (packedInteriorLayout shape.size).macroSampleCount
    index < domain ∧ value / domain = Nat.log2 index ∧
      value % domain = bpSparseLogSpan index ∧ value / domain < wordWidth shape.size := by
  rw [interior_global_level_read] at read
  exact interior_level_value_bounds shape.size _ index value
    (by unfold bpSparseLevelDomain; omega) (interior_canonical_count_bound shape .globalLevel) read

set_option maxRecDepth 30000 in
theorem interiorRangeBlock_maxEncodedField :
    (interiorRangeBlock logicalReadBlock).maxEncodedField = 8270 := by rfl

set_option maxRecDepth 30000 in
theorem interiorReadBlock_maxEncodedField :
    (interiorReadBlock logicalReadBlock).maxEncodedField = 8270 := by rfl

theorem interiorRangeBlock_fieldsFit (n : Nat) :
    (interiorRangeBlock logicalReadBlock).FieldsFit (wordWidth n) := by
  apply Block.fieldsFit_of_maxEncodedField
  rw [interiorRangeBlock_maxEncodedField]
  have h := interior_small_constants_fit n
  omega

theorem interiorReadBlock_fieldsFit (n : Nat) :
    (interiorReadBlock logicalReadBlock).FieldsFit (wordWidth n) := by
  apply Block.fieldsFit_of_maxEncodedField
  rw [interiorReadBlock_maxEncodedField]
  have h := interior_small_constants_fit n
  omega

theorem interiorRangeBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hstart : regs 896 ≤ metadataEnvelope shape.size)
    (hcount : regs 897 ≤ metadataEnvelope shape.size) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((interiorRangeBlock logicalReadBlock).compileAt 0 ++ [.halt 7000]) 479411 ⟨regs, 0, .running⟩ := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth shape.size by unfold wordWidth; omega)
  apply rank_compiled_safety (shapeMemory shape) (wordWidth shape.size)
    (interiorRangeBlock logicalReadBlock) 7000 479411 regs
    (by simp only [interiorRangeBlock_size, logicalReadBlock_size, locateBlock_size])
    (by omega) (interiorRangeBlock_fieldsFit shape.size)
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega) fit
  exact interiorRangeBlock_canonical_safe shape regs fit hm hstart hcount

theorem interiorReadBlock_execution_safe (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hc : regs 704 = packedReviewerInteriorEntryCount shape.size component)
    (hw : regs 705 = packedReviewerInteriorEntryWidth shape.size component)
    (hb : regs 706 = packedReviewerInteriorComponentWordPrefix shape.size component) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((interiorReadBlock logicalReadBlock).compileAt 0 ++ [.halt 708]) 8698 ⟨regs, 0, .running⟩ := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth shape.size by unfold wordWidth; omega)
  apply rank_compiled_safety (shapeMemory shape) (wordWidth shape.size)
    (interiorReadBlock logicalReadBlock) 708 8698 regs
    (by simp only [interiorReadBlock_size, logicalReadBlock_size, locateBlock_size])
    (by omega) (interiorReadBlock_fieldsFit shape.size)
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega) fit
  exact interiorReadBlock_canonical_safe shape component regs fit hm hc hw hb

theorem interiorRangeBlock_safe_machine (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hstart : regs 896 ≤ metadataEnvelope shape.size)
    (hcount : regs 897 ≤ metadataEnvelope shape.size) :
    let expected := packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 896) (regs 897)
    let source := (interiorRangeBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩
    let program := (interiorRangeBlock logicalReadBlock).compileAt 0 ++ [.halt 7000]
    let actual := run (shapeMemory shape) program 479411 ⟨regs, 0, .running⟩
    actual.result = some (source.final.regs 7000) ∧
      actual.final.status = .halted (source.final.regs 7000) ∧
      actual.final.regs 7000 = source.final.regs 7000 ∧
      actual.final.regs 7001 = source.final.regs 7001 ∧
      actual.final.regs 7002 = source.final.regs 7002 ∧
      candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
      actual.steps ≤ 479411 ∧
      (∀ r, ¬ InteriorRangeWrites r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace ∧
      source.final.Fits (wordWidth shape.size) ∧
      RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program 479411 ⟨regs, 0, .running⟩ := by
  have semantics := interiorRangeBlock_canonical_machine shape regs hm
  have safe := interiorRangeBlock_canonical_safe shape regs fit hm hstart hcount
  exact ⟨semantics.1, semantics.2.1, semantics.2.2.1, semantics.2.2.2.1,
    semantics.2.2.2.2.1, semantics.2.2.2.2.2.1, semantics.2.2.2.2.2.2.1,
    semantics.2.2.2.2.2.2.2.1, semantics.2.2.2.2.2.2.2.2.1,
    semantics.2.2.2.2.2.2.2.2.2, (interiorRangeBlock logicalReadBlock).eval_fits _ _ _ safe,
    interiorRangeBlock_execution_safe shape regs fit hm hstart hcount⟩

theorem interiorRangeBlock_sameAllocation_safety (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hstart : regs 896 ≤ metadataEnvelope shape.size)
    (hcount : regs 897 ≤ metadataEnvelope shape.size) :
    (shapeMemory shape).length * wordWidth shape.size ≤ 2 * shape.size + allocationRho shape.size ∧
    wordWidth shape.size ≤ 192 * (Nat.log2 (shape.size + 2) + 1) ∧
    (∀ value ∈ shapeMemory shape, value < 2 ^ wordWidth shape.size) ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((interiorRangeBlock logicalReadBlock).compileAt 0 ++ [.halt 7000]) 479411 ⟨regs, 0, .running⟩ :=
  ⟨shapeMemory_capacity_le shape, wordWidth_le_log shape.size, shapeMemory_words_fit shape,
    interiorRangeBlock_execution_safe shape regs fit hm hstart hcount⟩

namespace InteriorSafetyConsumers

theorem canonical_source (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hstart : regs 896 ≤ metadataEnvelope shape.size)
    (hcount : regs 897 ≤ metadataEnvelope shape.size) :
    (interiorRangeBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ :=
  interiorRangeBlock_canonical_safe shape regs fit hm hstart hcount

theorem actual_run (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hstart : regs 896 ≤ metadataEnvelope shape.size)
    (hcount : regs 897 ≤ metadataEnvelope shape.size) :
    let expected := packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 896) (regs 897)
    let source := (interiorRangeBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩
    let program := (interiorRangeBlock logicalReadBlock).compileAt 0 ++ [.halt 7000]
    let actual := run (shapeMemory shape) program 479411 ⟨regs, 0, .running⟩
    actual.result = some (source.final.regs 7000) ∧
      actual.final.status = .halted (source.final.regs 7000) ∧
      actual.final.regs 7000 = source.final.regs 7000 ∧
      actual.final.regs 7001 = source.final.regs 7001 ∧
      actual.final.regs 7002 = source.final.regs 7002 ∧
      candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
      ReadOnlyTrace expected.trace ∧ actual.steps ≤ 479411 ∧
      (∀ instruction ∈ program, instruction.Fits (wordWidth shape.size)) ∧
      actual.final.Fits (wordWidth shape.size) ∧
      (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
        Instruction.Safe (wordWidth shape.size) t.before t.instruction ∧ t.after.Fits (wordWidth shape.size)) ∧
      (∀ index, index ≤ 479411 →
        (run (shapeMemory shape) program index ⟨regs, 0, .running⟩).final.Fits (wordWidth shape.size)) ∧
      (∀ (index : Nat) (t : Transition) (receipt : Receipt), actual.transitions[index]? = some t →
        t.receipt = some receipt → receipt.address < 2 ^ wordWidth shape.size ∧
          receipt.reply = (shapeMemory shape)[receipt.address]? ∧
          ∀ value, receipt.reply = some value → value < 2 ^ wordWidth shape.size) := by
  have semantics := interiorRangeBlock_canonical_machine shape regs hm
  have safe := interiorRangeBlock_execution_safe shape regs fit hm hstart hcount
  exact ⟨semantics.1, semantics.2.1, semantics.2.2.1, semantics.2.2.2.1,
    semantics.2.2.2.2.1, semantics.2.2.2.2.2.1, semantics.2.2.2.2.2.2.1,
    semantics.2.2.2.2.2.2.2.2.2, semantics.2.2.2.2.2.2.2.1,
    safe.1, safe.2.1, safe.2.2.1, safe.2.2.2.1, safe.2.2.2.2⟩

theorem zero_count (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hstart : regs 896 ≤ metadataEnvelope shape.size)
    (hz : regs 897 = 0) :
    let source := (interiorRangeBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩
    source.final.status = .running ∧ candidateOfRegs 7000 source.final.regs = none ∧ source.reads = [] ∧
      RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
        ((interiorRangeBlock logicalReadBlock).compileAt 0 ++ [.halt 7000]) 479411 ⟨regs, 0, .running⟩ := by
  have hs := interiorRangeBlock_zero shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm hz
  exact ⟨hs.1, hs.2.1, hs.2.2, interiorRangeBlock_execution_safe shape regs fit hm hstart (by rw [hz]; omega)⟩

theorem dead_entry (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hc : regs 704 = packedReviewerInteriorEntryCount shape.size component)
    (hw : regs 705 = packedReviewerInteriorEntryWidth shape.size component)
    (hb : regs 706 = packedReviewerInteriorComponentWordPrefix shape.size component)
    (dead : regs 704 ≤ regs 707) :
    let source := (interiorReadBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩
    source.final.status = .running ∧ source.final.regs 708 = logicalPacket
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20 (packedInteriorOffsets shape.size).deadAddress) ∧
      source.reads = readerReceipts shape (shapeMemory shape) 20 (packedInteriorOffsets shape.size).deadAddress ∧
      RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
        ((interiorReadBlock logicalReadBlock).compileAt 0 ++ [.halt 708]) 8698 ⟨regs, 0, .running⟩ := by
  have hs := interiorEntry_dead_request shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly component regs hm hw dead
  exact ⟨hs.1, hs.2.1, hs.2.2, interiorReadBlock_execution_safe shape component regs fit hm hc hw hb⟩

theorem maximal_inputs (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hstart : regs 896 = metadataEnvelope shape.size) (hcount : regs 897 = metadataEnvelope shape.size) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((interiorRangeBlock logicalReadBlock).compileAt 0 ++ [.halt 7000]) 479411 ⟨regs, 0, .running⟩ :=
  interiorRangeBlock_execution_safe shape regs fit hm (by omega) (by omega)

theorem universal_cross (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hcount : regs 897 ≤ metadataEnvelope shape.size) (hfirst : regs 898 ≤ metadataEnvelope shape.size)
    (hstart : regs 899 ≤ metadataEnvelope shape.size) (hleft : regs 900 ≤ metadataEnvelope shape.size)
    (hone : regs 911 = 1) :
    (interiorRangeCrossBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ :=
  interiorRangeCrossBlock_canonical_safe shape regs fit hm hcount hfirst hstart hleft hone

theorem failure_flag_continues (shape : CartesianShape) (regs : Registers)
    (inv : InteriorWordInvariant shape ⟨regs, .running⟩)
    (active : regs 710 < regs 709) (failed : regs 713 = 0) :
    let source := (interiorReadBody logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩
    (interiorReadBody logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
      source.reads = readerReceipts shape (shapeMemory shape) 20 (regs 706 + regs 707 * regs 709 + regs 710) ∧
      source.final.regs 710 = regs 710 + 1 ∧ source.final.regs 713 = 0 ∧
      InteriorWordInvariant shape source.final := by
  have safe := interiorReadBody_preserves shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_readerSafe shape) (logicalReadBlock_correct shape) logicalReadBlock_writesOnly _ inv
  have source := interiorReadBody_active shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) regs inv.metadata inv.one active
  refine ⟨safe.1, source.2.1, source.2.2.1, ?_, safe.2⟩
  rw [source.2.2.2.1, failed]
  split <;> rfl

end InteriorSafetyConsumers

end RMQ.SuccinctFinal.PackedWordRAM
