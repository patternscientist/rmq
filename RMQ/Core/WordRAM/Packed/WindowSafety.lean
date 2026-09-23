import RMQ.Core.WordRAM.Packed.RankSafety
import RMQ.Core.WordRAM.Packed.WindowProof
import RMQ.Core.WordRAM.Packed.QueryStatic

/-! Scalar and actual-run safety of the four charged, possibly ragged replies. -/
namespace RMQ.SuccinctFinal.PackedWordRAM
open Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

theorem window_data_running (s : Data) (h : s.status = .running) :
    s = ⟨s.regs, .running⟩ := by cases s; simp_all

theorem window_safe_follow {memory : Memory} {width : Nat} {first second : Block} {s : Data}
    (head : first.Safe memory width s)
    (tail : (first.eval memory s).final.Fits width →
      second.Safe memory width (first.eval memory s).final) :
    (Block.seq first second).Safe memory width s :=
  Block.safe_seq head (tail (first.eval_fits memory width s head))

theorem window_safe_constant {memory : Memory} {width dst value : Nat}
    {regs : Registers} {tail : Block} (fit : (⟨regs, .running⟩ : Data).Fits width)
    (valueFit : value < 2 ^ width)
    (next : (⟨regs.write dst value, .running⟩ : Data).Fits width →
      tail.Safe memory width ⟨regs.write dst value, .running⟩) :
    (Block.seq (.action (.constant dst value)) tail).Safe memory width ⟨regs, .running⟩ :=
  window_safe_follow (Block.safe_action memory width (.constant dst value) _ fit valueFit) next

theorem window_safe_move {memory : Memory} {width dst src : Nat}
    {regs : Registers} {tail : Block} (fit : (⟨regs, .running⟩ : Data).Fits width)
    (next : (⟨regs.write dst (regs src), .running⟩ : Data).Fits width →
      tail.Safe memory width ⟨regs.write dst (regs src), .running⟩) :
    (Block.seq (.action (.move dst src)) tail).Safe memory width ⟨regs, .running⟩ :=
  window_safe_follow (Block.safe_action memory width (.move dst src) _ fit (fit.1 src)) next

theorem window_safe_arithmetic {memory : Memory} {width dst lhs rhs : Nat}
    {op : Arithmetic} {regs : Registers} {tail : Block}
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (localSafe : (Action.arithmetic op dst lhs rhs).LocalSafe memory width ⟨regs, .running⟩)
    (next : (⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩ : Data).Fits width →
      tail.Safe memory width ⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩) :
    (Block.seq (.action (.arithmetic op dst lhs rhs)) tail).Safe memory width ⟨regs, .running⟩ :=
  window_safe_follow (Block.safe_action memory width (.arithmetic op dst lhs rhs) _ fit localSafe) next

theorem window_safe_sub {memory : Memory} {width dst lhs rhs tmp : Nat}
    {regs : Registers} {tail : Block} (fit : (⟨regs, .running⟩ : Data).Fits width)
    (one : 1 < 2 ^ width) (hl : lhs ≠ tmp) (hr : rhs ≠ tmp)
    (next : (⟨(regs.write tmp (Comparison.le.eval (regs rhs) (regs lhs))).write dst
        (regs lhs - regs rhs), .running⟩ : Data).Fits width →
      tail.Safe memory width ⟨(regs.write tmp (Comparison.le.eval (regs rhs) (regs lhs))).write dst
        (regs lhs - regs rhs), .running⟩) :
    (Block.seq (natSubBlock dst lhs rhs tmp) tail).Safe memory width ⟨regs, .running⟩ := by
  apply window_safe_follow (natSubBlock_safe memory width dst lhs rhs tmp _ fit one hl hr)
  rw [natSubBlock_source dst lhs rhs tmp memory regs hl hr]
  exact next

theorem window_safe_min {memory : Memory} {width dst lhs rhs tmp : Nat}
    {regs : Registers} {tail : Block} (fit : (⟨regs, .running⟩ : Data).Fits width)
    (one : 1 < 2 ^ width) (hl : lhs ≠ tmp) (hr : rhs ≠ tmp)
    (next : (⟨(regs.write tmp (Comparison.le.eval (regs lhs) (regs rhs))).write dst
        (min (regs lhs) (regs rhs)), .running⟩ : Data).Fits width →
      tail.Safe memory width ⟨(regs.write tmp (Comparison.le.eval (regs lhs) (regs rhs))).write dst
        (min (regs lhs) (regs rhs)), .running⟩) :
    (Block.seq (minBlock dst lhs rhs tmp) tail).Safe memory width ⟨regs, .running⟩ := by
  apply window_safe_follow (minBlock_safe memory width dst lhs rhs tmp _ fit one)
  rw [minBlock_source dst lhs rhs tmp memory regs hl hr]
  exact next

theorem raggedWindowBlock_safe (base n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (values : ∀ j < 4, regs (base + j) < 2 ^ regs (base + 4 + j))
    (lengths : ∀ j < 4, regs (base + 4 + j) ≤ packedReviewerCellWidth n) :
    (raggedWindowBlock base).Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have h0 := values 0 (by decide)
  have h1 := values 1 (by decide)
  have h2 := values 2 (by decide)
  have h3 := values 3 (by decide)
  have l0 := lengths 0 (by decide)
  have l1 := lengths 1 (by decide)
  have l2 := lengths 2 (by decide)
  have l3 := lengths 3 (by decide)
  simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at h0 h1 h2 h3 l0 l1 l2 l3
  have finalBound := raggedWindowValue_fits n _ _ _ _ _ _ _ _ h0 h1 h2 h3 l0 l1 l2 l3
  have m0 := Nat.le_mul_of_pos_right
    (regs (base + 1) + 2 ^ regs (base + 5) *
      (regs (base + 2) + 2 ^ regs (base + 6) * regs (base + 3)))
    (Nat.two_pow_pos (regs (base + 4)))
  have m1 := Nat.le_mul_of_pos_right
    (regs (base + 2) + 2 ^ regs (base + 6) * regs (base + 3))
    (Nat.two_pow_pos (regs (base + 5)))
  have width := fourOldWidths_lt_wordWidth n
  have shiftLeft_numeric (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b
  apply ScalarChecks_safe memory (wordWidth n) _ _ fit
  simp only [raggedWindowValue, Nat.mul_comm] at finalBound m0 m1
  simp [ScalarChecks, raggedWindowBlock, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, shiftLeft_numeric, Nat.mul_comm] <;> omega

theorem window_reply_length (shape : CartesianShape) (index : Nat) :
    (((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 index).getD []).length ≤
      packedReviewerCellWidth shape.size := by
  have h := (rank_logicalPacket_bounds shape 0 index).2
  cases hr : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 index with
  | none => simp
  | some bits => simpa [logicalLength, hr] using h

theorem loadWindowInit_safe (shape : CartesianShape) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    loadWindowInit.Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hw : regs 32 = packedBpCodeWordWidth shape.size := hm 16 (by decide)
  have hb : regs 33 = (packedInteriorLayout shape.size).blockSize := hm 17 (by decide)
  have wp : 0 < regs 32 := by rw [hw]; exact SuccinctRank.machineWordBits_pos _
  have bp : 0 < regs 33 := by
    rw [hb]
    change 0 < 2 * (shape.size.log2 + 1)
    omega
  have closeFit := fit.1 1024
  dsimp only at closeFit
  have d1 := Nat.div_le_self (regs 1024) (regs 33)
  have m := Nat.div_mul_le_self (regs 1024) (regs 33)
  have d2 := Nat.div_le_self (regs 1024 / regs 33 * regs 33) (regs 32)
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth shape.size by unfold wordWidth; omega)
  have hwne : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe memory (wordWidth shape.size) _ _ fit
  simp [ScalarChecks, loadWindowInit, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, wp, bp, hwne] <;> omega

theorem loadWindowPart_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (part : Nat) (hp : part < 4) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (first : regs 1025 ≤ metadataEnvelope shape.size) :
    (loadWindowPart reader part).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have cap := reader_polynomial_fit shape.size
  have env := metadataEnvelope_pos shape.size
  have one : 1 < 2 ^ wordWidth shape.size := by omega
  let prepared := ((regs.write 1028 part).write 8193 (regs 1025 + part)).write 8192 0
  have hm' : MetadataMatches shape prepared := by
    intro i hi
    simp only [prepared, Registers.write, if_neg (show 16 + i ≠ 8192 by omega),
      if_neg (show 16 + i ≠ 8193 by omega), if_neg (show 16 + i ≠ 1028 by omega)]
    exact hm i hi
  unfold loadWindowPart Block.sequence
  refine window_safe_constant fit (by omega) (fun f1 => ?_)
  refine window_safe_arithmetic f1 ?_ (fun f2 => ?_)
  · simp [Action.LocalSafe, Arithmetic.eval, Registers.write]; omega
  refine window_safe_constant f2 (by omega) (fun f3 => ?_)
  have ready : (⟨prepared, .running⟩ : Data).Fits (wordWidth shape.size) := f3
  have safe := readerSafe _ ready hm'
  have source := readerCorrect prepared hm'
  have rs := window_data_running (reader.eval memory ⟨prepared, .running⟩).final source.1
  apply window_safe_follow safe
  intro f4
  rw [rs] at f4 ⊢
  have sub := natSubBlock_safe memory (wordWidth shape.size) (1056 + part) 8194 1026 1027
    _ f4 one (by decide) (by decide)
  apply window_safe_follow sub
  intro f5
  apply SimpleScalar.safe memory (wordWidth shape.size) _ _ _ f5
  trivial

theorem loadWindowParts_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (readerWrites : ReaderWrites reader) (part count : Nat) (hp : part + count ≤ 4)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (first : regs 1025 ≤ metadataEnvelope shape.size)
    (hone : regs 1026 = 1) :
    (loadWindowParts reader part count).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  induction count generalizing part regs with
  | zero => exact Block.safe_skip _ _ _ fit
  | succ count ih =>
    have head := loadWindowPart_safe shape memory reader readerSafe readerCorrect part (by omega)
      regs fit hm first
    have source := loadWindowPart_source shape memory reader readerCorrect part (by omega) regs hm hone
    have frame := loadWindowPart_frame reader readerWrites part memory (⟨regs, .running⟩ : Data)
    have status := window_data_running _ source.1
    apply window_safe_follow head
    intro f1
    rw [status] at f1 ⊢
    apply ih (part + 1) (by omega) _ f1
    · intro i hi
      rw [frame _ (by unfold WindowPartWrites; omega)]
      exact hm i hi
    · rw [frame _ (by unfold WindowPartWrites; omega)]
      exact first
    · rw [frame _ (by unfold WindowPartWrites; omega)]
      exact hone

private theorem loadWindow_tail_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (readerWrites : ReaderWrites reader) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (first : regs 1025 ≤ metadataEnvelope shape.size)
    (hone : regs 1026 = 1) (parts : Block) (heq : parts = loadWindowParts reader 0 4) :
    (Block.seq parts (.seq (raggedWindowBlock 1056) .skip)).Safe memory (wordWidth shape.size)
      ⟨regs, .running⟩ := by
  have safe : parts.Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
    rw [heq]; exact loadWindowParts_safe shape memory reader readerSafe readerCorrect readerWrites
      0 4 (by decide) regs fit hm first hone
  have source := loadWindowParts_source shape memory reader readerCorrect readerWrites 0 4
    (by decide) regs hm hone
  rw [← heq] at source
  apply window_safe_follow safe
  intro f1
  rw [window_data_running _ source.1] at f1 ⊢
  apply window_safe_follow (raggedWindowBlock_safe 1056 shape.size memory _ f1 ?_ ?_)
  · exact fun f2 => Block.safe_skip _ _ _ f2
  · intro j hj
    have h := source.2.1 j hj
    simp only [Nat.zero_add] at h
    rw [h.1, h.2]
    exact GenericSelect.bitsToNatLE_lt_two_pow_length _
  · intro j hj
    have h := source.2.1 j hj
    simp only [Nat.zero_add] at h
    rw [h.2]
    exact window_reply_length shape _

theorem loadWindowBlock_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (readerWrites : ReaderWrites reader) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (close : regs 1024 ≤ metadataEnvelope shape.size) :
    (loadWindowBlock reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ := by
  have init := loadWindowInit_safe shape memory regs fit hm
  have source := loadWindowInit_source memory regs
  have firstBound : windowFirstWord regs ≤ regs 1024 :=
    Nat.le_trans (Nat.div_le_self _ _) (Nat.div_mul_le_self _ _)
  unfold loadWindowBlock Block.sequence
  apply window_safe_follow init
  intro f1
  rw [source] at f1 ⊢
  apply loadWindow_tail_safe shape memory reader readerSafe readerCorrect readerWrites _ f1
  · intro i hi
    simp only [Registers.write, if_neg (show 16 + i ≠ 1025 by omega),
      if_neg (show 16 + i ≠ 1026 by omega)]
    exact hm i hi
  · simp [Registers.write]; omega
  · simp [Registers.write]
  · rfl

theorem loadWindowBlock_canonical_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (close : regs 1024 ≤ metadataEnvelope shape.size) :
    (loadWindowBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size)
      ⟨regs, .running⟩ :=
  loadWindowBlock_safe shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_readerSafe shape) (logicalReadBlock_correct shape)
    logicalReadBlock_writesOnly regs fit hm close

set_option maxRecDepth 30000 in
theorem loadWindowBlock_maxEncodedField :
    (loadWindowBlock logicalReadBlock).maxEncodedField = 8270 := by rfl

theorem loadWindowBlock_fieldsFit (n : Nat) :
    (loadWindowBlock logicalReadBlock).FieldsFit (wordWidth n) := by
  apply Block.fieldsFit_of_maxEncodedField
  rw [loadWindowBlock_maxEncodedField]
  have cap := query_small_fields_fit n
  omega

theorem loadWindowBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (close : regs 1024 ≤ metadataEnvelope shape.size) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((loadWindowBlock logicalReadBlock).compileAt 0 ++ [.halt 1064])
      4319 ⟨regs, 0, .running⟩ := by
  have cap := query_small_fields_fit shape.size
  exact rank_compiled_safety (shapeMemory shape) (wordWidth shape.size)
    (loadWindowBlock logicalReadBlock) 1064 4319 regs
    (by simp only [loadWindowBlock_size, logicalReadBlock_size, locateBlock_size])
    (by omega) (loadWindowBlock_fieldsFit _)
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega) fit
    (loadWindowBlock_canonical_safe shape regs fit hm close)

theorem loadWindowRun_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (close : regs 1024 ≤ metadataEnvelope shape.size) :
    let expected := packedLocalBPWindowBitsRead (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (packedInteriorLayout shape.size).blockSize (regs 1024)
    let program := (loadWindowBlock logicalReadBlock).compileAt 0 ++ [.halt 1064]
    let actual := run (shapeMemory shape) program 4319 ⟨regs, 0, .running⟩
    actual.result = some (bitsToNatLE expected.value) ∧
    actual.final.status = .halted (bitsToNatLE expected.value) ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 4319 ∧
    (∀ r, ¬ WindowWrites r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program 4319 ⟨regs, 0, .running⟩ := by
  have semantic := loadWindowBlock_canonical_machine shape regs hm
  exact ⟨semantic.1, semantic.2.1, semantic.2.2.1, semantic.2.2.2.1,
    semantic.2.2.2.2.1, semantic.2.2.2.2.2, loadWindowBlock_execution_safe shape regs fit hm close⟩

namespace WindowSafetyConsumers

/-- Values and actual lengths for [true], [], [false], [true]. -/
def raggedRegisters : Registers := fun r => if r = 0 ∨ r = 3 ∨ r = 4 ∨ r = 6 ∨ r = 7 then 1 else 0

theorem ragged_three_bits (n : Nat) (memory : Memory) :
    let program := (raggedWindowBlock 0).compileAt 0 ++ [.halt 8]
    let actual := run memory program 7 ⟨raggedRegisters, 0, .running⟩
    actual.result = some 5 ∧ actual.reads = [] ∧
    RankExecutionSafety memory (wordWidth n) program 7 ⟨raggedRegisters, 0, .running⟩ := by
  have cap := query_small_fields_fit n
  have old := packedReviewerCellWidth_pos n
  have fit : (⟨raggedRegisters, .running⟩ : Data).Fits (wordWidth n) := by
    constructor
    · intro r
      simp only [raggedRegisters]
      split <;> omega
    · intro value contradiction
      cases contradiction
  have safe := raggedWindowBlock_safe 0 n memory raggedRegisters fit
    (by intro j hj; have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
        rcases h with rfl | rfl | rfl | rfl <;> decide)
    (by intro j hj; have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
        rcases h with rfl | rfl | rfl | rfl <;> simp [raggedRegisters] <;> omega)
  have machine := raggedWindowBlock_machine 0 memory raggedRegisters
  have actualSafe := rank_compiled_safety memory (wordWidth n) (raggedWindowBlock 0) 8 7
    raggedRegisters rfl (by omega) (by
      apply Block.fieldsFit_of_maxEncodedField
      change 8 < 2 ^ wordWidth n
      omega)
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega) fit safe
  refine ⟨?_, machine.2.1, actualSafe⟩
  simpa [raggedRegisters, raggedWindowValue] using machine.1

theorem canonical_zero_close (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (zero : regs 1024 = 0) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((loadWindowBlock logicalReadBlock).compileAt 0 ++ [.halt 1064]) 4319 ⟨regs, 0, .running⟩ :=
  loadWindowBlock_execution_safe shape regs fit hm (by rw [zero]; exact Nat.zero_le _)

end WindowSafetyConsumers

end RMQ.SuccinctFinal.PackedWordRAM
