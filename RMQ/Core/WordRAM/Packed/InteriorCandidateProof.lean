import RMQ.Core.WordRAM.Packed.InteriorReadProof
import RMQ.Core.WordRAM.Packed.CandidateProof

/-! # Complete fixed interior candidate navigator -/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

private theorem eval_move (memory : Memory) (regs : Registers) (dst src : Nat) :
    (Block.action (.move dst src)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst (regs src), .running⟩, []⟩ := rfl

private theorem eval_constant (memory : Memory) (regs : Registers) (dst value : Nat) :
    (Block.action (.constant dst value)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst value, .running⟩, []⟩ := rfl

private theorem eval_arithmetic (memory : Memory) (regs : Registers)
    (op : Arithmetic) (dst lhs rhs : Nat) :
    (Block.action (.arithmetic op dst lhs rhs)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩, []⟩ := rfl

private theorem eval_comparison (memory : Memory) (regs : Registers)
    (op : Comparison) (dst lhs rhs : Nat) :
    (Block.action (.comparison op dst lhs rhs)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩, []⟩ := rfl

private theorem eval_skip (memory : Memory) (regs : Registers) :
    Block.skip.eval memory ⟨regs, .running⟩ = ⟨⟨regs, .running⟩, []⟩ := rfl

private theorem eval_ifZero (memory : Memory) (regs : Registers) (condition : Nat)
    (yes no : Block) :
    (Block.ifZero condition yes no).eval memory ⟨regs, .running⟩ =
      if regs condition = 0 then yes.eval memory ⟨regs, .running⟩
      else no.eval memory ⟨regs, .running⟩ := rfl

private theorem eval_seq_of_results (memory : Memory) (first second : Block) (s : Data)
    (a b : Evaluation) (ha : first.eval memory s = a)
    (hb : second.eval memory a.final = b) :
    (Block.seq first second).eval memory s = ⟨b.final, a.reads ++ b.reads⟩ := by
  rw [Block.eval_seq, ha]
  simp only [Evaluation.bind, hb]

def InteriorMinWrites (r : Nat) : Prop :=
  (704 ≤ r ∧ r < 719) ∨ (769 ≤ r ∧ r < 775) ∨
  (7000 ≤ r ∧ r < 7004) ∨ (8192 ≤ r ∧ r < 8271)

def InteriorLocalSpanWrites (r : Nat) : Prop :=
  InteriorMinWrites r ∨ r = 768 ∨ (803 ≤ r ∧ r < 805)

def InteriorGlobalSpanWrites (r : Nat) : Prop :=
  InteriorMinWrites r ∨ r = 768 ∨ (818 ≤ r ∧ r < 820)

def InteriorLocalTwoWrites (r : Nat) : Prop :=
  InteriorLocalSpanWrites r ∨ (800 ≤ r ∧ r < 803) ∨ (835 ≤ r ∧ r < 845)

def InteriorGlobalTwoWrites (r : Nat) : Prop :=
  InteriorGlobalSpanWrites r ∨ (816 ≤ r ∧ r < 818) ∨ (866 ≤ r ∧ r < 877)

def InteriorRangeWrites (r : Nat) : Prop :=
  InteriorLocalTwoWrites r ∨ InteriorGlobalTwoWrites r ∨
  (832 ≤ r ∧ r < 835) ∨ (864 ≤ r ∧ r < 866) ∨ (898 ≤ r ∧ r < 912)

theorem interiorMinBlock_writes (reader : Block) (hr : ReaderWrites reader) :
    (interiorMinBlock reader).WritesOnly InteriorMinWrites := by
  have he : (interiorReadBlock reader).WritesOnly InteriorMinWrites :=
    Block.WritesOnly.mono _ (interiorReadBlock_writes reader hr)
      (by intro r h; unfold InteriorReadWrites at h; unfold InteriorMinWrites; omega)
  simp only [interiorMinBlock, interiorMinProgram, interiorMinBaselineProgram, interiorMinBaselinePrefix, interiorMinRelativePrefix, interiorMinFieldProgram, interiorMinFinish, candidateNoneBlock, natSubBlock, Block.sequence, List.foldr, Block.WritesOnly, Action.destination, he]
  simp [InteriorMinWrites]

theorem interiorMinBlock_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ InteriorMinWrites r) :
    ((interiorMinBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (interiorMinBlock_writes reader hr) r outside s

theorem interiorMinBlock_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data)
    (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((interiorMinBlock reader).eval memory s).final.regs := by
  intro i hi
  rw [interiorMinBlock_frame reader hr memory s (16 + i)
    (by unfold InteriorMinWrites; omega)]
  exact hm i hi

theorem interiorLocalSpanBlock_writes (reader : Block) (hr : ReaderWrites reader) :
    (interiorLocalSpanBlock reader).WritesOnly InteriorLocalSpanWrites := by
  have he : (interiorReadBlock reader).WritesOnly InteriorLocalSpanWrites :=
    Block.WritesOnly.mono _ (interiorReadBlock_writes reader hr)
      (by intro r h; unfold InteriorReadWrites at h; unfold InteriorLocalSpanWrites InteriorMinWrites; omega)
  simp only [interiorMinBlock, interiorMinProgram, interiorMinBaselineProgram, interiorMinBaselinePrefix, interiorMinRelativePrefix, interiorMinFieldProgram, interiorMinFinish, interiorLocalSpanBlock, interiorLocalSpanProgram, interiorLocalSpanPrefix, interiorLocalSpanSelectedPrefix, candidateNoneBlock, natSubBlock, Block.sequence, List.foldr, Block.WritesOnly, Action.destination, he]
  simp [InteriorLocalSpanWrites, InteriorMinWrites]

theorem interiorLocalSpanBlock_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ InteriorLocalSpanWrites r) :
    ((interiorLocalSpanBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (interiorLocalSpanBlock_writes reader hr) r outside s

theorem interiorLocalSpanBlock_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data)
    (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((interiorLocalSpanBlock reader).eval memory s).final.regs := by
  intro i hi
  rw [interiorLocalSpanBlock_frame reader hr memory s (16 + i)
    (by unfold InteriorLocalSpanWrites InteriorMinWrites; omega)]
  exact hm i hi

theorem interiorGlobalSpanBlock_writes (reader : Block) (hr : ReaderWrites reader) :
    (interiorGlobalSpanBlock reader).WritesOnly InteriorGlobalSpanWrites := by
  have he : (interiorReadBlock reader).WritesOnly InteriorGlobalSpanWrites :=
    Block.WritesOnly.mono _ (interiorReadBlock_writes reader hr)
      (by intro r h; unfold InteriorReadWrites at h; unfold InteriorGlobalSpanWrites InteriorMinWrites; omega)
  simp only [interiorMinBlock, interiorMinProgram, interiorMinBaselineProgram, interiorMinBaselinePrefix, interiorMinRelativePrefix, interiorMinFieldProgram, interiorMinFinish, interiorGlobalSpanBlock, interiorGlobalSpanProgram, interiorGlobalSpanPrefix, interiorGlobalSpanSelectedPrefix, candidateNoneBlock, natSubBlock, Block.sequence, List.foldr, Block.WritesOnly, Action.destination, he]
  simp [InteriorGlobalSpanWrites, InteriorMinWrites]

theorem interiorGlobalSpanBlock_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ InteriorGlobalSpanWrites r) :
    ((interiorGlobalSpanBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (interiorGlobalSpanBlock_writes reader hr) r outside s

theorem interiorGlobalSpanBlock_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data)
    (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((interiorGlobalSpanBlock reader).eval memory s).final.regs := by
  intro i hi
  rw [interiorGlobalSpanBlock_frame reader hr memory s (16 + i)
    (by unfold InteriorGlobalSpanWrites InteriorMinWrites; omega)]
  exact hm i hi

theorem interiorLocalTwoBlock_writes (reader : Block) (hr : ReaderWrites reader) :
    (interiorLocalTwoBlock reader).WritesOnly InteriorLocalTwoWrites := by
  have he : (interiorReadBlock reader).WritesOnly InteriorLocalTwoWrites :=
    Block.WritesOnly.mono _ (interiorReadBlock_writes reader hr)
      (by intro r h; unfold InteriorReadWrites at h; unfold InteriorLocalTwoWrites InteriorLocalSpanWrites InteriorMinWrites; omega)
  simp only [interiorMinBlock, interiorMinProgram, interiorMinBaselineProgram, interiorMinBaselinePrefix, interiorMinRelativePrefix, interiorMinFieldProgram, interiorMinFinish, interiorLocalSpanBlock, interiorLocalSpanProgram, interiorLocalSpanPrefix, interiorLocalSpanSelectedPrefix, interiorLocalTwoBlock, interiorLocalTwoProgram, interiorLocalTwoPrefix, interiorLocalTwoFirstPrefix, interiorLocalTwoSecondPrefix, interiorLocalTwoSelectedProgram, candidateNoneBlock, candidateSaveBlock, candidateRestoreBlock, candidateMergeLeftBlock, natSubBlock, Block.sequence, List.foldr, Block.WritesOnly, Action.destination, he]
  simp [InteriorLocalTwoWrites, InteriorLocalSpanWrites, InteriorMinWrites]

theorem interiorLocalTwoBlock_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ InteriorLocalTwoWrites r) :
    ((interiorLocalTwoBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (interiorLocalTwoBlock_writes reader hr) r outside s

theorem interiorLocalTwoBlock_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data)
    (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((interiorLocalTwoBlock reader).eval memory s).final.regs := by
  intro i hi
  rw [interiorLocalTwoBlock_frame reader hr memory s (16 + i)
    (by unfold InteriorLocalTwoWrites InteriorLocalSpanWrites InteriorMinWrites; omega)]
  exact hm i hi

theorem interiorGlobalTwoBlock_writes (reader : Block) (hr : ReaderWrites reader) :
    (interiorGlobalTwoBlock reader).WritesOnly InteriorGlobalTwoWrites := by
  have he : (interiorReadBlock reader).WritesOnly InteriorGlobalTwoWrites :=
    Block.WritesOnly.mono _ (interiorReadBlock_writes reader hr)
      (by intro r h; unfold InteriorReadWrites at h; unfold InteriorGlobalTwoWrites InteriorGlobalSpanWrites InteriorMinWrites; omega)
  simp only [interiorMinBlock, interiorMinProgram, interiorMinBaselineProgram, interiorMinBaselinePrefix, interiorMinRelativePrefix, interiorMinFieldProgram, interiorMinFinish, interiorGlobalSpanBlock, interiorGlobalSpanProgram, interiorGlobalSpanPrefix, interiorGlobalSpanSelectedPrefix, interiorGlobalTwoBlock, interiorGlobalTwoProgram, interiorGlobalTwoPrefix, interiorGlobalTwoFirstPrefix, interiorGlobalTwoSecondPrefix, interiorGlobalTwoSelectedProgram, candidateNoneBlock, candidateSaveBlock, candidateRestoreBlock, candidateMergeLeftBlock, natSubBlock, Block.sequence, List.foldr, Block.WritesOnly, Action.destination, he]
  simp [InteriorGlobalTwoWrites, InteriorGlobalSpanWrites, InteriorMinWrites]

theorem interiorGlobalTwoBlock_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ InteriorGlobalTwoWrites r) :
    ((interiorGlobalTwoBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (interiorGlobalTwoBlock_writes reader hr) r outside s

theorem interiorGlobalTwoBlock_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data)
    (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((interiorGlobalTwoBlock reader).eval memory s).final.regs := by
  intro i hi
  rw [interiorGlobalTwoBlock_frame reader hr memory s (16 + i)
    (by unfold InteriorGlobalTwoWrites InteriorGlobalSpanWrites InteriorMinWrites; omega)]
  exact hm i hi

theorem interiorRangeBlock_writes (reader : Block) (hr : ReaderWrites reader) :
    (interiorRangeBlock reader).WritesOnly InteriorRangeWrites := by
  have he : (interiorReadBlock reader).WritesOnly InteriorRangeWrites :=
    Block.WritesOnly.mono _ (interiorReadBlock_writes reader hr)
      (by intro r h; unfold InteriorReadWrites at h; unfold InteriorRangeWrites InteriorGlobalTwoWrites InteriorLocalTwoWrites InteriorGlobalSpanWrites InteriorLocalSpanWrites InteriorMinWrites; omega)
  simp only [interiorMinBlock, interiorMinProgram, interiorMinBaselineProgram, interiorMinBaselinePrefix, interiorMinRelativePrefix, interiorMinFieldProgram, interiorMinFinish, interiorLocalSpanBlock, interiorLocalSpanProgram, interiorLocalSpanPrefix, interiorLocalSpanSelectedPrefix, interiorGlobalSpanBlock, interiorGlobalSpanProgram, interiorGlobalSpanPrefix, interiorGlobalSpanSelectedPrefix, interiorLocalTwoBlock, interiorLocalTwoProgram, interiorLocalTwoPrefix, interiorLocalTwoFirstPrefix, interiorLocalTwoSecondPrefix, interiorLocalTwoSelectedProgram, interiorGlobalTwoBlock, interiorGlobalTwoProgram, interiorGlobalTwoPrefix, interiorGlobalTwoFirstPrefix, interiorGlobalTwoSecondPrefix, interiorGlobalTwoSelectedProgram, interiorRangeBlock, interiorRangeProgram, interiorRangePrefix, interiorRangeSinglePrefix, interiorRangeCrossBlock, interiorRangeCrossProgram, interiorRangeCrossPrefix, interiorRangeAdjacentPrefix, interiorRangeMiddlePrefix, interiorRangeTrailingPrefix, interiorRangeTrailingProgram, interiorRangeMiddleProgram, interiorRangeMiddleStageProgram, interiorRangeBranchProgram, candidateNoneBlock, candidateSaveBlock, candidateRestoreBlock, candidateMergeLeftBlock, natSubBlock, Block.sequence, List.foldr, Block.WritesOnly, Action.destination, he]
  simp [InteriorRangeWrites, InteriorGlobalTwoWrites, InteriorLocalTwoWrites, InteriorGlobalSpanWrites, InteriorLocalSpanWrites, InteriorMinWrites]

theorem interiorRangeBlock_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ InteriorRangeWrites r) :
    ((interiorRangeBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (interiorRangeBlock_writes reader hr) r outside s

theorem interiorRangeBlock_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data)
    (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((interiorRangeBlock reader).eval memory s).final.regs := by
  intro i hi
  rw [interiorRangeBlock_frame reader hr memory s (16 + i)
    (by unfold InteriorRangeWrites InteriorGlobalTwoWrites InteriorLocalTwoWrites InteriorGlobalSpanWrites InteriorLocalSpanWrites InteriorMinWrites; omega)]
  exact hm i hi


/-- Ordered physical attempts produced by this one flat execution. -/
def interiorExecutionReads (shape : CartesianShape) (memory : Memory)
    (execution : FlatStoreExecution α) : List Receipt :=
  execution.reads.flatMap (fun read => readerReceipts shape memory 20 read.1)

def InteriorEntrySpec (shape : CartesianShape) (memory : Memory) (entry : Block) : Prop :=
  ∀ regs, MetadataMatches shape regs →
    fixedWidthNatTableMachineChunkCount (regs 705) (packedBpCodeWordWidth shape.size) ≤ 7 →
    let execution := (packedInteriorReadNatOf shape.size (regs 704) (regs 705)
      (regs 706) (regs 707)).run
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers, entry.eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      final 708 = (execution.value.map (· + 1)).getD 0

theorem interiorReadBlock_spec (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader) :
    InteriorEntrySpec shape memory (interiorReadBlock reader) := by
  intro regs hm hc
  have hs := interiorReadBlock_reference shape memory reader hr hw regs hm hc
  dsimp only at hs ⊢
  rw [logicalTraceReads_flatExecution] at hs
  generalize he : (interiorReadBlock reader).eval memory ⟨regs, .running⟩ = actual at hs
  rcases actual with ⟨⟨final, status⟩, reads⟩
  dsimp only at hs
  obtain ⟨rfl, hp, hreads, _⟩ := hs
  refine ⟨final, ?_, hp⟩
  exact congrArg (fun receipts => Evaluation.mk ⟨final, .running⟩ receipts) hreads

def InteriorFieldWrites (output r : Nat) : Prop :=
  (704 ≤ r ∧ r < 719) ∨ r = output ∨ (8192 ≤ r ∧ r < 8271)

theorem interiorMinFieldProgram_writes (entry : Block)
    (he : entry.WritesOnly InteriorReadWrites) (base output : Nat) :
    (interiorMinFieldProgram entry base output).WritesOnly (InteriorFieldWrites output) := by
  have he' : entry.WritesOnly (InteriorFieldWrites output) :=
    Block.WritesOnly.mono entry he (by intro r h; unfold InteriorReadWrites at h; unfold InteriorFieldWrites; omega)
  simp [interiorMinFieldProgram, interiorMinRelativePrefix, Block.sequence,
    Block.WritesOnly, Action.destination, he', InteriorFieldWrites]

theorem interiorMinRelativePrefix_source (memory : Memory) (regs : Registers)
    (base : Nat) (hb : base < 704) :
    (interiorMinRelativePrefix base).eval memory ⟨regs, .running⟩ =
      ⟨⟨(((regs.write 704 (regs 36)).write 705 (regs 42)).write 706 (regs base)).write
        707 (regs 768), .running⟩, []⟩ := by
  simp [interiorMinRelativePrefix, Block.sequence, Block.eval_seq, eval_move,
    eval_skip, Evaluation.bind, Registers.write,
    show base ≠ 704 by omega, show base ≠ 705 by omega]

theorem interiorMinBaselinePrefix_source (memory : Memory) (regs : Registers) :
    interiorMinBaselinePrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨((((regs.write 774 1).write 704 (regs 37)).write 705 (regs 32)).write
        706 (regs 49)).write 707 (regs 768 / regs 35), .running⟩, []⟩ := by
  simp [interiorMinBaselinePrefix, Block.sequence, Block.eval_seq, eval_move,
    eval_constant, eval_arithmetic, eval_skip, Evaluation.bind, Registers.write, Arithmetic.eval]

private theorem minField_eval (memory : Memory) (entry : Block) (base output : Nat)
    (regs rr : Registers) (hb : base < 704) (reads : List Receipt)
    (he : entry.eval memory
      ⟨(((regs.write 704 (regs 36)).write 705 (regs 42)).write 706 (regs base)).write
        707 (regs 768), .running⟩ = ⟨⟨rr, .running⟩, reads⟩) :
    (interiorMinFieldProgram entry base output).eval memory ⟨regs, .running⟩ =
      ⟨⟨rr.write output (rr 708), .running⟩, reads⟩ := by
  rw [interiorMinFieldProgram, Block.eval_seq,
    interiorMinRelativePrefix_source memory regs base hb]
  simp only [Evaluation.bind, Block.eval_seq, he, eval_move, List.nil_append,
    List.append_nil]

theorem interiorMinFieldProgram_source (shape : CartesianShape) (memory : Memory)
    (entry : Block) (hspec : InteriorEntrySpec shape memory entry)
    (hew : entry.WritesOnly InteriorReadWrites)
    (base output : Nat) (hb : base < 704)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let execution := (packedInteriorReadNatOf shape.size
      (packedInteriorLayout shape.size).blockCount (packedInteriorLayout shape.size).relativeWidth
      (regs base) (regs 768)).run
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers, (interiorMinFieldProgram entry base output).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      final output = (execution.value.map (· + 1)).getD 0 ∧
      (∀ r, ¬ InteriorFieldWrites output r → final r = regs r) := by
  let pr := (((regs.write 704 (regs 36)).write 705 (regs 42)).write
    706 (regs base)).write 707 (regs 768)
  have hpm : MetadataMatches shape pr := by
    intro i hi
    simpa [pr, Registers.write, show 16 + i ≠ 704 by omega,
      show 16 + i ≠ 705 by omega, show 16 + i ≠ 706 by omega,
      show 16 + i ≠ 707 by omega] using hm i hi
  have hc : regs 36 = (packedInteriorLayout shape.size).blockCount := hm 20 (by decide)
  have hw : regs 42 = (packedInteriorLayout shape.size).relativeWidth := hm 26 (by decide)
  have hcount : fixedWidthNatTableMachineChunkCount (pr 705)
      (packedBpCodeWordWidth shape.size) ≤ 7 := by
    simpa [pr, Registers.write, hw, packedReviewerInteriorEntryWidth] using
      canonical_interior_chunks_le_seven shape .minRel
  obtain ⟨rr, he, hp⟩ := hspec pr hpm hcount
  have hjoin := minField_eval memory entry base output regs rr hb _ he
  simp only [pr, Registers.write, reduceIte, hc, hw] at hjoin hp
  refine ⟨rr.write output (rr 708), hjoin, ?_, ?_⟩
  · simpa [Registers.write] using hp
  · intro r hr
    have hf := Block.eval_frame memory _ _ (interiorMinFieldProgram_writes entry hew base output)
      r hr ⟨regs, .running⟩
    rw [hjoin] at hf
    exact hf



def interiorMinPacketCandidate (regs : Registers) : Option (Nat × Nat) :=
  if regs 769 = 0 ∨ regs 770 = 0 ∨ regs 771 = 0 ∨ regs 772 = 0 then none
  else some (regs 769 - 1 + (regs 770 - 1) - regs 33 * regs 35,
    regs 768 * regs 33 + regs 772 - 1)

theorem interiorMinFinish_source (memory : Memory) (regs : Registers)
    (hone : regs 774 = 1) :
    let actual := interiorMinFinish.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
    candidateOfRegs 7000 actual.final.regs = interiorMinPacketCandidate regs := by
  by_cases h0 : regs 769 = 0
  · simp [interiorMinFinish, candidateNoneBlock, Block.sequence, Block.eval_seq,
      eval_constant, eval_ifZero, eval_skip, Evaluation.bind, Registers.write,
      candidateOfRegs, interiorMinPacketCandidate, h0]
  · by_cases h1 : regs 770 = 0
    · simp [interiorMinFinish, candidateNoneBlock, Block.sequence, Block.eval_seq,
        eval_constant, eval_ifZero, eval_skip, Evaluation.bind, Registers.write,
        candidateOfRegs, interiorMinPacketCandidate, h0, h1]
    · by_cases h2 : regs 771 = 0
      · simp [interiorMinFinish, candidateNoneBlock, Block.sequence, Block.eval_seq,
          eval_constant, eval_ifZero, eval_skip, Evaluation.bind, Registers.write,
          candidateOfRegs, interiorMinPacketCandidate, h0, h1, h2]
      · by_cases h3 : regs 772 = 0
        · simp [interiorMinFinish, candidateNoneBlock, Block.sequence, Block.eval_seq,
            eval_constant, eval_ifZero, eval_skip, Evaluation.bind, Registers.write,
            candidateOfRegs, interiorMinPacketCandidate, h0, h1, h2, h3]
        · simp [interiorMinFinish, candidateNoneBlock, Block.sequence, Block.eval_seq,
            eval_constant, eval_ifZero, eval_skip, eval_arithmetic,
            natSubBlock_source, Evaluation.bind, Registers.write, Arithmetic.eval,
            candidateOfRegs, interiorMinPacketCandidate, h0, h1, h2, h3, hone]

theorem interiorMinPacketCandidate_decode (regs : Registers)
    (baseline minRel maxRel argOffset : Option Nat)
    (h0 : regs 769 = (baseline.map (· + 1)).getD 0)
    (h1 : regs 770 = (minRel.map (· + 1)).getD 0)
    (h2 : regs 771 = (maxRel.map (· + 1)).getD 0)
    (h3 : regs 772 = (argOffset.map (· + 1)).getD 0) :
    interiorMinPacketCandidate regs =
      (match baseline, minRel, maxRel, argOffset with
      | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
      | _, _, _, _ => none).map
        (bpRelativeSummaryMinCandidate (regs 33) (regs 35) (regs 768)) := by
  cases baseline <;> cases minRel <;> cases maxRel <;> cases argOffset <;>
    simp [interiorMinPacketCandidate, h0, h1, h2, h3,
      bpRelativeSummaryMinCandidate, bpSuperblockSpan, blockStartOf, Nat.mul_comm] <;> omega



def InteriorBaselineWrites (r : Nat) : Prop :=
  (704 ≤ r ∧ r < 719) ∨ r = 769 ∨ r = 774 ∨ (8192 ≤ r ∧ r < 8271)

theorem interiorMinBaselineProgram_writes (entry : Block)
    (he : entry.WritesOnly InteriorReadWrites) :
    (interiorMinBaselineProgram entry).WritesOnly InteriorBaselineWrites := by
  have he' : entry.WritesOnly InteriorBaselineWrites :=
    Block.WritesOnly.mono entry he
      (by intro r h; unfold InteriorReadWrites at h; unfold InteriorBaselineWrites; omega)
  simp [interiorMinBaselineProgram, interiorMinBaselinePrefix, Block.sequence,
    Block.WritesOnly, Action.destination, he', InteriorBaselineWrites]

private theorem minBaseline_eval (memory : Memory) (entry : Block)
    (regs rr : Registers) (reads : List Receipt)
    (he : entry.eval memory
      ⟨((((regs.write 774 1).write 704 (regs 37)).write 705 (regs 32)).write
        706 (regs 49)).write 707 (regs 768 / regs 35), .running⟩ =
        ⟨⟨rr, .running⟩, reads⟩) :
    (interiorMinBaselineProgram entry).eval memory ⟨regs, .running⟩ =
      ⟨⟨rr.write 769 (rr 708), .running⟩, reads⟩ := by
  rw [interiorMinBaselineProgram, Block.eval_seq, interiorMinBaselinePrefix_source]
  simp only [Evaluation.bind, Block.eval_seq, he, eval_move, List.nil_append, List.append_nil]

theorem interiorMinBaselineProgram_source (shape : CartesianShape) (memory : Memory)
    (entry : Block) (hspec : InteriorEntrySpec shape memory entry)
    (hew : entry.WritesOnly InteriorReadWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let execution := (packedInteriorReadNatOf shape.size
      (packedInteriorLayout shape.size).superSampleCount (packedBpCodeWordWidth shape.size)
      (packedInteriorOffsets shape.size).baseline
      (regs 768 / (packedInteriorLayout shape.size).blocksPerSuper)).run
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers, (interiorMinBaselineProgram entry).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      final 769 = (execution.value.map (· + 1)).getD 0 ∧ final 774 = 1 ∧
      (∀ r, ¬ InteriorBaselineWrites r → final r = regs r) := by
  let pr := ((((regs.write 774 1).write 704 (regs 37)).write 705 (regs 32)).write
    706 (regs 49)).write 707 (regs 768 / regs 35)
  have hpm : MetadataMatches shape pr := by
    intro i hi
    simpa [pr, Registers.write, show 16 + i ≠ 774 by omega,
      show 16 + i ≠ 704 by omega, show 16 + i ≠ 705 by omega,
      show 16 + i ≠ 706 by omega, show 16 + i ≠ 707 by omega] using hm i hi
  have hc : regs 37 = (packedInteriorLayout shape.size).superSampleCount := hm 21 (by decide)
  have hw : regs 32 = packedBpCodeWordWidth shape.size := hm 16 (by decide)
  have hb : regs 49 = (packedInteriorOffsets shape.size).baseline := hm 33 (by decide)
  have hd : regs 35 = (packedInteriorLayout shape.size).blocksPerSuper := hm 19 (by decide)
  have hcount : fixedWidthNatTableMachineChunkCount (pr 705)
      (packedBpCodeWordWidth shape.size) ≤ 7 := by
    simpa [pr, Registers.write, hw, packedReviewerInteriorEntryWidth] using
      canonical_interior_chunks_le_seven shape .baseline
  obtain ⟨rr, he, hp⟩ := hspec pr hpm hcount
  have hkeep := Block.eval_frame memory entry InteriorReadWrites hew 774
    (by simp [InteriorReadWrites]) ⟨pr, .running⟩
  rw [he] at hkeep
  have hjoin := minBaseline_eval memory entry regs rr _ he
  simp only [pr, Registers.write, reduceIte, hc, hw, hb, hd] at hjoin hp hkeep
  refine ⟨rr.write 769 (rr 708), hjoin, ?_, ?_, ?_⟩
  · simpa [Registers.write] using hp
  · simpa [Registers.write] using hkeep
  · intro r hr
    have hf := Block.eval_frame memory _ _ (interiorMinBaselineProgram_writes entry hew)
      r hr ⟨regs, .running⟩
    rw [hjoin] at hf
    exact hf



private theorem eval_four_then (memory : Memory) (a b c d finish : Block)
    (r0 r1 r2 r3 r4 r5 : Registers) (ta tb tc td : List Receipt)
    (ha : a.eval memory ⟨r0, .running⟩ = ⟨⟨r1, .running⟩, ta⟩)
    (hb : b.eval memory ⟨r1, .running⟩ = ⟨⟨r2, .running⟩, tb⟩)
    (hc : c.eval memory ⟨r2, .running⟩ = ⟨⟨r3, .running⟩, tc⟩)
    (hd : d.eval memory ⟨r3, .running⟩ = ⟨⟨r4, .running⟩, td⟩)
    (hf : finish.eval memory ⟨r4, .running⟩ = ⟨⟨r5, .running⟩, []⟩) :
    (Block.seq a (.seq b (.seq c (.seq d finish)))).eval memory ⟨r0, .running⟩ =
      ⟨⟨r5, .running⟩, ta ++ tb ++ tc ++ td⟩ := by
  simp only [Block.eval_seq, ha, hb, hc, hd, hf, Evaluation.bind,
    List.append_nil, List.append_assoc]

theorem interiorMinProgram_source (shape : CartesianShape) (memory : Memory)
    (entry : Block) (hspec : InteriorEntrySpec shape memory entry)
    (hew : entry.WritesOnly InteriorReadWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let execution := (packedMinCandidateComputation shape.size (regs 768)).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers, (interiorMinProgram entry).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      candidateOfRegs 7000 final = execution.value := by
  obtain ⟨r0, he0, hv0, hone, hf0⟩ :=
    interiorMinBaselineProgram_source shape memory entry hspec hew regs hm
  have hm0 : MetadataMatches shape r0 := by
    intro i hi
    rw [hf0 (16 + i) (by simp [InteriorBaselineWrites]; omega)]
    exact hm i hi
  have hi0 : r0 768 = regs 768 := hf0 768 (by simp [InteriorBaselineWrites])
  have hb0 : r0 50 = (packedInteriorOffsets shape.size).minRel := hm0 34 (by decide)
  have hs1 := interiorMinFieldProgram_source shape memory entry hspec hew 50 770
    (by decide) r0 hm0
  simp only [hi0, hb0] at hs1
  obtain ⟨r1, he1, hv1, hf1⟩ := hs1
  have hm1 : MetadataMatches shape r1 := by
    intro i hi
    rw [hf1 (16 + i) (by simp [InteriorFieldWrites]; omega)]
    exact hm0 i hi
  have hi1 : r1 768 = regs 768 := (hf1 768 (by simp [InteriorFieldWrites])).trans hi0
  have hb1 : r1 51 = (packedInteriorOffsets shape.size).maxRel := hm1 35 (by decide)
  have hs2 := interiorMinFieldProgram_source shape memory entry hspec hew 51 771
    (by decide) r1 hm1
  simp only [hi1, hb1] at hs2
  obtain ⟨r2, he2, hv2, hf2⟩ := hs2
  have hm2 : MetadataMatches shape r2 := by
    intro i hi
    rw [hf2 (16 + i) (by simp [InteriorFieldWrites]; omega)]
    exact hm1 i hi
  have hi2 : r2 768 = regs 768 := (hf2 768 (by simp [InteriorFieldWrites])).trans hi1
  have hb2 : r2 52 = (packedInteriorOffsets shape.size).argOffset := hm2 36 (by decide)
  have hs3 := interiorMinFieldProgram_source shape memory entry hspec hew 52 772
    (by decide) r2 hm2
  simp only [hi2, hb2] at hs3
  obtain ⟨r3, he3, hv3, hf3⟩ := hs3
  have h33 : r3 33 = (packedInteriorLayout shape.size).blockSize := by
    rw [hf3 33 (by simp [InteriorFieldWrites])]
    exact hm2 17 (by decide)
  have h35 : r3 35 = (packedInteriorLayout shape.size).blocksPerSuper := by
    rw [hf3 35 (by simp [InteriorFieldWrites])]
    exact hm2 19 (by decide)
  have hi3 : r3 768 = regs 768 := (hf3 768 (by simp [InteriorFieldWrites])).trans hi2
  have h774 : r3 774 = 1 := by
    rw [hf3 774 (by simp [InteriorFieldWrites]),
      hf2 774 (by simp [InteriorFieldWrites]),
      hf1 774 (by simp [InteriorFieldWrites])]
    exact hone
  have hp0 : r3 769 = r0 769 := by
    rw [hf3 769 (by simp [InteriorFieldWrites]),
      hf2 769 (by simp [InteriorFieldWrites]), hf1 769 (by simp [InteriorFieldWrites])]
  have hp1 : r3 770 = r1 770 := by
    rw [hf3 770 (by simp [InteriorFieldWrites]), hf2 770 (by simp [InteriorFieldWrites])]
  have hp2 : r3 771 = r2 771 := hf3 771 (by simp [InteriorFieldWrites])
  have hs := interiorMinFinish_source memory r3 h774
  generalize hef : interiorMinFinish.eval memory ⟨r3, .running⟩ = finished at hs
  rcases finished with ⟨⟨final, status⟩, reads⟩
  dsimp only at hs
  obtain ⟨rfl, rfl, hvalue⟩ := hs
  have hjoin := eval_four_then memory (interiorMinBaselineProgram entry)
    (interiorMinFieldProgram entry 50 770) (interiorMinFieldProgram entry 51 771)
    (interiorMinFieldProgram entry 52 772) interiorMinFinish regs r0 r1 r2 r3 final
    _ _ _ _ he0 he1 he2 he3 hef
  refine ⟨final, ?_, ?_⟩
  · rw [interiorMinProgram, hjoin]
    congr 1
    simp [interiorExecutionReads, packedMinCandidateComputation, packedSummaryComputation,
      FlatStoreComputation.bind_run, FlatStoreExecution.append, List.flatMap_append,
      List.append_assoc]
  · rw [hvalue]
    have hdecode := interiorMinPacketCandidate_decode r3 _ _ _ _
      (hp0.trans hv0) (hp1.trans hv1) (hp2.trans hv2) hv3
    rw [hdecode]
    simp only [h33, h35, hi3, packedMinCandidateComputation,
      FlatStoreComputation.map_run_value, packedSummaryComputation,
      FlatStoreComputation.bind_run, FlatStoreExecution.append]
    rfl

theorem interiorMinBlock_source (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let execution := (packedMinCandidateComputation shape.size (regs 768)).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    let expected := flatStoreExecutionTraceResultAtSegment 20 execution
    let actual := (interiorMinBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  obtain ⟨final, he, hv⟩ := interiorMinProgram_source shape memory (interiorReadBlock reader)
    (interiorReadBlock_spec shape memory reader hr hw) (interiorReadBlock_writes reader hw) regs hm
  dsimp only
  rw [interiorMinBlock, he, logicalTraceReads_flatExecution]
  exact ⟨rfl, hv, rfl, flatExecution_readOnly 20 _⟩



def InteriorCandidateSpec (shape : CartesianShape) (memory : Memory) (program : Block)
    (computation : Registers → FlatStoreComputation (Option (Nat × Nat))) : Prop :=
  ∀ regs, MetadataMatches shape regs →
    let execution := (computation regs).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers, program.eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      candidateOfRegs 7000 final = execution.value

theorem interiorMinBlock_spec (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader) :
    InteriorCandidateSpec shape memory (interiorMinBlock reader)
      (fun regs => packedMinCandidateComputation shape.size (regs 768)) :=
  interiorMinProgram_source shape memory (interiorReadBlock reader)
    (interiorReadBlock_spec shape memory reader hr hw) (interiorReadBlock_writes reader hw)

private theorem optionalReadThenCandidate_source (shape : CartesianShape) (memory : Memory)
    (setup entry selected minimum : Block)
    (he : InteriorEntrySpec shape memory entry) (hew : entry.WritesOnly InteriorReadWrites)
    (hmin : InteriorCandidateSpec shape memory minimum
      (fun regs => packedMinCandidateComputation shape.size (regs 768)))
    (regs prepared : Registers)
    (hp : setup.eval memory ⟨regs, .running⟩ = ⟨⟨prepared, .running⟩, []⟩)
    (hm : MetadataMatches shape prepared)
    (hc : fixedWidthNatTableMachineChunkCount (prepared 705)
      (packedBpCodeWordWidth shape.size) ≤ 7)
    (index : Nat → Nat)
    (hselected : ∀ rr value, rr 708 = value + 1 →
      (∀ r, ¬ InteriorReadWrites r → rr r = prepared r) →
      ∃ sr : Registers, selected.eval memory ⟨rr, .running⟩ =
        ⟨⟨sr, .running⟩, []⟩ ∧ MetadataMatches shape sr ∧ sr 768 = index value) :
    let read := packedInteriorReadNatOf shape.size (prepared 704) (prepared 705)
      (prepared 706) (prepared 707)
    let computation := FlatStoreComputation.bind read (fun result =>
      match result with
      | none => FlatStoreComputation.pure none
      | some value => packedMinCandidateComputation shape.size (index value))
    let execution := computation.run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers,
      (Block.seq setup (.seq entry (.ifZero 708 candidateNoneBlock (.seq selected minimum)))).eval
        memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      candidateOfRegs 7000 final = execution.value := by
  let store := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
  let read := (packedInteriorReadNatOf shape.size (prepared 704) (prepared 705)
    (prepared 706) (prepared 707)).run store
  obtain ⟨rr, her, hpacket⟩ := he prepared hm hc
  have hframe (r : Nat) (hr : ¬ InteriorReadWrites r) : rr r = prepared r := by
    have hf := Block.eval_frame memory entry _ hew r hr ⟨prepared, .running⟩
    rw [her] at hf
    exact hf
  change rr 708 = (read.value.map (· + 1)).getD 0 at hpacket
  cases hvalue : read.value with
  | none =>
      have hval := hvalue
      dsimp only [read, store] at hval
      have hz : rr 708 = 0 := by simpa only [hvalue, Option.map_none, Option.getD_none] using hpacket
      have hn := candidateNoneBlock_source memory rr
      generalize hen : candidateNoneBlock.eval memory ⟨rr, .running⟩ = stopped at hn
      rcases stopped with ⟨⟨final, status⟩, reads⟩
      dsimp only at hn
      obtain ⟨rfl, rfl, hv⟩ := hn
      refine ⟨final, ?_, ?_⟩
      · simp only [Block.eval_seq, hp, Evaluation.bind, her, eval_ifZero, hz, if_true, hen,
          List.nil_append, List.append_nil]
        simp only [FlatStoreComputation.bind_run, hval, FlatStoreComputation.pure_run,
          FlatStoreExecution.append, interiorExecutionReads, List.append_nil]
      · simpa only [FlatStoreComputation.bind_run, hval, FlatStoreComputation.pure_run,
          FlatStoreExecution.append] using hv
  | some value =>
      have hval := hvalue
      dsimp only [read, store] at hval
      have hz : rr 708 = value + 1 := by simpa only [hvalue, Option.map_some, Option.getD_some] using hpacket
      obtain ⟨sr, hs, hsm, hsi⟩ := hselected rr value hz hframe
      have hnext := hmin sr hsm
      simp only [hsi] at hnext
      obtain ⟨final, hmr, hv⟩ := hnext
      refine ⟨final, ?_, ?_⟩
      · simp only [Block.eval_seq, hp, Evaluation.bind, her, eval_ifZero, hz,
          Nat.add_one_ne_zero, if_false, hs, hmr, List.nil_append]
        simp only [FlatStoreComputation.bind_run, hval,
          FlatStoreExecution.append, interiorExecutionReads, List.flatMap_append]
      · simpa only [FlatStoreComputation.bind_run, hval,
          FlatStoreExecution.append] using hv



def interiorLocalSpanPrepared (regs : Registers) : Registers :=
  (((((((regs.write 704 (regs 40 * regs 38)).write 707 (regs 800 * (regs 40 * regs 38))).write
    803 (regs 802 * regs 38)).write 707 (regs 800 * (regs 40 * regs 38) + regs 802 * regs 38)).write
    707 (regs 800 * (regs 40 * regs 38) + regs 802 * regs 38 + regs 801)).write
    704 (regs 39 * (regs 40 * regs 38))).write 705 (regs 43)).write 706 (regs 53)

def interiorGlobalSpanPrepared (regs : Registers) : Registers :=
  ((((regs.write 704 (regs 41 * regs 39)).write 705 (regs 44)).write
    706 (regs 54)).write 707 (regs 817 * regs 39)).write 707 (regs 817 * regs 39 + regs 816)

def interiorLocalSpanSelected (regs : Registers) : Registers :=
  ((((regs.write 804 1).write 768 (regs 800 * regs 38)).write
    768 (regs 800 * regs 38 + regs 708)).write 803
      (Comparison.le.eval 1 (regs 800 * regs 38 + regs 708))).write
    768 (regs 800 * regs 38 + regs 708 - 1)

def interiorGlobalSpanSelected (regs : Registers) : Registers :=
  ((regs.write 818 1).write 819 (Comparison.le.eval 1 (regs 708))).write 768 (regs 708 - 1)

theorem interiorLocalSpanPrefix_source (memory : Memory) (regs : Registers) :
    interiorLocalSpanPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorLocalSpanPrepared regs, .running⟩, []⟩ := by
  simp [interiorLocalSpanPrefix, interiorLocalSpanPrepared, Block.sequence, Block.eval_seq,
    eval_move, eval_arithmetic, eval_skip, Evaluation.bind, Registers.write, Arithmetic.eval]

theorem interiorGlobalSpanPrefix_source (memory : Memory) (regs : Registers) :
    interiorGlobalSpanPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorGlobalSpanPrepared regs, .running⟩, []⟩ := by
  simp [interiorGlobalSpanPrefix, interiorGlobalSpanPrepared, Block.sequence, Block.eval_seq,
    eval_move, eval_arithmetic, eval_skip, Evaluation.bind, Registers.write, Arithmetic.eval]

theorem interiorLocalSpanSelectedPrefix_source (memory : Memory) (regs : Registers) :
    interiorLocalSpanSelectedPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorLocalSpanSelected regs, .running⟩, []⟩ := by
  simp [interiorLocalSpanSelectedPrefix, interiorLocalSpanSelected, Block.sequence, Block.eval_seq,
    eval_constant, eval_arithmetic, natSubBlock_source, eval_skip, Evaluation.bind,
    Registers.write, Arithmetic.eval]

theorem interiorGlobalSpanSelectedPrefix_source (memory : Memory) (regs : Registers) :
    interiorGlobalSpanSelectedPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorGlobalSpanSelected regs, .running⟩, []⟩ := by
  simp [interiorGlobalSpanSelectedPrefix, interiorGlobalSpanSelected, Block.sequence, Block.eval_seq,
    eval_constant, natSubBlock_source, eval_skip, Evaluation.bind, Registers.write]

theorem interiorLocalSpanProgram_source (shape : CartesianShape) (memory : Memory)
    (entry minimum : Block) (he : InteriorEntrySpec shape memory entry)
    (hew : entry.WritesOnly InteriorReadWrites)
    (hmin : InteriorCandidateSpec shape memory minimum
      (fun regs => packedMinCandidateComputation shape.size (regs 768))) :
    InteriorCandidateSpec shape memory (interiorLocalSpanProgram entry minimum)
      (fun regs => packedLocalSpanCandidateComputation shape.size (regs 800) (regs 801) (regs 802)) := by
  intro regs hm
  have h38 : regs 38 = (packedInteriorLayout shape.size).macroSize := hm 22 (by decide)
  have h39 : regs 39 = (packedInteriorLayout shape.size).macroSampleCount := hm 23 (by decide)
  have h40 : regs 40 = (packedInteriorLayout shape.size).levelCount := hm 24 (by decide)
  have h43 : regs 43 = (packedInteriorLayout shape.size).offsetWidth := hm 27 (by decide)
  have h53 : regs 53 = (packedInteriorOffsets shape.size).localOffset := hm 37 (by decide)
  have hpm : MetadataMatches shape (interiorLocalSpanPrepared regs) := by
    intro i hi
    simpa [interiorLocalSpanPrepared, Registers.write,
      show 16 + i ≠ 704 by omega, show 16 + i ≠ 705 by omega,
      show 16 + i ≠ 706 by omega, show 16 + i ≠ 707 by omega,
      show 16 + i ≠ 803 by omega] using hm i hi
  have hc : fixedWidthNatTableMachineChunkCount ((interiorLocalSpanPrepared regs) 705)
      (packedBpCodeWordWidth shape.size) ≤ 7 := by
    simpa [interiorLocalSpanPrepared, Registers.write, h43, packedReviewerInteriorEntryWidth] using
      canonical_interior_chunks_le_seven shape .localOffset
  have hs := optionalReadThenCandidate_source shape memory
    interiorLocalSpanPrefix entry interiorLocalSpanSelectedPrefix minimum he hew hmin
    regs (interiorLocalSpanPrepared regs) (interiorLocalSpanPrefix_source memory regs)
    hpm hc (fun value => regs 800 * (packedInteriorLayout shape.size).macroSize + value) (by
      intro rr value hp hf
      have hrr800 : rr 800 = regs 800 := by
        simpa [interiorLocalSpanPrepared, Registers.write] using hf 800 (by simp [InteriorReadWrites])
      have hrr38 : rr 38 = (packedInteriorLayout shape.size).macroSize := by
        simpa [interiorLocalSpanPrepared, Registers.write, h38] using hf 38 (by simp [InteriorReadWrites])
      have hmr : MetadataMatches shape rr := by
        intro i hi
        rw [hf (16 + i) (by simp [InteriorReadWrites]; omega)]
        exact hpm i hi
      refine ⟨interiorLocalSpanSelected rr, interiorLocalSpanSelectedPrefix_source memory rr, ?_, ?_⟩
      · intro i hi
        simpa [interiorLocalSpanSelected, Registers.write,
          show 16 + i ≠ 768 by omega, show 16 + i ≠ 803 by omega,
          show 16 + i ≠ 804 by omega] using hmr i hi
      · simp [interiorLocalSpanSelected, Registers.write, hp, hrr800, hrr38])
  have href : FlatStoreComputation.bind
      (packedInteriorReadNatOf shape.size ((interiorLocalSpanPrepared regs) 704)
        ((interiorLocalSpanPrepared regs) 705) ((interiorLocalSpanPrepared regs) 706)
        ((interiorLocalSpanPrepared regs) 707))
      (fun result => match result with
        | none => FlatStoreComputation.pure none
        | some value => packedMinCandidateComputation shape.size
            (regs 800 * (packedInteriorLayout shape.size).macroSize + value)) =
      packedLocalSpanCandidateComputation shape.size (regs 800) (regs 801) (regs 802) := by
    simp [interiorLocalSpanPrepared, Registers.write, h38, h39, h40, h43, h53,
      packedLocalSpanCandidateComputation, bpLocalSparseCellSlot]
    congr 1
    funext result
    cases result <;> rfl
  dsimp only at hs ⊢
  rw [href] at hs
  exact hs

theorem interiorGlobalSpanProgram_source (shape : CartesianShape) (memory : Memory)
    (entry minimum : Block) (he : InteriorEntrySpec shape memory entry)
    (hew : entry.WritesOnly InteriorReadWrites)
    (hmin : InteriorCandidateSpec shape memory minimum
      (fun regs => packedMinCandidateComputation shape.size (regs 768))) :
    InteriorCandidateSpec shape memory (interiorGlobalSpanProgram entry minimum)
      (fun regs => packedGlobalSpanCandidateComputation shape.size (regs 816) (regs 817)) := by
  intro regs hm
  have h39 : regs 39 = (packedInteriorLayout shape.size).macroSampleCount := hm 23 (by decide)
  have h41 : regs 41 = (packedInteriorLayout shape.size).globalLevelCount := hm 25 (by decide)
  have h44 : regs 44 = (packedInteriorLayout shape.size).blockAddressWidth := hm 28 (by decide)
  have h54 : regs 54 = (packedInteriorOffsets shape.size).globalBlock := hm 38 (by decide)
  have hpm : MetadataMatches shape (interiorGlobalSpanPrepared regs) := by
    intro i hi
    simpa [interiorGlobalSpanPrepared, Registers.write,
      show 16 + i ≠ 704 by omega, show 16 + i ≠ 705 by omega,
      show 16 + i ≠ 706 by omega, show 16 + i ≠ 707 by omega] using hm i hi
  have hc : fixedWidthNatTableMachineChunkCount ((interiorGlobalSpanPrepared regs) 705)
      (packedBpCodeWordWidth shape.size) ≤ 7 := by
    simpa [interiorGlobalSpanPrepared, Registers.write, h44, packedReviewerInteriorEntryWidth] using
      canonical_interior_chunks_le_seven shape .globalBlock
  have hs := optionalReadThenCandidate_source shape memory
    interiorGlobalSpanPrefix entry interiorGlobalSpanSelectedPrefix minimum he hew hmin
    regs (interiorGlobalSpanPrepared regs) (interiorGlobalSpanPrefix_source memory regs)
    hpm hc id (by
      intro rr value hp hf
      have hmr : MetadataMatches shape rr := by
        intro i hi
        rw [hf (16 + i) (by simp [InteriorReadWrites]; omega)]
        exact hpm i hi
      refine ⟨interiorGlobalSpanSelected rr, interiorGlobalSpanSelectedPrefix_source memory rr, ?_, ?_⟩
      · intro i hi
        simpa [interiorGlobalSpanSelected, Registers.write,
          show 16 + i ≠ 768 by omega, show 16 + i ≠ 818 by omega,
          show 16 + i ≠ 819 by omega] using hmr i hi
      · simp [interiorGlobalSpanSelected, Registers.write, hp])
  have href : FlatStoreComputation.bind
      (packedInteriorReadNatOf shape.size ((interiorGlobalSpanPrepared regs) 704)
        ((interiorGlobalSpanPrepared regs) 705) ((interiorGlobalSpanPrepared regs) 706)
        ((interiorGlobalSpanPrepared regs) 707))
      (fun result => match result with
        | none => FlatStoreComputation.pure none
        | some value => packedMinCandidateComputation shape.size (id value)) =
      packedGlobalSpanCandidateComputation shape.size (regs 816) (regs 817) := by
    simp [interiorGlobalSpanPrepared, Registers.write, h39, h41, h44, h54,
      packedGlobalSpanCandidateComputation, bpGlobalSparseCellSlot]
    congr 1
    funext result
    cases result <;> rfl
  dsimp only at hs ⊢
  rw [href] at hs
  exact hs



theorem candidateSaveBlock_writes (base : Nat) :
    (candidateSaveBlock base).WritesOnly (fun r => base ≤ r ∧ r < base + 3) := by
  simp [candidateSaveBlock, Block.sequence, Block.WritesOnly, Action.destination]

theorem candidateSaveBlock_frame (base : Nat) (memory : Memory) (s : Data)
    (r : Nat) (hr : r < base ∨ base + 3 ≤ r) :
    ((candidateSaveBlock base).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (candidateSaveBlock_writes base) r (by omega) s

private theorem candidateSaveBlock_result (base : Nat) (hb : base + 3 ≤ 7000)
    (memory : Memory) (regs : Registers) :
    ∃ final : Registers, (candidateSaveBlock base).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, []⟩ ∧
      candidateOfRegs base final = candidateOfRegs 7000 regs ∧
      (∀ r, r < base ∨ base + 3 ≤ r → final r = regs r) := by
  have hs := candidateSaveBlock_source base hb memory regs
  generalize he : (candidateSaveBlock base).eval memory ⟨regs, .running⟩ = actual at hs
  rcases actual with ⟨⟨final, status⟩, reads⟩
  dsimp only at hs
  obtain ⟨rfl, rfl, hp, _⟩ := hs
  refine ⟨final, rfl, hp, ?_⟩
  intro r hr
  have hf := candidateSaveBlock_frame base memory ⟨regs, .running⟩ r hr
  rw [he] at hf
  exact hf

private theorem candidateMergeLeftBlock_result (base : Nat) (hb : base + 3 ≤ 7000)
    (memory : Memory) (regs : Registers) :
    ∃ final : Registers, (candidateMergeLeftBlock base).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, []⟩ ∧
      candidateOfRegs 7000 final =
        bpCandidateMerge? (candidateOfRegs base regs) (candidateOfRegs 7000 regs) := by
  have hs := candidateMergeLeftBlock_source base hb memory regs
  generalize he : (candidateMergeLeftBlock base).eval memory ⟨regs, .running⟩ = actual at hs
  rcases actual with ⟨⟨final, status⟩, reads⟩
  dsimp only at hs
  obtain ⟨rfl, rfl, hp⟩ := hs
  exact ⟨final, rfl, hp⟩

theorem candidateOfRegs_frame (base : Nat) (before after : Registers)
    (h : ∀ r, base ≤ r → r < base + 3 → after r = before r) :
    candidateOfRegs base after = candidateOfRegs base before := by
  simp only [candidateOfRegs, h base (by omega) (by omega),
    h (base + 1) (by omega) (by omega), h (base + 2) (by omega) (by omega)]



private theorem candidateTwoCalls_source (shape : CartesianShape) (memory : Memory)
    (firstPrep secondPrep span : Block) (base : Nat) (hb : base + 3 ≤ 7000)
    (allowed : Nat → Prop) (hspanWrites : span.WritesOnly allowed)
    (hfree : ∀ r, base ≤ r → r < base + 3 → ¬ allowed r)
    (computation : Registers → FlatStoreComputation (Option (Nat × Nat)))
    (hspan : InteriorCandidateSpec shape memory span computation)
    (regs first : Registers) (hp : firstPrep.eval memory ⟨regs, .running⟩ =
      ⟨⟨first, .running⟩, []⟩) (hm : MetadataMatches shape first)
    (left right : FlatStoreExecution (Option (Nat × Nat)))
    (hl : (computation first).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20) = left)
    (hsecond : ∀ saved,
      (∀ r, ¬ allowed r → (r < base ∨ base + 3 ≤ r) → saved r = first r) →
      ∃ second : Registers,
        secondPrep.eval memory ⟨saved, .running⟩ = ⟨⟨second, .running⟩, []⟩ ∧
        MetadataMatches shape second ∧
        (computation second).run
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20) = right ∧
        candidateOfRegs base second = candidateOfRegs base saved) :
    ∃ final : Registers,
      (Block.seq firstPrep (.seq span (.seq (candidateSaveBlock base)
        (.seq secondPrep (.seq span (candidateMergeLeftBlock base)))))).eval
          memory ⟨regs, .running⟩ =
        ⟨⟨final, .running⟩, interiorExecutionReads shape memory left ++
          interiorExecutionReads shape memory right⟩ ∧
      candidateOfRegs 7000 final = bpCandidateMerge? left.value right.value := by
  have hleft := hspan first hm
  dsimp only at hleft
  rw [hl] at hleft
  obtain ⟨lr, hel, hvl⟩ := hleft
  have hlf (r : Nat) (hr : ¬ allowed r) : lr r = first r := by
    have hf := Block.eval_frame memory span allowed hspanWrites r hr ⟨first, .running⟩
    rw [hel] at hf
    exact hf
  obtain ⟨saved, hes, hvs, hsf⟩ := candidateSaveBlock_result base hb memory lr
  obtain ⟨second, hep, hmp, hcomp, hsaved⟩ :=
    hsecond saved (by intro r hr hbr; exact (hsf r hbr).trans (hlf r hr))
  have hright := hspan second hmp
  dsimp only at hright
  rw [hcomp] at hright
  obtain ⟨rr, her, hvr⟩ := hright
  have hrkeep : candidateOfRegs base rr = candidateOfRegs base second := by
    apply candidateOfRegs_frame
    intro r hbr hbr'
    have hf := Block.eval_frame memory span allowed hspanWrites r (hfree r hbr hbr') ⟨second, .running⟩
    rw [her] at hf
    exact hf
  obtain ⟨final, hem, hvm⟩ := candidateMergeLeftBlock_result base hb memory rr
  refine ⟨final, ?_, ?_⟩
  · simp only [Block.eval_seq, hp, hel, hes, hep, her, hem, Evaluation.bind,
      List.nil_append, List.append_nil]
  · rw [hvm, hrkeep, hsaved, hvs, hvl, hvr]



private theorem optionalReadChoice_source (shape : CartesianShape) (memory : Memory)
    (setup entry chosen : Block)
    (he : InteriorEntrySpec shape memory entry) (hew : entry.WritesOnly InteriorReadWrites)
    (regs prepared : Registers)
    (hp : setup.eval memory ⟨regs, .running⟩ = ⟨⟨prepared, .running⟩, []⟩)
    (hm : MetadataMatches shape prepared)
    (hc : fixedWidthNatTableMachineChunkCount (prepared 705)
      (packedBpCodeWordWidth shape.size) ≤ 7)
    (next : Nat → FlatStoreComputation (Option (Nat × Nat)))
    (hchosen : ∀ rr value, rr 708 = value + 1 →
      (∀ r, ¬ InteriorReadWrites r → rr r = prepared r) →
      let execution := (next value).run
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
      ∃ final : Registers, chosen.eval memory ⟨rr, .running⟩ =
        ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
        candidateOfRegs 7000 final = execution.value) :
    let read := packedInteriorReadNatOf shape.size (prepared 704) (prepared 705)
      (prepared 706) (prepared 707)
    let computation := FlatStoreComputation.bind read (fun result =>
      match result with
      | none => FlatStoreComputation.pure none
      | some value => next value)
    let execution := computation.run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers,
      (Block.seq setup (.seq entry (.ifZero 708 candidateNoneBlock chosen))).eval
        memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      candidateOfRegs 7000 final = execution.value := by
  let store := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
  let read := (packedInteriorReadNatOf shape.size (prepared 704) (prepared 705)
    (prepared 706) (prepared 707)).run store
  obtain ⟨rr, her, hpacket⟩ := he prepared hm hc
  have hframe (r : Nat) (hr : ¬ InteriorReadWrites r) : rr r = prepared r := by
    have hf := Block.eval_frame memory entry _ hew r hr ⟨prepared, .running⟩
    rw [her] at hf
    exact hf
  change rr 708 = (read.value.map (· + 1)).getD 0 at hpacket
  cases hvalue : read.value with
  | none =>
      have hval := hvalue
      dsimp only [read, store] at hval
      have hz : rr 708 = 0 := by simpa only [hvalue, Option.map_none, Option.getD_none] using hpacket
      have hn := candidateNoneBlock_source memory rr
      generalize hen : candidateNoneBlock.eval memory ⟨rr, .running⟩ = stopped at hn
      rcases stopped with ⟨⟨final, status⟩, reads⟩
      dsimp only at hn
      obtain ⟨rfl, rfl, hv⟩ := hn
      refine ⟨final, ?_, ?_⟩
      · simp only [Block.eval_seq, hp, Evaluation.bind, her, eval_ifZero, hz, if_true, hen,
          List.nil_append, List.append_nil]
        simp only [FlatStoreComputation.bind_run, hval, FlatStoreComputation.pure_run,
          FlatStoreExecution.append, interiorExecutionReads, List.append_nil]
      · simpa only [FlatStoreComputation.bind_run, hval, FlatStoreComputation.pure_run,
          FlatStoreExecution.append] using hv
  | some value =>
      have hval := hvalue
      dsimp only [read, store] at hval
      have hz : rr 708 = value + 1 := by simpa only [hvalue, Option.map_some, Option.getD_some] using hpacket
      obtain ⟨final, hchoice, hv⟩ := hchosen rr value hz hframe
      refine ⟨final, ?_, ?_⟩
      · simp only [Block.eval_seq, hp, Evaluation.bind, her, eval_ifZero, hz,
          Nat.add_one_ne_zero, if_false, hchoice, List.nil_append]
        simp only [FlatStoreComputation.bind_run, hval,
          FlatStoreExecution.append, interiorExecutionReads, List.flatMap_append]
      · simpa only [FlatStoreComputation.bind_run, hval,
          FlatStoreExecution.append] using hv



def interiorLocalTwoPrepared (regs : Registers) : Registers :=
  (((regs.write 704 (regs 45)).write 705 (regs 47)).write 706 (regs 55)).write 707 (regs 834)

def interiorGlobalTwoPrepared (regs : Registers) : Registers :=
  (((regs.write 704 (regs 46)).write 705 (regs 48)).write 706 (regs 56)).write 707 (regs 865)

def interiorLocalTwoFirst (regs : Registers) : Registers :=
  (((((((regs.write 843 1).write 844 (Comparison.le.eval 1 (regs 708))).write
    835 (regs 708 - 1)).write 836 ((regs 708 - 1) / regs 45)).write
    837 ((regs 708 - 1) % regs 45)).write 800 (regs 832)).write 801 (regs 833)).write
    802 ((regs 708 - 1) / regs 45)

def interiorLocalTwoSecond (regs : Registers) : Registers :=
  ((((regs.write 800 (regs 832)).write 801 (regs 833 + regs 834)).write
    844 (Comparison.le.eval (regs 837) (regs 833 + regs 834))).write
    801 (regs 833 + regs 834 - regs 837)).write 802 (regs 836)

def interiorGlobalTwoFirst (regs : Registers) : Registers :=
  ((((((regs.write 875 1).write 876 (Comparison.le.eval 1 (regs 708))).write
    866 (regs 708 - 1)).write 867 ((regs 708 - 1) / regs 46)).write
    868 ((regs 708 - 1) % regs 46)).write 816 (regs 864)).write
    817 ((regs 708 - 1) / regs 46)

def interiorGlobalTwoSecond (regs : Registers) : Registers :=
  (((regs.write 816 (regs 864 + regs 865)).write
    876 (Comparison.le.eval (regs 868) (regs 864 + regs 865))).write
    816 (regs 864 + regs 865 - regs 868)).write 817 (regs 867)


theorem interiorLocalTwoPrefix_source (memory : Memory) (regs : Registers) :
    interiorLocalTwoPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorLocalTwoPrepared regs, .running⟩, []⟩ := by
  simp [interiorLocalTwoPrefix, interiorLocalTwoPrepared, Block.sequence, Block.eval_seq,
    eval_move, eval_skip, Evaluation.bind, Registers.write]

theorem interiorGlobalTwoPrefix_source (memory : Memory) (regs : Registers) :
    interiorGlobalTwoPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorGlobalTwoPrepared regs, .running⟩, []⟩ := by
  simp [interiorGlobalTwoPrefix, interiorGlobalTwoPrepared, Block.sequence, Block.eval_seq,
    eval_move, eval_skip, Evaluation.bind, Registers.write]

theorem interiorLocalTwoFirstPrefix_source (memory : Memory) (regs : Registers) :
    interiorLocalTwoFirstPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorLocalTwoFirst regs, .running⟩, []⟩ := by
  simp [interiorLocalTwoFirstPrefix, interiorLocalTwoFirst, Block.sequence, Block.eval_seq,
    eval_move, eval_constant, eval_arithmetic, natSubBlock_source, eval_skip, Evaluation.bind, Registers.write, Arithmetic.eval]

theorem interiorGlobalTwoFirstPrefix_source (memory : Memory) (regs : Registers) :
    interiorGlobalTwoFirstPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorGlobalTwoFirst regs, .running⟩, []⟩ := by
  simp [interiorGlobalTwoFirstPrefix, interiorGlobalTwoFirst, Block.sequence, Block.eval_seq,
    eval_move, eval_constant, eval_arithmetic, natSubBlock_source, eval_skip, Evaluation.bind, Registers.write, Arithmetic.eval]

theorem interiorLocalTwoSecondPrefix_source (memory : Memory) (regs : Registers) :
    interiorLocalTwoSecondPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorLocalTwoSecond regs, .running⟩, []⟩ := by
  simp [interiorLocalTwoSecondPrefix, interiorLocalTwoSecond, Block.sequence, Block.eval_seq,
    eval_move, eval_arithmetic, natSubBlock_source, eval_skip, Evaluation.bind, Registers.write, Arithmetic.eval]

theorem interiorGlobalTwoSecondPrefix_source (memory : Memory) (regs : Registers) :
    interiorGlobalTwoSecondPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorGlobalTwoSecond regs, .running⟩, []⟩ := by
  simp [interiorGlobalTwoSecondPrefix, interiorGlobalTwoSecond, Block.sequence, Block.eval_seq,
    eval_move, eval_arithmetic, natSubBlock_source, eval_skip, Evaluation.bind, Registers.write, Arithmetic.eval]


private theorem flatBindMap_run (first : FlatStoreComputation α)
    (second : FlatStoreComputation β) (combine : α → β → γ) (store : FlatWordStore) :
    (FlatStoreComputation.bind first (fun left =>
      FlatStoreComputation.map (combine left) second)).run store =
      ⟨combine (first.run store).value (second.run store).value,
        (first.run store).reads ++ (second.run store).reads⟩ := by
  rw [FlatStoreComputation.bind_run]
  simp only [FlatStoreExecution.append, FlatStoreComputation.map_run_value,
    FlatStoreComputation.map_run_reads]


theorem interiorLocalTwoSelectedProgram_source (shape : CartesianShape) (memory : Memory)
    (span : Block)
    (hspan : InteriorCandidateSpec shape memory span
      (fun regs => packedLocalSpanCandidateComputation shape.size (regs 800) (regs 801) (regs 802)))
    (hw : span.WritesOnly InteriorLocalSpanWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let domain := bpSparseLevelDomain (packedInteriorLayout shape.size).macroSize
    let value := regs 708 - 1
    let computation := FlatStoreComputation.bind
      (packedLocalSpanCandidateComputation shape.size (regs 832) (regs 833) (value / domain))
      (fun left => FlatStoreComputation.map (fun right => bpCandidateMerge? left right)
        (packedLocalSpanCandidateComputation shape.size (regs 832)
          (regs 833 + regs 834 - value % domain) (value / domain)))
    let execution := computation.run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers, (interiorLocalTwoSelectedProgram span).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      candidateOfRegs 7000 final = execution.value := by
  let domain := bpSparseLevelDomain (packedInteriorLayout shape.size).macroSize
  let store := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
  let left := (packedLocalSpanCandidateComputation shape.size (regs 832) (regs 833)
    ((regs 708 - 1) / domain)).run store
  let right := (packedLocalSpanCandidateComputation shape.size (regs 832)
    (regs 833 + regs 834 - (regs 708 - 1) % domain) ((regs 708 - 1) / domain)).run store
  have hd : regs 45 = domain := hm 29 (by decide)
  have hmf : MetadataMatches shape (interiorLocalTwoFirst regs) := by
    intro i hi
    simpa [interiorLocalTwoFirst, Registers.write,
      show 16 + i ≠ 843 by omega, show 16 + i ≠ 844 by omega,
      show 16 + i ≠ 835 by omega, show 16 + i ≠ 836 by omega,
      show 16 + i ≠ 837 by omega, show 16 + i ≠ 800 by omega,
      show 16 + i ≠ 801 by omega, show 16 + i ≠ 802 by omega] using hm i hi
  have hs := candidateTwoCalls_source shape memory
    interiorLocalTwoFirstPrefix interiorLocalTwoSecondPrefix span 840 (by decide)
    InteriorLocalSpanWrites hw
    (by intro r h0 h1; unfold InteriorLocalSpanWrites InteriorMinWrites; omega)
    (fun rs => packedLocalSpanCandidateComputation shape.size (rs 800) (rs 801) (rs 802))
    hspan regs (interiorLocalTwoFirst regs) (interiorLocalTwoFirstPrefix_source memory regs)
    hmf left right (by simp [interiorLocalTwoFirst, Registers.write, hd, left, store]) (by
      intro saved hf
      have hk (r : Nat) (hr : r < 704 ∨ r = 832 ∨ r = 833 ∨ r = 834 ∨ r = 836 ∨ r = 837) :
          saved r = (interiorLocalTwoFirst regs) r :=
        hf r (by unfold InteriorLocalSpanWrites InteriorMinWrites; omega) (by omega)
      have hms : MetadataMatches shape saved := by
        intro i hi
        rw [hk (16 + i) (by omega)]
        exact hmf i hi
      refine ⟨interiorLocalTwoSecond saved, interiorLocalTwoSecondPrefix_source memory saved, ?_, ?_, ?_⟩
      · intro i hi
        simpa [interiorLocalTwoSecond, Registers.write,
          show 16 + i ≠ 800 by omega, show 16 + i ≠ 801 by omega,
          show 16 + i ≠ 802 by omega, show 16 + i ≠ 844 by omega] using hms i hi
      · simp only [interiorLocalTwoSecond, Registers.write, reduceIte,
          hk 832 (by omega), hk 833 (by omega), hk 834 (by omega),
          hk 836 (by omega), hk 837 (by omega)]
        simp [interiorLocalTwoFirst, Registers.write, hd, right, store]
      · simp [candidateOfRegs, interiorLocalTwoSecond, Registers.write])
  dsimp only at hs ⊢
  rw [flatBindMap_run]
  obtain ⟨final, he, hv⟩ := hs
  refine ⟨final, ?_, hv⟩
  exact he.trans (congrArg (fun receipts => Evaluation.mk ⟨final, .running⟩ receipts)
    (by simp only [interiorExecutionReads, List.flatMap_append]; rfl))



theorem interiorGlobalTwoSelectedProgram_source (shape : CartesianShape) (memory : Memory)
    (span : Block)
    (hspan : InteriorCandidateSpec shape memory span
      (fun regs => packedGlobalSpanCandidateComputation shape.size (regs 816) (regs 817)))
    (hw : span.WritesOnly InteriorGlobalSpanWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let domain := bpSparseLevelDomain (packedInteriorLayout shape.size).macroSampleCount
    let value := regs 708 - 1
    let computation := FlatStoreComputation.bind
      (packedGlobalSpanCandidateComputation shape.size (regs 864) (value / domain))
      (fun left => FlatStoreComputation.map (fun right => bpCandidateMerge? left right)
        (packedGlobalSpanCandidateComputation shape.size
          (regs 864 + regs 865 - value % domain) (value / domain)))
    let execution := computation.run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers, (interiorGlobalTwoSelectedProgram span).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      candidateOfRegs 7000 final = execution.value := by
  let domain := bpSparseLevelDomain (packedInteriorLayout shape.size).macroSampleCount
  let store := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
  let left := (packedGlobalSpanCandidateComputation shape.size (regs 864)
    ((regs 708 - 1) / domain)).run store
  let right := (packedGlobalSpanCandidateComputation shape.size
    (regs 864 + regs 865 - (regs 708 - 1) % domain) ((regs 708 - 1) / domain)).run store
  have hd : regs 46 = domain := hm 30 (by decide)
  have hmf : MetadataMatches shape (interiorGlobalTwoFirst regs) := by
    intro i hi
    simpa [interiorGlobalTwoFirst, Registers.write,
      show 16 + i ≠ 875 by omega, show 16 + i ≠ 876 by omega,
      show 16 + i ≠ 866 by omega, show 16 + i ≠ 867 by omega,
      show 16 + i ≠ 868 by omega, show 16 + i ≠ 816 by omega,
      show 16 + i ≠ 817 by omega] using hm i hi
  have hs := candidateTwoCalls_source shape memory
    interiorGlobalTwoFirstPrefix interiorGlobalTwoSecondPrefix span 872 (by decide)
    InteriorGlobalSpanWrites hw
    (by intro r h0 h1; unfold InteriorGlobalSpanWrites InteriorMinWrites; omega)
    (fun rs => packedGlobalSpanCandidateComputation shape.size (rs 816) (rs 817))
    hspan regs (interiorGlobalTwoFirst regs) (interiorGlobalTwoFirstPrefix_source memory regs)
    hmf left right (by simp [interiorGlobalTwoFirst, Registers.write, hd, left, store]) (by
      intro saved hf
      have hk (r : Nat) (hr : r < 704 ∨ r = 864 ∨ r = 865 ∨ r = 867 ∨ r = 868) :
          saved r = (interiorGlobalTwoFirst regs) r :=
        hf r (by unfold InteriorGlobalSpanWrites InteriorMinWrites; omega) (by omega)
      have hms : MetadataMatches shape saved := by
        intro i hi
        rw [hk (16 + i) (by omega)]
        exact hmf i hi
      refine ⟨interiorGlobalTwoSecond saved, interiorGlobalTwoSecondPrefix_source memory saved, ?_, ?_, ?_⟩
      · intro i hi
        simpa [interiorGlobalTwoSecond, Registers.write,
          show 16 + i ≠ 816 by omega, show 16 + i ≠ 817 by omega,
          show 16 + i ≠ 876 by omega] using hms i hi
      · simp only [interiorGlobalTwoSecond, Registers.write, reduceIte,
          hk 864 (by omega), hk 865 (by omega), hk 867 (by omega), hk 868 (by omega)]
        simp [interiorGlobalTwoFirst, Registers.write, hd, right, store]
      · simp [candidateOfRegs, interiorGlobalTwoSecond, Registers.write])
  dsimp only at hs ⊢
  rw [flatBindMap_run]
  obtain ⟨final, he, hv⟩ := hs
  refine ⟨final, ?_, hv⟩
  exact he.trans (congrArg (fun receipts => Evaluation.mk ⟨final, .running⟩ receipts)
    (by simp only [interiorExecutionReads, List.flatMap_append]; rfl))



theorem interiorLocalTwoProgram_source (shape : CartesianShape) (memory : Memory)
    (entry span : Block) (he : InteriorEntrySpec shape memory entry)
    (hew : entry.WritesOnly InteriorReadWrites)
    (hspan : InteriorCandidateSpec shape memory span
      (fun regs => packedLocalSpanCandidateComputation shape.size (regs 800) (regs 801) (regs 802)))
    (hw : span.WritesOnly InteriorLocalSpanWrites) :
    InteriorCandidateSpec shape memory (interiorLocalTwoProgram entry span)
      (fun regs => packedLocalTwoSpanCandidateComputation shape.size (regs 832) (regs 833) (regs 834)) := by
  intro regs hm
  let domain := bpSparseLevelDomain (packedInteriorLayout shape.size).macroSize
  let next (value : Nat) := FlatStoreComputation.bind
    (packedLocalSpanCandidateComputation shape.size (regs 832) (regs 833) (value / domain))
    (fun left => FlatStoreComputation.map (fun right => bpCandidateMerge? left right)
      (packedLocalSpanCandidateComputation shape.size (regs 832)
        (regs 833 + regs 834 - value % domain) (value / domain)))
  have h45 : regs 45 = domain := hm 29 (by decide)
  have h47 : regs 47 = bpSparseLevelWidth domain := hm 31 (by decide)
  have h55 : regs 55 = (packedInteriorOffsets shape.size).localLevel := hm 39 (by decide)
  have hpm : MetadataMatches shape (interiorLocalTwoPrepared regs) := by
    intro i hi
    simpa [interiorLocalTwoPrepared, Registers.write,
      show 16 + i ≠ 704 by omega, show 16 + i ≠ 705 by omega,
      show 16 + i ≠ 706 by omega, show 16 + i ≠ 707 by omega] using hm i hi
  have hc : fixedWidthNatTableMachineChunkCount ((interiorLocalTwoPrepared regs) 705)
      (packedBpCodeWordWidth shape.size) ≤ 7 := by
    simpa [interiorLocalTwoPrepared, Registers.write, h47, domain, packedReviewerInteriorEntryWidth] using
      canonical_interior_chunks_le_seven shape .localLevel
  have hs := optionalReadChoice_source shape memory
    interiorLocalTwoPrefix entry (interiorLocalTwoSelectedProgram span) he hew
    regs (interiorLocalTwoPrepared regs) (interiorLocalTwoPrefix_source memory regs)
    hpm hc next (by
      intro rr value hp hf
      have hmr : MetadataMatches shape rr := by
        intro i hi
        rw [hf (16 + i) (by simp [InteriorReadWrites]; omega)]
        exact hpm i hi
      have h832 : rr 832 = regs 832 := by
        simpa [interiorLocalTwoPrepared, Registers.write] using hf 832 (by simp [InteriorReadWrites])
      have h833 : rr 833 = regs 833 := by
        simpa [interiorLocalTwoPrepared, Registers.write] using hf 833 (by simp [InteriorReadWrites])
      have h834 : rr 834 = regs 834 := by
        simpa [interiorLocalTwoPrepared, Registers.write] using hf 834 (by simp [InteriorReadWrites])
      have hchoice := interiorLocalTwoSelectedProgram_source shape memory span hspan hw rr hmr
      simpa only [hp, Nat.add_sub_cancel, h832, h833, h834, next, domain] using hchoice)
  have href : FlatStoreComputation.bind
      (packedInteriorReadNatOf shape.size ((interiorLocalTwoPrepared regs) 704)
        ((interiorLocalTwoPrepared regs) 705) ((interiorLocalTwoPrepared regs) 706)
        ((interiorLocalTwoPrepared regs) 707))
      (fun result => match result with
        | none => FlatStoreComputation.pure none
        | some value => next value) =
      packedLocalTwoSpanCandidateComputation shape.size (regs 832) (regs 833) (regs 834) := by
    simp [interiorLocalTwoPrepared, Registers.write, h45, h47, h55,
      packedLocalTwoSpanCandidateComputation, next, domain]
    congr 1
    funext result
    cases result <;> rfl
  dsimp only at hs ⊢
  rw [href] at hs
  exact hs

theorem interiorGlobalTwoProgram_source (shape : CartesianShape) (memory : Memory)
    (entry span : Block) (he : InteriorEntrySpec shape memory entry)
    (hew : entry.WritesOnly InteriorReadWrites)
    (hspan : InteriorCandidateSpec shape memory span
      (fun regs => packedGlobalSpanCandidateComputation shape.size (regs 816) (regs 817)))
    (hw : span.WritesOnly InteriorGlobalSpanWrites) :
    InteriorCandidateSpec shape memory (interiorGlobalTwoProgram entry span)
      (fun regs => packedGlobalTwoSpanCandidateComputation shape.size (regs 864) (regs 865)) := by
  intro regs hm
  let domain := bpSparseLevelDomain (packedInteriorLayout shape.size).macroSampleCount
  let next (value : Nat) := FlatStoreComputation.bind
    (packedGlobalSpanCandidateComputation shape.size (regs 864) (value / domain))
    (fun left => FlatStoreComputation.map (fun right => bpCandidateMerge? left right)
      (packedGlobalSpanCandidateComputation shape.size
        (regs 864 + regs 865 - value % domain) (value / domain)))
  have h46 : regs 46 = domain := hm 30 (by decide)
  have h48 : regs 48 = bpSparseLevelWidth domain := hm 32 (by decide)
  have h56 : regs 56 = (packedInteriorOffsets shape.size).globalLevel := hm 40 (by decide)
  have hpm : MetadataMatches shape (interiorGlobalTwoPrepared regs) := by
    intro i hi
    simpa [interiorGlobalTwoPrepared, Registers.write,
      show 16 + i ≠ 704 by omega, show 16 + i ≠ 705 by omega,
      show 16 + i ≠ 706 by omega, show 16 + i ≠ 707 by omega] using hm i hi
  have hc : fixedWidthNatTableMachineChunkCount ((interiorGlobalTwoPrepared regs) 705)
      (packedBpCodeWordWidth shape.size) ≤ 7 := by
    simpa [interiorGlobalTwoPrepared, Registers.write, h48, domain, packedReviewerInteriorEntryWidth] using
      canonical_interior_chunks_le_seven shape .globalLevel
  have hs := optionalReadChoice_source shape memory
    interiorGlobalTwoPrefix entry (interiorGlobalTwoSelectedProgram span) he hew
    regs (interiorGlobalTwoPrepared regs) (interiorGlobalTwoPrefix_source memory regs)
    hpm hc next (by
      intro rr value hp hf
      have hmr : MetadataMatches shape rr := by
        intro i hi
        rw [hf (16 + i) (by simp [InteriorReadWrites]; omega)]
        exact hpm i hi
      have h864 : rr 864 = regs 864 := by
        simpa [interiorGlobalTwoPrepared, Registers.write] using hf 864 (by simp [InteriorReadWrites])
      have h865 : rr 865 = regs 865 := by
        simpa [interiorGlobalTwoPrepared, Registers.write] using hf 865 (by simp [InteriorReadWrites])
      have hchoice := interiorGlobalTwoSelectedProgram_source shape memory span hspan hw rr hmr
      simpa only [hp, Nat.add_sub_cancel, h864, h865, next, domain] using hchoice)
  have href : FlatStoreComputation.bind
      (packedInteriorReadNatOf shape.size ((interiorGlobalTwoPrepared regs) 704)
        ((interiorGlobalTwoPrepared regs) 705) ((interiorGlobalTwoPrepared regs) 706)
        ((interiorGlobalTwoPrepared regs) 707))
      (fun result => match result with
        | none => FlatStoreComputation.pure none
        | some value => next value) =
      packedGlobalTwoSpanCandidateComputation shape.size (regs 864) (regs 865) := by
    simp [interiorGlobalTwoPrepared, Registers.write, h46, h48, h56,
      packedGlobalTwoSpanCandidateComputation, next, domain]
    congr 1
    funext result
    cases result <;> rfl
  dsimp only at hs ⊢
  rw [href] at hs
  exact hs



def interiorRangeCrossPrepared (regs : Registers) : Registers :=
  ((((((regs.write 910 (Comparison.le.eval (regs 900) (regs 897))).write
    901 (regs 897 - regs 900)).write 902 ((regs 897 - regs 900) / regs 38)).write
    903 ((regs 897 - regs 900) % regs 38)).write 832 (regs 898)).write
    833 (regs 899)).write 834 (regs 900)

def interiorRangeAdjacentPrepared (regs : Registers) : Registers :=
  ((regs.write 832 (regs 898 + regs 911)).write 833 0).write 834 (regs 903)

def interiorRangeMiddlePrepared (regs : Registers) : Registers :=
  (regs.write 864 (regs 898 + regs 911)).write 865 (regs 902)

def interiorRangeTrailingPrepared (regs : Registers) : Registers :=
  (((regs.write 832 (regs 898 + regs 911)).write 832 (regs 898 + regs 911 + regs 902)).write
    833 0).write 834 (regs 903)

def interiorRangePrepared (regs : Registers) : Registers :=
  (((((regs.write 911 1).write 898 (regs 896 / regs 38)).write 899 (regs 896 % regs 38)).write
    910 (Comparison.le.eval (regs 896 % regs 38) (regs 38))).write
    900 (regs 38 - regs 896 % regs 38)).write
    910 (Comparison.le.eval (regs 897) (regs 38 - regs 896 % regs 38))

def interiorRangeSinglePrepared (regs : Registers) : Registers :=
  ((regs.write 832 (regs 898)).write 833 (regs 899)).write 834 (regs 897)


theorem interiorRangeCrossPrefix_source (memory : Memory) (regs : Registers) :
    interiorRangeCrossPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorRangeCrossPrepared regs, .running⟩, []⟩ := by
  simp [interiorRangeCrossPrefix, interiorRangeCrossPrepared, Block.sequence, Block.eval_seq,
    eval_arithmetic, eval_move, natSubBlock_source, eval_skip, Evaluation.bind, Registers.write, Arithmetic.eval]

theorem interiorRangeAdjacentPrefix_source (memory : Memory) (regs : Registers) :
    interiorRangeAdjacentPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorRangeAdjacentPrepared regs, .running⟩, []⟩ := by
  simp [interiorRangeAdjacentPrefix, interiorRangeAdjacentPrepared, Block.sequence, Block.eval_seq,
    eval_arithmetic, eval_move, eval_constant, eval_skip, Evaluation.bind, Registers.write, Arithmetic.eval]

theorem interiorRangeMiddlePrefix_source (memory : Memory) (regs : Registers) :
    interiorRangeMiddlePrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorRangeMiddlePrepared regs, .running⟩, []⟩ := by
  simp [interiorRangeMiddlePrefix, interiorRangeMiddlePrepared, Block.sequence, Block.eval_seq,
    eval_arithmetic, eval_move, eval_skip, Evaluation.bind, Registers.write, Arithmetic.eval]

theorem interiorRangeTrailingPrefix_source (memory : Memory) (regs : Registers) :
    interiorRangeTrailingPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorRangeTrailingPrepared regs, .running⟩, []⟩ := by
  simp [interiorRangeTrailingPrefix, interiorRangeTrailingPrepared, Block.sequence, Block.eval_seq,
    eval_arithmetic, eval_move, eval_constant, eval_skip, Evaluation.bind, Registers.write, Arithmetic.eval]

theorem interiorRangePrefix_source (memory : Memory) (regs : Registers) :
    interiorRangePrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorRangePrepared regs, .running⟩, []⟩ := by
  simp [interiorRangePrefix, interiorRangePrepared, Block.sequence, Block.eval_seq,
    eval_arithmetic, eval_comparison, eval_constant, natSubBlock_source, eval_skip, Evaluation.bind, Registers.write, Arithmetic.eval]

theorem interiorRangeSinglePrefix_source (memory : Memory) (regs : Registers) :
    interiorRangeSinglePrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorRangeSinglePrepared regs, .running⟩, []⟩ := by
  simp [interiorRangeSinglePrefix, interiorRangeSinglePrepared, Block.sequence, Block.eval_seq,
    eval_move, eval_skip, Evaluation.bind, Registers.write]


private theorem candidateReadMerge_source (shape : CartesianShape) (memory : Memory)
    (setup call : Block) (base : Nat) (hb : base + 3 ≤ 7000)
    (allowed : Nat → Prop) (hw : call.WritesOnly allowed)
    (hfree : ∀ r, base ≤ r → r < base + 3 → ¬ allowed r)
    (computation : Registers → FlatStoreComputation (Option (Nat × Nat)))
    (hcall : InteriorCandidateSpec shape memory call computation)
    (regs prepared : Registers)
    (hp : setup.eval memory ⟨regs, .running⟩ = ⟨⟨prepared, .running⟩, []⟩)
    (hm : MetadataMatches shape prepared) (left : Option (Nat × Nat))
    (hl : candidateOfRegs base prepared = left) :
    let execution := (computation prepared).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers, (Block.seq setup (.seq call (candidateMergeLeftBlock base))).eval
      memory ⟨regs, .running⟩ = ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      candidateOfRegs 7000 final = bpCandidateMerge? left execution.value ∧
      (∀ r, ¬ allowed r → (r < 7000 ∨ 7004 ≤ r) → final r = prepared r) := by
  obtain ⟨rr, he, hv⟩ := hcall prepared hm
  have hframe (r : Nat) (hr : ¬ allowed r) : rr r = prepared r := by
    have hf := Block.eval_frame memory call allowed hw r hr ⟨prepared, .running⟩
    rw [he] at hf
    exact hf
  have hkeep : candidateOfRegs base rr = left := by
    rw [candidateOfRegs_frame base prepared rr
      (by intro r h0 h1; exact hframe r (hfree r h0 h1)), hl]
  obtain ⟨final, hem, hvm⟩ := candidateMergeLeftBlock_result base hb memory rr
  refine ⟨final, ?_, ?_, ?_⟩
  · simp only [Block.eval_seq, hp, he, hem, Evaluation.bind, List.nil_append, List.append_nil]
  · rw [hvm, hkeep, hv]
  · intro r hr hout
    have hf := candidateMergeLeftBlock_frame base memory ⟨rr, .running⟩ r hout
    rw [hem] at hf
    exact hf.trans (hframe r hr)



theorem interiorCandidateSpec_source (shape : CartesianShape) (memory : Memory)
    (program : Block) (computation : Registers → FlatStoreComputation (Option (Nat × Nat)))
    (hspec : InteriorCandidateSpec shape memory program computation)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let execution := (computation regs).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    let expected := flatStoreExecutionTraceResultAtSegment 20 execution
    let actual := program.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  obtain ⟨final, he, hv⟩ := hspec regs hm
  dsimp only
  rw [he, logicalTraceReads_flatExecution]
  exact ⟨rfl, hv, rfl, flatExecution_readOnly 20 _⟩


theorem interiorLocalSpanBlock_spec (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader) :
    InteriorCandidateSpec shape memory (interiorLocalSpanBlock reader)
      (fun regs => packedLocalSpanCandidateComputation shape.size (regs 800) (regs 801) (regs 802)) :=
  interiorLocalSpanProgram_source shape memory (interiorReadBlock reader) (interiorMinBlock reader)
    (interiorReadBlock_spec shape memory reader hr hw) (interiorReadBlock_writes reader hw)
    (interiorMinBlock_spec shape memory reader hr hw)

theorem interiorLocalSpanBlock_source (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let execution := (packedLocalSpanCandidateComputation shape.size (regs 800) (regs 801) (regs 802)).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    let expected := flatStoreExecutionTraceResultAtSegment 20 execution
    let actual := (interiorLocalSpanBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace :=
  interiorCandidateSpec_source shape memory _ _ (interiorLocalSpanBlock_spec shape memory reader hr hw) regs hm


theorem interiorGlobalSpanBlock_spec (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader) :
    InteriorCandidateSpec shape memory (interiorGlobalSpanBlock reader)
      (fun regs => packedGlobalSpanCandidateComputation shape.size (regs 816) (regs 817)) :=
  interiorGlobalSpanProgram_source shape memory (interiorReadBlock reader) (interiorMinBlock reader)
    (interiorReadBlock_spec shape memory reader hr hw) (interiorReadBlock_writes reader hw)
    (interiorMinBlock_spec shape memory reader hr hw)

theorem interiorGlobalSpanBlock_source (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let execution := (packedGlobalSpanCandidateComputation shape.size (regs 816) (regs 817)).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    let expected := flatStoreExecutionTraceResultAtSegment 20 execution
    let actual := (interiorGlobalSpanBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace :=
  interiorCandidateSpec_source shape memory _ _ (interiorGlobalSpanBlock_spec shape memory reader hr hw) regs hm


theorem interiorLocalTwoBlock_spec (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader) :
    InteriorCandidateSpec shape memory (interiorLocalTwoBlock reader)
      (fun regs => packedLocalTwoSpanCandidateComputation shape.size (regs 832) (regs 833) (regs 834)) :=
  interiorLocalTwoProgram_source shape memory (interiorReadBlock reader) (interiorLocalSpanBlock reader)
    (interiorReadBlock_spec shape memory reader hr hw) (interiorReadBlock_writes reader hw)
    (interiorLocalSpanBlock_spec shape memory reader hr hw) (interiorLocalSpanBlock_writes reader hw)

theorem interiorLocalTwoBlock_source (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let execution := (packedLocalTwoSpanCandidateComputation shape.size (regs 832) (regs 833) (regs 834)).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    let expected := flatStoreExecutionTraceResultAtSegment 20 execution
    let actual := (interiorLocalTwoBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace :=
  interiorCandidateSpec_source shape memory _ _ (interiorLocalTwoBlock_spec shape memory reader hr hw) regs hm


theorem interiorGlobalTwoBlock_spec (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader) :
    InteriorCandidateSpec shape memory (interiorGlobalTwoBlock reader)
      (fun regs => packedGlobalTwoSpanCandidateComputation shape.size (regs 864) (regs 865)) :=
  interiorGlobalTwoProgram_source shape memory (interiorReadBlock reader) (interiorGlobalSpanBlock reader)
    (interiorReadBlock_spec shape memory reader hr hw) (interiorReadBlock_writes reader hw)
    (interiorGlobalSpanBlock_spec shape memory reader hr hw) (interiorGlobalSpanBlock_writes reader hw)

theorem interiorGlobalTwoBlock_source (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let execution := (packedGlobalTwoSpanCandidateComputation shape.size (regs 864) (regs 865)).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    let expected := flatStoreExecutionTraceResultAtSegment 20 execution
    let actual := (interiorGlobalTwoBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace :=
  interiorCandidateSpec_source shape memory _ _ (interiorGlobalTwoBlock_spec shape memory reader hr hw) regs hm



private theorem interiorRangeAdjacent_source (shape : CartesianShape) (memory : Memory)
    (localTwo : Block)
    (hspec : InteriorCandidateSpec shape memory localTwo
      (fun regs => packedLocalTwoSpanCandidateComputation shape.size (regs 832) (regs 833) (regs 834)))
    (hw : localTwo.WritesOnly InteriorLocalTwoWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 911 = 1) :
    let execution := (packedLocalTwoSpanCandidateComputation shape.size (regs 898 + 1) 0 (regs 903)).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers,
      (Block.seq interiorRangeAdjacentPrefix (.seq localTwo (candidateMergeLeftBlock 904))).eval
        memory ⟨regs, .running⟩ = ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      candidateOfRegs 7000 final = bpCandidateMerge? (candidateOfRegs 904 regs) execution.value := by
  have hpm : MetadataMatches shape (interiorRangeAdjacentPrepared regs) := by
    intro i hi
    simpa [interiorRangeAdjacentPrepared, Registers.write,
      show 16 + i ≠ 832 by omega, show 16 + i ≠ 833 by omega,
      show 16 + i ≠ 834 by omega] using hm i hi
  have hs := candidateReadMerge_source shape memory interiorRangeAdjacentPrefix localTwo
    904 (by decide) InteriorLocalTwoWrites hw
    (by intro r h0 h1; unfold InteriorLocalTwoWrites InteriorLocalSpanWrites InteriorMinWrites; omega)
    (fun rs => packedLocalTwoSpanCandidateComputation shape.size (rs 832) (rs 833) (rs 834))
    hspec regs (interiorRangeAdjacentPrepared regs) (interiorRangeAdjacentPrefix_source memory regs)
    hpm (candidateOfRegs 904 regs) (by simp [candidateOfRegs, interiorRangeAdjacentPrepared, Registers.write])
  dsimp only at hs ⊢
  obtain ⟨final, he, hv, _⟩ := hs
  refine ⟨final, ?_, ?_⟩
  · simpa only [interiorRangeAdjacentPrepared, Registers.write, reduceIte, hone] using he
  · simpa only [interiorRangeAdjacentPrepared, Registers.write, reduceIte, hone] using hv

private theorem interiorRangeMiddleStage_source (shape : CartesianShape) (memory : Memory)
    (globalTwo : Block)
    (hspec : InteriorCandidateSpec shape memory globalTwo
      (fun regs => packedGlobalTwoSpanCandidateComputation shape.size (regs 864) (regs 865)))
    (hw : globalTwo.WritesOnly InteriorGlobalTwoWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 911 = 1) :
    let execution := (packedGlobalTwoSpanCandidateComputation shape.size (regs 898 + 1) (regs 902)).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers, (interiorRangeMiddleStageProgram globalTwo).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      candidateOfRegs 7000 final = bpCandidateMerge? (candidateOfRegs 904 regs) execution.value ∧
      MetadataMatches shape final ∧
      (∀ r, 896 ≤ r → (r < 904 ∨ r = 911) → final r = regs r) := by
  have hpm : MetadataMatches shape (interiorRangeMiddlePrepared regs) := by
    intro i hi
    simpa [interiorRangeMiddlePrepared, Registers.write,
      show 16 + i ≠ 864 by omega, show 16 + i ≠ 865 by omega] using hm i hi
  have hs := candidateReadMerge_source shape memory interiorRangeMiddlePrefix globalTwo
    904 (by decide) InteriorGlobalTwoWrites hw
    (by intro r h0 h1; unfold InteriorGlobalTwoWrites InteriorGlobalSpanWrites InteriorMinWrites; omega)
    (fun rs => packedGlobalTwoSpanCandidateComputation shape.size (rs 864) (rs 865))
    hspec regs (interiorRangeMiddlePrepared regs) (interiorRangeMiddlePrefix_source memory regs)
    hpm (candidateOfRegs 904 regs) (by simp [candidateOfRegs, interiorRangeMiddlePrepared, Registers.write])
  dsimp only at hs ⊢
  obtain ⟨final, he, hv, hf⟩ := hs
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · simpa only [interiorRangeMiddleStageProgram, interiorRangeMiddlePrepared,
      Registers.write, reduceIte, hone] using he
  · simpa only [interiorRangeMiddlePrepared, Registers.write, reduceIte, hone] using hv
  · intro i hi
    rw [hf (16 + i)
      (by unfold InteriorGlobalTwoWrites InteriorGlobalSpanWrites InteriorMinWrites; omega) (by omega)]
    exact hpm i hi
  · intro r h0 h1
    rw [hf r (by unfold InteriorGlobalTwoWrites InteriorGlobalSpanWrites InteriorMinWrites; omega) (by omega)]
    simp [interiorRangeMiddlePrepared, Registers.write,
      show r ≠ 864 by omega, show r ≠ 865 by omega]



private theorem interiorRangeTrailing_source (shape : CartesianShape) (memory : Memory)
    (localTwo : Block)
    (hspec : InteriorCandidateSpec shape memory localTwo
      (fun regs => packedLocalTwoSpanCandidateComputation shape.size (regs 832) (regs 833) (regs 834)))
    (hw : localTwo.WritesOnly InteriorLocalTwoWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 911 = 1) :
    let execution := (packedLocalTwoSpanCandidateComputation shape.size
      (regs 898 + 1 + regs 902) 0 (regs 903)).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers, (interiorRangeTrailingProgram localTwo).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      candidateOfRegs 7000 final = bpCandidateMerge? (candidateOfRegs 7000 regs) execution.value := by
  obtain ⟨saved, hes, hsv, hsf⟩ := candidateSaveBlock_result 907 (by decide) memory regs
  have hms : MetadataMatches shape saved := by
    intro i hi
    rw [hsf (16 + i) (by omega)]
    exact hm i hi
  have hpm : MetadataMatches shape (interiorRangeTrailingPrepared saved) := by
    intro i hi
    simpa [interiorRangeTrailingPrepared, Registers.write,
      show 16 + i ≠ 832 by omega, show 16 + i ≠ 833 by omega,
      show 16 + i ≠ 834 by omega] using hms i hi
  have hs := candidateReadMerge_source shape memory interiorRangeTrailingPrefix localTwo
    907 (by decide) InteriorLocalTwoWrites hw
    (by intro r h0 h1; unfold InteriorLocalTwoWrites InteriorLocalSpanWrites InteriorMinWrites; omega)
    (fun rs => packedLocalTwoSpanCandidateComputation shape.size (rs 832) (rs 833) (rs 834))
    hspec saved (interiorRangeTrailingPrepared saved) (interiorRangeTrailingPrefix_source memory saved)
    hpm (candidateOfRegs 7000 regs)
    (by simpa [candidateOfRegs, interiorRangeTrailingPrepared, Registers.write] using hsv)
  dsimp only at hs ⊢
  obtain ⟨final, he, hv, _⟩ := hs
  have h898 := hsf 898 (by decide)
  have h902 := hsf 902 (by decide)
  have h903 := hsf 903 (by decide)
  have h911 := (hsf 911 (by decide)).trans hone
  simp [interiorRangeTrailingPrepared, Registers.write,
    h898, h902, h903, h911] at he hv
  refine ⟨final, ?_, hv⟩
  rw [interiorRangeTrailingProgram, Block.eval_seq, hes]
  simp only [Evaluation.bind, he, List.nil_append]



private theorem interiorRangeMiddleProgram_source (shape : CartesianShape) (memory : Memory)
    (localTwo globalTwo : Block)
    (hl : InteriorCandidateSpec shape memory localTwo
      (fun regs => packedLocalTwoSpanCandidateComputation shape.size (regs 832) (regs 833) (regs 834)))
    (hwl : localTwo.WritesOnly InteriorLocalTwoWrites)
    (hg : InteriorCandidateSpec shape memory globalTwo
      (fun regs => packedGlobalTwoSpanCandidateComputation shape.size (regs 864) (regs 865)))
    (hwg : globalTwo.WritesOnly InteriorGlobalTwoWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 911 = 1) :
    let store := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
    let middle := (packedGlobalTwoSpanCandidateComputation shape.size (regs 898 + 1) (regs 902)).run store
    let right := (packedLocalTwoSpanCandidateComputation shape.size
      (regs 898 + 1 + regs 902) 0 (regs 903)).run store
    ∃ final : Registers, (interiorRangeMiddleProgram localTwo globalTwo).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, if regs 903 = 0 then interiorExecutionReads shape memory middle
        else interiorExecutionReads shape memory middle ++ interiorExecutionReads shape memory right⟩ ∧
      candidateOfRegs 7000 final =
        if regs 903 = 0 then bpCandidateMerge? (candidateOfRegs 904 regs) middle.value
        else bpCandidateMerge3? (candidateOfRegs 904 regs) middle.value right.value := by
  obtain ⟨mr, hem, hvm, hmm, hfm⟩ :=
    interiorRangeMiddleStage_source shape memory globalTwo hg hwg regs hm hone
  have h898 := hfm 898 (by decide) (by decide)
  have h902 := hfm 902 (by decide) (by decide)
  have h903 := hfm 903 (by decide) (by decide)
  have h911 := (hfm 911 (by decide) (by decide)).trans hone
  dsimp only
  by_cases hz : regs 903 = 0
  · refine ⟨mr, ?_, ?_⟩
    · rw [interiorRangeMiddleProgram, Block.eval_seq, hem]
      simp only [Evaluation.bind, eval_ifZero, h903, hz, if_true, eval_skip, List.append_nil]
    · simpa only [hz, if_true] using hvm
  · obtain ⟨final, het, hvt⟩ :=
      interiorRangeTrailing_source shape memory localTwo hl hwl mr hmm h911
    simp only [h898, h902, h903] at het hvt
    refine ⟨final, ?_, ?_⟩
    · rw [interiorRangeMiddleProgram, Block.eval_seq, hem]
      simp only [Evaluation.bind, eval_ifZero, h903, hz, if_false, het]
    · simpa only [hz, if_false, bpCandidateMerge3?, hvm] using hvt

private theorem interiorRangeBranchProgram_source (shape : CartesianShape) (memory : Memory)
    (localTwo globalTwo : Block)
    (hl : InteriorCandidateSpec shape memory localTwo
      (fun regs => packedLocalTwoSpanCandidateComputation shape.size (regs 832) (regs 833) (regs 834)))
    (hwl : localTwo.WritesOnly InteriorLocalTwoWrites)
    (hg : InteriorCandidateSpec shape memory globalTwo
      (fun regs => packedGlobalTwoSpanCandidateComputation shape.size (regs 864) (regs 865)))
    (hwg : globalTwo.WritesOnly InteriorGlobalTwoWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 911 = 1) :
    let store := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
    let adjacent := (packedLocalTwoSpanCandidateComputation shape.size (regs 898 + 1) 0 (regs 903)).run store
    let middle := (packedGlobalTwoSpanCandidateComputation shape.size (regs 898 + 1) (regs 902)).run store
    let right := (packedLocalTwoSpanCandidateComputation shape.size
      (regs 898 + 1 + regs 902) 0 (regs 903)).run store
    ∃ final : Registers, (interiorRangeBranchProgram localTwo globalTwo).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩,
        if regs 902 = 0 then interiorExecutionReads shape memory adjacent
        else if regs 903 = 0 then interiorExecutionReads shape memory middle
        else interiorExecutionReads shape memory middle ++ interiorExecutionReads shape memory right⟩ ∧
      candidateOfRegs 7000 final =
        if regs 902 = 0 then bpCandidateMerge? (candidateOfRegs 904 regs) adjacent.value
        else if regs 903 = 0 then bpCandidateMerge? (candidateOfRegs 904 regs) middle.value
        else bpCandidateMerge3? (candidateOfRegs 904 regs) middle.value right.value := by
  dsimp only
  by_cases hz : regs 902 = 0
  · have hs := interiorRangeAdjacent_source shape memory localTwo hl hwl regs hm hone
    simpa only [interiorRangeBranchProgram, eval_ifZero, hz, if_true] using hs
  · have hs := interiorRangeMiddleProgram_source shape memory localTwo globalTwo hl hwl hg hwg regs hm hone
    simpa only [interiorRangeBranchProgram, eval_ifZero, hz, if_false] using hs



private theorem flatBindBindMap_run (first : FlatStoreComputation α)
    (second : FlatStoreComputation β) (third : FlatStoreComputation γ)
    (combine : α → β → γ → δ) (store : FlatWordStore) :
    (FlatStoreComputation.bind first (fun left => FlatStoreComputation.bind second
      (fun middle => FlatStoreComputation.map (combine left middle) third))).run store =
      ⟨combine (first.run store).value (second.run store).value (third.run store).value,
        (first.run store).reads ++ (second.run store).reads ++ (third.run store).reads⟩ := by
  rw [FlatStoreComputation.bind_run]
  simp only [FlatStoreExecution.append, flatBindMap_run, List.append_assoc]

theorem interiorRangeCrossProgram_source (shape : CartesianShape) (memory : Memory)
    (localTwo globalTwo : Block)
    (hl : InteriorCandidateSpec shape memory localTwo
      (fun regs => packedLocalTwoSpanCandidateComputation shape.size (regs 832) (regs 833) (regs 834)))
    (hwl : localTwo.WritesOnly InteriorLocalTwoWrites)
    (hg : InteriorCandidateSpec shape memory globalTwo
      (fun regs => packedGlobalTwoSpanCandidateComputation shape.size (regs 864) (regs 865)))
    (hwg : globalTwo.WritesOnly InteriorGlobalTwoWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 911 = 1)
    (hleft : regs 900 = (packedInteriorLayout shape.size).macroSize - regs 899) :
    let size := (packedInteriorLayout shape.size).macroSize
    let middleCount := (regs 897 - regs 900) / size
    let rightCount := (regs 897 - regs 900) % size
    let computation := if middleCount = 0 then
      packedAdjacentMacroCandidateComputation shape.size (regs 898) (regs 899) rightCount
      else if rightCount = 0 then
        packedLeftMiddleMacroCandidateComputation shape.size (regs 898) (regs 899) middleCount
      else packedCrossMacroCandidateComputation shape.size (regs 898) (regs 899) middleCount rightCount
    let execution := computation.run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers, (interiorRangeCrossProgram localTwo globalTwo).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      candidateOfRegs 7000 final = execution.value := by
  have hsize : regs 38 = (packedInteriorLayout shape.size).macroSize := hm 22 (by decide)
  have hpm : MetadataMatches shape (interiorRangeCrossPrepared regs) := by
    intro i hi
    simpa [interiorRangeCrossPrepared, Registers.write,
      show 16 + i ≠ 910 by omega, show 16 + i ≠ 901 by omega,
      show 16 + i ≠ 902 by omega, show 16 + i ≠ 903 by omega,
      show 16 + i ≠ 832 by omega, show 16 + i ≠ 833 by omega,
      show 16 + i ≠ 834 by omega] using hm i hi
  have hp832 : (interiorRangeCrossPrepared regs) 832 = regs 898 := by
    simp [interiorRangeCrossPrepared, Registers.write]
  have hp833 : (interiorRangeCrossPrepared regs) 833 = regs 899 := by
    simp [interiorRangeCrossPrepared, Registers.write]
  have hp834 : (interiorRangeCrossPrepared regs) 834 = regs 900 := by
    simp [interiorRangeCrossPrepared, Registers.write]
  have hsleft := hl (interiorRangeCrossPrepared regs) hpm
  dsimp only at hsleft
  simp only [hp832, hp833, hp834] at hsleft
  obtain ⟨lr, hel, hvl⟩ := hsleft
  have hlf (r : Nat) (hr : ¬ InteriorLocalTwoWrites r) :
      lr r = (interiorRangeCrossPrepared regs) r := by
    have hf := Block.eval_frame memory localTwo _ hwl r hr ⟨interiorRangeCrossPrepared regs, .running⟩
    rw [hel] at hf
    exact hf
  obtain ⟨saved, hes, hsv, hsf⟩ := candidateSaveBlock_result 904 (by decide) memory lr
  have hk (r : Nat) (hr : r < 704 ∨ r = 898 ∨ r = 899 ∨ r = 900 ∨ r = 901 ∨
      r = 902 ∨ r = 903 ∨ r = 911) : saved r = (interiorRangeCrossPrepared regs) r := by
    rw [hsf r (by omega), hlf r (by unfold InteriorLocalTwoWrites InteriorLocalSpanWrites InteriorMinWrites; omega)]
  have hms : MetadataMatches shape saved := by
    intro i hi
    rw [hk (16 + i) (by omega)]
    exact hpm i hi
  have h911 : saved 911 = 1 := by
    simpa [interiorRangeCrossPrepared, Registers.write, hone] using hk 911 (by omega)
  have hsbranch := interiorRangeBranchProgram_source shape memory localTwo globalTwo hl hwl hg hwg
    saved hms h911
  dsimp only at hsbranch
  obtain ⟨final, heb, hvb⟩ := hsbranch
  have h898 : saved 898 = regs 898 := by
    simpa [interiorRangeCrossPrepared, Registers.write] using hk 898 (by omega)
  have h902 : saved 902 = (regs 897 - regs 900) / (packedInteriorLayout shape.size).macroSize := by
    simpa [interiorRangeCrossPrepared, Registers.write, hsize] using hk 902 (by omega)
  have h903 : saved 903 = (regs 897 - regs 900) % (packedInteriorLayout shape.size).macroSize := by
    simpa [interiorRangeCrossPrepared, Registers.write, hsize] using hk 903 (by omega)
  simp only [h898, h902, h903, hsv, hvl] at heb hvb
  have hj : (interiorRangeCrossProgram localTwo globalTwo).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩,
        interiorExecutionReads shape memory
          ((packedLocalTwoSpanCandidateComputation shape.size (regs 898) (regs 899) (regs 900)).run
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)) ++
        (if (regs 897 - regs 900) / (packedInteriorLayout shape.size).macroSize = 0 then
          interiorExecutionReads shape memory
            ((packedLocalTwoSpanCandidateComputation shape.size (regs 898 + 1) 0
              ((regs 897 - regs 900) % (packedInteriorLayout shape.size).macroSize)).run
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20))
        else if (regs 897 - regs 900) % (packedInteriorLayout shape.size).macroSize = 0 then
          interiorExecutionReads shape memory
            ((packedGlobalTwoSpanCandidateComputation shape.size (regs 898 + 1)
              ((regs 897 - regs 900) / (packedInteriorLayout shape.size).macroSize)).run
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20))
        else
          interiorExecutionReads shape memory
            ((packedGlobalTwoSpanCandidateComputation shape.size (regs 898 + 1)
              ((regs 897 - regs 900) / (packedInteriorLayout shape.size).macroSize)).run
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)) ++
          interiorExecutionReads shape memory
            ((packedLocalTwoSpanCandidateComputation shape.size
              (regs 898 + 1 + (regs 897 - regs 900) / (packedInteriorLayout shape.size).macroSize) 0
              ((regs 897 - regs 900) % (packedInteriorLayout shape.size).macroSize)).run
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)))⟩ := by
    rw [interiorRangeCrossProgram, Block.eval_seq, interiorRangeCrossPrefix_source]
    simp only [Evaluation.bind, Block.eval_seq, hel, hes, heb, List.nil_append]
  dsimp only
  refine ⟨final, ?_, ?_⟩
  · by_cases hz : (regs 897 - regs 900) / (packedInteriorLayout shape.size).macroSize = 0
    · simp only [hz, if_true] at hj ⊢
      rw [packedAdjacentMacroCandidateComputation, flatBindMap_run]
      exact hj.trans (congrArg (fun receipts => Evaluation.mk ⟨final, .running⟩ receipts)
        (by simp only [interiorExecutionReads, List.flatMap_append, hleft]))
    · by_cases hr : (regs 897 - regs 900) % (packedInteriorLayout shape.size).macroSize = 0
      · simp only [hz, if_false, hr, if_true] at hj ⊢
        rw [packedLeftMiddleMacroCandidateComputation, flatBindMap_run]
        exact hj.trans (congrArg (fun receipts => Evaluation.mk ⟨final, .running⟩ receipts)
          (by simp only [interiorExecutionReads, List.flatMap_append, hleft]))
      · simp only [hz, if_false, hr] at hj ⊢
        rw [packedCrossMacroCandidateComputation, flatBindBindMap_run]
        exact hj.trans (congrArg (fun receipts => Evaluation.mk ⟨final, .running⟩ receipts)
          (by simp only [interiorExecutionReads, List.flatMap_append, List.append_assoc, hleft]))
  · by_cases hz : (regs 897 - regs 900) / (packedInteriorLayout shape.size).macroSize = 0
    · simp only [hz, if_true] at hvb ⊢
      rw [packedAdjacentMacroCandidateComputation, flatBindMap_run]
      simpa only [hleft] using hvb
    · by_cases hr : (regs 897 - regs 900) % (packedInteriorLayout shape.size).macroSize = 0
      · simp only [hz, if_false, hr, if_true] at hvb ⊢
        rw [packedLeftMiddleMacroCandidateComputation, flatBindMap_run]
        simpa only [hleft] using hvb
      · simp only [hz, if_false, hr] at hvb ⊢
        rw [packedCrossMacroCandidateComputation, flatBindBindMap_run]
        simpa only [hleft] using hvb



def interiorCrossComputation (n : Nat) (regs : Registers) :
    FlatStoreComputation (Option (Nat × Nat)) :=
  let size := (packedInteriorLayout n).macroSize
  let middleCount := (regs 897 - regs 900) / size
  let rightCount := (regs 897 - regs 900) % size
  if middleCount = 0 then
    packedAdjacentMacroCandidateComputation n (regs 898) (regs 899) rightCount
  else if rightCount = 0 then
    packedLeftMiddleMacroCandidateComputation n (regs 898) (regs 899) middleCount
  else packedCrossMacroCandidateComputation n (regs 898) (regs 899) middleCount rightCount

def InteriorCrossSpec (shape : CartesianShape) (memory : Memory) (cross : Block) : Prop :=
  ∀ regs, MetadataMatches shape regs → regs 911 = 1 →
    regs 900 = (packedInteriorLayout shape.size).macroSize - regs 899 →
    let execution := (interiorCrossComputation shape.size regs).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    ∃ final : Registers, cross.eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, interiorExecutionReads shape memory execution⟩ ∧
      candidateOfRegs 7000 final = execution.value

theorem interiorRangeCrossProgram_spec (shape : CartesianShape) (memory : Memory)
    (localTwo globalTwo : Block)
    (hl : InteriorCandidateSpec shape memory localTwo
      (fun regs => packedLocalTwoSpanCandidateComputation shape.size (regs 832) (regs 833) (regs 834)))
    (hwl : localTwo.WritesOnly InteriorLocalTwoWrites)
    (hg : InteriorCandidateSpec shape memory globalTwo
      (fun regs => packedGlobalTwoSpanCandidateComputation shape.size (regs 864) (regs 865)))
    (hwg : globalTwo.WritesOnly InteriorGlobalTwoWrites) :
    InteriorCrossSpec shape memory (interiorRangeCrossProgram localTwo globalTwo) :=
  interiorRangeCrossProgram_source shape memory localTwo globalTwo hl hwl hg hwg

theorem interiorRangeProgram_source (shape : CartesianShape) (memory : Memory)
    (localTwo cross : Block)
    (hl : InteriorCandidateSpec shape memory localTwo
      (fun regs => packedLocalTwoSpanCandidateComputation shape.size (regs 832) (regs 833) (regs 834)))
    (hc : InteriorCrossSpec shape memory cross) :
    InteriorCandidateSpec shape memory (interiorRangeProgram localTwo cross)
      (fun regs => packedInteriorRangeMinComputation shape.size (regs 896) (regs 897)) := by
  intro regs hm
  dsimp only
  by_cases hz : regs 897 = 0
  · have hn := candidateNoneBlock_source memory regs
    generalize hen : candidateNoneBlock.eval memory ⟨regs, .running⟩ = actual at hn
    rcases actual with ⟨⟨final, status⟩, reads⟩
    dsimp only at hn
    obtain ⟨rfl, rfl, hv⟩ := hn
    refine ⟨final, ?_, ?_⟩
    · simp only [interiorRangeProgram, eval_ifZero, hz, if_true, hen,
        packedInteriorRangeMinComputation, FlatStoreComputation.pure_run,
        interiorExecutionReads, List.flatMap_nil]
    · simpa only [packedInteriorRangeMinComputation, hz, if_true,
        FlatStoreComputation.pure_run] using hv
  · have hsize : regs 38 = (packedInteriorLayout shape.size).macroSize := hm 22 (by decide)
    have hpm : MetadataMatches shape (interiorRangePrepared regs) := by
      intro i hi
      simpa [interiorRangePrepared, Registers.write,
        show 16 + i ≠ 911 by omega, show 16 + i ≠ 898 by omega,
        show 16 + i ≠ 899 by omega, show 16 + i ≠ 910 by omega,
        show 16 + i ≠ 900 by omega] using hm i hi
    by_cases hsingle : regs 897 ≤ (packedInteriorLayout shape.size).macroSize -
        regs 896 % (packedInteriorLayout shape.size).macroSize
    · have hmps : MetadataMatches shape (interiorRangeSinglePrepared (interiorRangePrepared regs)) := by
        intro i hi
        simpa [interiorRangeSinglePrepared, Registers.write,
          show 16 + i ≠ 832 by omega, show 16 + i ≠ 833 by omega,
          show 16 + i ≠ 834 by omega] using hpm i hi
      have hp832 : (interiorRangeSinglePrepared (interiorRangePrepared regs)) 832 =
          regs 896 / (packedInteriorLayout shape.size).macroSize := by
        simp [interiorRangeSinglePrepared, interiorRangePrepared, Registers.write, hsize]
      have hp833 : (interiorRangeSinglePrepared (interiorRangePrepared regs)) 833 =
          regs 896 % (packedInteriorLayout shape.size).macroSize := by
        simp [interiorRangeSinglePrepared, interiorRangePrepared, Registers.write, hsize]
      have hp834 : (interiorRangeSinglePrepared (interiorRangePrepared regs)) 834 = regs 897 := by
        simp [interiorRangeSinglePrepared, interiorRangePrepared, Registers.write]
      have hs := hl (interiorRangeSinglePrepared (interiorRangePrepared regs)) hmps
      dsimp only at hs
      simp only [hp832, hp833, hp834] at hs
      obtain ⟨final, hel, hvl⟩ := hs
      have hcmp : (interiorRangePrepared regs) 910 = 1 := by
        simp [interiorRangePrepared, Registers.write, Comparison.eval, hsize, hsingle]
      refine ⟨final, ?_, ?_⟩
      · rw [interiorRangeProgram, eval_ifZero, if_neg hz, Block.eval_seq, interiorRangePrefix_source]
        simp only [Evaluation.bind, eval_ifZero, hcmp, Nat.one_ne_zero, if_false,
          Block.eval_seq, interiorRangeSinglePrefix_source, hel, List.nil_append]
        simp only [packedInteriorRangeMinComputation, hz, if_false, hsingle, if_true]
      · simpa only [packedInteriorRangeMinComputation, hz, if_false, hsingle, if_true] using hvl
    · have hcmp : (interiorRangePrepared regs) 910 = 0 := by
        simp [interiorRangePrepared, Registers.write, Comparison.eval, hsize, hsingle]
      have hone : (interiorRangePrepared regs) 911 = 1 := by
        simp [interiorRangePrepared, Registers.write]
      have hleft : (interiorRangePrepared regs) 900 =
          (packedInteriorLayout shape.size).macroSize - (interiorRangePrepared regs) 899 := by
        simp [interiorRangePrepared, Registers.write, hsize]
      have hs := hc (interiorRangePrepared regs) hpm hone hleft
      have href : interiorCrossComputation shape.size (interiorRangePrepared regs) =
          packedInteriorRangeMinComputation shape.size (regs 896) (regs 897) := by
        simp [interiorCrossComputation, interiorRangePrepared, Registers.write, hsize,
          packedInteriorRangeMinComputation, hz, hsingle]
      dsimp only at hs
      rw [href] at hs
      obtain ⟨final, hec, hvc⟩ := hs
      refine ⟨final, ?_, hvc⟩
      rw [interiorRangeProgram, eval_ifZero, if_neg hz, Block.eval_seq, interiorRangePrefix_source]
      simp only [Evaluation.bind, eval_ifZero, hcmp, if_true, hec, List.nil_append]

theorem interiorRangeBlock_spec (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader) :
    InteriorCandidateSpec shape memory (interiorRangeBlock reader)
      (fun regs => packedInteriorRangeMinComputation shape.size (regs 896) (regs 897)) :=
  interiorRangeProgram_source shape memory (interiorLocalTwoBlock reader)
    (interiorRangeCrossBlock reader) (interiorLocalTwoBlock_spec shape memory reader hr hw)
    (interiorRangeCrossProgram_spec shape memory (interiorLocalTwoBlock reader) (interiorGlobalTwoBlock reader)
      (interiorLocalTwoBlock_spec shape memory reader hr hw) (interiorLocalTwoBlock_writes reader hw)
      (interiorGlobalTwoBlock_spec shape memory reader hr hw) (interiorGlobalTwoBlock_writes reader hw))

theorem interiorRangeBlock_source (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (interiorRangeBlock reader).eval memory ⟨regs, .running⟩
    let expected := packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 896) (regs 897)
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace :=
  interiorCandidateSpec_source shape memory _ _ (interiorRangeBlock_spec shape memory reader hr hw) regs hm



@[simp] theorem candidateMergeLeftBlock_size (base : Nat) :
    (candidateMergeLeftBlock base).size = 13 := by
  simp [candidateMergeLeftBlock, candidateRestoreBlock, Block.sequence, Block.size]


@[simp] theorem interiorMinBlock_size (reader : Block) :
    (interiorMinBlock reader).size = 669 + 32 * reader.size := by
  simp [interiorMinBlock, interiorMinProgram, interiorMinBaselineProgram, interiorMinBaselinePrefix, interiorMinFieldProgram, interiorMinRelativePrefix, interiorMinFinish, candidateNoneBlock, Block.sequence, Block.size, natSubBlock]
  omega

@[simp] theorem interiorLocalSpanBlock_size (reader : Block) :
    (interiorLocalSpanBlock reader).size = 843 + 40 * reader.size := by
  simp [interiorLocalSpanBlock, interiorLocalSpanProgram, interiorLocalSpanPrefix, interiorLocalSpanSelectedPrefix, candidateNoneBlock, Block.sequence, Block.size, natSubBlock]
  omega

@[simp] theorem interiorGlobalSpanBlock_size (reader : Block) :
    (interiorGlobalSpanBlock reader).size = 838 + 40 * reader.size := by
  simp [interiorGlobalSpanBlock, interiorGlobalSpanProgram, interiorGlobalSpanPrefix, interiorGlobalSpanSelectedPrefix, candidateNoneBlock, Block.sequence, Block.size, natSubBlock]
  omega

@[simp] theorem interiorLocalTwoBlock_size (reader : Block) :
    (interiorLocalTwoBlock reader).size = 1883 + 88 * reader.size := by
  simp [interiorLocalTwoBlock, interiorLocalTwoProgram, interiorLocalTwoPrefix, interiorLocalTwoFirstPrefix, interiorLocalTwoSecondPrefix, interiorLocalTwoSelectedProgram, candidateNoneBlock, candidateSaveBlock, Block.sequence, Block.size, natSubBlock]
  omega

@[simp] theorem interiorGlobalTwoBlock_size (reader : Block) :
    (interiorGlobalTwoBlock reader).size = 1871 + 88 * reader.size := by
  simp [interiorGlobalTwoBlock, interiorGlobalTwoProgram, interiorGlobalTwoPrefix, interiorGlobalTwoFirstPrefix, interiorGlobalTwoSecondPrefix, interiorGlobalTwoSelectedProgram, candidateNoneBlock, candidateSaveBlock, Block.sequence, Block.size, natSubBlock]
  omega

@[simp] theorem interiorRangeCrossBlock_size (reader : Block) :
    (interiorRangeCrossBlock reader).size = 7588 + 352 * reader.size := by
  simp [interiorRangeCrossBlock, interiorRangeCrossProgram, interiorRangeCrossPrefix, interiorRangeBranchProgram, interiorRangeAdjacentPrefix, interiorRangeMiddleProgram, interiorRangeMiddleStageProgram, interiorRangeMiddlePrefix, interiorRangeTrailingProgram, interiorRangeTrailingPrefix, candidateSaveBlock, Block.sequence, Block.size, natSubBlock]
  omega

@[simp] theorem interiorRangeBlock_size (reader : Block) :
    (interiorRangeBlock reader).size = 9490 + 440 * reader.size := by
  simp [interiorRangeBlock, interiorRangeProgram, interiorRangePrefix, interiorRangeSinglePrefix, candidateNoneBlock, Block.sequence, Block.size, natSubBlock]
  omega

theorem interiorCandidateSpec_machine (shape : CartesianShape) (memory : Memory)
    (program : Block) (computation : Registers → FlatStoreComputation (Option (Nat × Nat)))
    (hspec : InteriorCandidateSpec shape memory program computation)
    (allowed : Nat → Prop) (hwrites : program.WritesOnly allowed)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let execution := (computation regs).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    let expected := flatStoreExecutionTraceResultAtSegment 20 execution
    let source := program.eval memory ⟨regs, .running⟩
    let actual := run memory (program.compileAt 0 ++ [.halt 7000])
      (program.size + 1) ⟨regs, 0, .running⟩
    actual.result = some (source.final.regs 7000) ∧
      actual.final.status = .halted (source.final.regs 7000) ∧
      actual.final.regs 7000 = source.final.regs 7000 ∧
      actual.final.regs 7001 = source.final.regs 7001 ∧
      actual.final.regs 7002 = source.final.regs 7002 ∧
      candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧
      actual.steps ≤ program.size + 1 ∧
      (∀ r, ¬ allowed r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace := by
  have hs := interiorCandidateSpec_source shape memory program computation hspec regs hm
  have hc := program.compile_with_halt memory 7000 ⟨regs, 0, .running⟩ rfl
  dsimp only [Data.ofState] at hs hc ⊢
  rw [hs.1] at hc
  have hd := hc.1
  simp only [Block.eval, hs.1] at hd
  have hregs := congrArg Data.regs hd
  refine ⟨hc.2.1, congrArg Data.status hd, congrArg (fun r : Registers => r 7000) hregs,
    congrArg (fun r : Registers => r 7001) hregs,
    congrArg (fun r : Registers => r 7002) hregs,
    (congrArg (candidateOfRegs 7000) hregs).trans hs.2.1,
    hc.2.2.1.trans hs.2.2.1, ?_, ?_, hs.2.2.2⟩
  · simpa only [List.length_append, Block.compile_length, List.length_singleton] using hc.2.2.2
  · intro r hr
    exact (congrArg (fun values : Registers => values r) hregs).trans
      (Block.eval_frame memory program allowed hwrites r hr ⟨regs, .running⟩)

theorem interiorRangeBlock_machine (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 896) (regs 897)
    let source := (interiorRangeBlock reader).eval memory ⟨regs, .running⟩
    let actual := run memory ((interiorRangeBlock reader).compileAt 0 ++ [.halt 7000])
      (9491 + 440 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some (source.final.regs 7000) ∧
      actual.final.status = .halted (source.final.regs 7000) ∧
      actual.final.regs 7000 = source.final.regs 7000 ∧
      actual.final.regs 7001 = source.final.regs 7001 ∧
      actual.final.regs 7002 = source.final.regs 7002 ∧
      candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧
      actual.steps ≤ 9491 + 440 * reader.size ∧
      (∀ r, ¬ InteriorRangeWrites r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace := by
  have hs := interiorCandidateSpec_machine shape memory (interiorRangeBlock reader) _
    (interiorRangeBlock_spec shape memory reader hr hw) InteriorRangeWrites
    (interiorRangeBlock_writes reader hw) regs hm
  have hsize : (interiorRangeBlock reader).size + 1 = 9491 + 440 * reader.size := by
    rw [interiorRangeBlock_size]
    omega
  simpa only [hsize] using hs

theorem interiorRangeBlock_canonical_machine (shape : CartesianShape)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 896) (regs 897)
    let source := (interiorRangeBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩
    let actual := run (shapeMemory shape)
      ((interiorRangeBlock logicalReadBlock).compileAt 0 ++ [.halt 7000]) 479411 ⟨regs, 0, .running⟩
    actual.result = some (source.final.regs 7000) ∧
      actual.final.status = .halted (source.final.regs 7000) ∧
      actual.final.regs 7000 = source.final.regs 7000 ∧
      actual.final.regs 7001 = source.final.regs 7001 ∧
      actual.final.regs 7002 = source.final.regs 7002 ∧
      candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
      actual.steps ≤ 479411 ∧
      (∀ r, ¬ InteriorRangeWrites r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace :=
  interiorRangeBlock_machine shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm

/-- Independent concrete source consumer for the full LCA interface. -/
theorem interiorRangeBlock_sameAllocation (shape : CartesianShape)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (interiorRangeBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩
    let expected := packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 896) (regs 897)
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
      ReadOnlyTrace expected.trace :=
  interiorRangeBlock_source shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm

/-- The full navigator retains each raw read's transition position and pre-state. -/
theorem interiorRangeBlock_canonical_read_at (shape : CartesianShape)
    (regs : Registers) (k : Nat) (t : Transition) (receipt : Receipt)
    (ht : (run (shapeMemory shape)
      ((interiorRangeBlock logicalReadBlock).compileAt 0 ++ [.halt 7000])
        479411 ⟨regs, 0, .running⟩).transitions[k]? = some t)
    (hr : t.receipt = some receipt) :
    t.before = (run (shapeMemory shape)
      ((interiorRangeBlock logicalReadBlock).compileAt 0 ++ [.halt 7000])
        k ⟨regs, 0, .running⟩).final ∧
      t.before.status = .running ∧
      ((interiorRangeBlock logicalReadBlock).compileAt 0 ++ [.halt 7000])[t.before.pc]? =
        some t.instruction ∧
      execute (shapeMemory shape) t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧
        receipt.reply = (shapeMemory shape)[receipt.address]? :=
  run_read_at ht hr



theorem interiorRangeBlock_zero (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hz : regs 897 = 0) :
    let actual := (interiorRangeBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = none ∧ actual.reads = [] := by
  have hs := interiorRangeBlock_source shape memory reader hr hw regs hm
  dsimp only at hs ⊢
  simpa [packedInteriorRangeMinRead, concreteBPNativeInteriorTraceSegments,
    packedInteriorRangeMinComputation, hz, flatStoreExecutionTraceResultAtSegment,
    FlatStoreComputation.pure_run, logicalTraceReads, ReadOnlyTrace] using hs

theorem interiorMinFinish_missingMax (memory : Memory) (regs : Registers)
    (hone : regs 774 = 1) (hmissing : regs 771 = 0) :
    candidateOfRegs 7000 (interiorMinFinish.eval memory ⟨regs, .running⟩).final.regs = none ∧
      (interiorMinFinish.eval memory ⟨regs, .running⟩).reads = [] := by
  have hs := interiorMinFinish_source memory regs hone
  exact ⟨hs.2.2.trans (by simp [interiorMinPacketCandidate, hmissing]), hs.2.1⟩

theorem interiorEntry_dead_request (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hr : ReaderCorrect shape memory reader) (hw : ReaderWrites reader)
    (component : PackedReviewerInteriorComponentTag)
    (regs : Registers) (hm : MetadataMatches shape regs)
    (hwidth : regs 705 = packedReviewerInteriorEntryWidth shape.size component)
    (hdead : regs 704 ≤ regs 707) :
    let actual := (interiorReadBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 708 = logicalPacket
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
        (packedInteriorOffsets shape.size).deadAddress) ∧
      actual.reads = readerReceipts shape memory 20 (packedInteriorOffsets shape.size).deadAddress := by
  have hword : regs 32 = packedBpCodeWordWidth shape.size := hm 16 (by decide)
  have hd : regs 57 = (packedInteriorOffsets shape.size).deadAddress := hm 41 (by decide)
  have hs := interiorReadBlock_source shape memory reader hr hw regs hm
    (by rw [hwidth, hword]; exact canonical_interior_chunks_le_seven shape component)
  have hcollect (word : Option (List Bool)) : collectPayloadWords [word] = word := by
    cases word <;> simp [collectPayloadWords]
  simpa only [interiorRequests, if_neg (by omega : ¬ regs 707 < regs 704), hd,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, hcollect] using hs

theorem interiorNavigator_tie_machine (memory : Memory) (regs : Registers)
    (score leftPosition rightPosition : Nat)
    (hl : candidateOfRegs 840 regs = some (score, leftPosition))
    (hr : candidateOfRegs 7000 regs = some (score, rightPosition)) :
    candidateOfRegs 7000
      (run memory ((candidateMergeLeftBlock 840).compileAt 0) 13 ⟨regs, 0, .running⟩).final.regs =
        some (score, leftPosition) := by
  have hs := candidateMergeLeftBlock_tie 840 score leftPosition rightPosition (by decide) memory regs hl hr
  have hc := (candidateMergeLeftBlock 840).compile_run memory ⟨regs, 0, .running⟩ rfl
  rw [candidateMergeLeftBlock_size] at hc
  exact (congrArg (fun d : Data => candidateOfRegs 7000 d.regs) hc.1).trans hs


end RMQ.SuccinctFinal.PackedWordRAM
