import RMQ.Core.WordRAM.Packed.Locate
import RMQ.Core.WordRAM.Packed.LogicalSpan
import RMQ.Core.WordRAM.Packed.SpanAssembly
import RMQ.Core.WordRAM.Packed.ReadInterface

/-!
# One fixed physical logical-word reader

Location uses the charged metadata bank. The old absolute bit position is
shifted by the counted174-word prefix, then the primitive span routine reads
the new numeric allocation. Only the decoded logical value receives a packet
tag; raw physical cells are never incremented.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured Cartesian PackedCellProbe SuccinctSpace

def readSpanPrefix : Block := Block.sequence [
  .action (.move 8256 22),
  .action (.constant 8270 174),
  .action (.arithmetic .mul 8257 8270 8256),
  .action (.arithmetic .add 8257 8257 8195),
  .action (.move 8258 8196)]

def readSpanSuffix : Block := Block.sequence [
  .action (.constant 8270 1),
  .action (.arithmetic .add 8194 8259 8270),
  .action (.move 8195 8258)]

def readSpanBody : Block :=
  .seq readSpanPrefix (.seq (spanBlock 8256) readSpanSuffix)

def logicalReadBlock : Block :=
  .seq (locateBlock 8192)
    (.ifZero 8194 (.action (.constant 8195 0)) readSpanBody)

@[simp] theorem readSpanBody_size : readSpanBody.size = 30 := by
  simp [readSpanBody, readSpanPrefix, readSpanSuffix, Block.sequence, Block.size]

@[simp] theorem logicalReadBlock_size :
    logicalReadBlock.size = (locateBlock 8192).size + 33 := by
  simp [logicalReadBlock, Block.size]

/-- Proof-side names for the exact five scalar prefix writes. The source and
primitive program do not call this register function. -/
def physicalSpanInputs (regs : Registers) : Registers :=
  ((((regs.write 8256 (regs 22)).write 8270 174).write 8257 (174 * regs 22)).write
    8257 (174 * regs 22 + regs 8195)).write 8258 (regs 8196)

theorem readSpanPrefix_source (memory : Memory) (regs : Registers) :
    readSpanPrefix.eval memory ⟨regs, .running⟩ =
      ⟨⟨physicalSpanInputs regs, .running⟩, []⟩ := by
  simp [readSpanPrefix, Block.sequence, Block.eval, Action.eval, Action.instruction,
    execute, State.writeNext, Data.ofState, Arithmetic.eval, physicalSpanInputs,
    Registers.write]

def ReadSpanOutcome (value : Option Nat) (length : Nat) (data : Data) : Prop :=
  match value with
  | none => data.status = .fault
  | some answer => data.status = .running ∧ data.regs 8194 = answer + 1 ∧
      data.regs 8195 = length

theorem readSpanBody_source (memory : Memory) (regs : Registers) :
    let value := decodeSpanNat (regs 22) (174 * regs 22 + regs 8195) (regs 8196) memory
    let actual := readSpanBody.eval memory ⟨regs, .running⟩
    ReadSpanOutcome value (regs 8196) actual.final ∧
    actual.reads = spanAttemptReceipts (regs 22)
      (174 * regs 22 + regs 8195) (regs 8196) memory := by
  have hspan := spanBlock_source 8256 (regs 22) (174 * regs 22 + regs 8195)
    (regs 8196) memory (physicalSpanInputs regs)
    (by simp [physicalSpanInputs, Registers.write])
    (by simp [physicalSpanInputs, Registers.write])
    (by simp [physicalSpanInputs, Registers.write])
  have hlength := spanBlock_frame 8256 memory (physicalSpanInputs regs) 8258 (by omega)
  change ((spanBlock 8256).eval memory ⟨physicalSpanInputs regs, .running⟩).final.regs 8258 =
    regs 8196 at hlength
  simp only [readSpanBody, Block.eval_seq, readSpanPrefix_source, Evaluation.bind]
  cases hvalue : decodeSpanNat (regs 22) (174 * regs 22 + regs 8195) (regs 8196) memory with
  | none =>
      have hs : ((spanBlock 8256).eval memory ⟨physicalSpanInputs regs, .running⟩).final.status =
          .fault := by simpa [SpanOutcome, hvalue] using hspan.1
      simp [ReadSpanOutcome, hs, readSpanSuffix, Block.sequence, Block.eval, hspan.2]
  | some value =>
      have hs := hspan.1
      simp only [hvalue, SpanOutcome] at hs
      simp [ReadSpanOutcome, readSpanSuffix, Block.sequence, Block.eval, Action.eval,
        Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
        Arithmetic.eval, hs.1, hs.2, hlength, hspan.2]

theorem readSpanBody_writesOnly : ReaderWrites readSpanBody := by
  simp [ReaderWrites, readSpanBody, readSpanPrefix, readSpanSuffix, spanBlock,
    Block.sequence, Block.WritesOnly, Action.destination]

theorem logicalReadBlock_writesOnly : ReaderWrites logicalReadBlock := by
  refine ⟨?_, ?_, readSpanBody_writesOnly⟩
  · exact Block.WritesOnly.mono (locateBlock 8192) (locateBlock_writesOnly 8192)
      (by intro r hr; omega)
  · change 8194 ≤ 8195 ∧ 8195 < 8271
    decide

theorem readSpanBody_frame (memory : Memory) (s : Data) :
    ReaderFrame s.regs (readSpanBody.eval memory s).final.regs := by
  intro r hr
  exact Block.eval_frame memory readSpanBody _ readSpanBody_writesOnly r (by omega) s

theorem logicalReadBlock_after_locate (memory : Memory) (regs : Registers) :
    let located := (locateBlock 8192).eval memory ⟨regs, .running⟩
    logicalReadBlock.eval memory ⟨regs, .running⟩ =
      if located.final.regs 8194 = 0 then
        ⟨⟨located.final.regs.write 8195 0, .running⟩, []⟩
      else readSpanBody.eval memory ⟨located.final.regs, .running⟩ := by
  have hl := locateBlock_source 8192 (by decide) memory regs
  dsimp only
  rw [logicalReadBlock, Block.eval_seq]
  generalize (locateBlock 8192).eval memory ⟨regs, .running⟩ = located at hl ⊢
  have hs := hl.1.1
  have hr := hl.2.1
  rcases located with ⟨⟨r, status⟩, reads⟩
  dsimp only at hs hr
  subst status reads
  simp only [Evaluation.bind, Block.eval]
  split <;> simp [Action.eval, Action.instruction, execute,
    State.writeNext, Data.ofState]

theorem logicalReadBlock_frame (memory : Memory) (regs : Registers) :
    ReaderFrame regs (logicalReadBlock.eval memory ⟨regs, .running⟩).final.regs := by
  have hl := locateBlock_source 8192 (by decide) memory regs
  intro r hr
  have hf := hl.2.2 r (by simp only [LocateFrame] at *; omega)
  rw [logicalReadBlock_after_locate]
  split
  · simpa [Registers.write, show r ≠ 8195 by omega] using hf
  · exact (readSpanBody_frame memory _ r hr).trans hf

theorem metadata_wordWidth_field (shape : CartesianShape) :
    (metadata shape)[6]? = some (wordWidth shape.size) := by
  unfold metadata
  rw [List.getElem?_append_left (by rw [List.length_append, scalarMetadata_length]; omega)]
  rw [List.getElem?_append_left (by rw [scalarMetadata_length]; decide)]
  rfl

/-- A present canonical logical span always decodes, including an empty
sentinel. The proof uses the very allocation supplied to the physical reader. -/
theorem canonical_span_decode (shape : CartesianShape) (segment index : Nat)
    (span : NumericSpan)
    (hspan : reviewerLogicalSpan shape.size (longCount shape)
      (packedReviewerSparseCount shape) segment index = some span) :
    ∃ value, decodeSpanNat (wordWidth shape.size)
      (174 * wordWidth shape.size + span.position) span.length (shapeMemory shape) =
      some value := by
  let request : PackedReviewerLogicalRequest :=
    ⟨⟨.leftSelect, 0, 0⟩, .entryBaseOccurrence, segment, index⟩
  have hw := reviewerLogicalSpan_length_le shape.size (longCount shape)
    (packedReviewerSparseCount shape) request span hspan
  have hfit := reviewerLogicalSpan_canonical_fits shape request span hspan
  have h := decodeSpanNat_repacked_span (metadata shape) (wordWidth shape.size)
    (packedReviewerMemory shape) span.position span.length (wordWidth_pos shape.size)
    (Nat.le_trans hw (Nat.le_of_lt (oldWidth_lt_wordWidth shape.size))) hfit
  rw [metadata_length] at h
  exact ⟨_, h⟩

/-- Fixed source correctness is unconditional for every canonical logical
request. Metadata is installed by setup; geometry and answers are read from
registers and raw counted cells by the source itself. -/
theorem logicalReadBlock_correct (shape : CartesianShape) :
    ReaderCorrect shape (shapeMemory shape) logicalReadBlock := by
  intro regs hmetadata
  have hl := locateBlock_canonical 8192 (by decide) shape (shapeMemory shape) regs hmetadata
  let located := (locateBlock 8192).eval (shapeMemory shape) ⟨regs, .running⟩
  have hdata : located.final = ⟨located.final.regs, .running⟩ := by
    have hs : located.final.status = .running := hl.1.1
    generalize located.final = data at hs ⊢
    cases data; simp_all
  have hwidth : located.final.regs 22 = wordWidth shape.size := by
    rw [hl.2.2 22 (Or.inl (by decide))]
    have h := hmetadata 6 (by decide)
    rw [metadata_wordWidth_field] at h
    exact h
  have hcanonical := directLogicalReadNat_eq_globalReadStore shape (regs 8192) (regs 8193)
  have hframe := logicalReadBlock_frame (shapeMemory shape) regs
  suffices h :
      (logicalReadBlock.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running ∧
      (logicalReadBlock.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 8194 =
        logicalPacket ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (regs 8192) (regs 8193)) ∧
      (logicalReadBlock.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 8195 =
        logicalLength ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (regs 8192) (regs 8193)) ∧
      (logicalReadBlock.eval (shapeMemory shape) ⟨regs, .running⟩).reads =
        readerReceipts shape (shapeMemory shape) (regs 8192) (regs 8193) from
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hframe⟩
  cases hspan : reviewerLogicalSpan shape.size (longCount shape)
      (packedReviewerSparseCount shape) (regs 8192) (regs 8193) with
  | none =>
      have hout := hl.1
      simp only [hspan, LocationResult, spanPresence, spanPosition, spanLength,
        Option.map_none, Option.getD_none] at hout
      have hreply : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (regs 8192) (regs 8193) = none := by
        simp only [directLogicalReadNat, hspan, Option.bind_none] at hcanonical
        cases hr : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            (regs 8192) (regs 8193) with
        | none => rfl
        | some bits => rw [hr, Option.map_some] at hcanonical; contradiction
      rw [logicalReadBlock_after_locate, if_pos hout.2.1, hreply]
      exact ⟨rfl, hout.2.1, rfl, by simp only [readerReceipts, hspan]⟩
  | some span =>
      have hout := hl.1
      simp only [hspan, LocationResult, spanPresence, spanPosition, spanLength,
        Option.map_some, Option.getD_some] at hout
      obtain ⟨value, hd⟩ := canonical_span_decode shape (regs 8192) (regs 8193) span hspan
      have hpair : some (value, span.length) =
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            (regs 8192) (regs 8193)).map (fun bits => (bitsToNatLE bits, bits.length)) := by
        simpa [directLogicalReadNat, hspan, metadataWordCount, hd] using hcanonical
      obtain ⟨bits, hbits, hv, hlen⟩ : ∃ bits,
          (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            (regs 8192) (regs 8193) = some bits ∧
          value = bitsToNatLE bits ∧ span.length = bits.length := by
        cases hr : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            (regs 8192) (regs 8193) with
        | none => simp [hr] at hpair
        | some bits => exact ⟨bits, rfl, by simpa only [hr, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] using hpair⟩
      have hb := readSpanBody_source (shapeMemory shape) located.final.regs
      rw [hwidth, hout.2.2.1, hout.2.2.2, hd] at hb
      simp only [ReadSpanOutcome] at hb
      rw [logicalReadBlock_after_locate]
      simp only [hout.2.1, show ¬ (1 : Nat) = 0 by decide, if_false]
      exact ⟨hb.1.1, by simpa only [hbits, logicalPacket_some, hv] using hb.1.2.1,
        by simpa only [hbits, logicalLength_some, hlen] using hb.1.2.2,
        by simpa only [readerReceipts, hspan] using hb.2⟩

def logicalReaderProgram : Program := logicalReadBlock.compileAt 0 ++ [.halt 8194]

def logicalReaderRun (memory : Memory) (regs : Registers) : Run :=
  run memory logicalReaderProgram 1069 ⟨regs, 0, .running⟩

theorem logicalReaderProgram_length : logicalReaderProgram.length = 1069 := by
  simp [logicalReaderProgram]

/-- Actual primitive execution uses exactly the same allocation and input bank
as the source theorem. Its budget includes the final halt. -/
theorem logicalReaderRun_correct (shape : CartesianShape) (regs : Registers)
    (hmetadata : MetadataMatches shape regs) :
    let expected := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
      (regs 8192) (regs 8193)
    let actual := logicalReaderRun (shapeMemory shape) regs
    actual.result = some (logicalPacket expected) ∧
    actual.final.regs 8195 = logicalLength expected ∧
    actual.reads = readerReceipts shape (shapeMemory shape) (regs 8192) (regs 8193) ∧
    actual.steps ≤ 1069 ∧ ReaderFrame regs actual.final.regs := by
  have hs := logicalReadBlock_correct shape regs hmetadata
  have hc := logicalReadBlock.compile_with_halt (shapeMemory shape) 8194
    ⟨regs, 0, .running⟩ rfl
  dsimp only [Data.ofState] at hc
  have hd := congrArg Data.regs hc.1
  simp only [Block.eval, hs.1] at hd
  have hresult := hc.2.1
  rw [hs.1] at hresult
  have hsize : logicalReadBlock.size + 1 = 1069 := by simp
  change (run (shapeMemory shape) logicalReaderProgram 1069 ⟨regs, 0, .running⟩).final.regs =
    (logicalReadBlock.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs at hd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [logicalReaderRun, logicalReaderProgram, hsize, hs.2.1] using hresult
  · change (run _ _ _ _).final.regs 8195 = _
    rw [hd]
    exact hs.2.2.1
  · simpa only [logicalReaderRun, logicalReaderProgram, hsize, hs.2.2.2.1] using hc.2.2.1
  · simpa only [logicalReaderRun, logicalReaderProgram, List.length_append,
      Block.compile_length, List.length_singleton, hsize] using hc.2.2.2
  · change ReaderFrame regs (run _ _ _ _).final.regs
    rw [hd]
    exact hs.2.2.2.2

/-- Independently written consumer pins values, exact read order and the
constant actual-instruction budget at every canonical request. -/
theorem logicalReaderRun_expectedType : ∀ (shape : CartesianShape) (regs : Registers),
    (∀ i < 174, regs (16 + i) = ((metadata shape)[i]?).getD 0) →
    (run (shapeMemory shape) (logicalReadBlock.compileAt 0 ++ [.halt 8194])
      1069 ⟨regs, 0, .running⟩).result =
      some (logicalPacket ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        (regs 8192) (regs 8193))) ∧
    (run (shapeMemory shape) (logicalReadBlock.compileAt 0 ++ [.halt 8194])
      1069 ⟨regs, 0, .running⟩).reads =
      readerReceipts shape (shapeMemory shape) (regs 8192) (regs 8193) ∧
    (run (shapeMemory shape) (logicalReadBlock.compileAt 0 ++ [.halt 8194])
      1069 ⟨regs, 0, .running⟩).steps ≤ 1069 := by
  intro shape regs hmetadata
  have h := logicalReaderRun_correct shape regs hmetadata
  exact ⟨h.1, h.2.2.1, h.2.2.2.1⟩

end RMQ.SuccinctFinal.PackedWordRAM
