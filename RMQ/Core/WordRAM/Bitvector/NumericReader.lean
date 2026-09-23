import RMQ.Core.WordRAM.Bitvector.ReaderInterface
import RMQ.Core.WordRAM.Packed.Frame

/-! # Numeric source refinement of the generic bitvector reader

The descriptor and span hypotheses concern the supplied numeric memory. They
are discharged separately by the canonical allocation proof. This module
uses the actual shared location/decoder blocks and makes no word-safety claim.
-/

namespace RMQ.PackedBitvector

open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

def numericDescriptorAddress (regs : Registers) : Nat :=
  23 + regs 3 * 92 + regs 8192 * 4

def numericDescriptorReceipts (memory : Memory) (regs : Registers) : List Receipt :=
  (List.range 4).map fun i =>
    ⟨numericDescriptorAddress regs + i, memory[numericDescriptorAddress regs + i]?⟩

private theorem eval_action (memory : Memory) (op : Action) (regs : Registers) :
    (Block.action op).eval memory ⟨regs, .running⟩ = op.eval memory ⟨regs, .running⟩ := rfl

private theorem eval_skip (memory : Memory) (s : Data) :
    Block.skip.eval memory s = ⟨s, []⟩ := by
  cases s with
  | mk regs status => cases status <;> rfl

private theorem eval_ifZero (memory : Memory) (r : Nat) (a b : Block) (regs : Registers) :
    (Block.ifZero r a b).eval memory ⟨regs, .running⟩ =
      if regs r = 0 then a.eval memory ⟨regs, .running⟩
      else b.eval memory ⟨regs, .running⟩ := rfl

/-- Descriptor loading changes only its own scratch bank. -/
theorem descriptorLoads_writes :
    Experiment.descriptorLoads.WritesOnly (fun r => 8200 ≤ r ∧ r < 8212) := by
  simp [Experiment.descriptorLoads, regularLocateBlock, natSubBlock, minBlock,
    Block.sequence, Block.WritesOnly, Action.destination]

theorem finishPacket_writes :
    Experiment.finishPacket.WritesOnly (fun r => 8194 ≤ r ∧ r < 8212) := by
  simp [Experiment.finishPacket, Block.sequence, Block.WritesOnly, Action.destination]

theorem physicalReader_writes :
    Experiment.physicalReader.WritesOnly (fun r => 8194 ≤ r ∧ r < 8271) := by
  have hd := Block.WritesOnly.mono _ descriptorLoads_writes
    (show ∀ r, 8200 ≤ r ∧ r < 8212 → 8194 ≤ r ∧ r < 8271 by omega)
  have hf := Block.WritesOnly.mono _ finishPacket_writes
    (show ∀ r, 8194 ≤ r ∧ r < 8212 → 8194 ≤ r ∧ r < 8271 by omega)
  simpa [Experiment.physicalReader, spanBlock, Block.sequence,
    Block.WritesOnly, Action.destination] using And.intro hd hf

theorem physicalReader_frame (memory : Memory) (s : Data) :
    GenericReaderFrame s.regs (Experiment.physicalReader.eval memory s).final.regs := by
  intro r hr
  exact Block.eval_frame memory _ _ physicalReader_writes r (by omega) s

@[simp] theorem descriptorLoads_size : Experiment.descriptorLoads.size = 35 := by
  simp [Experiment.descriptorLoads, Block.sequence, Block.size]

@[simp] theorem finishPacket_size : Experiment.finishPacket.size = 9 := by
  simp [Experiment.finishPacket, Block.sequence, Block.size]

@[simp] theorem physicalReader_size : Experiment.physicalReader.size = 77 := by
  simp [Experiment.physicalReader, Block.sequence, Block.size]

private def descriptorInputRegisters (regs : Registers)
    (bitBase bitLength stride count : Nat) : Registers :=
  let r := (regs.write 8208 4).write 8209 (regs 8192 * 4)
  let r := (r.write 8210 92).write 8211 (regs 3 * 92)
  let r := (r.write 8209 (regs 8192 * 4 + regs 3 * 92)).write 8210 23
  let r := (r.write 8209 (numericDescriptorAddress regs)).write 8210 1
  let r := (r.write 8201 bitBase).write 8209 (numericDescriptorAddress regs + 1)
  let r := (r.write 8202 bitLength).write 8209 (numericDescriptorAddress regs + 2)
  let r := (r.write 8203 stride).write 8209 (numericDescriptorAddress regs + 3)
  (r.write 8204 count).write 8200 (regs 8193)

private theorem descriptorLoads_eval (memory : Memory) (regs : Registers)
    (bitBase bitLength stride count : Nat)
    (hbase : memory[numericDescriptorAddress regs]? = some bitBase)
    (hlen : memory[numericDescriptorAddress regs + 1]? = some bitLength)
    (hstride : memory[numericDescriptorAddress regs + 2]? = some stride)
    (hcount : memory[numericDescriptorAddress regs + 3]? = some count) :
    Experiment.descriptorLoads.eval memory ⟨regs, .running⟩ =
      let located := (regularLocateBlock 8200).eval memory
        ⟨descriptorInputRegisters regs bitBase bitLength stride count, .running⟩
      ⟨located.final, numericDescriptorReceipts memory regs ++ located.reads⟩ := by
  have hadd2 (a : Nat) : 1 + (1 + a) = 2 + a := by omega
  have hadd3 (a : Nat) : 1 + (2 + a) = 3 + a := by omega
  simp only [numericDescriptorAddress, Nat.add_assoc, Nat.add_comm] at hbase hlen hstride hcount
  simp [Experiment.descriptorLoads, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_action, eval_skip, Action.eval, Action.instruction, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, descriptorInputRegisters,
    numericDescriptorReceipts, numericDescriptorAddress, hbase, hlen, hstride, hcount,
    Nat.add_assoc, Nat.add_comm, List.range_succ, hadd2, hadd3]

/-- Four successful charged descriptor loads feed the actual generic locator.
The locator contributes no reads; descriptor receipt order and multiplicity
are retained on the same evaluation. -/
theorem descriptorLoads_source (memory : Memory) (regs : Registers)
    (bitBase bitLength stride count : Nat)
    (hbase : memory[numericDescriptorAddress regs]? = some bitBase)
    (hlen : memory[numericDescriptorAddress regs + 1]? = some bitLength)
    (hstride : memory[numericDescriptorAddress regs + 2]? = some stride)
    (hcount : memory[numericDescriptorAddress regs + 3]? = some count) :
    LocatedSpan 8200 (regularSpan (regs 8193) bitBase bitLength stride count)
      (Experiment.descriptorLoads.eval memory ⟨regs, .running⟩).final ∧
    (Experiment.descriptorLoads.eval memory ⟨regs, .running⟩).reads =
      numericDescriptorReceipts memory regs := by
  rw [descriptorLoads_eval memory regs bitBase bitLength stride count hbase hlen hstride hcount]
  have h := regularLocateBlock_source 8200 memory
    (descriptorInputRegisters regs bitBase bitLength stride count)
  constructor
  · simpa [descriptorInputRegisters, Registers.write] using h.1
  · simp only [h.2, List.append_nil]

theorem finishPacket_source (memory : Memory) (regs : Registers) :
    let actual := Experiment.finishPacket.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧
    actual.final.regs 8194 =
      (if regs 8192 = 0 ∧ regs 3 ≠ 0 then 2 ^ regs 8207 - regs 8259 else regs 8259 + 1) ∧
    actual.final.regs 8195 = regs 8207 ∧ actual.reads = [] := by
  have hshift : Nat.shiftLeft 1 (regs 8207) = 2 ^ regs 8207 := by
    simpa using Nat.shiftLeft_eq 1 (regs 8207)
  by_cases hs : regs 8192 = 0 <;> by_cases ht : regs 3 = 0
  all_goals simp [Experiment.finishPacket, Block.sequence, Block.eval_seq,
    Evaluation.bind, eval_action, eval_skip, eval_ifZero, Action.eval, Action.instruction,
    execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
    hs, ht, hshift]

theorem physicalReader_outside (memory : Memory) (regs : Registers)
    (outside : 23 ≤ regs 8192) :
    let actual := Experiment.physicalReader.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 8194 = 0 ∧
    actual.final.regs 8195 = 0 ∧ actual.reads = [] ∧
    GenericReaderFrame regs actual.final.regs := by
  have hframe := physicalReader_frame memory ⟨regs, .running⟩
  refine ⟨?_, ?_, ?_, ?_, hframe⟩
  all_goals simp [Experiment.physicalReader, Block.sequence, Block.eval_seq,
    Evaluation.bind, eval_action, eval_skip, eval_ifZero, Action.eval, Action.instruction,
    execute, State.writeNext, Data.ofState, Registers.write, Comparison.eval,
    show ¬ regs 8192 < 23 by omega]

private def readerPreparedRegisters (regs : Registers) : Registers :=
  (((regs.write 8194 0).write 8195 0).write 8208 23).write 8209 1

private def spanPreparedRegisters (regs : Registers) : Registers :=
  ((regs.write 8256 (regs 22)).write 8257 (regs 8206)).write 8258 (regs 8207)

private theorem readerSpan_source (memory : Memory) (regs : Registers) (value : Nat)
    (decoded : decodeSpanNat (regs 22) (regs 8206) (regs 8207) memory = some value) :
    let actual := (Block.sequence [
      .action (.move 8256 22), .action (.move 8257 8206),
      .action (.move 8258 8207), spanBlock 8256, Experiment.finishPacket]).eval
        memory ⟨regs, .running⟩
    actual.final.status = .running ∧
    actual.final.regs 8194 =
      (if regs 8192 = 0 ∧ regs 3 ≠ 0 then 2 ^ regs 8207 - value else value + 1) ∧
    actual.final.regs 8195 = regs 8207 ∧
    actual.reads = spanAttemptReceipts (regs 22) (regs 8206) (regs 8207) memory := by
  let prepared := spanPreparedRegisters regs
  have hw : prepared 8256 = regs 22 := by simp [prepared, spanPreparedRegisters, Registers.write]
  have hp : prepared 8257 = regs 8206 := by simp [prepared, spanPreparedRegisters, Registers.write]
  have hl : prepared 8258 = regs 8207 := by simp [prepared, spanPreparedRegisters]
  have hs := spanBlock_source 8256 (regs 22) (regs 8206) (regs 8207) memory prepared hw hp hl
  have hf (r : Nat) (hr : r < 8259 ∨ 8270 ≤ r) :=
    spanBlock_frame 8256 memory prepared r hr
  generalize hd : (spanBlock 8256).eval memory ⟨prepared, .running⟩ = loaded at hs hf
  rcases loaded with ⟨⟨out, status⟩, reads⟩
  simp only [decoded, SpanOutcome] at hs
  obtain ⟨⟨hstatus, hvalue⟩, hreads⟩ := hs
  subst status
  have hsegment : out 8192 = regs 8192 := by
    simpa [prepared, spanPreparedRegisters, Registers.write] using hf 8192 (by omega)
  have htarget : out 3 = regs 3 := by
    simpa [prepared, spanPreparedRegisters, Registers.write] using hf 3 (by omega)
  have hlength : out 8207 = regs 8207 := by
    simpa [prepared, spanPreparedRegisters, Registers.write] using hf 8207 (by omega)
  have hfinish := finishPacket_source memory out
  generalize he : Experiment.finishPacket.eval memory ⟨out, .running⟩ = finished at hfinish
  rcases finished with ⟨⟨finalRegs, finalStatus⟩, finalReads⟩
  dsimp only at hfinish
  obtain ⟨hfinalStatus, hpacket, hfinalLength, hfinalReads⟩ := hfinish
  subst finalStatus
  subst finalReads
  simp only [prepared, spanPreparedRegisters] at hd
  simp [Block.sequence, Block.eval_seq, Evaluation.bind, eval_action, eval_skip,
    Action.eval, Action.instruction, execute, State.writeNext, Data.ofState,
    Registers.write, hd, he, hpacket,
    hfinalLength, hvalue, hreads, hsegment, htarget, hlength]

theorem physicalReader_absent (memory : Memory) (regs : Registers)
    (bitBase bitLength stride count : Nat) (segment : regs 8192 < 23)
    (hbase : memory[numericDescriptorAddress regs]? = some bitBase)
    (hlen : memory[numericDescriptorAddress regs + 1]? = some bitLength)
    (hstride : memory[numericDescriptorAddress regs + 2]? = some stride)
    (hcount : memory[numericDescriptorAddress regs + 3]? = some count)
    (absent : count ≤ regs 8193) :
    let actual := Experiment.physicalReader.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 8194 = 0 ∧
    actual.final.regs 8195 = 0 ∧
    actual.reads = numericDescriptorReceipts memory regs ∧
    GenericReaderFrame regs actual.final.regs := by
  let prepared := readerPreparedRegisters regs
  have haddress : numericDescriptorAddress prepared = numericDescriptorAddress regs := by
    simp [prepared, readerPreparedRegisters, numericDescriptorAddress, Registers.write]
  have hs := descriptorLoads_source memory prepared bitBase bitLength stride count
    (by simpa only [haddress] using hbase) (by simpa only [haddress] using hlen)
    (by simpa only [haddress] using hstride) (by simpa only [haddress] using hcount)
  have hf (r : Nat) (hr : r < 8200 ∨ 8212 ≤ r) :=
    Block.eval_frame memory _ _ descriptorLoads_writes r (by omega) ⟨prepared, .running⟩
  generalize hd : Experiment.descriptorLoads.eval memory ⟨prepared, .running⟩ = loaded at hs hf
  rcases loaded with ⟨⟨out, status⟩, reads⟩
  have hindex : prepared 8193 = regs 8193 := by
    simp [prepared, readerPreparedRegisters, Registers.write]
  have hn : ¬ prepared 8193 < count := by omega
  simp only [LocatedSpan, regularSpan, hn, ↓reduceIte] at hs
  obtain ⟨⟨hstatus, hpresent, _hposition, _hlength⟩, hreads⟩ := hs
  subst status
  have hpacket : out 8194 = 0 := by
    simpa [prepared, readerPreparedRegisters, Registers.write] using hf 8194 (by omega)
  have hlength : out 8195 = 0 := by
    simpa [prepared, readerPreparedRegisters, Registers.write] using hf 8195 (by omega)
  have hframe := physicalReader_frame memory ⟨regs, .running⟩
  simp only [prepared, readerPreparedRegisters] at hd
  refine ⟨?_, ?_, ?_, ?_, hframe⟩
  all_goals simp [Experiment.physicalReader, Block.sequence, Block.eval_seq,
    Evaluation.bind, eval_action, eval_skip, eval_ifZero, Action.eval, Action.instruction,
    execute, State.writeNext, Data.ofState, Registers.write, Comparison.eval,
    segment, hd, hpresent, hpacket, hlength,
    hreads, numericDescriptorReceipts, haddress]

theorem physicalReader_present (memory : Memory) (regs : Registers)
    (bitBase bitLength stride count value : Nat) (segment : regs 8192 < 23)
    (hbase : memory[numericDescriptorAddress regs]? = some bitBase)
    (hlen : memory[numericDescriptorAddress regs + 1]? = some bitLength)
    (hstride : memory[numericDescriptorAddress regs + 2]? = some stride)
    (hcount : memory[numericDescriptorAddress regs + 3]? = some count)
    (present : regs 8193 < count)
    (decoded : decodeSpanNat (regs 22) (bitBase + regs 8193 * stride)
      (min stride (bitLength - regs 8193 * stride)) memory = some value) :
    let len := min stride (bitLength - regs 8193 * stride)
    let actual := Experiment.physicalReader.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧
    actual.final.regs 8194 =
      (if regs 8192 = 0 ∧ regs 3 ≠ 0 then 2 ^ len - value else value + 1) ∧
    actual.final.regs 8195 = len ∧
    actual.reads = numericDescriptorReceipts memory regs ++
      spanAttemptReceipts (regs 22) (bitBase + regs 8193 * stride) len memory ∧
    GenericReaderFrame regs actual.final.regs := by
  let prepared := readerPreparedRegisters regs
  have haddress : numericDescriptorAddress prepared = numericDescriptorAddress regs := by
    simp [prepared, readerPreparedRegisters, numericDescriptorAddress, Registers.write]
  have hs := descriptorLoads_source memory prepared bitBase bitLength stride count
    (by simpa only [haddress] using hbase) (by simpa only [haddress] using hlen)
    (by simpa only [haddress] using hstride) (by simpa only [haddress] using hcount)
  have hf (r : Nat) (hr : r < 8200 ∨ 8212 ≤ r) :=
    Block.eval_frame memory _ _ descriptorLoads_writes r (by omega) ⟨prepared, .running⟩
  generalize hd : Experiment.descriptorLoads.eval memory ⟨prepared, .running⟩ = loaded at hs hf
  rcases loaded with ⟨⟨out, status⟩, reads⟩
  have hindex : prepared 8193 = regs 8193 := by
    simp [prepared, readerPreparedRegisters, Registers.write]
  simp only [LocatedSpan, regularSpan, hindex, present, ↓reduceIte] at hs
  obtain ⟨⟨hstatus, hpresent, hposition, hlength⟩, hreads⟩ := hs
  subst status
  have hsegment : out 8192 = regs 8192 := by
    simpa [prepared, readerPreparedRegisters, Registers.write] using hf 8192 (by omega)
  have htarget : out 3 = regs 3 := by
    simpa [prepared, readerPreparedRegisters, Registers.write] using hf 3 (by omega)
  have hwidth : out 22 = regs 22 := by
    simpa [prepared, readerPreparedRegisters, Registers.write] using hf 22 (by omega)
  have hbody := readerSpan_source memory out value
    (by simpa only [hwidth, hposition, hlength] using decoded)
  simp [Block.sequence, Block.eval_seq, Evaluation.bind, eval_action, eval_skip,
    Action.eval, Action.instruction, execute, State.writeNext, Data.ofState,
    Registers.write, hsegment, htarget, hwidth, hposition, hlength] at hbody
  obtain ⟨hfinalStatus, hpacket, hfinalLength, hfinalReads⟩ := hbody
  have hframe := physicalReader_frame memory ⟨regs, .running⟩
  simp only [prepared, readerPreparedRegisters] at hd
  refine ⟨?_, ?_, ?_, ?_, hframe⟩
  all_goals simp [Experiment.physicalReader, Block.sequence, Block.eval_seq,
    Evaluation.bind, eval_action, eval_skip, eval_ifZero, Action.eval, Action.instruction,
    execute, State.writeNext, Data.ofState, Registers.write, Comparison.eval,
    segment, hd, hpresent, hfinalStatus,
    hpacket, hfinalLength, hfinalReads, hreads, numericDescriptorReceipts, haddress,
    hwidth, hposition, hlength]

/-- A missing first descriptor reply faults immediately. In particular the
four-receipt canonical specification is not asserted for arbitrary memory. -/
theorem physicalReader_first_descriptor_missing (memory : Memory) (regs : Registers)
    (segment : regs 8192 < 23)
    (missing : memory[numericDescriptorAddress regs]? = none) :
    let actual := Experiment.physicalReader.eval memory ⟨regs, .running⟩
    actual.final.status = .fault ∧
    actual.reads = [⟨numericDescriptorAddress regs, none⟩] ∧
    GenericReaderFrame regs actual.final.regs := by
  have hframe := physicalReader_frame memory ⟨regs, .running⟩
  simp only [numericDescriptorAddress, Nat.add_assoc] at missing
  refine ⟨?_, ?_, hframe⟩
  all_goals simp [Experiment.physicalReader, Experiment.descriptorLoads,
    Block.sequence, Block.eval_seq, Evaluation.bind, eval_action,
    eval_ifZero, Action.eval, Action.instruction, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval,
    Block.eval_stopped, segment, missing, numericDescriptorAddress,
    Nat.add_assoc, Nat.add_comm]

/-- Present empty sentinels return the present-zero packet for either target,
with no payload attempt and no assumption on their nominal bit position. -/
theorem physicalReader_present_empty (memory : Memory) (regs : Registers)
    (bitBase bitLength stride count : Nat) (segment : regs 8192 < 23)
    (hbase : memory[numericDescriptorAddress regs]? = some bitBase)
    (hlen : memory[numericDescriptorAddress regs + 1]? = some bitLength)
    (hstride : memory[numericDescriptorAddress regs + 2]? = some stride)
    (hcount : memory[numericDescriptorAddress regs + 3]? = some count)
    (present : regs 8193 < count)
    (empty : min stride (bitLength - regs 8193 * stride) = 0) :
    let actual := Experiment.physicalReader.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 8194 = 1 ∧
    actual.final.regs 8195 = 0 ∧
    actual.reads = numericDescriptorReceipts memory regs ∧
    GenericReaderFrame regs actual.final.regs := by
  have h := physicalReader_present memory regs bitBase bitLength stride count 0 segment
    hbase hlen hstride hcount present (by simp [empty, decodeSpanNat])
  simpa [empty, spanAttemptReceipts] using h

/-- The present-source consumer pins the full successful-descriptor interface,
including actual output, ordered attempts and frame on the same evaluation. -/
example (memory : Memory) (regs : Registers)
    (bitBase bitLength stride count value : Nat) (segment : regs 8192 < 23)
    (hbase : memory[numericDescriptorAddress regs]? = some bitBase)
    (hlen : memory[numericDescriptorAddress regs + 1]? = some bitLength)
    (hstride : memory[numericDescriptorAddress regs + 2]? = some stride)
    (hcount : memory[numericDescriptorAddress regs + 3]? = some count)
    (present : regs 8193 < count)
    (decoded : decodeSpanNat (regs 22) (bitBase + regs 8193 * stride)
      (min stride (bitLength - regs 8193 * stride)) memory = some value) :
    let len := min stride (bitLength - regs 8193 * stride)
    let actual := Experiment.physicalReader.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧
    actual.final.regs 8194 =
      (if regs 8192 = 0 ∧ regs 3 ≠ 0 then 2 ^ len - value else value + 1) ∧
    actual.final.regs 8195 = len ∧
    actual.reads = numericDescriptorReceipts memory regs ++
      spanAttemptReceipts (regs 22) (bitBase + regs 8193 * stride) len memory ∧
    GenericReaderFrame regs actual.final.regs :=
  physicalReader_present memory regs bitBase bitLength stride count value segment
    hbase hlen hstride hcount present decoded

#print axioms descriptorLoads_source
#print axioms finishPacket_source
#print axioms physicalReader_writes
#print axioms physicalReader_frame
#print axioms physicalReader_outside
#print axioms physicalReader_absent
#print axioms physicalReader_present
#print axioms physicalReader_first_descriptor_missing
#print axioms physicalReader_present_empty

end RMQ.PackedBitvector
