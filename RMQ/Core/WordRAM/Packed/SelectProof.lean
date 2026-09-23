import RMQ.Core.WordRAM.Packed.SelectSource
import RMQ.Core.WordRAM.Packed.ReadInterface
import RMQ.Core.WordRAM.Packed.PhysicalRead
import RMQ.Core.WordRAM.Packed.RankProof

/-!
# Value, ordered physical reads and primitive execution for close select

The source receives only fixed blocks and register numbers. The canonical
store and geometry in this module are reference objects used in proofs.
-/

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

private theorem eval_skip_any (memory : Memory) (s : Data) :
    Block.skip.eval memory s = ⟨s, []⟩ := by
  cases s with
  | mk regs status => cases status <;> rfl

private theorem eval_ifZero (memory : Memory) (regs : Registers) (condition : Nat)
    (zero nonzero : Block) :
    (Block.ifZero condition zero nonzero).eval memory ⟨regs, .running⟩ =
      if regs condition = 0 then zero.eval memory ⟨regs, .running⟩
      else nonzero.eval memory ⟨regs, .running⟩ := rfl

private theorem data_eq_running (s : Data) (hs : s.status = .running) :
    s = ⟨s.regs, .running⟩ := by cases s; simp_all

private theorem eval_seq_of_results (memory : Memory) (first second : Block) (s : Data)
    (a b : Evaluation) (ha : first.eval memory s = a)
    (hb : second.eval memory a.final = b) :
    (Block.seq first second).eval memory s = ⟨b.final, a.reads ++ b.reads⟩ := by
  rw [Block.eval_seq, ha]
  simp only [Evaluation.bind, hb]

private theorem writes_metadata (shape : CartesianShape) (memory : Memory)
    (block : Block) (allowed : Nat → Prop) (writes : block.WritesOnly allowed)
    (outside : ∀ r, 16 ≤ r → r < 190 → ¬ allowed r)
    (s : Data) (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape (block.eval memory s).final.regs := by
  intro i hi
  rw [Block.eval_frame memory block allowed writes _ (outside _ (by omega) (by omega))]
  exact hm i hi

def SelectFieldWrites (destination r : Nat) : Prop :=
  r = destination ∨ (8192 ≤ r ∧ r < 8271)

theorem selectFieldRead_writes (reader : Block) (hr : ReaderWrites reader)
    (segment indexReg destination : Nat) :
    (selectFieldRead reader segment indexReg destination).WritesOnly (SelectFieldWrites destination) := by
  have hreader : reader.WritesOnly (SelectFieldWrites destination) :=
    Block.WritesOnly.mono reader hr (by intro r h; exact Or.inr ⟨by omega, h.2⟩)
  simpa [selectFieldRead, Block.sequence, Block.WritesOnly, Action.destination,
    SelectFieldWrites] using hreader

theorem selectFieldRead_frame (reader : Block) (hr : ReaderWrites reader)
    (segment indexReg destination : Nat) (memory : Memory) (s : Data) (r : Nat)
    (outside : r ≠ destination ∧ (r < 8192 ∨ 8271 ≤ r)) :
    ((selectFieldRead reader segment indexReg destination).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (selectFieldRead_writes reader hr segment indexReg destination)
    r (by unfold SelectFieldWrites; omega) s

theorem selectFieldRead_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (segment indexReg destination : Nat) (hd : 190 ≤ destination)
    (memory : Memory) (s : Data) (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((selectFieldRead reader segment indexReg destination).eval memory s).final.regs :=
  writes_metadata shape memory _ _ (selectFieldRead_writes reader hr segment indexReg destination)
    (by intro r hlo hhi; unfold SelectFieldWrites; omega) s hm

theorem selectFieldRead_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (segment indexReg destination : Nat)
    (hi : indexReg < 8192) (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (selectFieldRead reader segment indexReg destination).eval memory ⟨regs, .running⟩
    let expected := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment (regs indexReg)
    actual.final.status = .running ∧ actual.final.regs destination = logicalPacket expected ∧
      actual.reads = readerReceipts shape memory segment (regs indexReg) := by
  let prepared := (regs.write 8192 segment).write 8193 (regs indexReg)
  have hmeta : MetadataMatches shape prepared :=
    MetadataMatches.write shape _
      (MetadataMatches.write shape regs hm 8192 segment (Or.inr (by decide)))
      8193 (regs indexReg) (Or.inr (by decide))
  have h := hreader prepared hmeta
  generalize he : reader.eval memory ⟨prepared, .running⟩ = loaded at h
  rcases loaded with ⟨⟨out, status⟩, reads⟩
  dsimp only at h
  obtain ⟨hstatus, hpacket, _hlength, hreads, _hframe⟩ := h
  subst status
  have hi2 : indexReg ≠ 8192 := by omega
  simp [prepared, Registers.write] at he hpacket hreads
  simpa [selectFieldRead, Block.sequence, Block.eval_seq, Evaluation.bind, eval_move,
    eval_constant, eval_skip, Registers.write, hi2, he] using And.intro hpacket hreads

@[simp] theorem selectFieldRead_size (reader : Block) (segment indexReg destination : Nat) :
    (selectFieldRead reader segment indexReg destination).size = 3 + reader.size := by
  simp [selectFieldRead, Block.sequence, Block.size]
  omega

def SelectFieldsWrites (destination count r : Nat) : Prop :=
  (destination ≤ r ∧ r < destination + count) ∨ (8192 ≤ r ∧ r < 8271)

theorem selectFieldsFrom_writes (reader : Block) (hr : ReaderWrites reader)
    (segment indexReg destination count : Nat) :
    (selectFieldsFrom reader segment indexReg destination count).WritesOnly
      (SelectFieldsWrites destination count) := by
  induction count generalizing segment destination with
  | zero => trivial
  | succ count ih =>
      refine ⟨Block.WritesOnly.mono _ (selectFieldRead_writes reader hr segment indexReg destination) ?_,
        Block.WritesOnly.mono _ (ih (segment + 1) (destination + 1)) ?_⟩
      all_goals intro r h; simp only [SelectFieldsWrites, SelectFieldWrites] at *; omega

theorem selectFieldsFrom_frame (reader : Block) (hr : ReaderWrites reader)
    (segment indexReg destination count : Nat) (memory : Memory) (s : Data) (r : Nat)
    (outside : (r < destination ∨ destination + count ≤ r) ∧ (r < 8192 ∨ 8271 ≤ r)) :
    ((selectFieldsFrom reader segment indexReg destination count).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (selectFieldsFrom_writes reader hr segment indexReg destination count)
    r (by unfold SelectFieldsWrites; omega) s

def selectFieldsReceipts (shape : CartesianShape) (memory : Memory)
    (segment index : Nat) : Nat → List Receipt
  | 0 => []
  | count + 1 => readerReceipts shape memory segment index ++
      selectFieldsReceipts shape memory (segment + 1) index count

theorem selectFieldsFrom_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (segment indexReg destination count : Nat) (hd : 190 ≤ destination)
    (hupper : destination + count ≤ 8192) (hi : indexReg < 8192)
    (hout : indexReg < destination ∨ destination + count ≤ indexReg)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (selectFieldsFrom reader segment indexReg destination count).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧
      (∀ j < count, actual.final.regs (destination + j) = logicalPacket
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? (segment + j) (regs indexReg))) ∧
      actual.reads = selectFieldsReceipts shape memory segment (regs indexReg) count ∧
      MetadataMatches shape actual.final.regs := by
  induction count generalizing segment destination regs with
  | zero => exact ⟨rfl, by intro j hj; omega, rfl, hm⟩
  | succ count ih =>
      have hfirst := selectFieldRead_source shape memory reader hreader segment indexReg destination hi regs hm
      have hmeta := selectFieldRead_metadata shape reader hwrites segment indexReg destination hd
        memory ⟨regs, .running⟩ hm
      have hindex := selectFieldRead_frame reader hwrites segment indexReg destination memory
        ⟨regs, .running⟩ indexReg ⟨by omega, Or.inl hi⟩
      generalize he : (selectFieldRead reader segment indexReg destination).eval memory
        ⟨regs, .running⟩ = first at hfirst hmeta hindex
      rcases first with ⟨⟨out, status⟩, reads⟩
      dsimp only at hfirst hmeta hindex
      obtain ⟨hstatus, hvalue, hreads⟩ := hfirst
      subst status
      have htail := ih (segment + 1) (destination + 1) (by omega) (by omega) (by omega) out hmeta
      rw [hindex] at htail
      have hkeep := selectFieldsFrom_frame reader hwrites (segment + 1) indexReg
        (destination + 1) count memory ⟨out, .running⟩ destination
        ⟨Or.inl (by omega), Or.inl (by omega)⟩
      rw [selectFieldsFrom, Block.eval_seq, he]
      simp only [Evaluation.bind]
      refine ⟨htail.1, ?_, ?_, htail.2.2.2⟩
      · intro j hj
        cases j with
        | zero => simpa only [Nat.add_zero] using hkeep.trans hvalue
        | succ j =>
            have ht := htail.2.1 j (by omega)
            simpa only [Nat.add_assoc, Nat.add_comm 1 j] using ht
      · rw [hreads, htail.2.2.1]
        rfl

@[simp] theorem selectFieldsFrom_size (reader : Block) (segment indexReg destination count : Nat) :
    (selectFieldsFrom reader segment indexReg destination count).size = count * (3 + reader.size) := by
  induction count generalizing segment destination with
  | zero => simp [selectFieldsFrom, Block.size]
  | succ count ih =>
      simp only [selectFieldsFrom, Block.size, selectFieldRead_size, ih, Nat.succ_mul]
      omega

def SelectEntryResult (base : Nat) (entry : Option GenericSelect.SparseDenseSelectDenseLocalEntry)
    (data : Data) : Prop :=
  data.status = .running ∧ match entry with
    | none => data.regs base = 0
    | some e => data.regs base = 1 ∧ data.regs (base + 1) = e.baseOccurrence ∧
        data.regs (base + 2) = e.baseWordIndex ∧ data.regs (base + 3) = e.rankBefore ∧
        data.regs (base + 4) = e.firstOffset

def selectEntryOfPackets (p0 p1 p2 p3 : Nat) : Option GenericSelect.SparseDenseSelectDenseLocalEntry :=
  if p0 = 0 ∨ p1 = 0 ∨ p2 = 0 ∨ p3 = 0 then none
  else some ⟨p0 - 1, p1 - 1, p2 - 1, p3 - 1⟩

theorem selectEntryDecode_source (base : Nat) (memory : Memory) (regs : Registers)
    (hzero : regs base = 0) (hone : regs (base + 9) = 1) :
    let actual := (selectEntryDecode base).eval memory ⟨regs, .running⟩
    SelectEntryResult base (selectEntryOfPackets (regs (base + 5)) (regs (base + 6))
      (regs (base + 7)) (regs (base + 8))) actual.final ∧ actual.reads = [] := by
  have hsub (i : Nat) (hi : i < 4) (r : Registers) :=
    natSubBlock_source (base + (i + 1)) (base + (i + 5)) (base + 9) (base + 10)
      memory r (by omega) (by omega)
  by_cases h5 : regs (base + 5) = 0
  · simp [selectEntryDecode, selectEntryOfPackets, SelectEntryResult, eval_ifZero, eval_skip, h5, hzero]
  by_cases h6 : regs (base + 6) = 0
  · simp [selectEntryDecode, selectEntryOfPackets, SelectEntryResult, eval_ifZero, eval_skip, h5, h6, hzero]
  by_cases h7 : regs (base + 7) = 0
  · simp [selectEntryDecode, selectEntryOfPackets, SelectEntryResult, eval_ifZero, eval_skip, h5, h6, h7, hzero]
  by_cases h8 : regs (base + 8) = 0
  · simp [selectEntryDecode, selectEntryOfPackets, SelectEntryResult, eval_ifZero, eval_skip, h5, h6, h7, h8, hzero]
  simp [selectEntryDecode, selectEntryOfPackets, SelectEntryResult, eval_ifZero, eval_skip,
    Block.sequence, Block.eval_seq, Evaluation.bind, eval_constant, Registers.write,
    hsub 0 (by decide), hsub 1 (by decide), hsub 2 (by decide), hsub 3 (by decide),
    h5, h6, h7, h8, hone]

theorem selectEntryOfPackets_logicalPacket (a b c d : Option (List Bool)) :
    selectEntryOfPackets (logicalPacket a) (logicalPacket b) (logicalPacket c) (logicalPacket d) =
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields
        (a.map bitsToNatLE) (b.map bitsToNatLE) (c.map bitsToNatLE) (d.map bitsToNatLE) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [selectEntryOfPackets, logicalPacket,
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields]

def selectEntryLayout (segment : Nat) : GenericSelect.SparseDenseEntryTableTraceSegmentBases :=
  ⟨segment, segment + 1, segment + 2, segment + 3, 29⟩

theorem selectEntryRead_value (store : WordRAM.ReadStore)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases) (index : Nat) :
    (packedSelectEntryRead layout store index).value =
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields
        ((store.readWord? layout.baseOccurrence index).map bitsToNatLE)
        ((store.readWord? layout.baseWordIndex index).map bitsToNatLE)
        ((store.readWord? layout.rankBefore index).map bitsToNatLE)
        ((store.readWord? layout.firstOffset index).map bitsToNatLE) := by
  change GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields
    ((store.readWord? layout.baseOccurrence index).map WordRAM.bitsToNatLE)
    ((store.readWord? layout.baseWordIndex index).map WordRAM.bitsToNatLE)
    ((store.readWord? layout.rankBefore index).map WordRAM.bitsToNatLE)
    ((store.readWord? layout.firstOffset index).map WordRAM.bitsToNatLE) = _
  have hdecode : WordRAM.bitsToNatLE = bitsToNatLE := funext WordRAMBridge.bitsToNatLE_eq
  rw [hdecode]

theorem selectEntryRead_trace (store : WordRAM.ReadStore)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases) (index : Nat) :
    (packedSelectEntryRead layout store index).trace =
      [.readWord layout.baseOccurrence index (store.readWord? layout.baseOccurrence index),
       .readWord layout.baseWordIndex index (store.readWord? layout.baseWordIndex index),
       .readWord layout.rankBefore index (store.readWord? layout.rankBefore index),
       .readWord layout.firstOffset index (store.readWord? layout.firstOffset index)] := rfl

theorem selectEntryRead_readOnly (store : WordRAM.ReadStore)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases) (index : Nat) :
    ReadOnlyTrace (packedSelectEntryRead layout store index).trace := by
  rw [selectEntryRead_trace]
  simp [ReadOnlyTrace, WordRAM.TraceEvent.isReadWord]

def SelectEntryWrites (base r : Nat) : Prop :=
  (base ≤ r ∧ r < base + 11) ∨ (8192 ≤ r ∧ r < 8271)

theorem selectEntryDecode_writes (base : Nat) :
    (selectEntryDecode base).WritesOnly (SelectEntryWrites base) := by
  simp [selectEntryDecode, Block.sequence, Block.WritesOnly, Action.destination,
    natSubBlock, SelectEntryWrites]

theorem selectEntryBlock_writes (reader : Block) (hr : ReaderWrites reader)
    (segment indexReg base : Nat) :
    (selectEntryBlock reader segment indexReg base).WritesOnly (SelectEntryWrites base) := by
  have hf := Block.WritesOnly.mono _
    (selectFieldsFrom_writes reader hr segment indexReg (base + 5) 4)
    (show ∀ r, SelectFieldsWrites (base + 5) 4 r → SelectEntryWrites base r by
      intro r h; unfold SelectFieldsWrites SelectEntryWrites at *; omega)
  have hd := selectEntryDecode_writes base
  simpa [selectEntryBlock, selectEntryFields, Block.sequence, Block.WritesOnly,
    Action.destination, SelectEntryWrites] using And.intro hf hd

theorem selectEntryBlock_frame (reader : Block) (hr : ReaderWrites reader)
    (segment indexReg base : Nat) (memory : Memory) (s : Data) (r : Nat)
    (outside : ¬ SelectEntryWrites base r) :
    ((selectEntryBlock reader segment indexReg base).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (selectEntryBlock_writes reader hr segment indexReg base) r outside s

theorem selectEntryBlock_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (segment indexReg base : Nat) (hb : 190 ≤ base)
    (memory : Memory) (s : Data) (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((selectEntryBlock reader segment indexReg base).eval memory s).final.regs :=
  writes_metadata shape memory _ _ (selectEntryBlock_writes reader hr segment indexReg base)
    (by intro r hlo hhi; unfold SelectEntryWrites; omega) s hm

theorem selectEntryBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (segment indexReg base : Nat) (hb : 190 ≤ base) (hupper : base + 11 ≤ 8192)
    (hi : indexReg < 8192) (hout : indexReg < base ∨ base + 11 ≤ indexReg)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (selectEntryBlock reader segment indexReg base).eval memory ⟨regs, .running⟩
    let expected := packedSelectEntryRead (selectEntryLayout segment)
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) (regs indexReg)
    SelectEntryResult base expected.value actual.final ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let prepared := (regs.write base 0).write (base + 9) 1
  have hmeta : MetadataMatches shape prepared :=
    MetadataMatches.write shape _ (MetadataMatches.write shape regs hm base 0 (Or.inr hb))
      (base + 9) 1 (Or.inr (by omega))
  have hi0 : indexReg ≠ base := by omega
  have hi9 : indexReg ≠ base + 9 := by omega
  have hpindex : prepared indexReg = regs indexReg := by simp [prepared, Registers.write, hi0, hi9]
  have hf := selectFieldsFrom_source shape memory reader hreader hwrites segment indexReg (base + 5) 4
    (by omega) (by omega) hi (by omega) prepared hmeta
  have hbase := selectFieldsFrom_frame reader hwrites segment indexReg (base + 5) 4 memory
    ⟨prepared, .running⟩ base ⟨Or.inl (by omega), Or.inl (by omega)⟩
  have hone := selectFieldsFrom_frame reader hwrites segment indexReg (base + 5) 4 memory
    ⟨prepared, .running⟩ (base + 9) ⟨Or.inr (by omega), Or.inl (by omega)⟩
  generalize he : (selectFieldsFrom reader segment indexReg (base + 5) 4).eval memory
    ⟨prepared, .running⟩ = fetched at hf hbase hone
  rcases fetched with ⟨⟨out, status⟩, reads⟩
  dsimp only at hf hbase hone
  obtain ⟨hstatus, hfields, hreads, _houtmeta⟩ := hf
  subst status
  simp [prepared, Registers.write] at hbase hone
  rw [hpindex] at hfields hreads
  have hd := selectEntryDecode_source base memory out hbase hone
  generalize heD : (selectEntryDecode base).eval memory ⟨out, .running⟩ = decoded at hd
  rcases decoded with ⟨⟨finalRegs, finalStatus⟩, finalReads⟩
  dsimp only at hd
  have hreadD := hd.2
  subst finalReads
  have hv0 := hfields 0 (by decide)
  have hv1 := hfields 1 (by decide)
  have hv2 := hfields 2 (by decide)
  have hv3 := hfields 3 (by decide)
  simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at hv0 hv1 hv2 hv3
  have hvalue := hd.1
  rw [hv0, hv1, hv2, hv3, selectEntryOfPackets_logicalPacket] at hvalue
  have hresult : SelectEntryResult base
      (packedSelectEntryRead (selectEntryLayout segment)
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) (regs indexReg)).value
      ⟨finalRegs, finalStatus⟩ := by
    rw [selectEntryRead_value]
    exact hvalue
  have hs : finalStatus = .running := hresult.1
  subst finalStatus
  simp [prepared] at he
  have heval : (selectEntryBlock reader segment indexReg base).eval memory ⟨regs, .running⟩ =
      ⟨⟨finalRegs, .running⟩, reads⟩ := by
    simp [selectEntryBlock, selectEntryFields, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_constant, eval_skip, he, heD]
  rw [heval]
  refine ⟨hresult, ?_, selectEntryRead_readOnly _ _ _⟩
  rw [hreads, selectEntryRead_trace]
  simp [selectFieldsReceipts, selectEntryLayout, logicalTraceReads]

@[simp] theorem selectEntryDecode_size (base : Nat) : (selectEntryDecode base).size = 29 := by
  simp [selectEntryDecode, Block.sequence, Block.size, natSubBlock_size]

@[simp] theorem selectEntryBlock_size (reader : Block) (segment indexReg base : Nat) :
    (selectEntryBlock reader segment indexReg base).size = 43 + 4 * reader.size := by
  simp [selectEntryBlock, selectEntryFields, Block.sequence, Block.size, selectFieldsFrom_size]
  omega

def optionNatPacket (value : Option Nat) : Nat := (value.map (· + 1)).getD 0

@[simp] theorem select_logicalTraceReads_append (shape : CartesianShape) (memory : Memory)
    (first second : List WordRAM.TraceEvent) :
    logicalTraceReads shape memory (first ++ second) =
      logicalTraceReads shape memory first ++ logicalTraceReads shape memory second := by
  simp [logicalTraceReads]

theorem selectFold_readOnly (store : WordRAM.ReadStore) (rankSegment selectSegment c : Nat)
    (target : Bool) (word : List Bool) (j count k : Nat) :
    ReadOnlyTrace (bpChunkedWordSelectTraceFromWithStore store rankSegment selectSegment c
      target word j count k).trace := by
  induction count generalizing j k with
  | zero => simp [bpChunkedWordSelectTraceFromWithStore, WordRAM.TraceResult.pure, ReadOnlyTrace]
  | succ count ih =>
      simp only [bpChunkedWordSelectTraceFromWithStore, WordRAM.TraceResult.bind,
        bpChunkReadTraceResult]
      split
      · simp [WordRAM.TraceResult.map, ReadOnlyTrace, WordRAM.TraceEvent.isReadWord]
      · simpa [ReadOnlyTrace, WordRAM.TraceEvent.isReadWord] using ih (j + 1) _

theorem selectWordAddress_writes :
    selectWordAddress.WritesOnly (fun r => (280 ≤ r ∧ r < 292) ∨ r = 8192 ∨ r = 8193) := by
  simp [selectWordAddress, Block.sequence, Block.WritesOnly, Action.destination, chunkSlotBlock,
    natSubBlock, minBlock]

theorem selectWordAddress_frame (memory : Memory) (s : Data) (r : Nat)
    (outside : (r < 280 ∨ 292 ≤ r) ∧ r ≠ 8192 ∧ r ≠ 8193) :
    (selectWordAddress.eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ selectWordAddress_writes r (by omega) s

theorem selectWordAddress_source (memory : Memory) (regs : Registers) :
    let actual := selectWordAddress.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 8192 = 21 ∧
      actual.final.regs 8193 = chunkSlot (regs 400) (regs 34) (regs 404) (regs 401) ∧
      actual.final.regs 284 = min (regs 34) (regs 401 - regs 404 * regs 34) ∧
      actual.final.regs 285 = regs 400 / 2 ^ (regs 404 * regs 34) % 2 ^ regs 34 := by
  let prepared := (((regs.write 280 (regs 400)).write 281 (regs 34)).write 282 (regs 404)).write 283 (regs 401)
  have hs := chunkSlotBlock_source 280 memory prepared
  generalize he : (chunkSlotBlock 280).eval memory ⟨prepared, .running⟩ = located at hs
  rcases located with ⟨⟨out, status⟩, reads⟩
  dsimp only at hs
  obtain ⟨hstatus, hreads, hlength, hvalue, hslot⟩ := hs
  subst status
  subst reads
  simp [prepared, Registers.write] at he hlength hvalue hslot
  simp [selectWordAddress, Block.sequence, Block.eval_seq, Evaluation.bind, eval_move,
    eval_constant, eval_skip, Registers.write, he, hslot, hlength, hvalue]

theorem selectWordDecode_writes :
    selectWordDecode.WritesOnly (fun r => (300 ≤ r ∧ r < 311) ∨ r = 409) := by
  simp [selectWordDecode, Block.sequence, Block.WritesOnly, Action.destination,
    chunkRankBlock, natSubBlock]

theorem selectWordDecode_source (memory : Memory) (regs : Registers) :
    let actual := selectWordDecode.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 304 = chunkRank (regs 34) (regs 284) (regs 8194 - regs 407) 0 := by
  let prepared := ((((regs.write 300 (regs 34)).write 301 (regs 284)).write
    409 (Comparison.le.eval (regs 407) (regs 8194))).write
    302 (regs 8194 - regs 407)).write 303 0
  have hs := chunkRankBlock_source 300 memory prepared
  generalize he : (chunkRankBlock 300).eval memory ⟨prepared, .running⟩ = ranked at hs
  rcases ranked with ⟨⟨out, status⟩, reads⟩
  dsimp only at hs
  obtain ⟨hstatus, hreads, hvalue⟩ := hs
  subst status
  subst reads
  simp [prepared, Registers.write] at he hvalue
  have hsub (r : Registers) := natSubBlock_source 302 8194 407 409 memory r (by decide) (by decide)
  simp [selectWordDecode, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_move, eval_constant, eval_skip, hsub, Registers.write, he, hvalue]

theorem selectWordMiss_source (memory : Memory) (regs : Registers) :
    let actual := selectWordMiss.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 404 = regs 404 + regs 407 ∧
      actual.final.regs 406 = regs 406 - regs 304 := by
  have hsub (r : Registers) := natSubBlock_source 406 406 304 409 memory r (by decide) (by decide)
  simp [selectWordMiss, Block.sequence, Block.eval_seq, Evaluation.bind, eval_arithmetic,
    eval_skip, hsub, Registers.write, Arithmetic.eval]

theorem selectWordSelectAddress_source (memory : Memory) (regs : Registers) :
    let actual := selectWordSelectAddress.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 8192 = 22 ∧
      actual.final.regs 8193 = regs 285 * (regs 34 + regs 407) + regs 406 := by
  simp [selectWordSelectAddress, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_arithmetic, eval_constant, eval_skip, Registers.write, Arithmetic.eval]

theorem selectWordFinish_source (memory : Memory) (regs : Registers) :
    let actual := selectWordFinish.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 403 = regs 404 * regs 34 + (regs 8194 - regs 407) + regs 407 := by
  have hsub (r : Registers) := natSubBlock_source 411 8194 407 409 memory r (by decide) (by decide)
  simp [selectWordFinish, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_arithmetic, eval_skip, hsub, Registers.write, Arithmetic.eval]

theorem selectWordInit_source (memory : Memory) (regs : Registers) :
    let actual := selectWordInit.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 403 = 0 ∧ actual.final.regs 404 = 0 ∧
      actual.final.regs 405 = bpWordChunkCount (regs 34) (regs 401) ∧
      actual.final.regs 406 = regs 402 ∧ actual.final.regs 407 = 1 := by
  have hsub (r : Registers) := natSubBlock_source 405 401 407 409 memory r (by decide) (by decide)
  have hmin (r : Registers) := minBlock_source 405 405 408 409 memory r (by decide) (by decide)
  simp [selectWordInit, Block.sequence, Block.eval_seq, Evaluation.bind, eval_constant,
    eval_move, eval_arithmetic, eval_skip, hsub, hmin, Registers.write, Arithmetic.eval,
    bpWordChunkCount]

def SelectWordBodyWrites (r : Nat) : Prop :=
  r = 403 ∨ r = 404 ∨ r = 406 ∨ (408 ≤ r ∧ r < 412) ∨
    (280 ≤ r ∧ r < 311) ∨ (8192 ≤ r ∧ r < 8271)

def SelectWordWrites (r : Nat) : Prop :=
  (403 ≤ r ∧ r < 412) ∨ (280 ≤ r ∧ r < 311) ∨ (8192 ≤ r ∧ r < 8271)

theorem selectWordSelected_writes (reader : Block) (hr : ReaderWrites reader) :
    (selectWordSelected reader).WritesOnly SelectWordBodyWrites := by
  have hreader : reader.WritesOnly SelectWordBodyWrites :=
    Block.WritesOnly.mono reader hr (by intro r h; unfold SelectWordBodyWrites; omega)
  simpa [selectWordSelected, selectWordSelectAddress, selectWordFinish, Block.sequence,
    Block.WritesOnly, Action.destination, natSubBlock, SelectWordBodyWrites] using hreader

theorem selectWordBody_writes (reader : Block) (hr : ReaderWrites reader) :
    (selectWordBody reader).WritesOnly SelectWordBodyWrites := by
  have hreader : reader.WritesOnly SelectWordBodyWrites :=
    Block.WritesOnly.mono reader hr (by intro r h; unfold SelectWordBodyWrites; omega)
  have hsel := selectWordSelected_writes reader hr
  simpa [selectWordBody, selectWordActive, selectWordAddress, selectWordDecode,
    selectWordMiss, Block.sequence, Block.WritesOnly, Action.destination,
    chunkSlotBlock, chunkRankBlock, natSubBlock, minBlock, SelectWordBodyWrites] using
    And.intro hreader hsel

theorem selectWordBody_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ SelectWordBodyWrites r) :
    ((selectWordBody reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (selectWordBody_writes reader hr) r outside s

theorem selectWordBody_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data) (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((selectWordBody reader).eval memory s).final.regs :=
  writes_metadata shape memory _ _ (selectWordBody_writes reader hr)
    (by intro r hlo hhi; unfold SelectWordBodyWrites; omega) s hm

theorem selectWordBlock_writes (reader : Block) (hr : ReaderWrites reader) :
    (selectWordBlock reader).WritesOnly SelectWordWrites := by
  have hbody := Block.WritesOnly.mono _ (selectWordBody_writes reader hr)
    (show ∀ r, SelectWordBodyWrites r → SelectWordWrites r by
      intro r h; unfold SelectWordBodyWrites SelectWordWrites at *; omega)
  simpa [selectWordBlock, selectWordInit, Block.sequence, Block.WritesOnly,
    Action.destination, natSubBlock, minBlock, SelectWordWrites] using hbody

theorem selectWordBlock_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ SelectWordWrites r) :
    ((selectWordBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (selectWordBlock_writes reader hr) r outside s

theorem selectWordSelected_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (regs : Registers)
    (hm : MetadataMatches shape regs) (hone : regs 407 = 1) :
    let actual := (selectWordSelected reader).eval memory ⟨regs, .running⟩
    let slot := regs 285 * (regs 34 + 1) + regs 406
    let reply := ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 22 slot).map bitsToNatLE
    actual.final.status = .running ∧
      actual.final.regs 403 = regs 404 * regs 34 + reply.getD 0 + 1 ∧
      actual.reads = readerReceipts shape memory 22 slot := by
  have hw : selectWordSelectAddress.WritesOnly (fun r => r = 410 ∨ r = 8192 ∨ r = 8193) := by
    simp [selectWordSelectAddress, Block.sequence, Block.WritesOnly, Action.destination]
  have ha := selectWordSelectAddress_source memory regs
  have hmeta := writes_metadata shape memory _ _ hw (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  have hframe (r : Nat) (hout : r ≠ 410 ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    Block.eval_frame memory _ _ hw r (by omega) ⟨regs, .running⟩
  generalize heA : selectWordSelectAddress.eval memory ⟨regs, .running⟩ = addressed
    at ha hmeta hframe
  rcases addressed with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha hmeta hframe
  obtain ⟨hast, hareads, hsegment, hslot⟩ := ha
  subst ast
  subst areads
  rw [hone] at hslot
  have hb := hreader ar hmeta
  generalize heB : reader.eval memory ⟨ar, .running⟩ = loaded at hb
  rcases loaded with ⟨⟨br, bst⟩, breads⟩
  dsimp only at hb
  obtain ⟨hbst, hpacket, _hlength, hreads, hreadFrame⟩ := hb
  subst bst
  rw [hsegment, hslot] at hpacket hreads
  have h34 : br 34 = regs 34 := (hreadFrame 34 (Or.inl (by decide))).trans (hframe 34 (by omega))
  have h404 : br 404 = regs 404 := (hreadFrame 404 (Or.inl (by decide))).trans (hframe 404 (by omega))
  have h407 : br 407 = 1 := ((hreadFrame 407 (Or.inl (by decide))).trans (hframe 407 (by omega))).trans hone
  have hc := selectWordFinish_source memory br
  generalize heC : selectWordFinish.eval memory ⟨br, .running⟩ = finished at hc
  rcases finished with ⟨⟨cr, cst⟩, creads⟩
  dsimp only at hc
  obtain ⟨hcst, hcreads, hvalue⟩ := hc
  subst cst
  subst creads
  rw [h34, h404, h407, hpacket, logicalPacket_pred] at hvalue
  simp [selectWordSelected, Block.sequence, Block.eval_seq, Evaluation.bind, eval_skip,
    heA, heB, heC, hvalue, hreads]

theorem selectWordSelected_precise_writes (reader : Block) (hr : ReaderWrites reader) :
    (selectWordSelected reader).WritesOnly
      (fun r => r = 403 ∨ r = 409 ∨ r = 410 ∨ r = 411 ∨ (8192 ≤ r ∧ r < 8271)) := by
  have hreader := Block.WritesOnly.mono reader hr
    (show ∀ r, 8194 ≤ r ∧ r < 8271 →
      r = 403 ∨ r = 409 ∨ r = 410 ∨ r = 411 ∨ (8192 ≤ r ∧ r < 8271) by
      intro r h; omega)
  simpa [selectWordSelected, selectWordSelectAddress, selectWordFinish, Block.sequence,
    Block.WritesOnly, Action.destination, natSubBlock] using hreader

theorem selectWordActive_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 407 = 1) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let rankSlot := chunkSlot (regs 400) (regs 34) (regs 404) (regs 401)
    let rank := chunkRank (regs 34) (min (regs 34) (regs 401 - regs 404 * regs 34))
      (((store.readWord? 21 rankSlot).map bitsToNatLE).getD 0) 0
    let selectSlot := (regs 400 / 2 ^ (regs 404 * regs 34) % 2 ^ regs 34) *
      (regs 34 + 1) + regs 406
    let actual := (selectWordActive reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧
      actual.final.regs 403 = (if regs 406 < rank then
        regs 404 * regs 34 + (((store.readWord? 22 selectSlot).map bitsToNatLE).getD 0) + 1
        else regs 403) ∧
      actual.final.regs 404 = (if regs 406 < rank then regs 404 else regs 404 + 1) ∧
      actual.final.regs 406 = (if regs 406 < rank then regs 406 else regs 406 - rank) ∧
      actual.reads = readerReceipts shape memory 21 rankSlot ++
        (if regs 406 < rank then readerReceipts shape memory 22 selectSlot else []) := by
  have ha := selectWordAddress_source memory regs
  have ham := writes_metadata shape memory _ _ selectWordAddress_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  have haf (r : Nat) (ho : (r < 280 ∨ 292 ≤ r) ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    selectWordAddress_frame memory ⟨regs, .running⟩ r ho
  generalize heA : selectWordAddress.eval memory ⟨regs, .running⟩ = addressed at ha ham haf
  rcases addressed with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha ham haf
  obtain ⟨hast, hareads, hsegment, hslot, hlength, hchunk⟩ := ha
  subst ast
  subst areads
  have hb := hreader ar ham
  generalize heB : reader.eval memory ⟨ar, .running⟩ = loaded at hb
  rcases loaded with ⟨⟨br, bst⟩, breads⟩
  dsimp only at hb
  obtain ⟨hbst, hpacket, _hblength, hreads, hbf⟩ := hb
  subst bst
  rw [hsegment, hslot] at hpacket hreads
  have hbm := ReaderFrame.metadata shape ar br hbf ham
  have hc := selectWordDecode_source memory br
  have hcm := writes_metadata shape memory _ _ selectWordDecode_writes
    (by intro r hlo hhi; omega) ⟨br, .running⟩ hbm
  have hcf (r : Nat) (ho : (r < 300 ∨ 311 ≤ r) ∧ r ≠ 409) :=
    Block.eval_frame memory _ _ selectWordDecode_writes r (by omega) ⟨br, .running⟩
  generalize heC : selectWordDecode.eval memory ⟨br, .running⟩ = ranked at hc hcm hcf
  rcases ranked with ⟨⟨cr, cst⟩, creads⟩
  dsimp only at hc hcm hcf
  obtain ⟨hcst, hcreads, hcount⟩ := hc
  subst cst
  subst creads
  have hp (r : Nat) (hrange : r < 280 ∨ (311 ≤ r ∧ r < 8192))
      (h409 : r ≠ 409) : cr r = regs r := by
    rw [hcf r ⟨by omega, h409⟩, hbf r (Or.inl (by omega)), haf r ⟨by omega, by omega, by omega⟩]
  have hp284 : br 284 = min (regs 34) (regs 401 - regs 404 * regs 34) := by
    rw [hbf 284 (Or.inl (by decide)), hlength]
  have hp34 : br 34 = regs 34 := by rw [hbf 34 (Or.inl (by decide)), haf 34 (by omega)]
  have hp407 : br 407 = 1 := by rw [hbf 407 (Or.inl (by decide)), haf 407 (by omega), hone]
  rw [hp34, hp284, hp407, hpacket, logicalPacket_pred] at hcount
  let rank := chunkRank (regs 34) (min (regs 34) (regs 401 - regs 404 * regs 34))
    ((((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
      21 (chunkSlot (regs 400) (regs 34) (regs 404) (regs 401))).map bitsToNatLE).getD 0) 0
  have hp403 : cr 403 = regs 403 := hp 403 (by omega) (by decide)
  have hp404 : cr 404 = regs 404 := hp 404 (by omega) (by decide)
  have hp406 : cr 406 = regs 406 := hp 406 (by omega) (by decide)
  have hp407' : cr 407 = 1 := (hp 407 (by omega) (by decide)).trans hone
  have hp34' : cr 34 = regs 34 := hp 34 (by omega) (by decide)
  have hp285 : cr 285 = regs 400 / 2 ^ (regs 404 * regs 34) % 2 ^ regs 34 := by
    rw [hcf 285 (by omega), hbf 285 (Or.inl (by decide)), hchunk]
  by_cases hchoose : regs 406 < rank
  · let tested := cr.write 408 1
    have htm : MetadataMatches shape tested := MetadataMatches.write shape cr hcm 408 1 (Or.inr (by decide))
    have hs := selectWordSelected_source shape memory reader hreader tested htm
      (by simpa [tested, Registers.write] using hp407')
    have hf (r : Nat) (ho : r ≠ 403 ∧ r ≠ 409 ∧ r ≠ 410 ∧ r ≠ 411 ∧ (r < 8192 ∨ 8271 ≤ r)) :=
      Block.eval_frame memory _ _ (selectWordSelected_precise_writes reader hwrites) r (by omega)
        ⟨tested, .running⟩
    generalize heS : (selectWordSelected reader).eval memory ⟨tested, .running⟩ = selected at hs hf
    rcases selected with ⟨⟨sr, sst⟩, sreads⟩
    dsimp only at hs hf
    obtain ⟨hsst, hsvalue, hsreads⟩ := hs
    subst sst
    have hs404 := hf 404 (by omega)
    have hs406 := hf 406 (by omega)
    simp [tested, Registers.write, hp285, hp34', hp406, hp404] at hsvalue hsreads hs404 hs406
    dsimp only [tested] at heS
    simp [selectWordActive, Block.sequence, Block.eval_seq, Evaluation.bind, eval_comparison,
      eval_ifZero, eval_skip, heA, heB, heC, Comparison.eval, hcount, hp406, hchoose,
      heS, hsvalue, hsreads, hs404, hs406, Registers.write, hreads, rank]
  · let tested := cr.write 408 0
    have hs := selectWordMiss_source memory tested
    have hw : selectWordMiss.WritesOnly (fun r => r = 404 ∨ r = 406 ∨ r = 409) := by
      simp [selectWordMiss, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]
    have hf := Block.eval_frame memory _ _ hw 403 (by decide) ⟨tested, .running⟩
    generalize heM : selectWordMiss.eval memory ⟨tested, .running⟩ = missed at hs hf
    rcases missed with ⟨⟨mr, mst⟩, mreads⟩
    dsimp only at hs hf
    obtain ⟨hmst, hmreads, hmindex, hmremain⟩ := hs
    subst mst
    subst mreads
    simp [tested, Registers.write, hp404, hp407', hp406, hcount, hp403] at hmindex hmremain hf
    dsimp only [tested] at heM
    simp [selectWordActive, Block.sequence, Block.eval_seq, Evaluation.bind, eval_comparison,
      eval_ifZero, eval_skip, heA, heB, heC, Comparison.eval, hcount, hp406, hchoose,
      heM, hmindex, hmremain, hf, Registers.write, hreads, rank]

theorem selectWordBody_found (reader : Block) (memory : Memory) (regs : Registers)
    (hfound : regs 403 ≠ 0) :
    (selectWordBody reader).eval memory ⟨regs, .running⟩ = ⟨⟨regs, .running⟩, []⟩ := by
  simp [selectWordBody, eval_ifZero, eval_skip, hfound]

theorem selectWordBody_inactive (reader : Block) (memory : Memory) (regs : Registers)
    (hzero : regs 403 = 0) (hinactive : regs 405 ≤ regs 404) :
    (selectWordBody reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write 408 0, .running⟩, []⟩ := by
  simp [selectWordBody, eval_ifZero, eval_skip, Block.eval_seq, Evaluation.bind,
    eval_comparison, Comparison.eval, Registers.write, hzero, Nat.not_lt.mpr hinactive]

structure SelectFoldState (word : List Bool) (c total j k : Nat) (regs : Registers) : Prop where
  word_eq : regs 400 = bitsToNatLE word
  length_eq : regs 401 = word.length
  chunk_eq : regs 34 = c
  out_eq : regs 403 = 0
  index_eq : regs 404 = j
  total_eq : regs 405 = total
  remaining_eq : regs 406 = k
  one_eq : regs 407 = 1

theorem selectWordBody_active_reference (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (c total j k : Nat) (regs : Registers) (hm : MetadataMatches shape regs)
    (hs : SelectFoldState word c total j k regs) (hactive : j < total) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let rankSlot := bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
      (bpWordChunkSliceLen c word.length j) (bpWordChunkSliceLen c word.length j)
    let rank := bpChunkRankOfEntry c false (bpWordChunkSliceLen c word.length j)
      (((store.readWord? 21 rankSlot).map bitsToNatLE).getD 0)
    let selectSlot := bpChunkSelectSlot c (bpFringeWindowChunkValue c word j) k
    let actual := (selectWordBody reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧
      actual.final.regs 403 = (if k < rank then
        j * c + (((store.readWord? 22 selectSlot).map bitsToNatLE).getD 0) + 1 else 0) ∧
      actual.final.regs 404 = (if k < rank then j else j + 1) ∧
      actual.final.regs 406 = (if k < rank then k else k - rank) ∧
      actual.reads = readerReceipts shape memory 21 rankSlot ++
        (if k < rank then readerReceipts shape memory 22 selectSlot else []) := by
  let compared := regs.write 408 1
  have hc := selectWordActive_source shape memory reader hreader hwrites compared
    (MetadataMatches.write shape regs hm 408 1 (Or.inr (by decide)))
    (by simpa [compared, Registers.write] using hs.one_eq)
  have heval : (selectWordBody reader).eval memory ⟨regs, .running⟩ =
      (selectWordActive reader).eval memory ⟨compared, .running⟩ := by
    simp [selectWordBody, eval_ifZero, Block.eval_seq, Evaluation.bind, eval_comparison,
      hs.out_eq, hs.index_eq, hs.total_eq, Comparison.eval, hactive, Registers.write, compared]
  rw [heval]
  have hrank (a b d : Nat) : chunkRank a b d 0 = bpChunkRankOfEntry a false b d :=
    chunkRank_eq_reference a b d false
  simpa [compared, Registers.write, hs.word_eq, hs.length_eq,
    hs.chunk_eq, hs.index_eq, hs.remaining_eq, hs.out_eq, chunkSlot_eq_reference,
    bpWordRankChunkSlotAt, hrank, bpChunkSelectSlot, bpWordChunkSliceLen,
    bpFringeWindowChunkValue_eq_div_mod] using hc

theorem selectWordRepeat_found (reader : Block) (memory : Memory) (cycles : Nat)
    (regs : Registers) (hfound : regs 403 ≠ 0) :
    (Block.repeat cycles (selectWordBody reader)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs, .running⟩, []⟩ := by
  induction cycles with
  | zero => rw [Block.eval_repeat]; rfl
  | succ cycles ih =>
      rw [Block.eval_repeat_succ, selectWordBody_found reader memory regs hfound]
      simp only [Evaluation.bind, ih, List.nil_append]

theorem selectWordRepeat_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (c total cycles j k : Nat) (regs : Registers) (hm : MetadataMatches shape regs)
    (hs : SelectFoldState word c total j k regs) (hcover : total ≤ j + cycles) :
    let actual := (Block.repeat cycles (selectWordBody reader)).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordSelectTraceFromWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 22 c false word j (total - j) k
    actual.final.status = .running ∧ actual.final.regs 403 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace := by
  induction cycles generalizing j k regs with
  | zero =>
      have hz : total - j = 0 := by omega
      simp [Block.eval_repeat, iterate, bpChunkedWordSelectTraceFromWithStore, hz,
        WordRAM.TraceResult.pure, logicalTraceReads, optionNatPacket, hs.out_eq]
  | succ cycles ih =>
      by_cases hactive : j < total
      · have hb := selectWordBody_active_reference shape memory reader hreader hwrites
          word c total j k regs hm hs hactive
        have hmeta := selectWordBody_metadata shape reader hwrites memory ⟨regs, .running⟩ hm
        have hframe (r : Nat) (ho : ¬ SelectWordBodyWrites r) :=
          selectWordBody_frame reader hwrites memory ⟨regs, .running⟩ r ho
        generalize he : (selectWordBody reader).eval memory ⟨regs, .running⟩ = first
          at hb hmeta hframe
        rcases first with ⟨⟨fr, fst⟩, freceipts⟩
        dsimp only at hb hmeta hframe
        obtain ⟨hfst, hvalue, hindex, hremaining, hreads⟩ := hb
        subst fst
        let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
        let slot := bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
          (bpWordChunkSliceLen c word.length j) (bpWordChunkSliceLen c word.length j)
        let rank := bpChunkRankOfEntry c false (bpWordChunkSliceLen c word.length j)
          (((store.readWord? 21 slot).map bitsToNatLE).getD 0)
        have hcount : total - j = (total - (j + 1)) + 1 := by omega
        by_cases hchoose : k < rank
        · rw [if_pos hchoose] at hvalue hindex hremaining hreads
          have hfound : fr 403 ≠ 0 := by rw [hvalue]; omega
          rw [Block.eval_repeat_succ, he]
          simp only [Evaluation.bind, selectWordRepeat_found reader memory cycles fr hfound,
            List.append_nil]
          rw [hcount, bpChunkedWordSelectTraceFromWithStore]
          dsimp only [WordRAM.TraceResult.bind, bpChunkReadTraceResult]
          rw [if_pos hchoose]
          dsimp only [WordRAM.TraceResult.map]
          refine ⟨True.intro, ?_, ?_⟩
          · simpa only [optionNatPacket, Option.map_some, Option.getD_some] using hvalue
          · rw [hreads, select_logicalTraceReads_append]
            simp [logicalTraceReads]
        · rw [if_neg hchoose] at hvalue hindex hremaining hreads
          have hnext : SelectFoldState word c total (j + 1) (k - rank) fr := by
            constructor
            · rw [hframe 400 (by simp [SelectWordBodyWrites])]; exact hs.word_eq
            · rw [hframe 401 (by simp [SelectWordBodyWrites])]; exact hs.length_eq
            · rw [hframe 34 (by simp [SelectWordBodyWrites])]; exact hs.chunk_eq
            · exact hvalue
            · exact hindex
            · rw [hframe 405 (by simp [SelectWordBodyWrites])]; exact hs.total_eq
            · exact hremaining
            · rw [hframe 407 (by simp [SelectWordBodyWrites])]; exact hs.one_eq
          have ht := ih (j + 1) (k - rank) fr hmeta hnext (by omega)
          rw [Block.eval_repeat_succ, he]
          dsimp only [Evaluation.bind]
          rw [hcount, bpChunkedWordSelectTraceFromWithStore]
          dsimp only [WordRAM.TraceResult.bind, bpChunkReadTraceResult]
          rw [if_neg hchoose]
          refine ⟨ht.1, ht.2.1, ?_⟩
          rw [hreads, ht.2.2, select_logicalTraceReads_append]
          simp [logicalTraceReads, rank, slot, store]
      · have hstop : regs 405 ≤ regs 404 := by rw [hs.total_eq, hs.index_eq]; omega
        have hnext : SelectFoldState word c total j k (regs.write 408 0) := by
          constructor <;> simp only [Registers.write] <;> first
            | exact hs.word_eq | exact hs.length_eq | exact hs.chunk_eq | exact hs.out_eq
            | exact hs.index_eq | exact hs.total_eq | exact hs.remaining_eq | exact hs.one_eq
        have ht := ih j k (regs.write 408 0)
          (MetadataMatches.write shape regs hm 408 0 (Or.inr (by decide))) hnext (by omega)
        rw [Block.eval_repeat_succ, selectWordBody_inactive reader memory regs hs.out_eq hstop]
        simpa only [Evaluation.bind, List.nil_append] using ht

theorem selectWordBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (occurrence : Nat) (regs : Registers) (hm : MetadataMatches shape regs)
    (hword : regs 400 = bitsToNatLE word) (hlength : regs 401 = word.length)
    (hoccurrence : regs 402 = occurrence) :
    let actual := (selectWordBlock reader).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordSelectTraceResultAtSegmentsWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 22
      (packedFringeChunkBits shape.size) false word occurrence
    actual.final.status = .running ∧ actual.final.regs 403 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hw : selectWordInit.WritesOnly (fun r => 403 ≤ r ∧ r < 410) := by
    simp [selectWordInit, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, minBlock]
  have hp := selectWordInit_source memory regs
  have hmeta := writes_metadata shape memory _ _ hw (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  have hf (r : Nat) (ho : r < 403 ∨ 410 ≤ r) :=
    Block.eval_frame memory _ _ hw r (by omega) ⟨regs, .running⟩
  generalize he : selectWordInit.eval memory ⟨regs, .running⟩ = initialized at hp hmeta hf
  rcases initialized with ⟨⟨pr, pst⟩, preads⟩
  dsimp only at hp hmeta hf
  obtain ⟨hpst, hpreads, hzero, hindex, htotal, hremaining, hone⟩ := hp
  subst pst
  subst preads
  have hc : regs 34 = packedFringeChunkBits shape.size := hm 18 (by decide)
  let c := packedFringeChunkBits shape.size
  have hstate : SelectFoldState word c (bpWordChunkCount c word.length) 0 occurrence pr := by
    constructor
    · rw [hf 400 (Or.inl (by decide))]; exact hword
    · rw [hf 401 (Or.inl (by decide))]; exact hlength
    · rw [hf 34 (Or.inl (by decide))]; exact hc
    · exact hzero
    · exact hindex
    · simpa only [hc, hlength] using htotal
    · simpa only [hoccurrence] using hremaining
    · exact hone
  have hl := selectWordRepeat_source shape memory reader hreader hwrites word c
    (bpWordChunkCount c word.length) 8 0 occurrence pr hmeta hstate (bpWordChunkCount_le_eight c word.length)
  rw [selectWordBlock, Block.eval_seq, he]
  dsimp only [Evaluation.bind]
  refine ⟨hl.1, hl.2.1, hl.2.2, ?_⟩
  exact selectFold_readOnly _ _ _ _ _ _ _ _ _

@[simp] theorem selectWordBody_size (reader : Block) :
    (selectWordBody reader).size = 81 + 2 * reader.size := by
  simp [selectWordBody, selectWordActive, selectWordAddress, selectWordDecode,
    selectWordMiss, selectWordSelected, selectWordSelectAddress, selectWordFinish,
    Block.sequence, Block.size]
  omega

@[simp] theorem selectWordBlock_size (reader : Block) :
    (selectWordBlock reader).size = 665 + 16 * reader.size := by
  simp [selectWordBlock, selectWordInit, Block.sequence, Block.size, Nat.mul_add]
  omega

theorem selectWordBlock_run (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (occurrence : Nat) (s : State) (hpc : s.pc = 0) (hs : s.status = .running)
    (hm : MetadataMatches shape s.regs) (hword : s.regs 400 = bitsToNatLE word)
    (hlength : s.regs 401 = word.length) (hoccurrence : s.regs 402 = occurrence) :
    let actual := run memory ((selectWordBlock reader).compileAt 0) (665 + 16 * reader.size) s
    let expected := bpChunkedWordSelectTraceResultAtSegmentsWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 22
      (packedFringeChunkBits shape.size) false word occurrence
    actual.final.status = .running ∧ actual.final.regs 403 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace ∧
      actual.steps ≤ 665 + 16 * reader.size ∧ actual.final.pc = 665 + 16 * reader.size := by
  have h := (selectWordBlock reader).compile_run memory s hpc
  rw [selectWordBlock_size] at h
  have hdata : Data.ofState s = ⟨s.regs, .running⟩ := by cases s; simp_all [Data.ofState]
  rw [hdata] at h
  have he := selectWordBlock_source shape memory reader hreader hwrites word occurrence s.regs hm
    hword hlength hoccurrence
  have hstatus : (run memory ((selectWordBlock reader).compileAt 0) (665 + 16 * reader.size) s).final.status = .running := by
    change (Data.ofState _).status = _
    rw [h.1]
    exact he.1
  refine ⟨hstatus, ?_, h.2.1.trans he.2.2.1, he.2.2.2, h.2.2.1, h.2.2.2 hstatus⟩
  change (Data.ofState _).regs 403 = _
  rw [h.1]
  exact he.2.1

def DenseWrites (r : Nat) : Prop :=
  (256 ≤ r ∧ r < 311) ∨ (400 ≤ r ∧ r < 412) ∨
    (643 ≤ r ∧ r < 660) ∨ (8192 ≤ r ∧ r < 8271)

theorem denseWordFinish_source (memory : Memory) (regs : Registers) (result : Option Nat)
    (hresult : regs 403 = optionNatPacket result) (hzero : regs 643 = 0) :
    let actual := denseWordFinish.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 643 = optionNatPacket (result.map (fun x => regs 644 * regs 32 + x)) := by
  cases result <;>
    simp [denseWordFinish, Block.sequence, Block.eval_seq, Evaluation.bind, eval_ifZero,
      eval_arithmetic, eval_skip, hresult, hzero, optionNatPacket, Arithmetic.eval,
      Registers.write, Nat.add_assoc]

theorem denseFirstPrepare_writes :
    denseFirstPrepare.WritesOnly (fun r => (400 ≤ r ∧ r < 403) ∨ r = 658) := by
  simp [denseFirstPrepare, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]

theorem denseFirstPrepare_source (memory : Memory) (regs : Registers) :
    let actual := denseFirstPrepare.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 400 = regs 645 - regs 659 ∧
      actual.final.regs 401 = regs 646 ∧ actual.final.regs 402 = regs 648 + regs 650 := by
  have hsub (r : Registers) := natSubBlock_source 400 645 659 658 memory r (by decide) (by decide)
  simp [denseFirstPrepare, Block.sequence, Block.eval_seq, Evaluation.bind, eval_move,
    eval_arithmetic, eval_skip, hsub, Arithmetic.eval, Registers.write]

theorem denseSecondPrepare_writes :
    denseSecondPrepare.WritesOnly (fun r => (400 ≤ r ∧ r < 403) ∨ r = 658) := by
  simp [denseSecondPrepare, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]

theorem denseSecondPrepare_source (memory : Memory) (regs : Registers) :
    let actual := denseSecondPrepare.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 400 = regs 8194 - regs 659 ∧
      actual.final.regs 401 = regs 8195 ∧ actual.final.regs 402 = regs 650 - regs 651 := by
  have hsub (r : Registers) := natSubBlock_source 400 8194 659 658 memory r (by decide) (by decide)
  have hsub' (r : Registers) := natSubBlock_source 402 650 651 658 memory r (by decide) (by decide)
  simp [denseSecondPrepare, Block.sequence, Block.eval_seq, Evaluation.bind, eval_move,
    eval_skip, hsub, hsub', Registers.write]

theorem denseWordPrepared_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (occurrence : Nat) (regs : Registers) (hm : MetadataMatches shape regs)
    (hword : regs 400 = bitsToNatLE word) (hlength : regs 401 = word.length)
    (hoccurrence : regs 402 = occurrence) (hzero : regs 643 = 0) :
    let actual := (Block.seq (selectWordBlock reader) denseWordFinish).eval memory ⟨regs, .running⟩
    let selected := bpChunkedWordSelectTraceResultAtSegmentsWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 22
      (packedFringeChunkBits shape.size) false word occurrence
    actual.final.status = .running ∧
      actual.final.regs 643 = optionNatPacket (selected.value.map (fun x => regs 644 * regs 32 + x)) ∧
      actual.reads = logicalTraceReads shape memory selected.trace ∧ ReadOnlyTrace selected.trace := by
  have hs := selectWordBlock_source shape memory reader hreader hwrites word occurrence regs hm
    hword hlength hoccurrence
  have hf (r : Nat) (ho : ¬ SelectWordWrites r) :=
    selectWordBlock_frame reader hwrites memory ⟨regs, .running⟩ r ho
  generalize he : (selectWordBlock reader).eval memory ⟨regs, .running⟩ = selected at hs hf
  rcases selected with ⟨⟨sr, status⟩, reads⟩
  dsimp only at hs hf
  obtain ⟨hstatus, hvalue, hreads, hreadonly⟩ := hs
  subst status
  have hz : sr 643 = 0 := (hf 643 (by simp [SelectWordWrites])).trans hzero
  have hd := denseWordFinish_source memory sr _ hvalue hz
  have h644 := hf 644 (by simp [SelectWordWrites])
  have h32 := hf 32 (by simp [SelectWordWrites])
  rw [Block.eval_seq, he]
  dsimp only [Evaluation.bind]
  exact ⟨hd.1, by simpa only [h644, h32] using hd.2.2,
    by rw [hd.2.1, List.append_nil]; exact hreads, hreadonly⟩

theorem denseFirstSelected_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (regs : Registers) (hm : MetadataMatches shape regs)
    (hpacket : regs 645 = bitsToNatLE word + 1) (hlength : regs 646 = word.length)
    (hone : regs 659 = 1) (hzero : regs 643 = 0) :
    let actual := (denseFirstSelected reader).eval memory ⟨regs, .running⟩
    let selected := bpChunkedWordSelectTraceResultAtSegmentsWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 22
      (packedFringeChunkBits shape.size) false word (regs 648 + regs 650)
    actual.final.status = .running ∧
      actual.final.regs 643 = optionNatPacket (selected.value.map (fun x => regs 644 * regs 32 + x)) ∧
      actual.reads = logicalTraceReads shape memory selected.trace ∧ ReadOnlyTrace selected.trace := by
  have hp := denseFirstPrepare_source memory regs
  have hf (r : Nat) (ho : ¬ ((400 ≤ r ∧ r < 403) ∨ r = 658)) :=
    Block.eval_frame memory _ _ denseFirstPrepare_writes r ho ⟨regs, .running⟩
  have hmeta := writes_metadata shape memory _ _ denseFirstPrepare_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  generalize he : denseFirstPrepare.eval memory ⟨regs, .running⟩ = prepared at hp hf hmeta
  rcases prepared with ⟨⟨pr, status⟩, reads⟩
  dsimp only at hp hf hmeta
  obtain ⟨hstatus, hreads, hword, hlen, hocc⟩ := hp
  subst status
  subst reads
  have hz : pr 643 = 0 := (hf 643 (by omega)).trans hzero
  have hs := denseWordPrepared_source shape memory reader hreader hwrites word _ pr hmeta
    (by simpa only [hpacket, hone, Nat.add_sub_cancel] using hword)
    (hlen.trans hlength) hocc hz
  have h644 := hf 644 (by omega)
  have h32 := hf 32 (by omega)
  have heq : (denseFirstSelected reader).eval memory ⟨regs, .running⟩ =
      (Block.seq (selectWordBlock reader) denseWordFinish).eval memory ⟨pr, .running⟩ := by
    simp [denseFirstSelected, Block.sequence, Block.eval_seq, he, Evaluation.bind,
      List.nil_append, eval_skip_any, List.append_nil]
  rw [heq]
  simpa only [h644, h32] using hs

theorem denseSecondPrepared_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (regs : Registers) (hm : MetadataMatches shape regs)
    (hpacket : regs 8194 = bitsToNatLE word + 1) (hlength : regs 8195 = word.length)
    (hone : regs 659 = 1) (hzero : regs 643 = 0) :
    let actual := (Block.sequence [denseSecondPrepare, selectWordBlock reader, denseWordFinish]).eval
      memory ⟨regs, .running⟩
    let selected := bpChunkedWordSelectTraceResultAtSegmentsWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 22
      (packedFringeChunkBits shape.size) false word (regs 650 - regs 651)
    actual.final.status = .running ∧
      actual.final.regs 643 = optionNatPacket (selected.value.map (fun x => regs 644 * regs 32 + x)) ∧
      actual.reads = logicalTraceReads shape memory selected.trace ∧ ReadOnlyTrace selected.trace := by
  have hp := denseSecondPrepare_source memory regs
  have hf (r : Nat) (ho : ¬ ((400 ≤ r ∧ r < 403) ∨ r = 658)) :=
    Block.eval_frame memory _ _ denseSecondPrepare_writes r ho ⟨regs, .running⟩
  have hmeta := writes_metadata shape memory _ _ denseSecondPrepare_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  generalize he : denseSecondPrepare.eval memory ⟨regs, .running⟩ = prepared at hp hf hmeta
  rcases prepared with ⟨⟨pr, status⟩, reads⟩
  dsimp only at hp hf hmeta
  obtain ⟨hstatus, hreads, hword, hlen, hocc⟩ := hp
  subst status
  subst reads
  have hz : pr 643 = 0 := (hf 643 (by omega)).trans hzero
  have hs := denseWordPrepared_source shape memory reader hreader hwrites word _ pr hmeta
    (by simpa only [hpacket, hone, Nat.add_sub_cancel] using hword)
    (hlen.trans hlength) hocc hz
  have h644 := hf 644 (by omega)
  have h32 := hf 32 (by omega)
  have heq : (Block.sequence [denseSecondPrepare, selectWordBlock reader, denseWordFinish]).eval
      memory ⟨regs, .running⟩ =
      (Block.seq (selectWordBlock reader) denseWordFinish).eval memory ⟨pr, .running⟩ := by
    simp [Block.sequence, Block.eval_seq, he, Evaluation.bind,
      List.nil_append, eval_skip_any, List.append_nil]
  rw [heq]
  simpa only [h644, h32] using hs

theorem denseSecondAddress_writes :
    denseSecondAddress.WritesOnly (fun r => r = 644 ∨ r = 8192 ∨ r = 8193) := by
  simp [denseSecondAddress, Block.sequence, Block.WritesOnly, Action.destination]

theorem denseSecondAddress_source (memory : Memory) (regs : Registers) :
    let actual := denseSecondAddress.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 8192 = 0 ∧
      actual.final.regs 8193 = regs 644 + regs 659 ∧
      actual.final.regs 644 = regs 644 + regs 659 := by
  simp [denseSecondAddress, Block.sequence, Block.eval_seq, Evaluation.bind, eval_arithmetic,
    eval_move, eval_constant, eval_skip, Arithmetic.eval, Registers.write]

def denseSecondReference (store : WordRAM.ReadStore) (c wordSize wordIndex remaining : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind (bpWordReadTraceResult store 0 (wordIndex + 1)) fun word? =>
    match word? with
    | none => WordRAM.TraceResult.pure none
    | some word => WordRAM.TraceResult.map
        (fun value? => value?.map (fun x => (wordIndex + 1) * wordSize + x))
        (bpChunkedWordSelectTraceResultAtSegmentsWithStore store 21 22 c false word remaining)

theorem denseSecondSelected_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs)
    (hone : regs 659 = 1) (hzero : regs 643 = 0) :
    let actual := (denseSecondSelected reader).eval memory ⟨regs, .running⟩
    let expected := denseSecondReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedFringeChunkBits shape.size) (regs 32) (regs 644) (regs 650 - regs 651)
    actual.final.status = .running ∧ actual.final.regs 643 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have ha := denseSecondAddress_source memory regs
  have haf (r : Nat) (ho : r ≠ 644 ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    Block.eval_frame memory _ _ denseSecondAddress_writes r (by omega) ⟨regs, .running⟩
  have ham := writes_metadata shape memory _ _ denseSecondAddress_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  generalize heA : denseSecondAddress.eval memory ⟨regs, .running⟩ = addressed at ha haf ham
  rcases addressed with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha haf ham
  obtain ⟨hast, hareads, hsegment, hindex, h644⟩ := ha
  subst ast
  subst areads
  rw [hone] at hindex h644
  have hb := hreader ar ham
  generalize heB : reader.eval memory ⟨ar, .running⟩ = fetched at hb
  rcases fetched with ⟨⟨br, bst⟩, breads⟩
  dsimp only at hb
  obtain ⟨hbst, hpacket, hlength, hreads, hbf⟩ := hb
  subst bst
  rw [hsegment, hindex] at hpacket hlength hreads
  have hp (r : Nat) (ho : r ≠ 644 ∧ r < 8192) : br r = regs r := by
    rw [hbf r (Or.inl (by omega)), haf r (by omega)]
  have hp644 : br 644 = regs 644 + 1 := (hbf 644 (Or.inl (by decide))).trans h644
  have hp32 := hp 32 (by omega)
  have hp650 := hp 650 (by omega)
  have hp651 := hp 651 (by omega)
  have hp659 : br 659 = 1 := (hp 659 (by omega)).trans hone
  have hp643 : br 643 = 0 := (hp 643 (by omega)).trans hzero
  have hbm := hbf.metadata shape ar br ham
  cases hword : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 (regs 644 + 1) with
  | none =>
      simp only [hword, logicalPacket, logicalLength, Option.map_none, Option.getD_none] at hpacket hlength
      simp [denseSecondSelected, Block.sequence, Block.eval_seq, Evaluation.bind, heA, heB,
        eval_ifZero, eval_skip, hpacket, hp643, hreads, denseSecondReference, bpWordReadTraceResult,
        hword, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure, optionNatPacket,
        logicalTraceReads, ReadOnlyTrace, WordRAM.TraceEvent.isReadWord]
  | some word =>
      simp only [hword, logicalPacket, logicalLength, Option.map_some, Option.getD_some] at hpacket hlength
      have hs := denseSecondPrepared_source shape memory reader hreader hwrites word br hbm
        hpacket hlength hp659 hp643
      generalize heS : (Block.sequence [denseSecondPrepare, selectWordBlock reader, denseWordFinish]).eval
          memory ⟨br, .running⟩ = selected at hs
      rcases selected with ⟨⟨sr, sst⟩, sreads⟩
      dsimp only at hs
      obtain ⟨hsst, hsvalue, hsreads, hsreadonly⟩ := hs
      subst sst
      simp only [hp644, hp32, hp650, hp651] at hsvalue hsreads hsreadonly
      have heval : (denseSecondSelected reader).eval memory ⟨regs, .running⟩ =
          ⟨⟨sr, .running⟩, breads ++ sreads⟩ := by
        change (Block.seq denseSecondAddress (.seq reader (.seq
          (.ifZero 8194 .skip (Block.sequence [denseSecondPrepare, selectWordBlock reader, denseWordFinish]))
          .skip))).eval memory ⟨regs, .running⟩ = _
        rw [Block.eval_seq, heA]
        simp only [Evaluation.bind, List.nil_append]
        rw [Block.eval_seq, heB]
        simp only [Evaluation.bind]
        rw [Block.eval_seq]
        simp [eval_ifZero, hpacket, heS, Evaluation.bind, eval_skip]
      rw [heval]
      dsimp only [denseSecondReference, bpWordReadTraceResult, WordRAM.TraceResult.bind]
      rw [hword]
      dsimp only [WordRAM.TraceResult.map]
      refine ⟨rfl, hsvalue, ?_, ?_⟩
      · rw [hreads, hsreads, select_logicalTraceReads_append]
        simp [logicalTraceReads]
      · simpa [ReadOnlyTrace, WordRAM.TraceEvent.isReadWord] using hsreadonly

theorem denseReadAddress_writes :
    denseReadAddress.WritesOnly (fun r => r = 643 ∨ r = 644 ∨ r = 659 ∨ r = 8192 ∨ r = 8193) := by
  simp [denseReadAddress, Block.sequence, Block.WritesOnly, Action.destination]

theorem denseReadAddress_source (memory : Memory) (regs : Registers) :
    let actual := denseReadAddress.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 643 = 0 ∧
      actual.final.regs 659 = 1 ∧ actual.final.regs 644 = regs 640 / regs 32 ∧
      actual.final.regs 8192 = 0 ∧ actual.final.regs 8193 = regs 640 / regs 32 := by
  simp [denseReadAddress, Block.sequence, Block.eval_seq, Evaluation.bind, eval_constant,
    eval_arithmetic, eval_move, eval_skip, Arithmetic.eval, Registers.write]

theorem denseReadSave_writes :
    denseReadSave.WritesOnly (fun r => r = 645 ∨ r = 646) := by
  simp [denseReadSave, Block.sequence, Block.WritesOnly, Action.destination]

theorem denseReadSave_source (memory : Memory) (regs : Registers) :
    let actual := denseReadSave.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 645 = regs 8194 ∧ actual.final.regs 646 = regs 8195 := by
  simp [denseReadSave, Block.sequence, Block.eval_seq, Evaluation.bind, eval_move,
    eval_skip, Registers.write]

theorem denseRankBeforePrepare_writes :
    denseRankBeforePrepare.WritesOnly (fun r => (256 ≤ r ∧ r < 260) ∨ r = 647 ∨ r = 658) := by
  simp [denseRankBeforePrepare, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]

theorem denseRankBeforePrepare_source (memory : Memory) (regs : Registers) :
    let actual := denseRankBeforePrepare.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 256 = regs 645 - regs 659 ∧ actual.final.regs 257 = regs 646 ∧
      actual.final.regs 258 = regs 640 - regs 644 * regs 32 ∧ actual.final.regs 259 = 0 := by
  have hsub (r : Registers) := natSubBlock_source 647 640 647 658 memory r (by decide) (by decide)
  have hsub' (r : Registers) := natSubBlock_source 256 645 659 658 memory r (by decide) (by decide)
  simp [denseRankBeforePrepare, Block.sequence, Block.eval_seq, Evaluation.bind, eval_arithmetic,
    eval_move, eval_constant, eval_skip, hsub, hsub', Arithmetic.eval, Registers.write]

theorem denseRankWholePrepare_writes :
    denseRankWholePrepare.WritesOnly (fun r => (256 ≤ r ∧ r < 260) ∨ r = 648 ∨ r = 658) := by
  simp [denseRankWholePrepare, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]

theorem denseRankWholePrepare_source (memory : Memory) (regs : Registers) :
    let actual := denseRankWholePrepare.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 648 = regs 260 ∧
      actual.final.regs 256 = regs 645 - regs 659 ∧ actual.final.regs 257 = regs 646 ∧
      actual.final.regs 258 = regs 646 ∧ actual.final.regs 259 = 0 := by
  have hsub (r : Registers) := natSubBlock_source 256 645 659 658 memory r (by decide) (by decide)
  simp [denseRankWholePrepare, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_move, eval_constant, eval_skip, hsub, Registers.write]

theorem denseChoosePrepare_writes :
    denseChoosePrepare.WritesOnly (fun r => (649 ≤ r ∧ r < 653) ∨ r = 658) := by
  simp [denseChoosePrepare, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]

theorem denseChoosePrepare_source (memory : Memory) (regs : Registers) :
    let actual := denseChoosePrepare.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 649 = regs 260 ∧
      actual.final.regs 650 = regs 642 - regs 641 ∧ actual.final.regs 651 = regs 260 - regs 648 ∧
      actual.final.regs 652 = if regs 642 - regs 641 < regs 260 - regs 648 then 1 else 0 := by
  have hsub (r : Registers) := natSubBlock_source 650 642 641 658 memory r (by decide) (by decide)
  have hsub' (r : Registers) := natSubBlock_source 651 649 648 658 memory r (by decide) (by decide)
  simp [denseChoosePrepare, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_move, eval_comparison, eval_skip, hsub, hsub', Comparison.eval, Registers.write]

theorem selectLongAddress_writes :
    selectLongAddress.WritesOnly (fun r => r = 534 ∨ r = 535 ∨ r = 550 ∨ r = 8192 ∨ r = 8193) := by
  simp [selectLongAddress, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]

theorem selectLongAddress_source (memory : Memory) (regs : Registers) :
    let actual := selectLongAddress.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 8192 = 12 ∧
      actual.final.regs 8193 = regs 360 * regs 25 + (regs 512 - regs 561) := by
  have hsub (r : Registers) := natSubBlock_source 535 512 561 550 memory r (by decide) (by decide)
  simp [selectLongAddress, Block.sequence, Block.eval_seq, Evaluation.bind, eval_arithmetic,
    eval_constant, eval_skip, hsub, Registers.write, Arithmetic.eval]

theorem selectSparseAddress_writes :
    selectSparseAddress.WritesOnly (fun r => r = 534 ∨ r = 535 ∨ r = 550 ∨ r = 8192 ∨ r = 8193) := by
  simp [selectSparseAddress, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]

theorem selectSparseAddress_source (memory : Memory) (regs : Registers) :
    let actual := selectSparseAddress.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 8192 = 16 ∧
      actual.final.regs 8193 = regs 360 * regs 26 + (regs 512 - regs 521) := by
  have hsub (r : Registers) := natSubBlock_source 535 512 521 550 memory r (by decide) (by decide)
  simp [selectSparseAddress, Block.sequence, Block.eval_seq, Evaluation.bind, eval_arithmetic,
    eval_constant, eval_skip, hsub, Registers.write, Arithmetic.eval]

theorem selectLongFinish_source (memory : Memory) (regs : Registers) (word : Option (List Bool))
    (hzero : regs 513 = 0) (hpacket : regs 8194 = logicalPacket word) :
    let actual := selectLongFinish.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 513 =
      optionNatPacket (word.map (fun bits => regs 562 * regs 32 + regs 564 + bitsToNatLE bits)) := by
  cases word <;>
    simp [selectLongFinish, Block.sequence, Block.eval_seq, Evaluation.bind,
      eval_ifZero, eval_arithmetic, eval_skip, hpacket, hzero, logicalPacket, optionNatPacket,
      Arithmetic.eval, Registers.write, Nat.add_assoc]

theorem selectSparseFinish_source (memory : Memory) (regs : Registers) (word : Option (List Bool))
    (hzero : regs 513 = 0) (hpacket : regs 8194 = logicalPacket word) :
    let actual := selectSparseFinish.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 513 =
      optionNatPacket (word.map (fun bits => regs 520 + bitsToNatLE bits)) := by
  cases word <;>
    simp [selectSparseFinish, eval_ifZero, eval_arithmetic, eval_skip, hpacket, hzero,
      logicalPacket, optionNatPacket, Arithmetic.eval, Registers.write, Nat.add_assoc]

private theorem relativeReaderTail_source (shape : CartesianShape) (memory : Memory) (reader finish : Block)
    (hreader : ReaderCorrect shape memory reader) (base : Registers → Nat)
    (hbase : ∀ before after, ReaderFrame before after → base after = base before)
    (hfinish : ∀ regs word, regs 513 = 0 → regs 8194 = logicalPacket word →
      let actual := finish.eval memory ⟨regs, .running⟩
      actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 513 =
        optionNatPacket (word.map (fun bits => base regs + bitsToNatLE bits)))
    (regs : Registers) (hm : MetadataMatches shape regs) (hzero : regs 513 = 0) :
    let actual := (Block.seq reader finish).eval memory ⟨regs, .running⟩
    let word := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? (regs 8192) (regs 8193)
    actual.final.status = .running ∧ actual.final.regs 513 =
      optionNatPacket (word.map (fun bits => base regs + bitsToNatLE bits)) ∧
      actual.reads = readerReceipts shape memory (regs 8192) (regs 8193) := by
  have hr := hreader regs hm
  generalize he : reader.eval memory ⟨regs, .running⟩ = fetched at hr
  rcases fetched with ⟨⟨fr, fst⟩, reads⟩
  dsimp only at hr
  obtain ⟨hfst, hpacket, _hlength, hreads, hframe⟩ := hr
  subst fst
  have hz : fr 513 = 0 := (hframe 513 (Or.inl (by decide))).trans hzero
  have hf := hfinish fr _ hz hpacket
  have hb := hbase regs fr hframe
  rw [Block.eval_seq, he]
  dsimp only [Evaluation.bind]
  exact ⟨hf.1, by simpa only [hb] using hf.2.2, by rw [hf.2.1, List.append_nil]; exact hreads⟩

theorem selectLongReaderTail_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (regs : Registers)
    (hm : MetadataMatches shape regs) (hzero : regs 513 = 0) :
    let actual := (Block.seq reader selectLongFinish).eval memory ⟨regs, .running⟩
    let word := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? (regs 8192) (regs 8193)
    actual.final.status = .running ∧ actual.final.regs 513 =
      optionNatPacket (word.map (fun bits => regs 562 * regs 32 + regs 564 + bitsToNatLE bits)) ∧
      actual.reads = readerReceipts shape memory (regs 8192) (regs 8193) := by
  exact relativeReaderTail_source shape memory reader selectLongFinish hreader
    (fun regs => regs 562 * regs 32 + regs 564)
    (by intro before after hf; dsimp only; rw [hf 562 (Or.inl (by decide)), hf 32 (Or.inl (by decide)),
        hf 564 (Or.inl (by decide))])
    (selectLongFinish_source memory) regs hm hzero

theorem selectSparseReaderTail_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (regs : Registers)
    (hm : MetadataMatches shape regs) (hzero : regs 513 = 0) :
    let actual := (Block.seq reader selectSparseFinish).eval memory ⟨regs, .running⟩
    let word := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? (regs 8192) (regs 8193)
    actual.final.status = .running ∧ actual.final.regs 513 =
      optionNatPacket (word.map (fun bits => regs 520 + bitsToNatLE bits)) ∧
      actual.reads = readerReceipts shape memory (regs 8192) (regs 8193) := by
  exact relativeReaderTail_source shape memory reader selectSparseFinish hreader
    (fun regs => regs 520) (by intro before after hf; exact hf 520 (Or.inl (by decide)))
    (selectSparseFinish_source memory) regs hm hzero

theorem selectLocalAddress_writes :
    selectLocalAddress.WritesOnly (fun r => r = 515 ∨ r = 534 ∨ r = 550) := by
  simp [selectLocalAddress, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]

theorem selectLocalAddress_source (memory : Memory) (regs : Registers) :
    let actual := selectLocalAddress.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 515 =
      regs 514 * regs 27 + (regs 512 - regs 561) / regs 26 := by
  have hsub (r : Registers) := natSubBlock_source 515 512 561 550 memory r (by decide) (by decide)
  simp [selectLocalAddress, Block.sequence, Block.eval_seq, Evaluation.bind, eval_arithmetic,
    eval_skip, hsub, Registers.write, Arithmetic.eval]

theorem selectLocalPrepare_writes :
    selectLocalPrepare.WritesOnly (fun r => r = 520 ∨ r = 521) := by
  simp [selectLocalPrepare, Block.sequence, Block.WritesOnly, Action.destination]

theorem selectLocalPrepare_source (memory : Memory) (regs : Registers) :
    let actual := selectLocalPrepare.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 520 = (regs 562 + regs 592) * regs 32 + regs 594 ∧
      actual.final.regs 521 = regs 561 + regs 591 := by
  simp [selectLocalPrepare, Block.sequence, Block.eval_seq, Evaluation.bind, eval_arithmetic,
    eval_skip, Registers.write, Arithmetic.eval]

theorem selectLongTail_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (regs : Registers)
    (hm : MetadataMatches shape regs) (hzero : regs 513 = 0) :
    let actual := (Block.sequence [selectLongAddress, reader, selectLongFinish]).eval
      memory ⟨regs, .running⟩
    let expected := GenericSelect.bpRelativeOffsetReadTraceResultWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 12 (regs 562 * regs 32 + regs 564)
      (regs 360 * regs 25 + (regs 512 - regs 561))
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have ha := selectLongAddress_source memory regs
  have hf (r : Nat) (ho : r ≠ 534 ∧ r ≠ 535 ∧ r ≠ 550 ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    Block.eval_frame memory _ _ selectLongAddress_writes r (by omega) ⟨regs, .running⟩
  have hmeta := writes_metadata shape memory _ _ selectLongAddress_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  generalize heA : selectLongAddress.eval memory ⟨regs, .running⟩ = addressed at ha hf hmeta
  rcases addressed with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha hf hmeta
  obtain ⟨hast, hareads, hsegment, hindex⟩ := ha
  subst ast
  subst areads
  have hzero' : ar 513 = 0 := (hf 513 (by omega)).trans hzero
  have ht := selectLongReaderTail_source shape memory reader hreader ar hmeta hzero'
  have h562 := hf 562 (by omega)
  have h32 := hf 32 (by omega)
  have h564 := hf 564 (by omega)
  simp only [hsegment, hindex, h562, h32, h564] at ht
  have heq : (Block.sequence [selectLongAddress, reader, selectLongFinish]).eval memory ⟨regs, .running⟩ =
      (Block.seq reader selectLongFinish).eval memory ⟨ar, .running⟩ := by
    simp [Block.sequence, Block.eval_seq, heA, Evaluation.bind, eval_skip_any]
  rw [heq]
  dsimp only [GenericSelect.bpRelativeOffsetReadTraceResultWithStore, bpChunkReadTraceResult,
    WordRAM.TraceResult.map]
  refine ⟨ht.1, ?_, ?_, ?_⟩
  · simpa only [WordRAM.TraceResult.bind, WordRAM.TraceResult.pure, Option.map_map, Function.comp_def] using ht.2.1
  · simpa [logicalTraceReads] using ht.2.2
  · simp [ReadOnlyTrace, WordRAM.TraceEvent.isReadWord]

theorem selectSparseTail_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (regs : Registers)
    (hm : MetadataMatches shape regs) (hzero : regs 513 = 0) :
    let actual := (Block.sequence [selectSparseAddress, reader, selectSparseFinish]).eval
      memory ⟨regs, .running⟩
    let expected := GenericSelect.bpRelativeOffsetReadTraceResultWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 16 (regs 520)
      (regs 360 * regs 26 + (regs 512 - regs 521))
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have ha := selectSparseAddress_source memory regs
  have hf (r : Nat) (ho : r ≠ 534 ∧ r ≠ 535 ∧ r ≠ 550 ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    Block.eval_frame memory _ _ selectSparseAddress_writes r (by omega) ⟨regs, .running⟩
  have hmeta := writes_metadata shape memory _ _ selectSparseAddress_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  generalize heA : selectSparseAddress.eval memory ⟨regs, .running⟩ = addressed at ha hf hmeta
  rcases addressed with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha hf hmeta
  obtain ⟨hast, hareads, hsegment, hindex⟩ := ha
  subst ast
  subst areads
  have hzero' : ar 513 = 0 := (hf 513 (by omega)).trans hzero
  have ht := selectSparseReaderTail_source shape memory reader hreader ar hmeta hzero'
  have h520 := hf 520 (by omega)
  simp only [hsegment, hindex, h520] at ht
  have heq : (Block.sequence [selectSparseAddress, reader, selectSparseFinish]).eval memory ⟨regs, .running⟩ =
      (Block.seq reader selectSparseFinish).eval memory ⟨ar, .running⟩ := by
    simp [Block.sequence, Block.eval_seq, heA, Evaluation.bind, eval_skip_any]
  rw [heq]
  dsimp only [GenericSelect.bpRelativeOffsetReadTraceResultWithStore, bpChunkReadTraceResult,
    WordRAM.TraceResult.map]
  refine ⟨ht.1, ?_, ?_, ?_⟩
  · simpa only [WordRAM.TraceResult.bind, WordRAM.TraceResult.pure, Option.map_map, Function.comp_def] using ht.2.1
  · simpa [logicalTraceReads] using ht.2.2
  · simp [ReadOnlyTrace, WordRAM.TraceEvent.isReadWord]

theorem select_empty_word_reference (store : WordRAM.ReadStore) (c occurrence : Nat) :
    (bpChunkedWordSelectTraceResultAtSegmentsWithStore store 21 22 c false [] occurrence).value = none ∧
    (bpChunkedWordSelectTraceResultAtSegmentsWithStore store 21 22 c false [] occurrence).trace =
      [WordRAM.TraceEvent.readWord 21 (bpFringeChunkSlot c (bpFringeWindowChunkValue c [] 0) 0 0)
        (store.readWord? 21 (bpFringeChunkSlot c (bpFringeWindowChunkValue c [] 0) 0 0))] := by
  simp [bpChunkedWordSelectTraceResultAtSegmentsWithStore, bpWordChunkCount,
    bpChunkedWordSelectTraceFromWithStore, bpWordChunkSliceLen, bpChunkRankOfEntry,
    WordRAM.TraceResult.bind, bpChunkReadTraceResult, WordRAM.TraceResult.pure]

example : selectEntryOfPackets 0 1 1 1 = none := rfl
example : selectEntryOfPackets 1 0 1 1 = none := rfl
example : selectEntryOfPackets 1 1 0 1 = none := rfl
example : selectEntryOfPackets 1 1 1 0 = none := rfl
example : selectEntryOfPackets 1 1 1 1 = some ⟨0, 0, 0, 0⟩ := rfl
example (c : Nat) : bpWordChunkCount c 0 = 1 := by simp [bpWordChunkCount]
example : bpWordChunkCount 3 4 = 2 := by decide
example : bpWordChunkCount 3 100 = 8 := by decide
example : bpWordChunkSliceLen 3 4 1 = 1 := by decide

example : (bpChunkedWordSelectTraceResultAtSegmentsWithStore
    ⟨fun _ _ => none⟩ 21 22 1 false [false] 0).value = some 0 := by decide

example : (bpChunkedWordSelectTraceResultAtSegmentsWithStore
    ⟨fun _ _ => none⟩ 21 22 1 false [false] 1).value = none := by decide

theorem selectReadOnly_append (first second : List WordRAM.TraceEvent)
    (hf : ReadOnlyTrace first) (hs : ReadOnlyTrace second) : ReadOnlyTrace (first ++ second) := by
  intro event he
  rcases List.mem_append.mp he with h | h
  · exact hf event h
  · exact hs event h

private theorem denseRankPrepared_source (shape : CartesianShape) (memory : Memory) (reader prepare : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (limit : Nat) (regs : Registers)
    (hp : let actual := prepare.eval memory ⟨regs, .running⟩
      actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 256 = bitsToNatLE word ∧ actual.final.regs 257 = word.length ∧
      actual.final.regs 258 = limit ∧ actual.final.regs 259 = 0)
    (hm : MetadataMatches shape (prepare.eval memory ⟨regs, .running⟩).final.regs) :
    let actual := (Block.seq prepare (rankWordBlock reader)).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 (packedFringeChunkBits shape.size)
      false word limit
    actual.final.status = .running ∧ actual.final.regs 260 = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  generalize he : prepare.eval memory ⟨regs, .running⟩ = prepared at hp hm
  rcases prepared with ⟨⟨pr, status⟩, reads⟩
  dsimp only at hp hm
  obtain ⟨hstatus, hreads, hword, hlength, hlimit, htarget⟩ := hp
  subst status
  subst reads
  have hs := rankWordBlock_source shape memory reader hreader hwrites word false limit pr hm
    hword hlength hlimit htarget
  rw [Block.eval_seq, he]
  simpa only [Evaluation.bind, List.nil_append] using hs

theorem denseRankBefore_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (regs : Registers) (hm : MetadataMatches shape regs)
    (hpacket : regs 645 = bitsToNatLE word + 1) (hlength : regs 646 = word.length)
    (hone : regs 659 = 1) :
    let actual := (denseRankBefore reader).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 (packedFringeChunkBits shape.size)
      false word (regs 640 - regs 644 * regs 32)
    actual.final.status = .running ∧ actual.final.regs 260 = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hp := denseRankBeforePrepare_source memory regs
  have hmeta := writes_metadata shape memory _ _ denseRankBeforePrepare_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  exact denseRankPrepared_source shape memory reader denseRankBeforePrepare hreader hwrites
    word _ regs (by simpa only [hpacket, hlength, hone, Nat.add_sub_cancel] using hp) hmeta

theorem denseRankWhole_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (regs : Registers) (hm : MetadataMatches shape regs)
    (hpacket : regs 645 = bitsToNatLE word + 1) (hlength : regs 646 = word.length)
    (hone : regs 659 = 1) :
    let actual := (denseRankWhole reader).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 (packedFringeChunkBits shape.size)
      false word word.length
    actual.final.status = .running ∧ actual.final.regs 260 = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hp := denseRankWholePrepare_source memory regs
  have hmeta := writes_metadata shape memory _ _ denseRankWholePrepare_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  exact denseRankPrepared_source shape memory reader denseRankWholePrepare hreader hwrites
    word _ regs ⟨hp.1, hp.2.1, by simpa only [hpacket, hone, Nat.add_sub_cancel] using hp.2.2.2.1,
      hp.2.2.2.2.1.trans hlength, hp.2.2.2.2.2.1.trans hlength, hp.2.2.2.2.2.2⟩ hmeta

def DenseRankBeforeWrites (r : Nat) : Prop :=
  (256 ≤ r ∧ r < 311) ∨ r = 647 ∨ r = 658 ∨ (8192 ≤ r ∧ r < 8271)

def DenseRankWholeWrites (r : Nat) : Prop :=
  (256 ≤ r ∧ r < 311) ∨ r = 648 ∨ r = 658 ∨ (8192 ≤ r ∧ r < 8271)

theorem denseRankBefore_writes (reader : Block) (hw : ReaderWrites reader) :
    (denseRankBefore reader).WritesOnly DenseRankBeforeWrites := by
  have hp := Block.WritesOnly.mono _ denseRankBeforePrepare_writes
    (show ∀ r, (256 ≤ r ∧ r < 260) ∨ r = 647 ∨ r = 658 → DenseRankBeforeWrites r from by
      intro r h; unfold DenseRankBeforeWrites; omega)
  have hr := Block.WritesOnly.mono _ (rankWordBlock_writes reader hw)
    (show ∀ r, RankWordWrites r → DenseRankBeforeWrites r from by
      intro r h; unfold RankWordWrites at h; unfold DenseRankBeforeWrites; omega)
  exact ⟨hp, hr⟩

theorem denseRankWhole_writes (reader : Block) (hw : ReaderWrites reader) :
    (denseRankWhole reader).WritesOnly DenseRankWholeWrites := by
  have hp := Block.WritesOnly.mono _ denseRankWholePrepare_writes
    (show ∀ r, (256 ≤ r ∧ r < 260) ∨ r = 648 ∨ r = 658 → DenseRankWholeWrites r from by
      intro r h; unfold DenseRankWholeWrites; omega)
  have hr := Block.WritesOnly.mono _ (rankWordBlock_writes reader hw)
    (show ∀ r, RankWordWrites r → DenseRankWholeWrites r from by
      intro r h; unfold RankWordWrites at h; unfold DenseRankWholeWrites; omega)
  exact ⟨hp, hr⟩

theorem denseRankWhole_saved (memory : Memory) (reader : Block) (hwrites : ReaderWrites reader)
    (regs : Registers) :
    ((denseRankWhole reader).eval memory ⟨regs, .running⟩).final.regs 648 = regs 260 := by
  have hp := denseRankWholePrepare_source memory regs
  rw [denseRankWhole, Block.eval_seq]
  dsimp only [Evaluation.bind]
  rw [rankWordBlock_frame reader hwrites memory _ 648 (by simp [RankWordWrites])]
  exact hp.2.2.1

def denseChoiceReference (store : WordRAM.ReadStore) (c wordSize wordIndex remaining before upto : Nat)
    (word : List Bool) : WordRAM.TraceResult (Option Nat) :=
  if remaining < upto - before then
    WordRAM.TraceResult.map (fun value? => value?.map (fun x => wordIndex * wordSize + x))
      (bpChunkedWordSelectTraceResultAtSegmentsWithStore store 21 22 c false word (before + remaining))
  else denseSecondReference store c wordSize wordIndex (remaining - (upto - before))

theorem denseSelectBranch_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (before upto remaining : Nat) (regs : Registers)
    (hm : MetadataMatches shape regs) (hpacket : regs 645 = bitsToNatLE word + 1)
    (hlength : regs 646 = word.length) (hone : regs 659 = 1) (hzero : regs 643 = 0)
    (hbefore : regs 648 = before) (hremaining : regs 650 = remaining)
    (havailable : regs 651 = upto - before)
    (htest : regs 652 = if remaining < upto - before then 1 else 0) :
    let actual := (denseSelectBranch reader).eval memory ⟨regs, .running⟩
    let expected := denseChoiceReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedFringeChunkBits shape.size) (regs 32) (regs 644) remaining before upto word
    actual.final.status = .running ∧ actual.final.regs 643 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  by_cases hchoose : remaining < upto - before
  · have hs := denseFirstSelected_source shape memory reader hreader hwrites word regs hm
      hpacket hlength hone hzero
    simpa [denseSelectBranch, eval_ifZero, htest, hchoose, denseChoiceReference,
      WordRAM.TraceResult.map, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
      hbefore, hremaining] using hs
  · have hs := denseSecondSelected_source shape memory reader hreader hwrites regs hm hone hzero
    simpa [denseSelectBranch, eval_ifZero, htest, hchoose, denseChoiceReference,
      hremaining, havailable] using hs

def densePresentReference (store : WordRAM.ReadStore) (c wordSize basePosition baseOccurrence occurrence : Nat)
    (word : List Bool) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (bpChunkedWordRankTraceResultAtSegmentWithStore store 21 c false word
      (basePosition - basePosition / wordSize * wordSize)) fun before =>
    WordRAM.TraceResult.bind
      (bpChunkedWordRankTraceResultAtSegmentWithStore store 21 c false word word.length) fun upto =>
      denseChoiceReference store c wordSize (basePosition / wordSize)
        (occurrence - baseOccurrence) before upto word

theorem densePresent_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (regs : Registers) (hm : MetadataMatches shape regs)
    (hpacket : regs 645 = bitsToNatLE word + 1) (hlength : regs 646 = word.length)
    (hone : regs 659 = 1) (hzero : regs 643 = 0) (hindex : regs 644 = regs 640 / regs 32) :
    let actual := (densePresent reader).eval memory ⟨regs, .running⟩
    let expected := densePresentReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedFringeChunkBits shape.size) (regs 32) (regs 640) (regs 641) (regs 642) word
    actual.final.status = .running ∧ actual.final.regs 643 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hb := denseRankBefore_source shape memory reader hreader hwrites word regs hm hpacket hlength hone
  have hbf (r : Nat) (ho : ¬ DenseRankBeforeWrites r) :=
    Block.eval_frame memory _ _ (denseRankBefore_writes reader hwrites) r ho ⟨regs, .running⟩
  have hbm := writes_metadata shape memory _ _ (denseRankBefore_writes reader hwrites)
    (by intro r hlo hhi; unfold DenseRankBeforeWrites; omega) ⟨regs, .running⟩ hm
  generalize heB : (denseRankBefore reader).eval memory ⟨regs, .running⟩ = beforeEval at hb hbf hbm
  rcases beforeEval with ⟨⟨br, bst⟩, breads⟩
  dsimp only at hb hbf hbm
  obtain ⟨hbst, hbvalue, hbreads, hbro⟩ := hb
  subst bst
  rw [hindex] at hbvalue hbreads hbro
  have hp645 : br 645 = bitsToNatLE word + 1 := (hbf 645 (by simp [DenseRankBeforeWrites])).trans hpacket
  have hp646 : br 646 = word.length := (hbf 646 (by simp [DenseRankBeforeWrites])).trans hlength
  have hp659 : br 659 = 1 := (hbf 659 (by simp [DenseRankBeforeWrites])).trans hone
  have hc := denseRankWhole_source shape memory reader hreader hwrites word br hbm hp645 hp646 hp659
  have hc648 := denseRankWhole_saved memory reader hwrites br
  have hcf (r : Nat) (ho : ¬ DenseRankWholeWrites r) :=
    Block.eval_frame memory _ _ (denseRankWhole_writes reader hwrites) r ho ⟨br, .running⟩
  have hcm := writes_metadata shape memory _ _ (denseRankWhole_writes reader hwrites)
    (by intro r hlo hhi; unfold DenseRankWholeWrites; omega) ⟨br, .running⟩ hbm
  generalize heC : (denseRankWhole reader).eval memory ⟨br, .running⟩ = wholeEval at hc hc648 hcf hcm
  rcases wholeEval with ⟨⟨cr, cst⟩, creads⟩
  dsimp only at hc hc648 hcf hcm
  obtain ⟨hcst, hcvalue, hcreads, hcro⟩ := hc
  subst cst
  have hp (r : Nat) (ho : r < 8192 ∧ (r < 256 ∨ 311 ≤ r) ∧ r ≠ 647 ∧ r ≠ 648 ∧ r ≠ 658) :
      cr r = regs r := by
    rw [hcf r (by unfold DenseRankWholeWrites; omega), hbf r (by unfold DenseRankBeforeWrites; omega)]
  have hd := denseChoosePrepare_source memory cr
  have hdf (r : Nat) (ho : ¬ ((649 ≤ r ∧ r < 653) ∨ r = 658)) :=
    Block.eval_frame memory _ _ denseChoosePrepare_writes r ho ⟨cr, .running⟩
  have hdm := writes_metadata shape memory _ _ denseChoosePrepare_writes
    (by intro r hlo hhi; omega) ⟨cr, .running⟩ hcm
  generalize heD : denseChoosePrepare.eval memory ⟨cr, .running⟩ = choiceEval at hd hdf hdm
  rcases choiceEval with ⟨⟨dr, dst⟩, dreads⟩
  dsimp only at hd hdf hdm
  obtain ⟨hdst, hdreads, _hd649, hd650, hd651, hd652⟩ := hd
  subst dst
  subst dreads
  have hp' (r : Nat) (ho : r < 8192 ∧ (r < 256 ∨ 311 ≤ r) ∧ r ≠ 647 ∧ r ≠ 648 ∧ r ≠ 658 ∧
      (r < 649 ∨ 653 ≤ r)) : dr r = regs r := by
    rw [hdf r (by omega), hp r (by omega)]
  have h648 : dr 648 = br 260 := (hdf 648 (by omega)).trans hc648
  have h640 := hp 640 (by omega)
  have h641 := hp 641 (by omega)
  have h642 := hp 642 (by omega)
  rw [h641, h642] at hd650 hd652
  rw [hc648] at hd651 hd652
  have hs := denseSelectBranch_source shape memory reader hreader hwrites word (br 260) (cr 260)
    (regs 642 - regs 641) dr hdm
    ((hp' 645 (by omega)).trans hpacket) ((hp' 646 (by omega)).trans hlength)
    ((hp' 659 (by omega)).trans hone) ((hp' 643 (by omega)).trans hzero)
    h648 hd650 hd651 hd652
  generalize heS : (denseSelectBranch reader).eval memory ⟨dr, .running⟩ = selected at hs
  rcases selected with ⟨⟨sr, sst⟩, sreads⟩
  dsimp only at hs
  obtain ⟨hsst, hsvalue, hsreads, hsro⟩ := hs
  subst sst
  have h32' := hp' 32 (by omega)
  have h644' : dr 644 = regs 640 / regs 32 := (hp' 644 (by omega)).trans hindex
  simp only [h32', h644', hbvalue, hcvalue] at hsvalue hsreads hsro
  have heval : (densePresent reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨sr, .running⟩, breads ++ creads ++ sreads⟩ := by
    simp [densePresent, Block.sequence, Block.eval_seq, Evaluation.bind, heB, heC, heD, heS,
      eval_skip, List.append_assoc]
  rw [heval]
  dsimp only [densePresentReference, WordRAM.TraceResult.bind]
  refine ⟨rfl, hsvalue, ?_, ?_⟩
  · rw [hbreads, hcreads, hsreads, select_logicalTraceReads_append, select_logicalTraceReads_append]
    simp only [List.append_assoc]
  · exact selectReadOnly_append _ _ hbro (selectReadOnly_append _ _ hcro hsro)

theorem packedDenseTwoWordSelectRead_normalForm (store : WordRAM.ReadStore)
    (c wordSize basePosition baseOccurrence occurrence : Nat) :
    packedDenseTwoWordSelectRead 0 21 22 c false store wordSize basePosition baseOccurrence occurrence =
      WordRAM.TraceResult.bind (bpWordReadTraceResult store 0 (basePosition / wordSize))
        (fun word? => match word? with
          | none => WordRAM.TraceResult.pure none
          | some word => densePresentReference store c wordSize basePosition baseOccurrence occurrence word) := rfl

theorem denseSelectBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (denseSelectBlock reader).eval memory ⟨regs, .running⟩
    let expected := packedDenseTwoWordSelectRead 0 21 22 (packedFringeChunkBits shape.size) false
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) (regs 32) (regs 640) (regs 641) (regs 642)
    actual.final.status = .running ∧ actual.final.regs 643 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have ha := denseReadAddress_source memory regs
  have haf (r : Nat) (ho : r ≠ 643 ∧ r ≠ 644 ∧ r ≠ 659 ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    Block.eval_frame memory _ _ denseReadAddress_writes r (by omega) ⟨regs, .running⟩
  have ham := writes_metadata shape memory _ _ denseReadAddress_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  generalize heA : denseReadAddress.eval memory ⟨regs, .running⟩ = addressed at ha haf ham
  rcases addressed with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha haf ham
  obtain ⟨hast, hareads, hzero, hone, h644, hsegment, hindex⟩ := ha
  subst ast
  subst areads
  have hb := hreader ar ham
  generalize heB : reader.eval memory ⟨ar, .running⟩ = fetched at hb
  rcases fetched with ⟨⟨br, bst⟩, breads⟩
  dsimp only at hb
  obtain ⟨hbst, hpacket, hlength, hreads, hbf⟩ := hb
  subst bst
  rw [hsegment, hindex] at hpacket hlength hreads
  have hbm := hbf.metadata shape ar br ham
  have hc := denseReadSave_source memory br
  have hcf (r : Nat) (ho : r ≠ 645 ∧ r ≠ 646) :=
    Block.eval_frame memory _ _ denseReadSave_writes r (by omega) ⟨br, .running⟩
  have hcm := writes_metadata shape memory _ _ denseReadSave_writes
    (by intro r hlo hhi; omega) ⟨br, .running⟩ hbm
  generalize heC : denseReadSave.eval memory ⟨br, .running⟩ = saved at hc hcf hcm
  rcases saved with ⟨⟨cr, cst⟩, creads⟩
  dsimp only at hc hcf hcm
  obtain ⟨hcst, hcreads, hc645, hc646⟩ := hc
  subst cst
  subst creads
  have hp (r : Nat) (ho : r < 8192 ∧ r ≠ 643 ∧ r ≠ 644 ∧ r ≠ 645 ∧ r ≠ 646 ∧ r ≠ 659) :
      cr r = regs r := by
    rw [hcf r (by omega), hbf r (Or.inl (by omega)), haf r (by omega)]
  have hp643 : cr 643 = 0 := by rw [hcf 643 (by omega), hbf 643 (Or.inl (by decide)), hzero]
  have hp659 : cr 659 = 1 := by rw [hcf 659 (by omega), hbf 659 (Or.inl (by decide)), hone]
  have hp644 : cr 644 = regs 640 / regs 32 := by
    rw [hcf 644 (by omega), hbf 644 (Or.inl (by decide)), h644]
  have hp32 := hp 32 (by omega)
  have hp640 := hp 640 (by omega)
  have hp641 := hp 641 (by omega)
  have hp642 := hp 642 (by omega)
  rw [hpacket] at hc645
  rw [hlength] at hc646
  cases hword : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 (regs 640 / regs 32) with
  | none =>
      simp only [hword, logicalPacket_none, logicalLength_none] at hc645 hc646
      simp [denseSelectBlock, Block.sequence, Block.eval_seq, Evaluation.bind, heA, heB, heC,
        eval_ifZero, eval_skip, hc645, hp643, hreads, packedDenseTwoWordSelectRead_normalForm,
        bpWordReadTraceResult, hword, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
        optionNatPacket, logicalTraceReads, ReadOnlyTrace, WordRAM.TraceEvent.isReadWord]
  | some word =>
      simp only [hword, logicalPacket_some, logicalLength_some] at hc645 hc646
      have hs := densePresent_source shape memory reader hreader hwrites word cr hcm hc645 hc646
        hp659 hp643 (by simpa only [hp32, hp640] using hp644)
      generalize heS : (densePresent reader).eval memory ⟨cr, .running⟩ = selected at hs
      rcases selected with ⟨⟨sr, sst⟩, sreads⟩
      dsimp only at hs
      obtain ⟨hsst, hsvalue, hsreads, hsro⟩ := hs
      subst sst
      simp only [hp32, hp640, hp641, hp642] at hsvalue hsreads hsro
      have heval : (denseSelectBlock reader).eval memory ⟨regs, .running⟩ =
          ⟨⟨sr, .running⟩, breads ++ sreads⟩ := by
        simp [denseSelectBlock, Block.sequence, Block.eval_seq, Evaluation.bind, heA, heB, heC,
          eval_ifZero, hc645, heS, eval_skip]
      rw [heval]
      rw [packedDenseTwoWordSelectRead_normalForm]
      dsimp only [bpWordReadTraceResult, WordRAM.TraceResult.bind]
      rw [hword]
      refine ⟨rfl, hsvalue, ?_, ?_⟩
      · rw [hreads, hsreads, select_logicalTraceReads_append]
        simp [logicalTraceReads]
      · simpa [ReadOnlyTrace, WordRAM.TraceEvent.isReadWord] using hsro

theorem selectLongBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hzero : regs 513 = 0) :
    let actual := (selectLongBlock reader).eval memory ⟨regs, .running⟩
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let expected := WordRAM.TraceResult.bind
      (packedRankRead 9 10 11 21 (packedFringeChunkBits shape.size) true store
        (packedSuperSlots shape.size) (packedLongFlagWordSize shape.size) 1 (regs 514))
      (fun rank => GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 12
        (regs 562 * regs 32 + regs 564) (rank * regs 25 + (regs 512 - regs 561)))
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let prepared := regs.write 352 (regs 514)
  have hpm := MetadataMatches.write shape regs hm 352 (regs 514) (Or.inr (by decide))
  have hr := rankLongBlock_source shape memory reader hreader hwrites prepared hpm
  have hrf (r : Nat) (ho : ¬ RankWrapperWrites r) :=
    rankLongBlock_frame reader hwrites memory ⟨prepared, .running⟩ r ho
  have hrm := writes_metadata shape memory _ _ (rankLongBlock_writes reader hwrites)
    (by intro r hlo hhi; unfold RankWrapperWrites; omega) ⟨prepared, .running⟩ hpm
  generalize heR : (rankLongBlock reader).eval memory ⟨prepared, .running⟩ = ranked at hr hrf hrm
  rcases ranked with ⟨⟨rr, rst⟩, rreads⟩
  dsimp only at hr hrf hrm
  obtain ⟨hrst, hrvalue, hrreads, hrro⟩ := hr
  subst rst
  simp [prepared] at hrvalue hrreads hrro
  have hp (r : Nat) (ho : ¬ RankWrapperWrites r ∧ r ≠ 352) : rr r = regs r := by
    rw [hrf r ho.1]
    simp [prepared, Registers.write, ho.2]
  have hz : rr 513 = 0 := (hp 513 (by simp [RankWrapperWrites])).trans hzero
  have ht := selectLongTail_source shape memory reader hreader rr hrm hz
  generalize heT : (Block.sequence [selectLongAddress, reader, selectLongFinish]).eval
      memory ⟨rr, .running⟩ = finished at ht
  rcases finished with ⟨⟨fr, fst⟩, freads⟩
  dsimp only at ht
  obtain ⟨hfst, hfvalue, hfreads, hfro⟩ := ht
  subst fst
  have h562 := hp 562 (by simp [RankWrapperWrites])
  have h32 := hp 32 (by simp [RankWrapperWrites])
  have h564 := hp 564 (by simp [RankWrapperWrites])
  have h25 := hp 25 (by simp [RankWrapperWrites])
  have h512 := hp 512 (by simp [RankWrapperWrites])
  have h561 := hp 561 (by simp [RankWrapperWrites])
  simp only [h562, h32, h564, h25, h512, h561, hrvalue] at hfvalue hfreads hfro
  have heval : (selectLongBlock reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨fr, .running⟩, rreads ++ freads⟩ := by
    have hj := eval_seq_of_results memory (rankLongBlock reader)
      (Block.sequence [selectLongAddress, reader, selectLongFinish]) ⟨prepared, .running⟩
      ⟨⟨rr, .running⟩, rreads⟩ ⟨⟨fr, .running⟩, freads⟩ heR heT
    have hpref := eval_seq_of_results memory (.action (.move 352 514))
      (.seq (rankLongBlock reader) (Block.sequence [selectLongAddress, reader, selectLongFinish]))
      ⟨regs, .running⟩ ⟨⟨prepared, .running⟩, []⟩ ⟨⟨fr, .running⟩, rreads ++ freads⟩
      (eval_move memory regs 352 514) hj
    simpa only [selectLongBlock, Block.sequence, List.foldr_cons, List.foldr_nil,
      List.nil_append] using hpref
  rw [heval]
  dsimp only [WordRAM.TraceResult.bind]
  refine ⟨rfl, hfvalue, ?_, selectReadOnly_append _ _ hrro hfro⟩
  rw [hrreads, hfreads, select_logicalTraceReads_append]

theorem selectSparseBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hzero : regs 513 = 0) :
    let actual := (selectSparseBlock reader).eval memory ⟨regs, .running⟩
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let expected := WordRAM.TraceResult.bind
      (packedRankRead 13 14 15 21 (packedFringeChunkBits shape.size) true store
        (packedSparseSlots shape.size) (packedSparseWordSize shape.size) 1 (regs 515))
      (fun rank => GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 16
        (regs 520) (rank * regs 26 + (regs 512 - regs 521)))
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let prepared := regs.write 352 (regs 515)
  have hpm := MetadataMatches.write shape regs hm 352 (regs 515) (Or.inr (by decide))
  have hr := rankSparseBlock_source shape memory reader hreader hwrites prepared hpm
  have hrf (r : Nat) (ho : ¬ RankWrapperWrites r) :=
    rankSparseBlock_frame reader hwrites memory ⟨prepared, .running⟩ r ho
  have hrm := writes_metadata shape memory _ _ (rankSparseBlock_writes reader hwrites)
    (by intro r hlo hhi; unfold RankWrapperWrites; omega) ⟨prepared, .running⟩ hpm
  generalize heR : (rankSparseBlock reader).eval memory ⟨prepared, .running⟩ = ranked at hr hrf hrm
  rcases ranked with ⟨⟨rr, rst⟩, rreads⟩
  dsimp only at hr hrf hrm
  obtain ⟨hrst, hrvalue, hrreads, hrro⟩ := hr
  subst rst
  simp [prepared] at hrvalue hrreads hrro
  have hp (r : Nat) (ho : ¬ RankWrapperWrites r ∧ r ≠ 352) : rr r = regs r := by
    rw [hrf r ho.1]
    simp [prepared, Registers.write, ho.2]
  have hz : rr 513 = 0 := (hp 513 (by simp [RankWrapperWrites])).trans hzero
  have ht := selectSparseTail_source shape memory reader hreader rr hrm hz
  generalize heT : (Block.sequence [selectSparseAddress, reader, selectSparseFinish]).eval
      memory ⟨rr, .running⟩ = finished at ht
  rcases finished with ⟨⟨fr, fst⟩, freads⟩
  dsimp only at ht
  obtain ⟨hfst, hfvalue, hfreads, hfro⟩ := ht
  subst fst
  have h520 := hp 520 (by simp [RankWrapperWrites])
  have h26 := hp 26 (by simp [RankWrapperWrites])
  have h512 := hp 512 (by simp [RankWrapperWrites])
  have h521 := hp 521 (by simp [RankWrapperWrites])
  simp only [h520, h26, h512, h521, hrvalue] at hfvalue hfreads hfro
  have heval : (selectSparseBlock reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨fr, .running⟩, rreads ++ freads⟩ := by
    have hj := eval_seq_of_results memory (rankSparseBlock reader)
      (Block.sequence [selectSparseAddress, reader, selectSparseFinish]) ⟨prepared, .running⟩
      ⟨⟨rr, .running⟩, rreads⟩ ⟨⟨fr, .running⟩, freads⟩ heR heT
    have hpref := eval_seq_of_results memory (.action (.move 352 515))
      (.seq (rankSparseBlock reader) (Block.sequence [selectSparseAddress, reader, selectSparseFinish]))
      ⟨regs, .running⟩ ⟨⟨prepared, .running⟩, []⟩ ⟨⟨fr, .running⟩, rreads ++ freads⟩
      (eval_move memory regs 352 515) hj
    simpa only [selectSparseBlock, Block.sequence, List.foldr_cons, List.foldr_nil,
      List.nil_append] using hpref
  rw [heval]
  dsimp only [WordRAM.TraceResult.bind]
  refine ⟨rfl, hfvalue, ?_, selectReadOnly_append _ _ hrro hfro⟩
  rw [hrreads, hfreads, select_logicalTraceReads_append]

theorem denseFirstSelected_writes (reader : Block) (hw : ReaderWrites reader) :
    (denseFirstSelected reader).WritesOnly DenseWrites := by
  have hs : (selectWordBlock reader).WritesOnly DenseWrites :=
    Block.WritesOnly.mono _ (selectWordBlock_writes reader hw) (by
      intro r h; unfold SelectWordWrites at h; unfold DenseWrites; omega)
  simpa [denseFirstSelected, denseFirstPrepare, denseWordFinish, Block.sequence,
    Block.WritesOnly, Action.destination, natSubBlock, DenseWrites] using hs

theorem denseSecondSelected_writes (reader : Block) (hw : ReaderWrites reader) :
    (denseSecondSelected reader).WritesOnly DenseWrites := by
  have hs : (selectWordBlock reader).WritesOnly DenseWrites :=
    Block.WritesOnly.mono _ (selectWordBlock_writes reader hw) (by
      intro r h; unfold SelectWordWrites at h; unfold DenseWrites; omega)
  have hr : reader.WritesOnly DenseWrites :=
    Block.WritesOnly.mono _ hw (by intro r h; unfold DenseWrites; omega)
  simpa [denseSecondSelected, denseSecondAddress, denseSecondPrepare, denseWordFinish,
    Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, DenseWrites] using ⟨hr, hs⟩

theorem densePresent_writes (reader : Block) (hw : ReaderWrites reader) :
    (densePresent reader).WritesOnly DenseWrites := by
  have hb : (denseRankBefore reader).WritesOnly DenseWrites :=
    Block.WritesOnly.mono _ (denseRankBefore_writes reader hw) (by
      intro r h; unfold DenseRankBeforeWrites at h; unfold DenseWrites; omega)
  have hc : (denseRankWhole reader).WritesOnly DenseWrites :=
    Block.WritesOnly.mono _ (denseRankWhole_writes reader hw) (by
      intro r h; unfold DenseRankWholeWrites at h; unfold DenseWrites; omega)
  have hs := denseSecondSelected_writes reader hw
  have hf := denseFirstSelected_writes reader hw
  simpa [densePresent, denseChoosePrepare, denseSelectBranch, Block.sequence, Block.WritesOnly,
    Action.destination, natSubBlock, DenseWrites] using ⟨hb, hc, hs, hf⟩

theorem denseSelectBlock_writes (reader : Block) (hw : ReaderWrites reader) :
    (denseSelectBlock reader).WritesOnly DenseWrites := by
  have hr : reader.WritesOnly DenseWrites :=
    Block.WritesOnly.mono _ hw (by intro r h; unfold DenseWrites; omega)
  have hs := densePresent_writes reader hw
  simpa [denseSelectBlock, denseReadAddress, denseReadSave, Block.sequence, Block.WritesOnly,
    Action.destination, DenseWrites] using ⟨hr, hs⟩

theorem denseSelectBlock_frame (reader : Block) (hw : ReaderWrites reader) (memory : Memory)
    (s : Data) (r : Nat) (outside : ¬ DenseWrites r) :
    ((denseSelectBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (denseSelectBlock_writes reader hw) r outside s

def SelectWrites (r : Nat) : Prop :=
  (256 ≤ r ∧ r < 311) ∨ (352 ≤ r ∧ r < 371) ∨ (400 ≤ r ∧ r < 412) ∨
    (513 ≤ r ∧ r < 551) ∨ (560 ≤ r ∧ r < 571) ∨ (590 ≤ r ∧ r < 601) ∨
    (640 ≤ r ∧ r < 660) ∨ (8192 ≤ r ∧ r < 8271)

theorem selectLongBlock_writes (reader : Block) (hw : ReaderWrites reader) :
    (selectLongBlock reader).WritesOnly SelectWrites := by
  have hrank : (rankLongBlock reader).WritesOnly SelectWrites :=
    Block.WritesOnly.mono _ (rankLongBlock_writes reader hw) (by
      intro r h; unfold RankWrapperWrites at h; unfold SelectWrites; omega)
  have hr : reader.WritesOnly SelectWrites :=
    Block.WritesOnly.mono _ hw (by intro r h; unfold SelectWrites; omega)
  simpa [selectLongBlock, selectLongAddress, selectLongFinish, Block.sequence, Block.WritesOnly,
    Action.destination, natSubBlock, SelectWrites] using ⟨hrank, hr⟩

theorem selectSparseBlock_writes (reader : Block) (hw : ReaderWrites reader) :
    (selectSparseBlock reader).WritesOnly SelectWrites := by
  have hrank : (rankSparseBlock reader).WritesOnly SelectWrites :=
    Block.WritesOnly.mono _ (rankSparseBlock_writes reader hw) (by
      intro r h; unfold RankWrapperWrites at h; unfold SelectWrites; omega)
  have hr : reader.WritesOnly SelectWrites :=
    Block.WritesOnly.mono _ hw (by intro r h; unfold SelectWrites; omega)
  simpa [selectSparseBlock, selectSparseAddress, selectSparseFinish, Block.sequence, Block.WritesOnly,
    Action.destination, natSubBlock, SelectWrites] using ⟨hrank, hr⟩

theorem selectLocalDense_writes (reader : Block) (hw : ReaderWrites reader) :
    (selectLocalDense reader).WritesOnly SelectWrites := by
  have hd : (denseSelectBlock reader).WritesOnly SelectWrites :=
    Block.WritesOnly.mono _ (denseSelectBlock_writes reader hw) (by
      intro r h; unfold DenseWrites at h; unfold SelectWrites; omega)
  simpa [selectLocalDense, Block.sequence, Block.WritesOnly, Action.destination, SelectWrites] using hd

theorem selectLocalBlock_writes (reader : Block) (hw : ReaderWrites reader) :
    (selectLocalBlock reader).WritesOnly SelectWrites := by
  have he : (selectEntryBlock reader 5 515 590).WritesOnly SelectWrites :=
    Block.WritesOnly.mono _ (selectEntryBlock_writes reader hw 5 515 590) (by
      intro r h; unfold SelectEntryWrites at h; unfold SelectWrites; omega)
  have hd := selectLocalDense_writes reader hw
  have hs := selectSparseBlock_writes reader hw
  simpa [selectLocalBlock, selectLocalAddress, selectLocalPresent, selectLocalPrepare, Block.sequence, Block.WritesOnly,
    Action.destination, natSubBlock, SelectWrites] using ⟨he, hd, hs⟩

theorem selectCloseBlock_writes (reader : Block) (hw : ReaderWrites reader) :
    (selectCloseBlock reader).WritesOnly SelectWrites := by
  have he : (selectEntryBlock reader 1 514 560).WritesOnly SelectWrites :=
    Block.WritesOnly.mono _ (selectEntryBlock_writes reader hw 1 514 560) (by
      intro r h; unfold SelectEntryWrites at h; unfold SelectWrites; omega)
  have hl := selectLocalBlock_writes reader hw
  have hx := selectLongBlock_writes reader hw
  simpa [selectCloseBlock, selectEligible, selectSuperPresent, Block.sequence, Block.WritesOnly, Action.destination, SelectWrites]
    using ⟨he, hl, hx⟩

theorem selectCloseBlock_frame (reader : Block) (hw : ReaderWrites reader) (memory : Memory)
    (s : Data) (r : Nat) (outside : ¬ SelectWrites r) :
    ((selectCloseBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (selectCloseBlock_writes reader hw) r outside s

theorem selectCloseBlock_metadata (shape : CartesianShape) (reader : Block) (hw : ReaderWrites reader)
    (memory : Memory) (s : Data) (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((selectCloseBlock reader).eval memory s).final.regs :=
  writes_metadata shape memory _ _ (selectCloseBlock_writes reader hw)
    (by intro r hlo hhi; unfold SelectWrites; omega) s hm

theorem selectLocalDense_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (selectLocalDense reader).eval memory ⟨regs, .running⟩
    let expected := packedDenseTwoWordSelectRead 0 21 22 (packedFringeChunkBits shape.size) false
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) (regs 32) (regs 520) (regs 521) (regs 512)
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let prepared := ((regs.write 640 (regs 520)).write 641 (regs 521)).write 642 (regs 512)
  have hpm : MetadataMatches shape prepared := by
    apply MetadataMatches.write _ _ _ _ _ (Or.inr (by decide))
    apply MetadataMatches.write _ _ _ _ _ (Or.inr (by decide))
    exact MetadataMatches.write shape regs hm 640 (regs 520) (Or.inr (by decide))
  have hs := denseSelectBlock_source shape memory reader hreader hwrites prepared hpm
  generalize heD : (denseSelectBlock reader).eval memory ⟨prepared, .running⟩ = dense at hs
  rcases dense with ⟨⟨dr, dst⟩, dreads⟩
  dsimp only at hs
  obtain ⟨hdst, hdvalue, hdreads, hdro⟩ := hs
  subst dst
  simp [prepared, Registers.write] at hdvalue hdreads hdro
  dsimp only [prepared] at heD
  simp [selectLocalDense, Block.sequence, Block.eval_seq, Evaluation.bind, eval_move, heD,
    eval_skip, Registers.write, hdvalue, hdreads, hdro]

def selectLocalChoiceReference (store : WordRAM.ReadStore) (n wordSize superWord superOccurrence idx slot : Nat)
    (loc : GenericSelect.SparseDenseSelectDenseLocalEntry) : WordRAM.TraceResult (Option Nat) :=
  let base := (superWord + loc.baseWordIndex) * wordSize + loc.firstOffset
  let occurrence := superOccurrence + loc.baseOccurrence
  if loc.rankBefore = 0 then
    packedDenseTwoWordSelectRead 0 21 22 (packedFringeChunkBits n) false store wordSize base occurrence idx
  else WordRAM.TraceResult.bind
    (packedRankRead 13 14 15 21 (packedFringeChunkBits n) true store
      (packedSparseSlots n) (packedSparseWordSize n) 1 slot)
    (fun rank => GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 16 base
      (rank * packedSelectLocalStride n + (idx - occurrence)))

theorem selectLocalPresent_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (loc : GenericSelect.SparseDenseSelectDenseLocalEntry) (regs : Registers)
    (hm : MetadataMatches shape regs) (hzero : regs 513 = 0)
    (h591 : regs 591 = loc.baseOccurrence) (h592 : regs 592 = loc.baseWordIndex)
    (h593 : regs 593 = loc.rankBefore) (h594 : regs 594 = loc.firstOffset) :
    let actual := (selectLocalPresent reader).eval memory ⟨regs, .running⟩
    let expected := selectLocalChoiceReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 32) (regs 562) (regs 561) (regs 512) (regs 515) loc
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hp := selectLocalPrepare_source memory regs
  have hpf (r : Nat) (ho : r ≠ 520 ∧ r ≠ 521) :=
    Block.eval_frame memory _ _ selectLocalPrepare_writes r (by omega) ⟨regs, .running⟩
  have hpm := writes_metadata shape memory _ _ selectLocalPrepare_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  generalize heP : selectLocalPrepare.eval memory ⟨regs, .running⟩ = prepared at hp hpf hpm
  rcases prepared with ⟨⟨pr, pst⟩, preads⟩
  dsimp only at hp hpf hpm
  obtain ⟨hpst, hpreads, hp520, hp521⟩ := hp
  subst pst
  subst preads
  rw [h592, h594] at hp520
  rw [h591] at hp521
  have hp513 : pr 513 = 0 := (hpf 513 (by omega)).trans hzero
  have hp593 : pr 593 = loc.rankBefore := (hpf 593 (by omega)).trans h593
  have hp32 := hpf 32 (by omega)
  have hp512 := hpf 512 (by omega)
  have hp515 := hpf 515 (by omega)
  have hp26 : pr 26 = packedSelectLocalStride shape.size := by
    rw [hpf 26 (by omega)]
    exact hm 10 (by decide)
  by_cases hmark : loc.rankBefore = 0
  · have hs := selectLocalDense_source shape memory reader hreader hwrites pr hpm
    generalize heS : (selectLocalDense reader).eval memory ⟨pr, .running⟩ = selected at hs
    rcases selected with ⟨⟨sr, sst⟩, sreads⟩
    dsimp only at hs
    obtain ⟨hsst, hsvalue, hsreads, hsro⟩ := hs
    subst sst
    simp only [hp32, hp520, hp521, hp512] at hsvalue hsreads hsro
    simp [selectLocalPresent, Block.sequence, Block.eval_seq, Evaluation.bind, heP,
      eval_ifZero, hp593, hmark, heS, eval_skip, selectLocalChoiceReference, hsvalue, hsreads, hsro]
  · have hs := selectSparseBlock_source shape memory reader hreader hwrites pr hpm hp513
    generalize heS : (selectSparseBlock reader).eval memory ⟨pr, .running⟩ = selected at hs
    rcases selected with ⟨⟨sr, sst⟩, sreads⟩
    dsimp only at hs
    obtain ⟨hsst, hsvalue, hsreads, hsro⟩ := hs
    subst sst
    simp only [hp26, hp520, hp521, hp512, hp515] at hsvalue hsreads hsro
    dsimp only [WordRAM.TraceResult.bind] at hsro
    simp [selectLocalPresent, Block.sequence, Block.eval_seq, Evaluation.bind, heP,
      eval_ifZero, hp593, hmark, heS, eval_skip, selectLocalChoiceReference, hsvalue, hsreads, hsro]

def selectLocalReference (store : WordRAM.ReadStore) (n wordSize superWord superOccurrence idx slot : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind (packedSelectEntryRead (selectEntryLayout 5) store slot)
    (fun loc? => match loc? with
      | none => WordRAM.TraceResult.pure none
      | some loc => selectLocalChoiceReference store n wordSize superWord superOccurrence idx slot loc)

theorem selectLocalBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hzero : regs 513 = 0) :
    let actual := (selectLocalBlock reader).eval memory ⟨regs, .running⟩
    let slot := regs 514 * regs 27 + (regs 512 - regs 561) / regs 26
    let expected := selectLocalReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 32) (regs 562) (regs 561) (regs 512) slot
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have ha := selectLocalAddress_source memory regs
  have haf (r : Nat) (ho : r ≠ 515 ∧ r ≠ 534 ∧ r ≠ 550) :=
    Block.eval_frame memory _ _ selectLocalAddress_writes r (by omega) ⟨regs, .running⟩
  have ham := writes_metadata shape memory _ _ selectLocalAddress_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  generalize heA : selectLocalAddress.eval memory ⟨regs, .running⟩ = addressed at ha haf ham
  rcases addressed with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha haf ham
  obtain ⟨hast, hareads, hindex⟩ := ha
  subst ast
  subst areads
  have he := selectEntryBlock_source shape memory reader hreader hwrites 5 515 590
    (by decide) (by decide) (by decide) (Or.inl (by decide)) ar ham
  have hef (r : Nat) (ho : ¬ SelectEntryWrites 590 r) :=
    selectEntryBlock_frame reader hwrites 5 515 590 memory ⟨ar, .running⟩ r ho
  have hem := selectEntryBlock_metadata shape reader hwrites 5 515 590 (by decide)
    memory ⟨ar, .running⟩ ham
  generalize heE : (selectEntryBlock reader 5 515 590).eval memory ⟨ar, .running⟩ = entered at he hef hem
  rcases entered with ⟨⟨er, est⟩, ereads⟩
  dsimp only at he hef hem
  obtain ⟨hentry, hereads, hero⟩ := he
  have hest : est = .running := hentry.1
  subst est
  rw [hindex] at hentry hereads hero
  have hp (r : Nat) (ho : r < 590 ∧ r ≠ 515 ∧ r ≠ 534 ∧ r ≠ 550) : er r = regs r := by
    rw [hef r (by unfold SelectEntryWrites; omega), haf r (by omega)]
  have hp513 : er 513 = 0 := (hp 513 (by omega)).trans hzero
  have hp515 : er 515 = regs 514 * regs 27 + (regs 512 - regs 561) / regs 26 := by
    rw [hef 515 (by simp [SelectEntryWrites]), hindex]
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let slot := regs 514 * regs 27 + (regs 512 - regs 561) / regs 26
  cases hloc : (packedSelectEntryRead (selectEntryLayout 5) store slot).value with
  | none =>
      have h590 : er 590 = 0 := by
        dsimp only [store, slot] at hloc
        simpa only [hloc] using hentry.2
      have heval : (selectLocalBlock reader).eval memory ⟨regs, .running⟩ =
          ⟨⟨er, .running⟩, ereads⟩ := by
        simp [selectLocalBlock, Block.sequence, Block.eval_seq, Evaluation.bind, heA, heE,
          eval_ifZero, h590, eval_skip]
      rw [heval]
      dsimp only [selectLocalReference, WordRAM.TraceResult.bind]
      rw [hloc]
      simp only [WordRAM.TraceResult.pure, optionNatPacket, Option.map_none, Option.getD_none,
        List.append_nil]
      exact ⟨True.intro, hp513, hereads, hero⟩
  | some loc =>
      have hfields : er 590 = 1 ∧ er 591 = loc.baseOccurrence ∧ er 592 = loc.baseWordIndex ∧
          er 593 = loc.rankBefore ∧ er 594 = loc.firstOffset := by
        dsimp only [store, slot] at hloc
        simpa only [hloc] using hentry.2
      have hs := selectLocalPresent_source shape memory reader hreader hwrites loc er hem hp513
        hfields.2.1 hfields.2.2.1 hfields.2.2.2.1 hfields.2.2.2.2
      generalize heS : (selectLocalPresent reader).eval memory ⟨er, .running⟩ = selected at hs
      rcases selected with ⟨⟨sr, sst⟩, sreads⟩
      dsimp only at hs
      obtain ⟨hsst, hsvalue, hsreads, hsro⟩ := hs
      subst sst
      have hp32 := hp 32 (by omega)
      have hp562 := hp 562 (by omega)
      have hp561 := hp 561 (by omega)
      have hp512 := hp 512 (by omega)
      simp only [hp32, hp562, hp561, hp512, hp515] at hsvalue hsreads hsro
      have heval : (selectLocalBlock reader).eval memory ⟨regs, .running⟩ =
          ⟨⟨sr, .running⟩, ereads ++ sreads⟩ := by
        simp [selectLocalBlock, Block.sequence, Block.eval_seq, Evaluation.bind, heA, heE,
          eval_ifZero, hfields.1, heS, eval_skip]
      rw [heval]
      dsimp only [selectLocalReference, WordRAM.TraceResult.bind]
      rw [hloc]
      refine ⟨rfl, hsvalue, ?_, selectReadOnly_append _ _ hero hsro⟩
      rw [hereads, hsreads, select_logicalTraceReads_append]

def selectSuperReference (store : WordRAM.ReadStore) (n idx slot : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry) : WordRAM.TraceResult (Option Nat) :=
  if super.rankBefore = 0 then
    selectLocalReference store n (packedSelectWordSize n) super.baseWordIndex super.baseOccurrence idx
      (slot * packedSelectLocalSlotsPerSuper n + (idx - super.baseOccurrence) / packedSelectLocalStride n)
  else WordRAM.TraceResult.bind
    (packedRankRead 9 10 11 21 (packedFringeChunkBits n) true store
      (packedSuperSlots n) (packedLongFlagWordSize n) 1 slot)
    (fun rank => GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 12
      (super.baseWordIndex * packedSelectWordSize n + super.firstOffset)
      (rank * packedSelectSuperStride n + (idx - super.baseOccurrence)))

def selectCloseReference (store : WordRAM.ReadStore) (n idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  if idx < n then
    WordRAM.TraceResult.bind (packedSelectEntryRead (selectEntryLayout 1) store (idx / packedSelectSuperStride n))
      (fun super? => match super? with
        | none => WordRAM.TraceResult.pure none
        | some super => selectSuperReference store n idx (idx / packedSelectSuperStride n) super)
  else WordRAM.TraceResult.pure none

theorem packedSelectCloseLeaf_normalForm (store : WordRAM.ReadStore) (n idx : Nat) :
    packedSelectCloseLeaf store n idx = selectCloseReference store n idx := by
  simp [packedSelectCloseLeaf, packedSelectCloseRead, selectCloseReference, selectSuperReference,
    selectLocalReference, selectLocalChoiceReference, packedSparseDirectoryRead,
    concreteBPNativeSelectCloseTraceSegmentLayout, concreteBPNativeFringeChunkTraceSegment,
    concreteBPNativeSelectChunkTraceSegment, concreteBPNativeDeadTraceSegment, selectEntryLayout,
    GenericSelect.relativeSplitSelectEntryIsMarked, GenericSelect.selectSuperSlot,
    GenericSelect.relativeSplitSelectLocalSlot, GenericSelect.relativeSplitSelectLocalSlotInSuper,
    GenericSelect.relativeSplitSelectEntryBasePosition, GenericSelect.relativeSplitSelectLongCompactSlot,
    GenericSelect.relativeSplitSelectLocalBasePosition, GenericSelect.relativeSplitSelectLocalBaseOccurrence,
    GenericSelect.relativeSplitSelectSparseCompactSlot]
  rfl

theorem selectSuperPresent_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry) (regs : Registers)
    (hm : MetadataMatches shape regs) (hzero : regs 513 = 0)
    (h561 : regs 561 = super.baseOccurrence) (h562 : regs 562 = super.baseWordIndex)
    (h563 : regs 563 = super.rankBefore) (h564 : regs 564 = super.firstOffset) :
    let actual := (selectSuperPresent reader).eval memory ⟨regs, .running⟩
    let expected := selectSuperReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 512) (regs 514) super
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have h25 : regs 25 = packedSelectSuperStride shape.size := hm 9 (by decide)
  have h26 : regs 26 = packedSelectLocalStride shape.size := hm 10 (by decide)
  have h27 : regs 27 = packedSelectLocalSlotsPerSuper shape.size := hm 11 (by decide)
  have h32 : regs 32 = packedSelectWordSize shape.size := hm 16 (by decide)
  by_cases hmark : super.rankBefore = 0
  · have hs := selectLocalBlock_source shape memory reader hreader hwrites regs hm hzero
    simpa [selectSuperPresent, eval_ifZero, h563, hmark, selectSuperReference,
      h26, h27, h32, h561, h562] using hs
  · have hs := selectLongBlock_source shape memory reader hreader hwrites regs hm hzero
    simpa [selectSuperPresent, eval_ifZero, h563, hmark, selectSuperReference,
      h25, h32, h561, h562, h564] using hs

theorem selectEligible_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hzero : regs 513 = 0) :
    let actual := (selectEligible reader).eval memory ⟨regs, .running⟩
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let slot := regs 512 / packedSelectSuperStride shape.size
    let expected := WordRAM.TraceResult.bind (packedSelectEntryRead (selectEntryLayout 1) store slot)
      (fun super? => match super? with
        | none => WordRAM.TraceResult.pure none
        | some super => selectSuperReference store shape.size (regs 512) slot super)
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let prepared := regs.write 514 (regs 512 / regs 25)
  have hpm : MetadataMatches shape prepared := MetadataMatches.write shape regs hm 514
    (regs 512 / regs 25) (Or.inr (by decide))
  have h25 : regs 25 = packedSelectSuperStride shape.size := hm 9 (by decide)
  have he := selectEntryBlock_source shape memory reader hreader hwrites 1 514 560
    (by decide) (by decide) (by decide) (Or.inl (by decide)) prepared hpm
  have hef (r : Nat) (ho : ¬ SelectEntryWrites 560 r) :=
    selectEntryBlock_frame reader hwrites 1 514 560 memory ⟨prepared, .running⟩ r ho
  have hem := selectEntryBlock_metadata shape reader hwrites 1 514 560 (by decide)
    memory ⟨prepared, .running⟩ hpm
  generalize heE : (selectEntryBlock reader 1 514 560).eval memory ⟨prepared, .running⟩ = entered at he hef hem
  rcases entered with ⟨⟨er, est⟩, ereads⟩
  dsimp only at he hef hem
  obtain ⟨hentry, hereads, hero⟩ := he
  have hest : est = .running := hentry.1
  subst est
  simp [prepared, h25] at hentry hereads hero
  have hp512 : er 512 = regs 512 := by
    rw [hef 512 (by simp [SelectEntryWrites])]
    simp [prepared, Registers.write]
  have hp513 : er 513 = 0 := by
    rw [hef 513 (by simp [SelectEntryWrites])]
    simp [prepared, Registers.write, hzero]
  have hp514 : er 514 = regs 512 / packedSelectSuperStride shape.size := by
    rw [hef 514 (by simp [SelectEntryWrites])]
    simp [prepared, h25]
  dsimp only [prepared] at heE
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let slot := regs 512 / packedSelectSuperStride shape.size
  cases hsuper : (packedSelectEntryRead (selectEntryLayout 1) store slot).value with
  | none =>
      have h560 : er 560 = 0 := by
        dsimp only [store, slot] at hsuper
        simpa only [hsuper] using hentry.2
      have heval : (selectEligible reader).eval memory ⟨regs, .running⟩ =
          ⟨⟨er, .running⟩, ereads⟩ := by
        simp [selectEligible, Block.sequence, Block.eval_seq, Evaluation.bind, eval_arithmetic,
          Arithmetic.eval, heE, eval_ifZero, h560, eval_skip]
      rw [heval]
      dsimp only [WordRAM.TraceResult.bind]
      rw [hsuper]
      simp only [WordRAM.TraceResult.pure, optionNatPacket, Option.map_none, Option.getD_none,
        List.append_nil]
      exact ⟨True.intro, hp513, hereads, hero⟩
  | some super =>
      have hfields : er 560 = 1 ∧ er 561 = super.baseOccurrence ∧ er 562 = super.baseWordIndex ∧
          er 563 = super.rankBefore ∧ er 564 = super.firstOffset := by
        dsimp only [store, slot] at hsuper
        simpa only [hsuper] using hentry.2
      have hs := selectSuperPresent_source shape memory reader hreader hwrites super er hem hp513
        hfields.2.1 hfields.2.2.1 hfields.2.2.2.1 hfields.2.2.2.2
      generalize heS : (selectSuperPresent reader).eval memory ⟨er, .running⟩ = selected at hs
      rcases selected with ⟨⟨sr, sst⟩, sreads⟩
      dsimp only at hs
      obtain ⟨hsst, hsvalue, hsreads, hsro⟩ := hs
      subst sst
      simp only [hp512, hp514] at hsvalue hsreads hsro
      have heval : (selectEligible reader).eval memory ⟨regs, .running⟩ =
          ⟨⟨sr, .running⟩, ereads ++ sreads⟩ := by
        simp [selectEligible, Block.sequence, Block.eval_seq, Evaluation.bind, eval_arithmetic,
          Arithmetic.eval, heE, eval_ifZero, hfields.1, heS, eval_skip]
      rw [heval]
      dsimp only [WordRAM.TraceResult.bind]
      rw [hsuper]
      refine ⟨rfl, hsvalue, ?_, selectReadOnly_append _ _ hero hsro⟩
      rw [hereads, hsreads, select_logicalTraceReads_append]

theorem selectCloseBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (selectCloseBlock reader).eval memory ⟨regs, .running⟩
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 512)
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hn : regs 16 = shape.size := hm 0 (by decide)
  let prepared := (regs.write 513 0).write 550 (if regs 512 < shape.size then 1 else 0)
  have hpm : MetadataMatches shape prepared := by
    apply MetadataMatches.write _ _ _ _ _ (Or.inr (by decide))
    exact MetadataMatches.write shape regs hm 513 0 (Or.inr (by decide))
  have hz : prepared 513 = 0 := by simp [prepared, Registers.write]
  by_cases hvalid : regs 512 < shape.size
  · have hs := selectEligible_source shape memory reader hreader hwrites prepared hpm hz
    generalize heS : (selectEligible reader).eval memory ⟨prepared, .running⟩ = selected at hs
    rcases selected with ⟨⟨sr, sst⟩, sreads⟩
    dsimp only at hs
    obtain ⟨hsst, hsvalue, hsreads, hsro⟩ := hs
    subst sst
    simp [prepared, Registers.write] at hsvalue hsreads hsro
    dsimp only [prepared] at heS
    simp only [hvalid, if_pos] at heS
    simp [selectCloseBlock, Block.sequence, Block.eval_seq, Evaluation.bind, eval_constant,
      eval_comparison, Comparison.eval, Registers.write, hn, hvalid, eval_ifZero, heS, eval_skip,
      packedSelectCloseLeaf_normalForm, selectCloseReference, hsvalue, hsreads, hsro]
  · simp [selectCloseBlock, Block.sequence, Block.eval_seq, Evaluation.bind, eval_constant,
      eval_comparison, Comparison.eval, Registers.write, hn, hvalid, eval_ifZero, eval_skip,
      packedSelectCloseLeaf_normalForm, selectCloseReference, WordRAM.TraceResult.pure,
      optionNatPacket, logicalTraceReads, ReadOnlyTrace]

@[simp] theorem denseFirstSelected_size (reader : Block) :
    (denseFirstSelected reader).size = 676 + 16 * reader.size := by
  simp [denseFirstSelected, denseFirstPrepare, denseWordFinish, Block.sequence, Block.size]
  omega

@[simp] theorem denseSecondSelected_size (reader : Block) :
    (denseSecondSelected reader).size = 685 + 17 * reader.size := by
  simp [denseSecondSelected, denseSecondAddress, denseSecondPrepare, denseWordFinish, Block.sequence, Block.size]
  omega

@[simp] theorem densePresent_size (reader : Block) :
    (densePresent reader).size = 2400 + 49 * reader.size := by
  simp [densePresent, denseRankBefore, denseRankWhole, denseRankBeforePrepare, denseRankWholePrepare,
    denseChoosePrepare, denseSelectBranch, Block.sequence, Block.size]
  omega

@[simp] theorem denseSelectBlock_size (reader : Block) :
    (denseSelectBlock reader).size = 2409 + 50 * reader.size := by
  simp [denseSelectBlock, denseReadAddress, denseReadSave, Block.sequence, Block.size]
  omega

@[simp] theorem selectLongBlock_size (reader : Block) :
    (selectLongBlock reader).size = 572 + 12 * reader.size := by
  simp [selectLongBlock, selectLongAddress, selectLongFinish, Block.sequence, Block.size]
  omega

@[simp] theorem selectSparseBlock_size (reader : Block) :
    (selectSparseBlock reader).size = 570 + 12 * reader.size := by
  simp [selectSparseBlock, selectSparseAddress, selectSparseFinish, Block.sequence, Block.size]
  omega

@[simp] theorem selectLocalDense_size (reader : Block) :
    (selectLocalDense reader).size = 2413 + 50 * reader.size := by
  simp [selectLocalDense, Block.sequence, Block.size]
  omega

@[simp] theorem selectLocalPresent_size (reader : Block) :
    (selectLocalPresent reader).size = 2989 + 62 * reader.size := by
  simp [selectLocalPresent, selectLocalPrepare, Block.sequence, Block.size]
  omega

@[simp] theorem selectLocalBlock_size (reader : Block) :
    (selectLocalBlock reader).size = 3042 + 66 * reader.size := by
  simp [selectLocalBlock, selectLocalAddress, Block.sequence, Block.size]
  omega

@[simp] theorem selectCloseBlock_size (reader : Block) :
    (selectCloseBlock reader).size = 3666 + 82 * reader.size := by
  simp [selectCloseBlock, selectEligible, selectSuperPresent, Block.sequence, Block.size]
  omega

theorem selectCloseBlock_run (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (s : State) (hpc : s.pc = 0) (hs : s.status = .running) (hm : MetadataMatches shape s.regs) :
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (s.regs 512)
    let actual := run memory ((selectCloseBlock reader).compileAt 0) (3666 + 82 * reader.size) s
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace ∧
      actual.steps ≤ 3666 + 82 * reader.size ∧ actual.final.pc = 3666 + 82 * reader.size ∧
      (∀ r, ¬ SelectWrites r → actual.final.regs r = s.regs r) := by
  have hc := (selectCloseBlock reader).compile_run memory s hpc
  rw [selectCloseBlock_size] at hc
  have hdata : Data.ofState s = ⟨s.regs, .running⟩ := by cases s; simp_all [Data.ofState]
  rw [hdata] at hc
  have he := selectCloseBlock_source shape memory reader hreader hwrites s.regs hm
  have hstatus : (run memory ((selectCloseBlock reader).compileAt 0) (3666 + 82 * reader.size) s).final.status = .running := by
    change (Data.ofState _).status = _
    rw [hc.1]
    exact he.1
  refine ⟨hstatus, ?_, hc.2.1.trans he.2.2.1, he.2.2.2, hc.2.2.1, hc.2.2.2 hstatus, ?_⟩
  · change (Data.ofState _).regs 513 = _
    rw [hc.1]
    exact he.2.1
  · intro r ho
    change (Data.ofState _).regs r = _
    rw [hc.1]
    exact selectCloseBlock_frame reader hwrites memory ⟨s.regs, .running⟩ r ho

theorem selectCloseBlock_hosted_run (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (program : Program) (codeBase : Nat) (s : State) (hpc : s.pc = codeBase)
    (hs : s.status = .running) (hm : MetadataMatches shape s.regs)
    (host : HostedAt program codeBase ((selectCloseBlock reader).compileAt codeBase)) :
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (s.regs 512)
    ∃ used ≤ 3666 + 82 * reader.size,
      let actual := run memory program used s
      actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace ∧
      actual.steps = used ∧ actual.final.pc = codeBase + (3666 + 82 * reader.size) ∧
      (∀ r, ¬ SelectWrites r → actual.final.regs r = s.regs r) := by
  obtain ⟨used, hu, hd, hr, ht, hp⟩ := (selectCloseBlock reader).compile_correct memory program codeBase s hpc host
  rw [selectCloseBlock_size] at hu hp
  have hdata : Data.ofState s = ⟨s.regs, .running⟩ := by cases s; simp_all [Data.ofState]
  rw [hdata] at hd hr
  have he := selectCloseBlock_source shape memory reader hreader hwrites s.regs hm
  have hstatus : (run memory program used s).final.status = .running := by
    change (Data.ofState _).status = _
    rw [hd]
    exact he.1
  refine ⟨used, hu, hstatus, ?_, hr.trans he.2.2.1, he.2.2.2, ht, hp hstatus, ?_⟩
  · change (Data.ofState _).regs 513 = _
    rw [hd]
    exact he.2.1
  · intro r ho
    change (Data.ofState _).regs r = _
    rw [hd]
    exact selectCloseBlock_frame reader hwrites memory ⟨s.regs, .running⟩ r ho

theorem selectCloseBlock_machine (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 512)
    let actual := run memory ((selectCloseBlock reader).compileAt 0 ++ [.halt 513])
      (3667 + 82 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some (optionNatPacket expected.value) ∧
      actual.final.status = .halted (optionNatPacket expected.value) ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧
      actual.steps ≤ 3667 + 82 * reader.size ∧
      (∀ r, ¬ SelectWrites r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace := by
  have hs := selectCloseBlock_source shape memory reader hreader hwrites regs hm
  have hc := rank_compile_with_halt (selectCloseBlock reader) 513 memory regs _ _ SelectWrites
    (selectCloseBlock_writes reader hwrites) hs.1 hs.2.1 hs.2.2.1
  have hsize : (selectCloseBlock reader).size + 1 = 3667 + 82 * reader.size := by
    rw [selectCloseBlock_size]; omega
  rw [hsize] at hc
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, hs.2.2.2⟩

theorem selectCloseBlock_canonical (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    let actual := (selectCloseBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 512)
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧ ReadOnlyTrace expected.trace :=
  selectCloseBlock_source shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm

def selectCloseProgram : Program := (selectCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 513]

def selectCloseRun (memory : Memory) (regs : Registers) : Run :=
  run memory selectCloseProgram 91243 ⟨regs, 0, .running⟩

theorem selectCloseRun_canonical (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    let actual := selectCloseRun (shapeMemory shape) regs
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 512)
    actual.result = some (optionNatPacket expected.value) ∧
      actual.final.status = .halted (optionNatPacket expected.value) ∧
      actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧ actual.steps ≤ 91243 ∧
      (∀ r, ¬ SelectWrites r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace := by
  have hs := selectCloseBlock_machine shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm
  simpa only [selectCloseRun, selectCloseProgram, logicalReadBlock_size, locateBlock_size] using hs

def setupSelectBlock : Block := .seq metadataSetupBlock (selectCloseBlock logicalReadBlock)

@[simp] theorem setupSelectBlock_size : setupSelectBlock.size = 91590 := by
  simp [setupSelectBlock, Block.size, metadataSetupBlock_size]

theorem buildMemory_setup_select (xs : List Int) (regs : Registers) :
    let shape := SuccinctClassic.cartesianShape xs
    let actual := setupSelectBlock.eval (buildMemory xs) ⟨regs, .running⟩
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) xs.length (regs 512)
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = (List.range 174).map (fun i => ⟨i, (metadata shape)[i]?⟩) ++
        logicalTraceReads shape (buildMemory xs) expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hp := buildMemory_setup xs ⟨regs, .running⟩ rfl
  generalize heP : metadataSetupBlock.eval (buildMemory xs) ⟨regs, .running⟩ = prepared at hp
  rcases prepared with ⟨⟨pr, pst⟩, preads⟩
  dsimp only at hp
  obtain ⟨hpst, hpmeta, _hp6, hpframe, hpreads⟩ := hp
  subst pst
  have hp512 : pr 512 = regs 512 := hpframe 512 (by decide) (Or.inr (by decide))
  have hs := selectCloseBlock_canonical (SuccinctClassic.cartesianShape xs) pr hpmeta
  rw [packedReviewerCartesianShape_size, hp512] at hs
  rw [setupSelectBlock, Block.eval_seq, heP]
  dsimp only [Evaluation.bind]
  exact ⟨hs.1, hs.2.1, by rw [hpreads]; exact congrArg (_ ++ ·) hs.2.2.1, hs.2.2.2⟩

def setupSelectProgram : Program := setupSelectBlock.compileAt 0 ++ [.halt 513]

def SetupSelectWrites (r : Nat) : Prop := r = 6 ∨ (16 ≤ r ∧ r < 190) ∨ SelectWrites r

theorem setupSelectBlock_writes : setupSelectBlock.WritesOnly SetupSelectWrites := by
  have hwSetup (start count : Nat) (hbound : start + count ≤ 174) :
      (metadataSetupFrom start count).WritesOnly SetupSelectWrites := by
    induction count generalizing start with
    | zero => trivial
    | succ count ih =>
      have ht := ih (start + 1) (by omega)
      simp only [metadataSetupFrom, metadataLoadPair, Block.WritesOnly, Action.destination]
      exact ⟨⟨Or.inl rfl, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩, ht⟩
  exact And.intro (hwSetup 0 174 (by decide))
    (Block.WritesOnly.mono _ (selectCloseBlock_writes logicalReadBlock logicalReadBlock_writesOnly)
      (by intro r h; exact Or.inr (Or.inr h)))

private theorem setupSelect_machine_from (block : Block) (memory : Memory) (regs : Registers)
    (value : Nat) (receipts : List Receipt) (trace : List WordRAM.TraceEvent)
    (hsize : block.size = 91590) (hw : block.WritesOnly SetupSelectWrites)
    (hs : (block.eval memory ⟨regs, .running⟩).final.status = .running)
    (hv : (block.eval memory ⟨regs, .running⟩).final.regs 513 = value)
    (ht : (block.eval memory ⟨regs, .running⟩).reads = receipts) (hro : ReadOnlyTrace trace) :
    let actual := run memory (block.compileAt 0 ++ [.halt 513]) 91591 ⟨regs, 0, .running⟩
    actual.result = some value ∧ actual.final.status = .halted value ∧
      actual.reads = receipts ∧ actual.steps ≤ 91591 ∧
      (∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → ¬ SelectWrites r → actual.final.regs r = regs r) ∧
      ReadOnlyTrace trace := by
  have hc := rank_compile_with_halt block 513 memory regs value receipts SetupSelectWrites hw hs hv ht
  rw [hsize] at hc
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, ?_, hro⟩
  intro r h6 hbank hout
  exact hc.2.2.2.2 r (by
    intro h
    rcases h with h | h | h
    · exact h6 h
    · omega
    · exact hout h)

theorem buildMemory_setup_select_machine (xs : List Int) (regs : Registers) :
    let shape := SuccinctClassic.cartesianShape xs
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) xs.length (regs 512)
    let actual := run (buildMemory xs) setupSelectProgram 91591 ⟨regs, 0, .running⟩
    actual.result = some (optionNatPacket expected.value) ∧
      actual.final.status = .halted (optionNatPacket expected.value) ∧
      actual.reads = (List.range 174).map (fun i => ⟨i, (metadata shape)[i]?⟩) ++
        logicalTraceReads shape (buildMemory xs) expected.trace ∧ actual.steps ≤ 91591 ∧
      (∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → ¬ SelectWrites r → actual.final.regs r = regs r) ∧
      ReadOnlyTrace expected.trace := by
  let shape := SuccinctClassic.cartesianShape xs
  let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) xs.length (regs 512)
  let receipts := (List.range 174).map (fun i => ⟨i, (metadata shape)[i]?⟩) ++
    logicalTraceReads shape (buildMemory xs) expected.trace
  have hs := buildMemory_setup_select xs regs
  simpa only [setupSelectProgram] using setupSelect_machine_from setupSelectBlock (buildMemory xs) regs
    (optionNatPacket expected.value) receipts expected.trace setupSelectBlock_size setupSelectBlock_writes
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

/-- Independently written consumer fixes the canonical program, packet, receipt
order, bank frame and primitive budget in one actual run. -/
theorem selectCloseRun_expectedType (shape : CartesianShape) (regs : Registers)
    (hm : ∀ i < 174, regs (16 + i) = ((metadata shape)[i]?).getD 0) :
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 512)
    let actual := run (shapeMemory shape)
      ((selectCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 513]) 91243 ⟨regs, 0, .running⟩
    actual.result = some ((expected.value.map (fun position => position + 1)).getD 0) ∧
      actual.final.status = .halted ((expected.value.map (fun position => position + 1)).getD 0) ∧
      actual.reads = expected.trace.flatMap (fun event => match event with
        | .readWord segment index _ => readerReceipts shape (shapeMemory shape) segment index
        | _ => []) ∧ actual.steps ≤ 91243 ∧
      (∀ r, ¬ ((256 ≤ r ∧ r < 311) ∨ (352 ≤ r ∧ r < 371) ∨ (400 ≤ r ∧ r < 412) ∨
        (513 ≤ r ∧ r < 551) ∨ (560 ≤ r ∧ r < 571) ∨ (590 ≤ r ∧ r < 601) ∨
        (640 ≤ r ∧ r < 660) ∨ (8192 ≤ r ∧ r < 8271)) → actual.final.regs r = regs r) ∧
      (∀ event ∈ expected.trace, event.isReadWord) := by
  simpa only [selectCloseRun, selectCloseProgram, optionNatPacket, logicalTraceReads,
    SelectWrites, ReadOnlyTrace] using selectCloseRun_canonical shape regs hm

theorem selectEntrySuper_expectedType (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (selectEntryBlock reader 1 514 560).eval memory ⟨regs, .running⟩
    let expected := packedSelectEntryRead ⟨1, 2, 3, 4, 29⟩
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) (regs 514)
    actual.final.status = .running ∧
      (match expected.value with
        | none => actual.final.regs 560 = 0
        | some entry => actual.final.regs 560 = 1 ∧
            actual.final.regs 561 = entry.baseOccurrence ∧ actual.final.regs 562 = entry.baseWordIndex ∧
            actual.final.regs 563 = entry.rankBefore ∧ actual.final.regs 564 = entry.firstOffset) ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have h := selectEntryBlock_source shape memory reader hreader hwrites 1 514 560
    (by decide) (by decide) (by decide) (Or.inl (by decide)) regs hm
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

theorem selectEntryLocal_expectedType (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (selectEntryBlock reader 5 515 590).eval memory ⟨regs, .running⟩
    let expected := packedSelectEntryRead ⟨5, 6, 7, 8, 29⟩
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) (regs 515)
    actual.final.status = .running ∧
      (match expected.value with
        | none => actual.final.regs 590 = 0
        | some entry => actual.final.regs 590 = 1 ∧
            actual.final.regs 591 = entry.baseOccurrence ∧ actual.final.regs 592 = entry.baseWordIndex ∧
            actual.final.regs 593 = entry.rankBefore ∧ actual.final.regs 594 = entry.firstOffset) ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have h := selectEntryBlock_source shape memory reader hreader hwrites 5 515 590
    (by decide) (by decide) (by decide) (Or.inl (by decide)) regs hm
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

theorem selectCloseRun_invalid (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (hindex : shape.size ≤ regs 512) :
    (selectCloseRun (shapeMemory shape) regs).result = some 0 ∧
      (selectCloseRun (shapeMemory shape) regs).reads = [] := by
  have hs := selectCloseRun_canonical shape regs hm
  simp only [packedSelectCloseLeaf_normalForm, selectCloseReference,
    if_neg (Nat.not_lt.mpr hindex), WordRAM.TraceResult.pure, optionNatPacket,
    Option.map_none, Option.getD_none, logicalTraceReads, List.flatMap_nil] at hs
  exact ⟨hs.1, hs.2.2.1⟩

example (memory : Memory) (regs : Registers) :
    (selectLongAddress.eval memory ⟨regs.write 360 1, .running⟩).final.regs 8193 =
      regs 25 + (regs 512 - regs 561) := by
  have hs := selectLongAddress_source memory (regs.write 360 1)
  simpa [Registers.write] using hs.2.2.2

example (memory : Memory) (regs : Registers) :
    (selectSparseAddress.eval memory ⟨regs.write 360 2, .running⟩).final.regs 8193 =
      2 * regs 26 + (regs 512 - regs 521) := by
  have hs := selectSparseAddress_source memory (regs.write 360 2)
  simpa [Registers.write] using hs.2.2.2

end RMQ.SuccinctFinal.PackedWordRAM
