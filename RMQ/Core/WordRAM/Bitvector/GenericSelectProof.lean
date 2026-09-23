import RMQ.Core.WordRAM.Bitvector.GenericRankProof
import RMQ.Core.WordRAM.Packed.SelectProof

/-! # Generic proof refinement of the existing packed select controller -/

namespace RMQ.PackedBitvector.Controller

open SuccinctFinal SuccinctFinal.PackedWordRAM Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

def selectReference (store : WordRAM.ReadStore) (snapshot : Registers) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout 21 22 store
    (snapshot 34) false (snapshot 16) (snapshot 25) (snapshot 32) (snapshot 27) (snapshot 26)
    (snapshot 28) (snapshot 30) 1 (snapshot 29) (snapshot 31) 1 (snapshot 26) idx

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

theorem selectFieldRead_metadata (model : ControllerModel) (reader : Block)
    (hr : ReaderWrites reader) (segment indexReg destination : Nat) (hd : 190 ≤ destination)
    (memory : Memory) (s : Data) (hm : MetadataMatches model s.regs) :
    MetadataMatches model ((selectFieldRead reader segment indexReg destination).eval memory s).final.regs :=
  writes_metadata model memory _ _ (selectFieldRead_writes reader hr segment indexReg destination)
    (by intro r hlo hhi; unfold SelectFieldWrites; omega) s hm

theorem selectFieldRead_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (segment indexReg destination : Nat)
    (hi : indexReg < 8192) (regs : Registers) (hm : MetadataMatches model regs) :
    let actual := (selectFieldRead reader segment indexReg destination).eval memory ⟨regs, .running⟩
    let expected := (model.store).readWord? segment (regs indexReg)
    actual.final.status = .running ∧ actual.final.regs destination = logicalPacket expected ∧
      actual.reads = model.receipts segment (regs indexReg) := by
  let prepared := (regs.write 8192 segment).write 8193 (regs indexReg)
  have hmeta : MetadataMatches model prepared :=
    MetadataMatches.write model _
      (MetadataMatches.write model regs hm 8192 segment (Or.inr (by decide)))
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

def selectFieldsReceipts (model : ControllerModel) (memory : Memory)
    (segment index : Nat) : Nat → List Receipt
  | 0 => []
  | count + 1 => model.receipts segment index ++
      selectFieldsReceipts model memory (segment + 1) index count

theorem selectFieldsFrom_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (segment indexReg destination count : Nat) (hd : 190 ≤ destination)
    (hupper : destination + count ≤ 8192) (hi : indexReg < 8192)
    (hout : indexReg < destination ∨ destination + count ≤ indexReg)
    (regs : Registers) (hm : MetadataMatches model regs) :
    let actual := (selectFieldsFrom reader segment indexReg destination count).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧
      (∀ j < count, actual.final.regs (destination + j) = logicalPacket
        ((model.store).readWord? (segment + j) (regs indexReg))) ∧
      actual.reads = selectFieldsReceipts model memory segment (regs indexReg) count ∧
      MetadataMatches model actual.final.regs := by
  induction count generalizing segment destination regs with
  | zero => exact ⟨rfl, by intro j hj; omega, rfl, hm⟩
  | succ count ih =>
      have hfirst := selectFieldRead_source model memory reader hreader segment indexReg destination hi regs hm
      have hmeta := selectFieldRead_metadata model reader hwrites segment indexReg destination hd
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

theorem selectEntryBlock_metadata (model : ControllerModel) (reader : Block)
    (hr : ReaderWrites reader) (segment indexReg base : Nat) (hb : 190 ≤ base)
    (memory : Memory) (s : Data) (hm : MetadataMatches model s.regs) :
    MetadataMatches model ((selectEntryBlock reader segment indexReg base).eval memory s).final.regs :=
  writes_metadata model memory _ _ (selectEntryBlock_writes reader hr segment indexReg base)
    (by intro r hlo hhi; unfold SelectEntryWrites; omega) s hm

theorem selectEntryBlock_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (segment indexReg base : Nat) (hb : 190 ≤ base) (hupper : base + 11 ≤ 8192)
    (hi : indexReg < 8192) (hout : indexReg < base ∨ base + 11 ≤ indexReg)
    (regs : Registers) (hm : MetadataMatches model regs) :
    let actual := (selectEntryBlock reader segment indexReg base).eval memory ⟨regs, .running⟩
    let expected := packedSelectEntryRead (selectEntryLayout segment)
      (model.store) (regs indexReg)
    SelectEntryResult base expected.value actual.final ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let prepared := (regs.write base 0).write (base + 9) 1
  have hmeta : MetadataMatches model prepared :=
    MetadataMatches.write model _ (MetadataMatches.write model regs hm base 0 (Or.inr hb))
      (base + 9) 1 (Or.inr (by omega))
  have hi0 : indexReg ≠ base := by omega
  have hi9 : indexReg ≠ base + 9 := by omega
  have hpindex : prepared indexReg = regs indexReg := by simp [prepared, Registers.write, hi0, hi9]
  have hf := selectFieldsFrom_source model memory reader hreader hwrites segment indexReg (base + 5) 4
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
        (model.store) (regs indexReg)).value
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
  simp [selectFieldsReceipts, selectEntryLayout, logicalTraceReads, traceReads]

@[simp] theorem select_logicalTraceReads_append (model : ControllerModel) (memory : Memory)
    (first second : List WordRAM.TraceEvent) :
    logicalTraceReads model memory (first ++ second) =
      logicalTraceReads model memory first ++ logicalTraceReads model memory second := by
  simp [logicalTraceReads, traceReads]

theorem selectWordBody_metadata (model : ControllerModel) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data) (hm : MetadataMatches model s.regs) :
    MetadataMatches model ((selectWordBody reader).eval memory s).final.regs :=
  writes_metadata model memory _ _ (selectWordBody_writes reader hr)
    (by intro r hlo hhi; unfold SelectWordBodyWrites; omega) s hm

theorem selectWordSelected_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (regs : Registers)
    (hm : MetadataMatches model regs) (hone : regs 407 = 1) :
    let actual := (selectWordSelected reader).eval memory ⟨regs, .running⟩
    let slot := regs 285 * (regs 34 + 1) + regs 406
    let reply := ((model.store).readWord? 22 slot).map bitsToNatLE
    actual.final.status = .running ∧
      actual.final.regs 403 = regs 404 * regs 34 + reply.getD 0 + 1 ∧
      actual.reads = model.receipts 22 slot := by
  have hw : selectWordSelectAddress.WritesOnly (fun r => r = 410 ∨ r = 8192 ∨ r = 8193) := by
    simp [selectWordSelectAddress, Block.sequence, Block.WritesOnly, Action.destination]
  have ha := selectWordSelectAddress_source memory regs
  have hmeta := writes_metadata model memory _ _ hw (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
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

theorem selectWordActive_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches model regs) (hone : regs 407 = 1) :
    let store := model.store
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
      actual.reads = model.receipts 21 rankSlot ++
        (if regs 406 < rank then model.receipts 22 selectSlot else []) := by
  have ha := selectWordAddress_source memory regs
  have ham := writes_metadata model memory _ _ selectWordAddress_writes
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
  have hbm := readerFrame_metadata model ar br hbf ham
  have hc := selectWordDecode_source memory br
  have hcm := writes_metadata model memory _ _ selectWordDecode_writes
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
    ((((model.store).readWord?
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
    have htm : MetadataMatches model tested := MetadataMatches.write model cr hcm 408 1 (Or.inr (by decide))
    have hs := selectWordSelected_source model memory reader hreader tested htm
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

theorem selectWordBody_active_reference (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (c total j k : Nat) (regs : Registers) (hm : MetadataMatches model regs)
    (hs : SelectFoldState word c total j k regs) (hactive : j < total) :
    let store := model.store
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
      actual.reads = model.receipts 21 rankSlot ++
        (if k < rank then model.receipts 22 selectSlot else []) := by
  let compared := regs.write 408 1
  have hc := selectWordActive_source model memory reader hreader hwrites compared
    (MetadataMatches.write model regs hm 408 1 (Or.inr (by decide)))
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

theorem selectWordRepeat_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (c total cycles j k : Nat) (regs : Registers) (hm : MetadataMatches model regs)
    (hs : SelectFoldState word c total j k regs) (hcover : total ≤ j + cycles) :
    let actual := (Block.repeat cycles (selectWordBody reader)).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordSelectTraceFromWithStore
      (model.store) 21 22 c false word j (total - j) k
    actual.final.status = .running ∧ actual.final.regs 403 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace := by
  induction cycles generalizing j k regs with
  | zero =>
      have hz : total - j = 0 := by omega
      simp [Block.eval_repeat, iterate, bpChunkedWordSelectTraceFromWithStore, hz,
        WordRAM.TraceResult.pure, logicalTraceReads, traceReads, optionNatPacket, hs.out_eq]
  | succ cycles ih =>
      by_cases hactive : j < total
      · have hb := selectWordBody_active_reference model memory reader hreader hwrites
          word c total j k regs hm hs hactive
        have hmeta := selectWordBody_metadata model reader hwrites memory ⟨regs, .running⟩ hm
        have hframe (r : Nat) (ho : ¬ SelectWordBodyWrites r) :=
          selectWordBody_frame reader hwrites memory ⟨regs, .running⟩ r ho
        generalize he : (selectWordBody reader).eval memory ⟨regs, .running⟩ = first
          at hb hmeta hframe
        rcases first with ⟨⟨fr, fst⟩, freceipts⟩
        dsimp only at hb hmeta hframe
        obtain ⟨hfst, hvalue, hindex, hremaining, hreads⟩ := hb
        subst fst
        let store := model.store
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
            simp [logicalTraceReads, traceReads]
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
          simp [logicalTraceReads, traceReads, rank, slot, store]
      · have hstop : regs 405 ≤ regs 404 := by rw [hs.total_eq, hs.index_eq]; omega
        have hnext : SelectFoldState word c total j k (regs.write 408 0) := by
          constructor <;> simp only [Registers.write] <;> first
            | exact hs.word_eq | exact hs.length_eq | exact hs.chunk_eq | exact hs.out_eq
            | exact hs.index_eq | exact hs.total_eq | exact hs.remaining_eq | exact hs.one_eq
        have ht := ih j k (regs.write 408 0)
          (MetadataMatches.write model regs hm 408 0 (Or.inr (by decide))) hnext (by omega)
        rw [Block.eval_repeat_succ, selectWordBody_inactive reader memory regs hs.out_eq hstop]
        simpa only [Evaluation.bind, List.nil_append] using ht

theorem selectWordBlock_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (occurrence : Nat) (regs : Registers) (hm : MetadataMatches model regs)
    (hword : regs 400 = bitsToNatLE word) (hlength : regs 401 = word.length)
    (hoccurrence : regs 402 = occurrence) :
    let actual := (selectWordBlock reader).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordSelectTraceResultAtSegmentsWithStore
      (model.store) 21 22
      (model.metadata 34) false word occurrence
    actual.final.status = .running ∧ actual.final.regs 403 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hw : selectWordInit.WritesOnly (fun r => 403 ≤ r ∧ r < 410) := by
    simp [selectWordInit, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, minBlock]
  have hp := selectWordInit_source memory regs
  have hmeta := writes_metadata model memory _ _ hw (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  have hf (r : Nat) (ho : r < 403 ∨ 410 ≤ r) :=
    Block.eval_frame memory _ _ hw r (by omega) ⟨regs, .running⟩
  generalize he : selectWordInit.eval memory ⟨regs, .running⟩ = initialized at hp hmeta hf
  rcases initialized with ⟨⟨pr, pst⟩, preads⟩
  dsimp only at hp hmeta hf
  obtain ⟨hpst, hpreads, hzero, hindex, htotal, hremaining, hone⟩ := hp
  subst pst
  subst preads
  have hc : regs 34 = model.metadata 34 := hm 34 (by decide)
  let c := model.metadata 34
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
  have hl := selectWordRepeat_source model memory reader hreader hwrites word c
    (bpWordChunkCount c word.length) 8 0 occurrence pr hmeta hstate (bpWordChunkCount_le_eight c word.length)
  rw [selectWordBlock, Block.eval_seq, he]
  dsimp only [Evaluation.bind]
  refine ⟨hl.1, hl.2.1, hl.2.2, ?_⟩
  exact selectFold_readOnly _ _ _ _ _ _ _ _ _

theorem denseWordPrepared_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (occurrence : Nat) (regs : Registers) (hm : MetadataMatches model regs)
    (hword : regs 400 = bitsToNatLE word) (hlength : regs 401 = word.length)
    (hoccurrence : regs 402 = occurrence) (hzero : regs 643 = 0) :
    let actual := (Block.seq (selectWordBlock reader) denseWordFinish).eval memory ⟨regs, .running⟩
    let selected := bpChunkedWordSelectTraceResultAtSegmentsWithStore
      (model.store) 21 22
      (model.metadata 34) false word occurrence
    actual.final.status = .running ∧
      actual.final.regs 643 = optionNatPacket (selected.value.map (fun x => regs 644 * regs 32 + x)) ∧
      actual.reads = logicalTraceReads model memory selected.trace ∧ ReadOnlyTrace selected.trace := by
  have hs := selectWordBlock_source model memory reader hreader hwrites word occurrence regs hm
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

theorem denseFirstSelected_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (regs : Registers) (hm : MetadataMatches model regs)
    (hpacket : regs 645 = bitsToNatLE word + 1) (hlength : regs 646 = word.length)
    (hone : regs 659 = 1) (hzero : regs 643 = 0) :
    let actual := (denseFirstSelected reader).eval memory ⟨regs, .running⟩
    let selected := bpChunkedWordSelectTraceResultAtSegmentsWithStore
      (model.store) 21 22
      (model.metadata 34) false word (regs 648 + regs 650)
    actual.final.status = .running ∧
      actual.final.regs 643 = optionNatPacket (selected.value.map (fun x => regs 644 * regs 32 + x)) ∧
      actual.reads = logicalTraceReads model memory selected.trace ∧ ReadOnlyTrace selected.trace := by
  have hp := denseFirstPrepare_source memory regs
  have hf (r : Nat) (ho : ¬ ((400 ≤ r ∧ r < 403) ∨ r = 658)) :=
    Block.eval_frame memory _ _ denseFirstPrepare_writes r ho ⟨regs, .running⟩
  have hmeta := writes_metadata model memory _ _ denseFirstPrepare_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  generalize he : denseFirstPrepare.eval memory ⟨regs, .running⟩ = prepared at hp hf hmeta
  rcases prepared with ⟨⟨pr, status⟩, reads⟩
  dsimp only at hp hf hmeta
  obtain ⟨hstatus, hreads, hword, hlen, hocc⟩ := hp
  subst status
  subst reads
  have hz : pr 643 = 0 := (hf 643 (by omega)).trans hzero
  have hs := denseWordPrepared_source model memory reader hreader hwrites word _ pr hmeta
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

theorem denseSecondPrepared_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (regs : Registers) (hm : MetadataMatches model regs)
    (hpacket : regs 8194 = bitsToNatLE word + 1) (hlength : regs 8195 = word.length)
    (hone : regs 659 = 1) (hzero : regs 643 = 0) :
    let actual := (Block.sequence [denseSecondPrepare, selectWordBlock reader, denseWordFinish]).eval
      memory ⟨regs, .running⟩
    let selected := bpChunkedWordSelectTraceResultAtSegmentsWithStore
      (model.store) 21 22
      (model.metadata 34) false word (regs 650 - regs 651)
    actual.final.status = .running ∧
      actual.final.regs 643 = optionNatPacket (selected.value.map (fun x => regs 644 * regs 32 + x)) ∧
      actual.reads = logicalTraceReads model memory selected.trace ∧ ReadOnlyTrace selected.trace := by
  have hp := denseSecondPrepare_source memory regs
  have hf (r : Nat) (ho : ¬ ((400 ≤ r ∧ r < 403) ∨ r = 658)) :=
    Block.eval_frame memory _ _ denseSecondPrepare_writes r ho ⟨regs, .running⟩
  have hmeta := writes_metadata model memory _ _ denseSecondPrepare_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  generalize he : denseSecondPrepare.eval memory ⟨regs, .running⟩ = prepared at hp hf hmeta
  rcases prepared with ⟨⟨pr, status⟩, reads⟩
  dsimp only at hp hf hmeta
  obtain ⟨hstatus, hreads, hword, hlen, hocc⟩ := hp
  subst status
  subst reads
  have hz : pr 643 = 0 := (hf 643 (by omega)).trans hzero
  have hs := denseWordPrepared_source model memory reader hreader hwrites word _ pr hmeta
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

theorem denseSecondSelected_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches model regs)
    (hone : regs 659 = 1) (hzero : regs 643 = 0) :
    let actual := (denseSecondSelected reader).eval memory ⟨regs, .running⟩
    let expected := denseSecondReference (model.store)
      (model.metadata 34) (regs 32) (regs 644) (regs 650 - regs 651)
    actual.final.status = .running ∧ actual.final.regs 643 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have ha := denseSecondAddress_source memory regs
  have haf (r : Nat) (ho : r ≠ 644 ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    Block.eval_frame memory _ _ denseSecondAddress_writes r (by omega) ⟨regs, .running⟩
  have ham := writes_metadata model memory _ _ denseSecondAddress_writes
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
  have hbm := readerFrame_metadata model ar br hbf ham
  cases hword : (model.store).readWord? 0 (regs 644 + 1) with
  | none =>
      simp only [hword, logicalPacket, logicalLength, Option.map_none, Option.getD_none] at hpacket hlength
      simp [denseSecondSelected, Block.sequence, Block.eval_seq, Evaluation.bind, heA, heB,
        eval_ifZero, eval_skip, hpacket, hp643, hreads, denseSecondReference, bpWordReadTraceResult,
        hword, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure, optionNatPacket,
        logicalTraceReads, traceReads, ReadOnlyTrace, WordRAM.TraceEvent.isReadWord]
  | some word =>
      simp only [hword, logicalPacket, logicalLength, Option.map_some, Option.getD_some] at hpacket hlength
      have hs := denseSecondPrepared_source model memory reader hreader hwrites word br hbm
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
        simp [logicalTraceReads, traceReads]
      · simpa [ReadOnlyTrace, WordRAM.TraceEvent.isReadWord] using hsreadonly

private theorem relativeReaderTail_source (model : ControllerModel) (memory : Memory) (reader finish : Block)
    (hreader : ReaderSimulation model memory reader) (base : Registers → Nat)
    (hbase : ∀ before after, ReaderFrame before after → base after = base before)
    (hfinish : ∀ regs word, regs 513 = 0 → regs 8194 = logicalPacket word →
      let actual := finish.eval memory ⟨regs, .running⟩
      actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 513 =
        optionNatPacket (word.map (fun bits => base regs + bitsToNatLE bits)))
    (regs : Registers) (hm : MetadataMatches model regs) (hzero : regs 513 = 0) :
    let actual := (Block.seq reader finish).eval memory ⟨regs, .running⟩
    let word := (model.store).readWord? (regs 8192) (regs 8193)
    actual.final.status = .running ∧ actual.final.regs 513 =
      optionNatPacket (word.map (fun bits => base regs + bitsToNatLE bits)) ∧
      actual.reads = model.receipts (regs 8192) (regs 8193) := by
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

theorem selectLongReaderTail_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (regs : Registers)
    (hm : MetadataMatches model regs) (hzero : regs 513 = 0) :
    let actual := (Block.seq reader selectLongFinish).eval memory ⟨regs, .running⟩
    let word := (model.store).readWord? (regs 8192) (regs 8193)
    actual.final.status = .running ∧ actual.final.regs 513 =
      optionNatPacket (word.map (fun bits => regs 562 * regs 32 + regs 564 + bitsToNatLE bits)) ∧
      actual.reads = model.receipts (regs 8192) (regs 8193) := by
  exact relativeReaderTail_source model memory reader selectLongFinish hreader
    (fun regs => regs 562 * regs 32 + regs 564)
    (by intro before after hf; dsimp only; rw [hf 562 (Or.inl (by decide)), hf 32 (Or.inl (by decide)),
        hf 564 (Or.inl (by decide))])
    (selectLongFinish_source memory) regs hm hzero

theorem selectSparseReaderTail_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (regs : Registers)
    (hm : MetadataMatches model regs) (hzero : regs 513 = 0) :
    let actual := (Block.seq reader selectSparseFinish).eval memory ⟨regs, .running⟩
    let word := (model.store).readWord? (regs 8192) (regs 8193)
    actual.final.status = .running ∧ actual.final.regs 513 =
      optionNatPacket (word.map (fun bits => regs 520 + bitsToNatLE bits)) ∧
      actual.reads = model.receipts (regs 8192) (regs 8193) := by
  exact relativeReaderTail_source model memory reader selectSparseFinish hreader
    (fun regs => regs 520) (by intro before after hf; exact hf 520 (Or.inl (by decide)))
    (selectSparseFinish_source memory) regs hm hzero

theorem selectLongTail_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (regs : Registers)
    (hm : MetadataMatches model regs) (hzero : regs 513 = 0) :
    let actual := (Block.sequence [selectLongAddress, reader, selectLongFinish]).eval
      memory ⟨regs, .running⟩
    let expected := GenericSelect.bpRelativeOffsetReadTraceResultWithStore
      (model.store) 12 (regs 562 * regs 32 + regs 564)
      (regs 360 * regs 25 + (regs 512 - regs 561))
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have ha := selectLongAddress_source memory regs
  have hf (r : Nat) (ho : r ≠ 534 ∧ r ≠ 535 ∧ r ≠ 550 ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    Block.eval_frame memory _ _ selectLongAddress_writes r (by omega) ⟨regs, .running⟩
  have hmeta := writes_metadata model memory _ _ selectLongAddress_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  generalize heA : selectLongAddress.eval memory ⟨regs, .running⟩ = addressed at ha hf hmeta
  rcases addressed with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha hf hmeta
  obtain ⟨hast, hareads, hsegment, hindex⟩ := ha
  subst ast
  subst areads
  have hzero' : ar 513 = 0 := (hf 513 (by omega)).trans hzero
  have ht := selectLongReaderTail_source model memory reader hreader ar hmeta hzero'
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
  · simpa [logicalTraceReads, traceReads] using ht.2.2
  · simp [ReadOnlyTrace, WordRAM.TraceEvent.isReadWord]

theorem selectSparseTail_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (regs : Registers)
    (hm : MetadataMatches model regs) (hzero : regs 513 = 0) :
    let actual := (Block.sequence [selectSparseAddress, reader, selectSparseFinish]).eval
      memory ⟨regs, .running⟩
    let expected := GenericSelect.bpRelativeOffsetReadTraceResultWithStore
      (model.store) 16 (regs 520)
      (regs 360 * regs 26 + (regs 512 - regs 521))
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have ha := selectSparseAddress_source memory regs
  have hf (r : Nat) (ho : r ≠ 534 ∧ r ≠ 535 ∧ r ≠ 550 ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    Block.eval_frame memory _ _ selectSparseAddress_writes r (by omega) ⟨regs, .running⟩
  have hmeta := writes_metadata model memory _ _ selectSparseAddress_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  generalize heA : selectSparseAddress.eval memory ⟨regs, .running⟩ = addressed at ha hf hmeta
  rcases addressed with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha hf hmeta
  obtain ⟨hast, hareads, hsegment, hindex⟩ := ha
  subst ast
  subst areads
  have hzero' : ar 513 = 0 := (hf 513 (by omega)).trans hzero
  have ht := selectSparseReaderTail_source model memory reader hreader ar hmeta hzero'
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
  · simpa [logicalTraceReads, traceReads] using ht.2.2
  · simp [ReadOnlyTrace, WordRAM.TraceEvent.isReadWord]

private theorem denseRankPrepared_source (model : ControllerModel) (memory : Memory) (reader prepare : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (limit : Nat) (regs : Registers)
    (hp : let actual := prepare.eval memory ⟨regs, .running⟩
      actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 256 = bitsToNatLE word ∧ actual.final.regs 257 = word.length ∧
      actual.final.regs 258 = limit ∧ actual.final.regs 259 = 0)
    (hm : MetadataMatches model (prepare.eval memory ⟨regs, .running⟩).final.regs) :
    let actual := (Block.seq prepare (rankWordBlock reader)).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
      (model.store) 21 (model.metadata 34)
      false word limit
    actual.final.status = .running ∧ actual.final.regs 260 = expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  generalize he : prepare.eval memory ⟨regs, .running⟩ = prepared at hp hm
  rcases prepared with ⟨⟨pr, status⟩, reads⟩
  dsimp only at hp hm
  obtain ⟨hstatus, hreads, hword, hlength, hlimit, htarget⟩ := hp
  subst status
  subst reads
  have hs := rankWordBlock_source model memory reader hreader hwrites word false limit pr hm
    hword hlength hlimit htarget
  rw [Block.eval_seq, he]
  simpa only [Evaluation.bind, List.nil_append] using hs

theorem denseRankBefore_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (regs : Registers) (hm : MetadataMatches model regs)
    (hpacket : regs 645 = bitsToNatLE word + 1) (hlength : regs 646 = word.length)
    (hone : regs 659 = 1) :
    let actual := (denseRankBefore reader).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
      (model.store) 21 (model.metadata 34)
      false word (regs 640 - regs 644 * regs 32)
    actual.final.status = .running ∧ actual.final.regs 260 = expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hp := denseRankBeforePrepare_source memory regs
  have hmeta := writes_metadata model memory _ _ denseRankBeforePrepare_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  exact denseRankPrepared_source model memory reader denseRankBeforePrepare hreader hwrites
    word _ regs (by simpa only [hpacket, hlength, hone, Nat.add_sub_cancel] using hp) hmeta

theorem denseRankWhole_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (regs : Registers) (hm : MetadataMatches model regs)
    (hpacket : regs 645 = bitsToNatLE word + 1) (hlength : regs 646 = word.length)
    (hone : regs 659 = 1) :
    let actual := (denseRankWhole reader).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
      (model.store) 21 (model.metadata 34)
      false word word.length
    actual.final.status = .running ∧ actual.final.regs 260 = expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hp := denseRankWholePrepare_source memory regs
  have hmeta := writes_metadata model memory _ _ denseRankWholePrepare_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  exact denseRankPrepared_source model memory reader denseRankWholePrepare hreader hwrites
    word _ regs ⟨hp.1, hp.2.1, by simpa only [hpacket, hone, Nat.add_sub_cancel] using hp.2.2.2.1,
      hp.2.2.2.2.1.trans hlength, hp.2.2.2.2.2.1.trans hlength, hp.2.2.2.2.2.2⟩ hmeta

theorem denseSelectBranch_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (before upto remaining : Nat) (regs : Registers)
    (hm : MetadataMatches model regs) (hpacket : regs 645 = bitsToNatLE word + 1)
    (hlength : regs 646 = word.length) (hone : regs 659 = 1) (hzero : regs 643 = 0)
    (hbefore : regs 648 = before) (hremaining : regs 650 = remaining)
    (havailable : regs 651 = upto - before)
    (htest : regs 652 = if remaining < upto - before then 1 else 0) :
    let actual := (denseSelectBranch reader).eval memory ⟨regs, .running⟩
    let expected := denseChoiceReference (model.store)
      (model.metadata 34) (regs 32) (regs 644) remaining before upto word
    actual.final.status = .running ∧ actual.final.regs 643 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  by_cases hchoose : remaining < upto - before
  · have hs := denseFirstSelected_source model memory reader hreader hwrites word regs hm
      hpacket hlength hone hzero
    simpa [denseSelectBranch, eval_ifZero, htest, hchoose, denseChoiceReference,
      WordRAM.TraceResult.map, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
      hbefore, hremaining] using hs
  · have hs := denseSecondSelected_source model memory reader hreader hwrites regs hm hone hzero
    simpa [denseSelectBranch, eval_ifZero, htest, hchoose, denseChoiceReference,
      hremaining, havailable] using hs

theorem densePresent_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (regs : Registers) (hm : MetadataMatches model regs)
    (hpacket : regs 645 = bitsToNatLE word + 1) (hlength : regs 646 = word.length)
    (hone : regs 659 = 1) (hzero : regs 643 = 0) (hindex : regs 644 = regs 640 / regs 32) :
    let actual := (densePresent reader).eval memory ⟨regs, .running⟩
    let expected := densePresentReference (model.store)
      (model.metadata 34) (regs 32) (regs 640) (regs 641) (regs 642) word
    actual.final.status = .running ∧ actual.final.regs 643 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hb := denseRankBefore_source model memory reader hreader hwrites word regs hm hpacket hlength hone
  have hbf (r : Nat) (ho : ¬ DenseRankBeforeWrites r) :=
    Block.eval_frame memory _ _ (denseRankBefore_writes reader hwrites) r ho ⟨regs, .running⟩
  have hbm := writes_metadata model memory _ _ (denseRankBefore_writes reader hwrites)
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
  have hc := denseRankWhole_source model memory reader hreader hwrites word br hbm hp645 hp646 hp659
  have hc648 := denseRankWhole_saved memory reader hwrites br
  have hcf (r : Nat) (ho : ¬ DenseRankWholeWrites r) :=
    Block.eval_frame memory _ _ (denseRankWhole_writes reader hwrites) r ho ⟨br, .running⟩
  have hcm := writes_metadata model memory _ _ (denseRankWhole_writes reader hwrites)
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
  have hdm := writes_metadata model memory _ _ denseChoosePrepare_writes
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
  have hs := denseSelectBranch_source model memory reader hreader hwrites word (br 260) (cr 260)
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

theorem denseSelectBlock_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches model regs) :
    let actual := (denseSelectBlock reader).eval memory ⟨regs, .running⟩
    let expected := packedDenseTwoWordSelectRead 0 21 22 (model.metadata 34) false
      (model.store) (regs 32) (regs 640) (regs 641) (regs 642)
    actual.final.status = .running ∧ actual.final.regs 643 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have ha := denseReadAddress_source memory regs
  have haf (r : Nat) (ho : r ≠ 643 ∧ r ≠ 644 ∧ r ≠ 659 ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    Block.eval_frame memory _ _ denseReadAddress_writes r (by omega) ⟨regs, .running⟩
  have ham := writes_metadata model memory _ _ denseReadAddress_writes
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
  have hbm := readerFrame_metadata model ar br hbf ham
  have hc := denseReadSave_source memory br
  have hcf (r : Nat) (ho : r ≠ 645 ∧ r ≠ 646) :=
    Block.eval_frame memory _ _ denseReadSave_writes r (by omega) ⟨br, .running⟩
  have hcm := writes_metadata model memory _ _ denseReadSave_writes
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
  cases hword : (model.store).readWord? 0 (regs 640 / regs 32) with
  | none =>
      simp only [hword, logicalPacket_none, logicalLength_none] at hc645 hc646
      simp [denseSelectBlock, Block.sequence, Block.eval_seq, Evaluation.bind, heA, heB, heC,
        eval_ifZero, eval_skip, hc645, hp643, hreads, packedDenseTwoWordSelectRead_normalForm,
        bpWordReadTraceResult, hword, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
        optionNatPacket, logicalTraceReads, traceReads, ReadOnlyTrace, WordRAM.TraceEvent.isReadWord]
  | some word =>
      simp only [hword, logicalPacket_some, logicalLength_some] at hc645 hc646
      have hs := densePresent_source model memory reader hreader hwrites word cr hcm hc645 hc646
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
        simp [logicalTraceReads, traceReads]
      · simpa [ReadOnlyTrace, WordRAM.TraceEvent.isReadWord] using hsro

theorem selectLongBlock_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches model regs) (hzero : regs 513 = 0) :
    let actual := (selectLongBlock reader).eval memory ⟨regs, .running⟩
    let store := model.store
    let expected := WordRAM.TraceResult.bind
      (packedRankRead 9 10 11 21 (model.metadata 34) true store
        (model.metadata 28) (model.metadata 30) 1 (regs 514))
      (fun rank => GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 12
        (regs 562 * regs 32 + regs 564) (rank * regs 25 + (regs 512 - regs 561)))
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let prepared := regs.write 352 (regs 514)
  have hpm := MetadataMatches.write model regs hm 352 (regs 514) (Or.inr (by decide))
  have hr := rankLongBlock_source model memory reader hreader hwrites prepared hpm
  have hrf (r : Nat) (ho : ¬ RankWrapperWrites r) :=
    rankLongBlock_frame reader hwrites memory ⟨prepared, .running⟩ r ho
  have hrm := writes_metadata model memory _ _ (rankLongBlock_writes reader hwrites)
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
  have ht := selectLongTail_source model memory reader hreader rr hrm hz
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

theorem selectSparseBlock_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches model regs) (hzero : regs 513 = 0) :
    let actual := (selectSparseBlock reader).eval memory ⟨regs, .running⟩
    let store := model.store
    let expected := WordRAM.TraceResult.bind
      (packedRankRead 13 14 15 21 (model.metadata 34) true store
        (model.metadata 29) (model.metadata 31) 1 (regs 515))
      (fun rank => GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 16
        (regs 520) (rank * regs 26 + (regs 512 - regs 521)))
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let prepared := regs.write 352 (regs 515)
  have hpm := MetadataMatches.write model regs hm 352 (regs 515) (Or.inr (by decide))
  have hr := rankSparseBlock_source model memory reader hreader hwrites prepared hpm
  have hrf (r : Nat) (ho : ¬ RankWrapperWrites r) :=
    rankSparseBlock_frame reader hwrites memory ⟨prepared, .running⟩ r ho
  have hrm := writes_metadata model memory _ _ (rankSparseBlock_writes reader hwrites)
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
  have ht := selectSparseTail_source model memory reader hreader rr hrm hz
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

theorem selectCloseBlock_metadata (model : ControllerModel) (reader : Block) (hw : ReaderWrites reader)
    (memory : Memory) (s : Data) (hm : MetadataMatches model s.regs) :
    MetadataMatches model ((selectCloseBlock reader).eval memory s).final.regs :=
  writes_metadata model memory _ _ (selectCloseBlock_writes reader hw)
    (by intro r hlo hhi; unfold SelectWrites; omega) s hm

theorem selectLocalDense_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches model regs) :
    let actual := (selectLocalDense reader).eval memory ⟨regs, .running⟩
    let expected := packedDenseTwoWordSelectRead 0 21 22 (model.metadata 34) false
      (model.store) (regs 32) (regs 520) (regs 521) (regs 512)
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let prepared := ((regs.write 640 (regs 520)).write 641 (regs 521)).write 642 (regs 512)
  have hpm : MetadataMatches model prepared := by
    apply MetadataMatches.write _ _ _ _ _ (Or.inr (by decide))
    apply MetadataMatches.write _ _ _ _ _ (Or.inr (by decide))
    exact MetadataMatches.write model regs hm 640 (regs 520) (Or.inr (by decide))
  have hs := denseSelectBlock_source model memory reader hreader hwrites prepared hpm
  generalize heD : (denseSelectBlock reader).eval memory ⟨prepared, .running⟩ = dense at hs
  rcases dense with ⟨⟨dr, dst⟩, dreads⟩
  dsimp only at hs
  obtain ⟨hdst, hdvalue, hdreads, hdro⟩ := hs
  subst dst
  simp [prepared, Registers.write] at hdvalue hdreads hdro
  dsimp only [prepared] at heD
  simp [selectLocalDense, Block.sequence, Block.eval_seq, Evaluation.bind, eval_move, heD,
    eval_skip, Registers.write, hdvalue, hdreads, hdro]

def selectLocalChoiceReference (store : WordRAM.ReadStore) (snapshot : Registers) (wordSize superWord superOccurrence idx slot : Nat)
    (loc : GenericSelect.SparseDenseSelectDenseLocalEntry) : WordRAM.TraceResult (Option Nat) :=
  let base := (superWord + loc.baseWordIndex) * wordSize + loc.firstOffset
  let occurrence := superOccurrence + loc.baseOccurrence
  if loc.rankBefore = 0 then
    packedDenseTwoWordSelectRead 0 21 22 (snapshot 34) false store wordSize base occurrence idx
  else WordRAM.TraceResult.bind
    (packedRankRead 13 14 15 21 (snapshot 34) true store
      (snapshot 29) (snapshot 31) 1 slot)
    (fun rank => GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 16 base
      (rank * snapshot 26 + (idx - occurrence)))

theorem selectLocalPresent_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (loc : GenericSelect.SparseDenseSelectDenseLocalEntry) (regs : Registers)
    (hm : MetadataMatches model regs) (hzero : regs 513 = 0)
    (h591 : regs 591 = loc.baseOccurrence) (h592 : regs 592 = loc.baseWordIndex)
    (h593 : regs 593 = loc.rankBefore) (h594 : regs 594 = loc.firstOffset) :
    let actual := (selectLocalPresent reader).eval memory ⟨regs, .running⟩
    let expected := selectLocalChoiceReference (model.store)
      model.metadata (regs 32) (regs 562) (regs 561) (regs 512) (regs 515) loc
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hp := selectLocalPrepare_source memory regs
  have hpf (r : Nat) (ho : r ≠ 520 ∧ r ≠ 521) :=
    Block.eval_frame memory _ _ selectLocalPrepare_writes r (by omega) ⟨regs, .running⟩
  have hpm := writes_metadata model memory _ _ selectLocalPrepare_writes
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
  have hp26 : pr 26 = model.metadata 26 := by
    rw [hpf 26 (by omega)]
    exact hm 26 (by decide)
  by_cases hmark : loc.rankBefore = 0
  · have hs := selectLocalDense_source model memory reader hreader hwrites pr hpm
    generalize heS : (selectLocalDense reader).eval memory ⟨pr, .running⟩ = selected at hs
    rcases selected with ⟨⟨sr, sst⟩, sreads⟩
    dsimp only at hs
    obtain ⟨hsst, hsvalue, hsreads, hsro⟩ := hs
    subst sst
    simp only [hp32, hp520, hp521, hp512] at hsvalue hsreads hsro
    simp [selectLocalPresent, Block.sequence, Block.eval_seq, Evaluation.bind, heP,
      eval_ifZero, hp593, hmark, heS, eval_skip, selectLocalChoiceReference, hsvalue, hsreads, hsro]
  · have hs := selectSparseBlock_source model memory reader hreader hwrites pr hpm hp513
    generalize heS : (selectSparseBlock reader).eval memory ⟨pr, .running⟩ = selected at hs
    rcases selected with ⟨⟨sr, sst⟩, sreads⟩
    dsimp only at hs
    obtain ⟨hsst, hsvalue, hsreads, hsro⟩ := hs
    subst sst
    simp only [hp26, hp520, hp521, hp512, hp515] at hsvalue hsreads hsro
    dsimp only [WordRAM.TraceResult.bind] at hsro
    simp [selectLocalPresent, Block.sequence, Block.eval_seq, Evaluation.bind, heP,
      eval_ifZero, hp593, hmark, heS, eval_skip, selectLocalChoiceReference, hsvalue, hsreads, hsro]

def selectLocalReference (store : WordRAM.ReadStore) (snapshot : Registers) (wordSize superWord superOccurrence idx slot : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind (packedSelectEntryRead (selectEntryLayout 5) store slot)
    (fun loc? => match loc? with
      | none => WordRAM.TraceResult.pure none
      | some loc => selectLocalChoiceReference store snapshot wordSize superWord superOccurrence idx slot loc)

theorem selectLocalBlock_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches model regs) (hzero : regs 513 = 0) :
    let actual := (selectLocalBlock reader).eval memory ⟨regs, .running⟩
    let slot := regs 514 * regs 27 + (regs 512 - regs 561) / regs 26
    let expected := selectLocalReference (model.store)
      model.metadata (regs 32) (regs 562) (regs 561) (regs 512) slot
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have ha := selectLocalAddress_source memory regs
  have haf (r : Nat) (ho : r ≠ 515 ∧ r ≠ 534 ∧ r ≠ 550) :=
    Block.eval_frame memory _ _ selectLocalAddress_writes r (by omega) ⟨regs, .running⟩
  have ham := writes_metadata model memory _ _ selectLocalAddress_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  generalize heA : selectLocalAddress.eval memory ⟨regs, .running⟩ = addressed at ha haf ham
  rcases addressed with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha haf ham
  obtain ⟨hast, hareads, hindex⟩ := ha
  subst ast
  subst areads
  have he := selectEntryBlock_source model memory reader hreader hwrites 5 515 590
    (by decide) (by decide) (by decide) (Or.inl (by decide)) ar ham
  have hef (r : Nat) (ho : ¬ SelectEntryWrites 590 r) :=
    selectEntryBlock_frame reader hwrites 5 515 590 memory ⟨ar, .running⟩ r ho
  have hem := selectEntryBlock_metadata model reader hwrites 5 515 590 (by decide)
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
  let store := model.store
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
      have hs := selectLocalPresent_source model memory reader hreader hwrites loc er hem hp513
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

def selectSuperReference (store : WordRAM.ReadStore) (snapshot : Registers) (idx slot : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry) : WordRAM.TraceResult (Option Nat) :=
  if super.rankBefore = 0 then
    selectLocalReference store snapshot (snapshot 32) super.baseWordIndex super.baseOccurrence idx
      (slot * snapshot 27 + (idx - super.baseOccurrence) / snapshot 26)
  else WordRAM.TraceResult.bind
    (packedRankRead 9 10 11 21 (snapshot 34) true store
      (snapshot 28) (snapshot 30) 1 slot)
    (fun rank => GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 12
      (super.baseWordIndex * snapshot 32 + super.firstOffset)
      (rank * snapshot 25 + (idx - super.baseOccurrence)))

def selectCloseReference (store : WordRAM.ReadStore) (snapshot : Registers) (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  if idx < snapshot 16 then
    WordRAM.TraceResult.bind (packedSelectEntryRead (selectEntryLayout 1) store (idx / snapshot 25))
      (fun super? => match super? with
        | none => WordRAM.TraceResult.pure none
        | some super => selectSuperReference store snapshot idx (idx / snapshot 25) super)
  else WordRAM.TraceResult.pure none

theorem selectReference_normalForm (store : WordRAM.ReadStore) (snapshot : Registers) (idx : Nat) :
    selectReference store snapshot idx = selectCloseReference store snapshot idx := by
  simp [selectReference, packedSelectCloseRead, selectCloseReference, selectSuperReference,
    selectLocalReference, selectLocalChoiceReference, packedSparseDirectoryRead,
    concreteBPNativeSelectCloseTraceSegmentLayout, concreteBPNativeDeadTraceSegment, selectEntryLayout,
    GenericSelect.relativeSplitSelectEntryIsMarked, GenericSelect.selectSuperSlot,
    GenericSelect.relativeSplitSelectLocalSlot, GenericSelect.relativeSplitSelectLocalSlotInSuper,
    GenericSelect.relativeSplitSelectEntryBasePosition, GenericSelect.relativeSplitSelectLongCompactSlot,
    GenericSelect.relativeSplitSelectLocalBasePosition, GenericSelect.relativeSplitSelectLocalBaseOccurrence,
    GenericSelect.relativeSplitSelectSparseCompactSlot]
  rfl

theorem selectSuperPresent_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry) (regs : Registers)
    (hm : MetadataMatches model regs) (hzero : regs 513 = 0)
    (h561 : regs 561 = super.baseOccurrence) (h562 : regs 562 = super.baseWordIndex)
    (h563 : regs 563 = super.rankBefore) (h564 : regs 564 = super.firstOffset) :
    let actual := (selectSuperPresent reader).eval memory ⟨regs, .running⟩
    let expected := selectSuperReference (model.store)
      model.metadata (regs 512) (regs 514) super
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have h25 : regs 25 = model.metadata 25 := hm 25 (by decide)
  have h26 : regs 26 = model.metadata 26 := hm 26 (by decide)
  have h27 : regs 27 = model.metadata 27 := hm 27 (by decide)
  have h32 : regs 32 = model.metadata 32 := hm 32 (by decide)
  by_cases hmark : super.rankBefore = 0
  · have hs := selectLocalBlock_source model memory reader hreader hwrites regs hm hzero
    simpa [selectSuperPresent, eval_ifZero, h563, hmark, selectSuperReference,
      h26, h27, h32, h561, h562] using hs
  · have hs := selectLongBlock_source model memory reader hreader hwrites regs hm hzero
    simpa [selectSuperPresent, eval_ifZero, h563, hmark, selectSuperReference,
      h25, h32, h561, h562, h564] using hs

theorem selectEligible_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches model regs) (hzero : regs 513 = 0) :
    let actual := (selectEligible reader).eval memory ⟨regs, .running⟩
    let store := model.store
    let slot := regs 512 / model.metadata 25
    let expected := WordRAM.TraceResult.bind (packedSelectEntryRead (selectEntryLayout 1) store slot)
      (fun super? => match super? with
        | none => WordRAM.TraceResult.pure none
        | some super => selectSuperReference store model.metadata (regs 512) slot super)
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let prepared := regs.write 514 (regs 512 / regs 25)
  have hpm : MetadataMatches model prepared := MetadataMatches.write model regs hm 514
    (regs 512 / regs 25) (Or.inr (by decide))
  have h25 : regs 25 = model.metadata 25 := hm 25 (by decide)
  have he := selectEntryBlock_source model memory reader hreader hwrites 1 514 560
    (by decide) (by decide) (by decide) (Or.inl (by decide)) prepared hpm
  have hef (r : Nat) (ho : ¬ SelectEntryWrites 560 r) :=
    selectEntryBlock_frame reader hwrites 1 514 560 memory ⟨prepared, .running⟩ r ho
  have hem := selectEntryBlock_metadata model reader hwrites 1 514 560 (by decide)
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
  have hp514 : er 514 = regs 512 / model.metadata 25 := by
    rw [hef 514 (by simp [SelectEntryWrites])]
    simp [prepared, h25]
  dsimp only [prepared] at heE
  let store := model.store
  let slot := regs 512 / model.metadata 25
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
      have hs := selectSuperPresent_source model memory reader hreader hwrites super er hem hp513
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

theorem selectCloseBlock_source (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches model regs) :
    let actual := (selectCloseBlock reader).eval memory ⟨regs, .running⟩
    let expected := selectReference (model.store) model.metadata (regs 512)
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hn : regs 16 = model.metadata 16 := hm 16 (by decide)
  let prepared := (regs.write 513 0).write 550 (if regs 512 < model.metadata 16 then 1 else 0)
  have hpm : MetadataMatches model prepared := by
    apply MetadataMatches.write _ _ _ _ _ (Or.inr (by decide))
    exact MetadataMatches.write model regs hm 513 0 (Or.inr (by decide))
  have hz : prepared 513 = 0 := by simp [prepared, Registers.write]
  by_cases hvalid : regs 512 < model.metadata 16
  · have hs := selectEligible_source model memory reader hreader hwrites prepared hpm hz
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
      selectReference_normalForm, selectCloseReference, hsvalue, hsreads, hsro]
  · simp [selectCloseBlock, Block.sequence, Block.eval_seq, Evaluation.bind, eval_constant,
      eval_comparison, Comparison.eval, Registers.write, hn, hvalid, eval_ifZero, eval_skip,
      selectReference_normalForm, selectCloseReference, WordRAM.TraceResult.pure,
      optionNatPacket, logicalTraceReads, traceReads, ReadOnlyTrace]

theorem selectCloseBlock_machine (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches model regs) :
    let expected := selectReference (model.store) model.metadata (regs 512)
    let actual := run memory ((selectCloseBlock reader).compileAt 0 ++ [.halt 513])
      (3667 + 82 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some (optionNatPacket expected.value) ∧
      actual.final.status = .halted (optionNatPacket expected.value) ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧
      actual.steps ≤ 3667 + 82 * reader.size ∧
      (∀ r, ¬ SelectWrites r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace := by
  have hs := selectCloseBlock_source model memory reader hreader hwrites regs hm
  have hc := rank_compile_with_halt (selectCloseBlock reader) 513 memory regs _ _ SelectWrites
    (selectCloseBlock_writes reader hwrites) hs.1 hs.2.1 hs.2.2.1
  have hsize : (selectCloseBlock reader).size + 1 = 3667 + 82 * reader.size := by
    rw [selectCloseBlock_size]; omega
  rw [hsize] at hc
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, hs.2.2.2⟩

/-- Independent expected-type consumer for the shared source refinement. The
reference and receipt projection are expanded at their exact model objects. -/
theorem selectCloseBlock_source_expectedType
    (snapshot : Registers) (store : WordRAM.ReadStore) (receipts : Nat → Nat → List Receipt)
    (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation ⟨snapshot, store, receipts⟩ memory reader)
    (hwrites : ReaderWrites reader) (regs : Registers)
    (hm : ∀ r < 190, regs r = snapshot r) :
    let actual := (selectCloseBlock reader).eval memory ⟨regs, .running⟩
    let expected := packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout 21 22 store
      (snapshot 34) false (snapshot 16) (snapshot 25) (snapshot 32) (snapshot 27) (snapshot 26)
      (snapshot 28) (snapshot 30) 1 (snapshot 29) (snapshot 31) 1 (snapshot 26) (regs 512)
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = traceReads receipts expected.trace ∧ ReadOnlyTrace expected.trace :=
  selectCloseBlock_source ⟨snapshot, store, receipts⟩ memory reader hreader hwrites regs hm

end RMQ.PackedBitvector.Controller
