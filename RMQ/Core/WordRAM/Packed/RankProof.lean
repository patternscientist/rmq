import RMQ.Core.WordRAM.Packed.RankSource
import RMQ.Core.WordRAM.Packed.ReadInterface

/-! # Value, ordered reads and primitive execution for fixed rank source -/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

def RankWordWrites (r : Nat) : Prop :=
  (260 ≤ r ∧ r < 311) ∨ (8192 ≤ r ∧ r < 8271)

def RankWrites (r : Nat) : Prop :=
  (256 ≤ r ∧ r < 311) ∨ (360 ≤ r ∧ r < 371) ∨ (8192 ≤ r ∧ r < 8271)

def RankWrapperWrites (r : Nat) : Prop :=
  (256 ≤ r ∧ r < 311) ∨ (353 ≤ r ∧ r < 371) ∨ (8192 ≤ r ∧ r < 8271)

theorem rankWordBody_writes (reader : Block) (hr : ReaderWrites reader) :
    (rankWordBody reader).WritesOnly RankWordWrites := by
  have hreader : reader.WritesOnly RankWordWrites :=
    Block.WritesOnly.mono reader hr (by intro r h; exact Or.inr ⟨by omega, h.2⟩)
  simpa [rankWordBody, rankWordAddress, rankWordDecode, Block.sequence, Block.WritesOnly, Action.destination,
    RankWordWrites, chunkSlotBlock, chunkRankBlock, natSubBlock, minBlock] using hreader

theorem rankWordBlock_writes (reader : Block) (hr : ReaderWrites reader) :
    (rankWordBlock reader).WritesOnly RankWordWrites := by
  have hb := rankWordBody_writes reader hr
  simpa [rankWordBlock, rankWordInit, Block.sequence, Block.WritesOnly, Action.destination,
    RankWordWrites, natSubBlock, minBlock] using hb

theorem rankBlock_writes (reader : Block) (hr : ReaderWrites reader) :
    (rankBlock reader).WritesOnly RankWrites := by
  have hreader : reader.WritesOnly RankWrites :=
    Block.WritesOnly.mono reader hr (by intro r h; exact Or.inr (Or.inr ⟨by omega, h.2⟩))
  have hword : (rankWordBlock reader).WritesOnly RankWrites :=
    Block.WritesOnly.mono _ (rankWordBlock_writes reader hr) (by
      intro r h
      rcases h with h | h
      · exact Or.inl ⟨by omega, h.2⟩
      · exact Or.inr (Or.inr h))
  simpa [rankBlock, rankSeeds, rankInit, rankSeedRead, rankFinish, rankPrepareWord,
    rankCombine, Block.sequence, Block.WritesOnly, Action.destination,
    RankWrites, natSubBlock, minBlock] using And.intro hreader (And.intro hreader
      (And.intro hreader hword))

theorem rankWordBlock_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ RankWordWrites r) :
    ((rankWordBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (rankWordBlock_writes reader hr) r outside s

theorem rankBlock_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ RankWrites r) :
    ((rankBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (rankBlock_writes reader hr) r outside s

private theorem writes_metadata (shape : CartesianShape) (memory : Memory)
    (block : Block) (allowed : Nat → Prop) (writes : block.WritesOnly allowed)
    (outside : ∀ r, 16 ≤ r → r < 190 → ¬ allowed r)
    (s : Data) (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape (block.eval memory s).final.regs := by
  intro i hi
  rw [Block.eval_frame memory block allowed writes _ (outside _ (by omega) (by omega))]
  exact hm i hi

theorem rankWordBlock_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data)
    (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((rankWordBlock reader).eval memory s).final.regs :=
  writes_metadata shape memory _ _ (rankWordBlock_writes reader hr)
    (by intro r hlo hhi; unfold RankWordWrites; omega) s hm

theorem rankBlock_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data)
    (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((rankBlock reader).eval memory s).final.regs :=
  writes_metadata shape memory _ _ (rankBlock_writes reader hr)
    (by intro r hlo hhi; unfold RankWrites; omega) s hm

private theorem data_eq_running (s : Data) (hs : s.status = .running) :
    s = ⟨s.regs, .running⟩ := by cases s; simp_all

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

private theorem eval_skip (memory : Memory) (regs : Registers) :
    Block.skip.eval memory ⟨regs, .running⟩ = ⟨⟨regs, .running⟩, []⟩ := rfl

theorem rankWordAddress_writes :
    rankWordAddress.WritesOnly (fun r => (280 ≤ r ∧ r < 292) ∨ r = 8192 ∨ r = 8193) := by
  simp [rankWordAddress, Block.sequence, Block.WritesOnly, Action.destination,
    chunkSlotBlock, natSubBlock, minBlock]

theorem rankWordAddress_frame (memory : Memory) (s : Data) (r : Nat)
    (outside : (r < 280 ∨ 292 ≤ r) ∧ r ≠ 8192 ∧ r ≠ 8193) :
    (rankWordAddress.eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ rankWordAddress_writes r (by omega) s

theorem rankWordAddress_source (memory : Memory) (regs : Registers) :
    let actual := rankWordAddress.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
    actual.final.regs 8192 = 21 ∧
    actual.final.regs 8193 = chunkSlot (regs 256) (regs 34) (regs 261) (regs 262) ∧
    actual.final.regs 284 = min (regs 34) (regs 262 - regs 261 * regs 34) := by
  let prepared := (((regs.write 280 (regs 256)).write 281 (regs 34)).write
    282 (regs 261)).write 283 (regs 262)
  have hs := chunkSlotBlock_source 280 memory prepared
  generalize he : (chunkSlotBlock 280).eval memory ⟨prepared, .running⟩ = located at hs
  rcases located with ⟨⟨out, status⟩, reads⟩
  dsimp only at hs
  obtain ⟨hstatus, hreads, hlength, _hvalue, hslot⟩ := hs
  subst status
  subst reads
  simp [prepared, Registers.write] at he hlength hslot
  simp [rankWordAddress, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_move, eval_constant, eval_skip, Registers.write, he, hslot, hlength]
theorem rankWordDecode_writes :
    rankWordDecode.WritesOnly (fun r => r = 260 ∨ r = 261 ∨ (300 ≤ r ∧ r < 311)) := by
  simp [rankWordDecode, Block.sequence, Block.WritesOnly, Action.destination,
    chunkRankBlock, natSubBlock]

theorem rankWordDecode_frame (memory : Memory) (s : Data) (r : Nat)
    (outside : r ≠ 260 ∧ r ≠ 261 ∧ (r < 300 ∨ 311 ≤ r)) :
    (rankWordDecode.eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ rankWordDecode_writes r (by omega) s

theorem rankWordDecode_source (memory : Memory) (regs : Registers) :
    let actual := rankWordDecode.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
    actual.final.regs 260 = regs 260 +
      chunkRank (regs 34) (regs 284) (regs 8194 - regs 265) (regs 259) ∧
    actual.final.regs 261 = regs 261 + regs 265 := by
  let prepared := ((((regs.write 300 (regs 34)).write 301 (regs 284)).write
    303 (Comparison.le.eval (regs 265) (regs 8194))).write
    302 (regs 8194 - regs 265)).write 303 (regs 259)
  have hs := chunkRankBlock_source 300 memory prepared
  have hf260 := chunkRankBlock_frame 300 memory ⟨prepared, .running⟩ 260 (by omega)
  have hf261 := chunkRankBlock_frame 300 memory ⟨prepared, .running⟩ 261 (by omega)
  have hf265 := chunkRankBlock_frame 300 memory ⟨prepared, .running⟩ 265 (by omega)
  generalize he : (chunkRankBlock 300).eval memory ⟨prepared, .running⟩ = ranked
    at hs hf260 hf261 hf265
  rcases ranked with ⟨⟨out, status⟩, reads⟩
  dsimp only at hs hf260 hf261 hf265
  obtain ⟨hstatus, hreads, hvalue⟩ := hs
  subst status
  subst reads
  simp [prepared, Registers.write] at he hvalue hf260 hf261 hf265
  have hsub (r : Registers) := natSubBlock_source 302 8194 265 303 memory r (by decide) (by decide)
  simp [rankWordDecode, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_move, eval_arithmetic, eval_skip, hsub, Registers.write, Arithmetic.eval,
    he, hvalue, hf260, hf261, hf265]
def RankWordBodyWrites (r : Nat) : Prop :=
  r = 260 ∨ r = 261 ∨ r = 264 ∨ (280 ≤ r ∧ r < 311) ∨ (8192 ≤ r ∧ r < 8271)

theorem rankWordBody_precise_writes (reader : Block) (hr : ReaderWrites reader) :
    (rankWordBody reader).WritesOnly RankWordBodyWrites := by
  have hreader : reader.WritesOnly RankWordBodyWrites :=
    Block.WritesOnly.mono reader hr (by
      intro r h
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h.2⟩))))
  simpa [rankWordBody, rankWordAddress, rankWordDecode, Block.sequence,
    Block.WritesOnly, Action.destination, RankWordBodyWrites,
    chunkSlotBlock, chunkRankBlock, natSubBlock, minBlock] using hreader

theorem rankWordBody_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ RankWordBodyWrites r) :
    ((rankWordBody reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (rankWordBody_precise_writes reader hr) r outside s

theorem rankWordBody_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data)
    (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((rankWordBody reader).eval memory s).final.regs :=
  writes_metadata shape memory _ _ (rankWordBody_precise_writes reader hr)
    (by intro r hlo hhi; unfold RankWordBodyWrites; omega) s hm

private theorem eval_comparison (memory : Memory) (regs : Registers)
    (op : Comparison) (dst lhs rhs : Nat) :
    (Block.action (.comparison op dst lhs rhs)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩, []⟩ := rfl

private theorem eval_ifZero (memory : Memory) (regs : Registers) (cond : Nat)
    (yes no : Block) :
    (Block.ifZero cond yes no).eval memory ⟨regs, .running⟩ =
      if regs cond = 0 then yes.eval memory ⟨regs, .running⟩
      else no.eval memory ⟨regs, .running⟩ := rfl

theorem rankWordBody_inactive (reader : Block) (memory : Memory) (regs : Registers)
    (hinactive : regs 263 ≤ regs 261) :
    (rankWordBody reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write 264 0, .running⟩, []⟩ := by
  simp [rankWordBody, Block.eval_seq, Evaluation.bind, eval_comparison,
    eval_ifZero, eval_skip, Comparison.eval, Registers.write, Nat.not_lt.mpr hinactive]

theorem rankWordBody_active (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (regs : Registers)
    (hm : MetadataMatches shape regs) (hactive : regs 261 < regs 263)
    (hone : regs 265 = 1) :
    let actual := (rankWordBody reader).eval memory ⟨regs, .running⟩
    let slot := chunkSlot (regs 256) (regs 34) (regs 261) (regs 262)
    actual.final.status = .running ∧ actual.reads = readerReceipts shape memory 21 slot ∧
    actual.final.regs 260 = regs 260 + chunkRank (regs 34)
      (min (regs 34) (regs 262 - regs 261 * regs 34))
      ((((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21 slot).map
        bitsToNatLE).getD 0) (regs 259) ∧
    actual.final.regs 261 = regs 261 + 1 := by
  let compared := regs.write 264 1
  have ha := rankWordAddress_source memory compared
  have ham := writes_metadata shape memory rankWordAddress _ rankWordAddress_writes
    (by intro r hlo hhi; omega) ⟨compared, .running⟩
    (MetadataMatches.write shape regs hm 264 1 (Or.inr (by decide)))
  have haf (r : Nat) (ho : (r < 280 ∨ 292 ≤ r) ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    rankWordAddress_frame memory ⟨compared, .running⟩ r ho
  generalize heA : rankWordAddress.eval memory ⟨compared, .running⟩ = addressed at ha ham haf
  rcases addressed with ⟨⟨ar, ast⟩, ard⟩
  dsimp only at ha ham haf
  obtain ⟨hast, hard, hsegment, hslot, hlength⟩ := ha
  subst ast
  subst ard
  have hb := hreader ar ham
  generalize heB : reader.eval memory ⟨ar, .running⟩ = loaded at hb
  rcases loaded with ⟨⟨br, bst⟩, brd⟩
  dsimp only at hb
  obtain ⟨hbst, hpacket, _hlength, hreads, hframe⟩ := hb
  subst bst
  have hp (r : Nat) (hsmall : r < 280) (hne : r ≠ 264) : br r = regs r := by
    rw [hframe r (Or.inl (by omega)), haf r ⟨Or.inl hsmall, by omega, by omega⟩]
    simp [compared, Registers.write, hne]
  have h284 : br 284 = min (regs 34) (regs 262 - regs 261 * regs 34) := by
    rw [hframe 284 (Or.inl (by decide)), hlength]
    simp [compared, Registers.write]
  rw [hsegment, hslot] at hpacket hreads
  simp [compared, Registers.write] at hpacket hreads
  have hc := rankWordDecode_source memory br
  generalize heC : rankWordDecode.eval memory ⟨br, .running⟩ = decoded at hc
  rcases decoded with ⟨⟨cr, cst⟩, crd⟩
  dsimp only at hc
  obtain ⟨hcst, hcrd, hvalue, hindex⟩ := hc
  subst cst
  subst crd
  have heval : (rankWordBody reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨cr, .running⟩, brd⟩ := by
    have hcmp : Comparison.lt.eval (regs 261) (regs 263) = 1 := by
      simp [Comparison.eval, hactive]
    have hpositive : (Block.seq rankWordAddress (.seq reader rankWordDecode)).eval
        memory ⟨compared, .running⟩ = ⟨⟨cr, .running⟩, brd⟩ := by
      rw [Block.eval_seq, heA]
      change (Block.seq reader rankWordDecode).eval memory ⟨ar, .running⟩ = _
      rw [Block.eval_seq, heB]
      simp only [Evaluation.bind, heC, List.append_nil]
    have hgate : (Block.ifZero 264 .skip (.seq rankWordAddress (.seq reader rankWordDecode))).eval
        memory ⟨compared, .running⟩ = ⟨⟨cr, .running⟩, brd⟩ := by
      rw [eval_ifZero, if_neg (by simp [compared])]
      exact hpositive
    dsimp only [compared] at hgate
    rw [rankWordBody, Block.eval_seq, eval_comparison, hcmp]
    simp only [Evaluation.bind, hgate, List.nil_append]
  rw [heval]
  dsimp only
  refine ⟨rfl, hreads, ?_, ?_⟩
  · rw [hvalue, hp 260 (by decide) (by decide), hp 34 (by decide) (by decide),
      hp 265 (by decide) (by decide), hp 259 (by decide) (by decide), h284, hpacket, hone,
      logicalPacket_pred]
  · rw [hindex, hp 261 (by decide) (by decide), hp 265 (by decide) (by decide), hone]

structure RankFoldState (word : List Bool) (target : Bool) (c e total j acc : Nat)
    (regs : Registers) : Prop where
  word_eq : regs 256 = bitsToNatLE word
  target_eq : regs 259 = if target then 1 else 0
  chunk_eq : regs 34 = c
  out_eq : regs 260 = acc
  index_eq : regs 261 = j
  effective_eq : regs 262 = e
  total_eq : regs 263 = total
  one_eq : regs 265 = 1

theorem rankWordBody_active_reference (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hreader : ReaderCorrect shape memory reader)
    (word : List Bool) (target : Bool) (c e total j acc : Nat) (regs : Registers)
    (hm : MetadataMatches shape regs) (hs : RankFoldState word target c e total j acc regs)
    (hactive : j < total) :
    let actual := (rankWordBody reader).eval memory ⟨regs, .running⟩
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let slot := bpWordRankChunkSlotAt c word e j
    actual.final.status = .running ∧ actual.reads = readerReceipts shape memory 21 slot ∧
    actual.final.regs 260 = bpWordRankStepDecoded c target (bpWordChunkSliceLen c e j)
      acc ((store.readWord? 21 slot).map bitsToNatLE) ∧
    actual.final.regs 261 = j + 1 := by
  have h := rankWordBody_active shape memory reader hreader regs hm
    (by rw [hs.index_eq, hs.total_eq]; exact hactive) hs.one_eq
  simpa only [hs.word_eq, hs.target_eq, hs.chunk_eq, hs.out_eq, hs.index_eq,
    hs.effective_eq, chunkSlot_eq_reference, chunkRank_eq_reference,
    bpWordRankStepDecoded, bpWordChunkSliceLen] using h

@[simp] theorem rank_logicalTraceReads_append (shape : CartesianShape) (memory : Memory)
    (first second : List WordRAM.TraceEvent) :
    logicalTraceReads shape memory (first ++ second) =
      logicalTraceReads shape memory first ++ logicalTraceReads shape memory second := by
  simp [logicalTraceReads]

theorem rank_readOnly_cons (segment index : Nat) (word : Option (List Bool))
    (trace : List WordRAM.TraceEvent) (ht : ReadOnlyTrace trace) :
    ReadOnlyTrace (.readWord segment index word :: trace) := by
  intro event he
  rcases List.mem_cons.mp he with rfl | he
  · trivial
  · exact ht event he

theorem rankFold_readOnly (store : WordRAM.ReadStore) (segment c : Nat) (target : Bool)
    (word : List Bool) (e j count acc : Nat) :
    ReadOnlyTrace (bpChunkedWordRankTraceFromWithStore store segment c target
      word e j count acc).trace := by
  rw [bpChunkedWordRankTraceFromWithStore_trace_map]
  intro event he
  obtain ⟨d, _hd, rfl⟩ := List.mem_map.mp he
  trivial

theorem rankWordRepeat_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (target : Bool) (c e total cycles j acc : Nat)
    (regs : Registers) (hm : MetadataMatches shape regs)
    (hs : RankFoldState word target c e total j acc regs) (hcover : total ≤ j + cycles) :
    let actual := (Block.repeat cycles (rankWordBody reader)).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordRankTraceFromWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 c target word e j (total - j) acc
    actual.final.status = .running ∧ actual.final.regs 260 = expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace := by
  induction cycles generalizing j acc regs with
  | zero =>
      have hz : total - j = 0 := by omega
      simp [Block.eval_repeat, iterate, bpChunkedWordRankTraceFromWithStore, hz,
        WordRAM.TraceResult.pure, logicalTraceReads, hs.out_eq]
  | succ cycles ih =>
      by_cases hactive : j < total
      · have hb := rankWordBody_active_reference shape memory reader hreader
          word target c e total j acc regs hm hs hactive
        have hmeta := rankWordBody_metadata shape reader hwrites memory ⟨regs, .running⟩ hm
        have hframe (r : Nat) (ho : ¬ RankWordBodyWrites r) :=
          rankWordBody_frame reader hwrites memory ⟨regs, .running⟩ r ho
        generalize he : (rankWordBody reader).eval memory ⟨regs, .running⟩ = first
          at hb hmeta hframe
        rcases first with ⟨⟨fr, fst⟩, freceipts⟩
        dsimp only at hb hmeta hframe
        obtain ⟨hfst, hreads, hvalue, hindex⟩ := hb
        subst fst
        let nextAcc := bpWordRankStepDecoded c target (bpWordChunkSliceLen c e j) acc
          (((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            21 (bpWordRankChunkSlotAt c word e j)).map bitsToNatLE)
        have hnext : RankFoldState word target c e total (j + 1) nextAcc fr := by
          constructor
          · rw [hframe 256 (by simp [RankWordBodyWrites])]; exact hs.word_eq
          · rw [hframe 259 (by simp [RankWordBodyWrites])]; exact hs.target_eq
          · rw [hframe 34 (by simp [RankWordBodyWrites])]; exact hs.chunk_eq
          · exact hvalue
          · exact hindex
          · rw [hframe 262 (by simp [RankWordBodyWrites])]; exact hs.effective_eq
          · rw [hframe 263 (by simp [RankWordBodyWrites])]; exact hs.total_eq
          · rw [hframe 265 (by simp [RankWordBodyWrites])]; exact hs.one_eq
        have ht := ih (j + 1) nextAcc fr hmeta hnext (by omega)
        have hremaining : total - j = (total - (j + 1)) + 1 := by omega
        rw [Block.eval_repeat_succ, he]
        dsimp only [Evaluation.bind]
        rw [hremaining, bpChunkedWordRankTraceFromWithStore]
        dsimp only [WordRAM.TraceResult.bind, bpChunkReadTraceResult]
        refine ⟨ht.1, ht.2.1, ?_⟩
        rw [hreads, ht.2.2, rank_logicalTraceReads_append]
        simp only [logicalTraceReads, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          nextAcc, bpWordRankChunkSlotAt]
      · have hstop : regs 263 ≤ regs 261 := by rw [hs.total_eq, hs.index_eq]; omega
        have hnext : RankFoldState word target c e total j acc (regs.write 264 0) := by
          constructor <;> simp only [Registers.write] <;> first
            | exact hs.word_eq | exact hs.target_eq | exact hs.chunk_eq | exact hs.out_eq
            | exact hs.index_eq | exact hs.effective_eq | exact hs.total_eq | exact hs.one_eq
        have ht := ih j acc (regs.write 264 0)
          (MetadataMatches.write shape regs hm 264 0 (Or.inr (by decide))) hnext (by omega)
        rw [Block.eval_repeat_succ, rankWordBody_inactive reader memory regs hstop]
        simpa only [Evaluation.bind, List.nil_append] using ht

theorem rankWordInit_writes :
    rankWordInit.WritesOnly (fun r => 260 ≤ r ∧ r < 267) := by
  simp [rankWordInit, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, minBlock]

theorem rankWordInit_source (memory : Memory) (regs : Registers) :
    let actual := rankWordInit.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
    actual.final.regs 260 = 0 ∧ actual.final.regs 261 = 0 ∧
    actual.final.regs 262 = min (regs 258) (regs 257) ∧
    actual.final.regs 263 = bpWordChunkCount (regs 34) (min (regs 258) (regs 257)) ∧
    actual.final.regs 265 = 1 := by
  have hsub (r : Registers) := natSubBlock_source 263 262 265 264 memory r (by decide) (by decide)
  have hmin1 (r : Registers) := minBlock_source 262 258 257 264 memory r (by decide) (by decide)
  have hmin2 (r : Registers) := minBlock_source 263 263 266 264 memory r (by decide) (by decide)
  simp [rankWordInit, Block.sequence, Block.eval_seq, Evaluation.bind, eval_constant,
    eval_arithmetic, eval_skip, hsub, hmin1, hmin2, Registers.write,
    Arithmetic.eval, bpWordChunkCount]

theorem metadata_chunkBits (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) : regs 34 = packedFringeChunkBits shape.size :=
  hm 18 (by decide)

private theorem eval_seq_summary (memory : Memory) (first second : Block)
    (regs : Registers) (value output : Nat) (receipts : List Receipt)
    (hfirst : (first.eval memory ⟨regs, .running⟩).final.status = .running)
    (hsecond : let actual := second.eval memory ⟨(first.eval memory ⟨regs, .running⟩).final.regs, .running⟩
      actual.final.status = .running ∧ actual.final.regs output = value ∧
      (first.eval memory ⟨regs, .running⟩).reads ++ actual.reads = receipts) :
    let actual := (Block.seq first second).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs output = value ∧
    actual.reads = receipts := by
  rw [Block.eval_seq]
  dsimp only [Evaluation.bind]
  rw [data_eq_running _ hfirst]
  exact hsecond

private theorem eval_seq_of_results (memory : Memory) (first second : Block) (s : Data)
    (a b : Evaluation) (ha : first.eval memory s = a)
    (hb : second.eval memory a.final = b) :
    (Block.seq first second).eval memory s = ⟨b.final, a.reads ++ b.reads⟩ := by
  rw [Block.eval_seq, ha]
  simp only [Evaluation.bind, hb]

private theorem rankWordBlock_initialized_source (shape : CartesianShape) (memory : Memory)
    (reader initializer : Block) (copies : Nat)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (target : Bool) (limit : Nat) (regs : Registers)
    (hm : MetadataMatches shape regs) (hword : regs 256 = bitsToNatLE word)
    (hlength : regs 257 = word.length) (hlimit : regs 258 = limit)
    (htarget : regs 259 = if target then 1 else 0)
    (hp : let actual := initializer.eval memory ⟨regs, .running⟩
      actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 260 = 0 ∧ actual.final.regs 261 = 0 ∧
      actual.final.regs 262 = min (regs 258) (regs 257) ∧
      actual.final.regs 263 = bpWordChunkCount (regs 34) (min (regs 258) (regs 257)) ∧
      actual.final.regs 265 = 1)
    (hf : ∀ r, r < 260 ∨ 267 ≤ r →
      (initializer.eval memory ⟨regs, .running⟩).final.regs r = regs r)
    (hcover : bpWordChunkCount (packedFringeChunkBits shape.size) (bpWordRankEffLimit word limit) ≤ copies) :
    let actual := (Block.seq initializer (.repeat copies (rankWordBody reader))).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21
      (packedFringeChunkBits shape.size) target word limit
    actual.final.status = .running ∧ actual.final.regs 260 = expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hmeta : MetadataMatches shape (initializer.eval memory ⟨regs, .running⟩).final.regs := by
    intro i hi
    rw [hf (16 + i) (Or.inl (by omega))]
    exact hm i hi
  let pr := (initializer.eval memory ⟨regs, .running⟩).final.regs
  obtain ⟨hpst, hreceipts, hzero, hindex, heffective, htotal, hone⟩ := hp
  have hc := metadata_chunkBits shape regs hm
  let c := packedFringeChunkBits shape.size
  let e := bpWordRankEffLimit word limit
  have hstate : RankFoldState word target c e (bpWordChunkCount c e) 0 0 pr := by
    constructor
    · exact (hf 256 (Or.inl (by decide))).trans hword
    · exact (hf 259 (Or.inl (by decide))).trans htarget
    · exact (hf 34 (Or.inl (by decide))).trans hc
    · exact hzero
    · exact hindex
    · simpa only [hlimit, hlength, bpWordRankEffLimit] using heffective
    · simpa only [hlimit, hlength, hc, bpWordRankEffLimit] using htotal
    · exact hone
  have hl := rankWordRepeat_source shape memory reader hreader hwrites word target c e
    (bpWordChunkCount c e) copies 0 0 (initializer.eval memory ⟨regs, .running⟩).final.regs
    hmeta hstate (by simpa only [Nat.zero_add] using hcover)
  let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 c target word limit
  let foldExpected := bpChunkedWordRankTraceFromWithStore
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 c target word e 0
    (bpWordChunkCount c e - 0) 0
  have href : expected = foldExpected := by
    dsimp only [expected, foldExpected, bpChunkedWordRankTraceResultAtSegmentWithStore, e]
    rw [Nat.sub_zero]
  have hjoin := eval_seq_summary memory initializer (.repeat copies (rankWordBody reader))
    regs foldExpected.value 260 (logicalTraceReads shape memory foldExpected.trace) hpst
    ⟨hl.1, hl.2.1, by rw [hreceipts]; exact hl.2.2⟩
  refine ⟨hjoin.1, ?_, ?_, ?_⟩
  · exact hjoin.2.1.trans (congrArg WordRAM.TraceResult.value href.symm)
  · exact hjoin.2.2.trans (congrArg (fun result => logicalTraceReads shape memory result.trace) href.symm)
  · exact (congrArg (fun result => ReadOnlyTrace result.trace) href.symm).mp
      (rankFold_readOnly (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 c target
        word e 0 (bpWordChunkCount c e - 0) 0)

theorem rankWordBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (target : Bool) (limit : Nat) (regs : Registers)
    (hm : MetadataMatches shape regs) (hword : regs 256 = bitsToNatLE word)
    (hlength : regs 257 = word.length) (hlimit : regs 258 = limit)
    (htarget : regs 259 = if target then 1 else 0) :
    let actual := (rankWordBlock reader).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21
      (packedFringeChunkBits shape.size) target word limit
    actual.final.status = .running ∧ actual.final.regs 260 = expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace :=
  rankWordBlock_initialized_source shape memory reader rankWordInit 8 hreader hwrites
    word target limit regs hm hword hlength hlimit htarget (rankWordInit_source memory regs)
    (fun r ho => Block.eval_frame memory rankWordInit _ rankWordInit_writes r (by omega)
      ⟨regs, .running⟩)
    (bpWordChunkCount_le_eight _ _)

/-- Compile an already proved source result and frame into one actual halt run.
The instruction budget is the literal finite source expansion plus its halt. -/
theorem rank_compile_with_halt (block : Block) (output : Nat) (memory : Memory)
    (regs : Registers) (value : Nat) (receipts : List Receipt) (allowed : Nat → Prop)
    (writes : block.WritesOnly allowed)
    (hs : (block.eval memory ⟨regs, .running⟩).final.status = .running)
    (hv : (block.eval memory ⟨regs, .running⟩).final.regs output = value)
    (ht : (block.eval memory ⟨regs, .running⟩).reads = receipts) :
    let actual := run memory (block.compileAt 0 ++ [.halt output]) (block.size + 1)
      ⟨regs, 0, .running⟩
    actual.result = some value ∧ actual.final.status = .halted value ∧
    actual.reads = receipts ∧ actual.steps ≤ block.size + 1 ∧
    (∀ r, ¬ allowed r → actual.final.regs r = regs r) := by
  have hm := block.compile_with_halt memory output ⟨regs, 0, .running⟩ rfl
  dsimp only [Data.ofState] at hm
  have hdata := hm.1
  rw [data_eq_running _ hs] at hdata
  have hregs := congrArg Data.regs hdata
  have hstatus := congrArg Data.status hdata
  change (run memory (block.compileAt 0 ++ [.halt output]) (block.size + 1)
    ⟨regs, 0, .running⟩).final.regs = (block.eval memory ⟨regs, .running⟩).final.regs at hregs
  change (run memory (block.compileAt 0 ++ [.halt output]) (block.size + 1)
    ⟨regs, 0, .running⟩).final.status =
      .halted ((block.eval memory ⟨regs, .running⟩).final.regs output) at hstatus
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hs, hv] using hm.2.1
  · simpa only [hv] using hstatus
  · exact hm.2.2.1.trans ht
  · simpa only [List.length_append, Block.compile_length, List.length_cons,
      List.length_nil] using hm.2.2.2
  · intro r hr
    rw [congrFun hregs r]
    exact Block.eval_frame memory block allowed writes r hr ⟨regs, .running⟩

theorem rankWordBlock_machine (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (target : Bool) (limit : Nat) (regs : Registers)
    (hm : MetadataMatches shape regs) (hword : regs 256 = bitsToNatLE word)
    (hlength : regs 257 = word.length) (hlimit : regs 258 = limit)
    (htarget : regs 259 = if target then 1 else 0) :
    let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21
      (packedFringeChunkBits shape.size) target word limit
    let actual := run memory ((rankWordBlock reader).compileAt 0 ++ [.halt 260])
      (502 + 8 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧
    actual.steps ≤ 502 + 8 * reader.size ∧
    (∀ r, ¬ RankWordWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace := by
  have hs := rankWordBlock_source shape memory reader hreader hwrites word target limit regs
    hm hword hlength hlimit htarget
  have hc := rank_compile_with_halt (rankWordBlock reader) 260 memory regs _ _ RankWordWrites
    (rankWordBlock_writes reader hwrites) hs.1 hs.2.1 hs.2.2.1
  have hsize : (rankWordBlock reader).size + 1 = 502 + 8 * reader.size := by
    rw [rankWordBlock_size]; omega
  rw [hsize] at hc
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, hs.2.2.2⟩

theorem rankSeedRead_writes (reader : Block) (hwrites : ReaderWrites reader)
    (segment index output : Nat) :
    (rankSeedRead reader segment index output).WritesOnly
      (fun r => r = output ∨ (8192 ≤ r ∧ r < 8271)) := by
  have hr : reader.WritesOnly (fun r => r = output ∨ (8192 ≤ r ∧ r < 8271)) :=
    Block.WritesOnly.mono reader hwrites (by intro r h; exact Or.inr ⟨by omega, h.2⟩)
  simpa [rankSeedRead, Block.sequence, Block.WritesOnly, Action.destination] using hr

theorem rankSeedRead_frame (reader : Block) (hwrites : ReaderWrites reader)
    (segment index output : Nat) (memory : Memory) (s : Data) (r : Nat)
    (outside : r ≠ output ∧ (r < 8192 ∨ 8271 ≤ r)) :
    ((rankSeedRead reader segment index output).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (rankSeedRead_writes reader hwrites segment index output)
    r (by omega) s

theorem rankSeedRead_metadata (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hwrites : ReaderWrites reader) (segment index output : Nat) (houtput : 190 ≤ output)
    (s : Data) (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((rankSeedRead reader segment index output).eval memory s).final.regs :=
  writes_metadata shape memory _ _ (rankSeedRead_writes reader hwrites segment index output)
    (by intro r hlo hhi; omega) s hm

/-- A fixed inlined logical reader call, useful to rank and other callers.
Its source register identifiers and destination are compile-time operands. -/
theorem rankSeedRead_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (segment index output : Nat)
    (hindex : index < 8192) (houtput : output < 8192)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (rankSeedRead reader segment index output).eval memory ⟨regs, .running⟩
    let expected := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
      (regs segment) (regs index)
    actual.final.status = .running ∧ actual.final.regs output = logicalPacket expected ∧
    actual.final.regs 8195 = logicalLength expected ∧
    actual.reads = readerReceipts shape memory (regs segment) (regs index) := by
  let prepared := (regs.write 8192 (regs segment)).write 8193 (regs index)
  have hp : MetadataMatches shape prepared :=
    MetadataMatches.write shape _
      (MetadataMatches.write shape regs hm 8192 (regs segment) (Or.inr (by decide)))
      8193 (regs index) (Or.inr (by decide))
  have hr := hreader prepared hp
  generalize he : reader.eval memory ⟨prepared, .running⟩ = read at hr
  rcases read with ⟨⟨rr, rst⟩, receipts⟩
  dsimp only at hr
  obtain ⟨hrst, hpacket, hlength, hreceipts, _hframe⟩ := hr
  subst rst
  simp [prepared, Registers.write] at he hpacket hlength hreceipts
  have hne : index ≠ 8192 := by omega
  have hout : 8195 ≠ output := by omega
  simp [rankSeedRead, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_move, eval_skip, Registers.write, he, hne, hout, hpacket, hlength, hreceipts]

theorem rankInit_writes : rankInit.WritesOnly (fun r => 360 ≤ r ∧ r < 371) := by
  simp [rankInit, Block.sequence, Block.WritesOnly, Action.destination, minBlock]

theorem rankInit_source (memory : Memory) (regs : Registers) :
    let actual := rankInit.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 360 = 0 ∧
    actual.final.regs 361 = min (regs 352) (regs 353) ∧
    actual.final.regs 362 = min (regs 352) (regs 353) / regs 354 ∧
    actual.final.regs 363 = min (regs 352) (regs 353) / regs 354 / regs 355 ∧
    actual.final.regs 370 = 1 := by
  have hmin (r : Registers) := minBlock_source 361 352 353 369 memory r (by decide) (by decide)
  simp [rankInit, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_constant, eval_arithmetic, eval_skip, hmin, Registers.write, Arithmetic.eval]

theorem rankPrepareWord_writes :
    rankPrepareWord.WritesOnly (fun r => (256 ≤ r ∧ r < 260) ∨ r = 368 ∨ r = 369) := by
  simp [rankPrepareWord, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]

theorem rankPrepareWord_source (memory : Memory) (regs : Registers) :
    let actual := rankPrepareWord.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
    actual.final.regs 256 = regs 366 - regs 370 ∧ actual.final.regs 257 = regs 367 ∧
    actual.final.regs 258 = regs 361 - regs 362 * regs 354 ∧ actual.final.regs 259 = regs 359 := by
  have hsub1 (r : Registers) := natSubBlock_source 256 366 370 369 memory r (by decide) (by decide)
  have hsub2 (r : Registers) := natSubBlock_source 258 361 368 369 memory r (by decide) (by decide)
  simp [rankPrepareWord, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_move, eval_arithmetic, eval_skip, hsub1, hsub2, Registers.write, Arithmetic.eval]

theorem rankCombine_source (memory : Memory) (regs : Registers) :
    let actual := rankCombine.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
    actual.final.regs 360 = (regs 364 - regs 370) + (regs 365 - regs 370) + regs 260 := by
  have hsub1 (r : Registers) := natSubBlock_source 364 364 370 369 memory r (by decide) (by decide)
  have hsub2 (r : Registers) := natSubBlock_source 365 365 370 369 memory r (by decide) (by decide)
  simp [rankCombine, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_arithmetic, eval_skip, hsub1, hsub2, Registers.write, Arithmetic.eval]

theorem rankFinish_missing (reader : Block) (memory : Memory) (regs : Registers)
    (hmissing : regs 364 = 0 ∨ regs 365 = 0 ∨ regs 366 = 0) :
    (rankFinish reader).eval memory ⟨regs, .running⟩ = ⟨⟨regs, .running⟩, []⟩ := by
  rcases hmissing with h | h | h <;>
    simp [rankFinish, eval_ifZero, eval_skip, h]

theorem rankFinish_present (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (super delta : Nat)
    (word : List Bool) (target : Bool) (hsuper : regs 364 = super + 1)
    (hdelta : regs 365 = delta + 1) (hword : regs 366 = bitsToNatLE word + 1)
    (hlength : regs 367 = word.length) (hone : regs 370 = 1)
    (htarget : regs 359 = if target then 1 else 0) :
    let actual := (rankFinish reader).eval memory ⟨regs, .running⟩
    let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21
      (packedFringeChunkBits shape.size) target word (regs 361 - regs 362 * regs 354)
    actual.final.status = .running ∧
    actual.final.regs 360 = super + delta + expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace := by
  have hp := rankPrepareWord_source memory regs
  have hmeta := writes_metadata shape memory rankPrepareWord _ rankPrepareWord_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  have hf (r : Nat) (ho : ¬ ((256 ≤ r ∧ r < 260) ∨ r = 368 ∨ r = 369)) :=
    Block.eval_frame memory rankPrepareWord _ rankPrepareWord_writes r ho ⟨regs, .running⟩
  generalize heP : rankPrepareWord.eval memory ⟨regs, .running⟩ = prepared at hp hmeta hf
  rcases prepared with ⟨⟨pr, pst⟩, preceipts⟩
  dsimp only at hp hmeta hf
  obtain ⟨hpst, hpr, hpword, hplen, hplimit, hptarget⟩ := hp
  subst pst
  subst preceipts
  have hw := rankWordBlock_source shape memory reader hreader hwrites word target
    (regs 361 - regs 362 * regs 354) pr hmeta
    (by rw [hpword, hword, hone]; omega) (hplen.trans hlength) hplimit (hptarget.trans htarget)
  have hwf (r : Nat) (ho : ¬ RankWordWrites r) :=
    rankWordBlock_frame reader hwrites memory ⟨pr, .running⟩ r ho
  generalize heW : (rankWordBlock reader).eval memory ⟨pr, .running⟩ = ranked at hw hwf
  rcases ranked with ⟨⟨wr, wst⟩, wreceipts⟩
  dsimp only at hw hwf
  obtain ⟨hwst, hwvalue, hwreads, _hreadonly⟩ := hw
  subst wst
  have hs364 : wr 364 = super + 1 := by
    rw [hwf 364 (by simp [RankWordWrites]), hf 364 (by omega)]; exact hsuper
  have hs365 : wr 365 = delta + 1 := by
    rw [hwf 365 (by simp [RankWordWrites]), hf 365 (by omega)]; exact hdelta
  have hs370 : wr 370 = 1 := by
    rw [hwf 370 (by simp [RankWordWrites]), hf 370 (by omega)]; exact hone
  have hc := rankCombine_source memory wr
  generalize heC : rankCombine.eval memory ⟨wr, .running⟩ = combined at hc
  rcases combined with ⟨⟨cr, cst⟩, creceipts⟩
  dsimp only at hc
  obtain ⟨hcst, hcr, hcvalue⟩ := hc
  subst cst
  subst creceipts
  have hpositive : (Block.seq rankPrepareWord (.seq (rankWordBlock reader) rankCombine)).eval
      memory ⟨regs, .running⟩ = ⟨⟨cr, .running⟩, wreceipts⟩ := by
    have ht := eval_seq_of_results memory (rankWordBlock reader) rankCombine
      ⟨pr, .running⟩ _ _ heW heC
    have hp := eval_seq_of_results memory rankPrepareWord (.seq (rankWordBlock reader) rankCombine)
      ⟨regs, .running⟩ _ _ heP ht
    simpa only [List.append_nil, List.nil_append] using hp
  have heval : (rankFinish reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨cr, .running⟩, wreceipts⟩ := by
    simp only [rankFinish, eval_ifZero, hsuper, hdelta, hword,
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
    exact hpositive
  rw [heval]
  dsimp only
  refine ⟨rfl, ?_, hwreads⟩
  rw [hcvalue, hs364, hs365, hs370, hwvalue]
  simp only [Nat.add_sub_cancel]

theorem rankSeeds_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (rankSeeds reader).WritesOnly
      (fun r => (360 ≤ r ∧ r < 371) ∨ (8192 ≤ r ∧ r < 8271)) := by
  have hr : reader.WritesOnly
      (fun r => (360 ≤ r ∧ r < 371) ∨ (8192 ≤ r ∧ r < 8271)) :=
    Block.WritesOnly.mono reader hwrites (by intro r h; exact Or.inr ⟨by omega, h.2⟩)
  simpa [rankSeeds, rankInit, rankSeedRead, Block.sequence, Block.WritesOnly,
    Action.destination, minBlock] using And.intro hr (And.intro hr hr)

theorem rankSeeds_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (rankSeeds reader).eval memory ⟨regs, .running⟩
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let e := min (regs 352) (regs 353)
    let b := e / regs 354
    let s := b / regs 355
    actual.final.status = .running ∧ actual.final.regs 360 = 0 ∧
    actual.final.regs 361 = e ∧ actual.final.regs 362 = b ∧
    actual.final.regs 363 = s ∧ actual.final.regs 370 = 1 ∧
    actual.final.regs 364 = logicalPacket (store.readWord? (regs 356) s) ∧
    actual.final.regs 365 = logicalPacket (store.readWord? (regs 357) b) ∧
    actual.final.regs 366 = logicalPacket (store.readWord? (regs 358) b) ∧
    actual.final.regs 367 = logicalLength (store.readWord? (regs 358) b) ∧
    actual.reads = readerReceipts shape memory (regs 356) s ++
      readerReceipts shape memory (regs 357) b ++ readerReceipts shape memory (regs 358) b := by
  have hi := rankInit_source memory regs
  have him := writes_metadata shape memory rankInit _ rankInit_writes
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  have hif (r : Nat) (ho : r < 360 ∨ 371 ≤ r) :=
    Block.eval_frame memory rankInit _ rankInit_writes r (by omega) ⟨regs, .running⟩
  generalize heI : rankInit.eval memory ⟨regs, .running⟩ = initialized at hi him hif
  rcases initialized with ⟨⟨ir, ist⟩, itr⟩
  dsimp only at hi him hif
  obtain ⟨his, hit, hi0, hie, hib, hisi, hi1⟩ := hi
  subst ist
  subst itr
  have ha := rankSeedRead_source shape memory reader hreader 356 363 364
    (by decide) (by decide) ir him
  have ham := rankSeedRead_metadata shape memory reader hwrites 356 363 364
    (by decide) ⟨ir, .running⟩ him
  have haf (r : Nat) (ho : r ≠ 364 ∧ r < 8192) :=
    rankSeedRead_frame reader hwrites 356 363 364 memory ⟨ir, .running⟩ r ⟨ho.1, Or.inl ho.2⟩
  generalize heA : (rankSeedRead reader 356 363 364).eval memory ⟨ir, .running⟩ = first
    at ha ham haf
  rcases first with ⟨⟨ar, ast⟩, atr⟩
  dsimp only at ha ham haf
  obtain ⟨has, hap, _hal, hat⟩ := ha
  subst ast
  have hb := rankSeedRead_source shape memory reader hreader 357 362 365
    (by decide) (by decide) ar ham
  have hbm := rankSeedRead_metadata shape memory reader hwrites 357 362 365
    (by decide) ⟨ar, .running⟩ ham
  have hbf (r : Nat) (ho : r ≠ 365 ∧ r < 8192) :=
    rankSeedRead_frame reader hwrites 357 362 365 memory ⟨ar, .running⟩ r ⟨ho.1, Or.inl ho.2⟩
  generalize heB : (rankSeedRead reader 357 362 365).eval memory ⟨ar, .running⟩ = second
    at hb hbm hbf
  rcases second with ⟨⟨br, bst⟩, btr⟩
  dsimp only at hb hbm hbf
  obtain ⟨hbs, hbp, _hbl, hbt⟩ := hb
  subst bst
  have hc := rankSeedRead_source shape memory reader hreader 358 362 366
    (by decide) (by decide) br hbm
  have hcf (r : Nat) (ho : r ≠ 366 ∧ r < 8192) :=
    rankSeedRead_frame reader hwrites 358 362 366 memory ⟨br, .running⟩ r ⟨ho.1, Or.inl ho.2⟩
  generalize heC : (rankSeedRead reader 358 362 366).eval memory ⟨br, .running⟩ = third
    at hc hcf
  rcases third with ⟨⟨cr, cst⟩, ctr⟩
  dsimp only at hc hcf
  obtain ⟨hcs, hcp, hcl, hct⟩ := hc
  subst cst
  have ha356 : ir 356 = regs 356 := hif 356 (by omega)
  have ha357 : ar 357 = regs 357 := (haf 357 (by omega)).trans (hif 357 (by omega))
  have ha362 : ar 362 = min (regs 352) (regs 353) / regs 354 := (haf 362 (by omega)).trans hib
  have hb358 : br 358 = regs 358 :=
    (hbf 358 (by omega)).trans ((haf 358 (by omega)).trans (hif 358 (by omega)))
  have hb362 : br 362 = min (regs 352) (regs 353) / regs 354 := (hbf 362 (by omega)).trans ha362
  rw [ha356, hisi] at hap hat
  rw [ha357, ha362] at hbp hbt
  rw [hb358, hb362] at hcp hcl hct
  have heval : (rankSeeds reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨cr.write 367 (cr 8195), .running⟩, atr ++ btr ++ ctr⟩ := by
    unfold rankSeeds
    have ht : (Block.sequence [.action (.move 367 8195)]).eval memory ⟨cr, .running⟩ =
        ⟨⟨cr.write 367 (cr 8195), .running⟩, []⟩ := rfl
    have hc := eval_seq_of_results memory (rankSeedRead reader 358 362 366) _
      ⟨br, .running⟩ _ _ heC ht
    have hb := eval_seq_of_results memory (rankSeedRead reader 357 362 365) _
      ⟨ar, .running⟩ _ _ heB hc
    have ha := eval_seq_of_results memory (rankSeedRead reader 356 363 364) _
      ⟨ir, .running⟩ _ _ heA hb
    have hi := eval_seq_of_results memory rankInit _ ⟨regs, .running⟩ _ _ heI ha
    simpa only [Block.sequence, List.foldr_cons, List.foldr_nil, List.append_nil,
      List.nil_append, List.append_assoc] using hi
  rw [heval]
  dsimp only
  simp only [Registers.write, reduceIte]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcp, hcl, ?_⟩
  · rw [hcf 360 (by omega), hbf 360 (by omega), haf 360 (by omega)]; exact hi0
  · rw [hcf 361 (by omega), hbf 361 (by omega), haf 361 (by omega)]; exact hie
  · rw [hcf 362 (by omega)]; exact hb362
  · rw [hcf 363 (by omega), hbf 363 (by omega), haf 363 (by omega)]; exact hisi
  · rw [hcf 370 (by omega), hbf 370 (by omega), haf 370 (by omega)]; exact hi1
  · rw [hcf 364 (by omega), hbf 364 (by omega)]; exact hap
  · rw [hcf 365 (by omega)]; exact hbp
  · rw [hat, hbt, hct]

private theorem rankFinish_zero_summary (reader : Block) (memory : Memory) (regs : Registers)
    (hz : regs 360 = 0) (hmissing : regs 364 = 0 ∨ regs 365 = 0 ∨ regs 366 = 0) :
    let actual := (rankFinish reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 360 = 0 ∧ actual.reads = [] := by
  rw [rankFinish_missing reader memory regs hmissing]
  exact ⟨rfl, hz, rfl⟩

private theorem rankFinish_options (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs)
    (superWord deltaWord word : Option (List Bool)) (target : Bool)
    (hs : regs 364 = logicalPacket superWord) (hd : regs 365 = logicalPacket deltaWord)
    (hw : regs 366 = logicalPacket word) (hl : regs 367 = logicalLength word)
    (hone : regs 370 = 1) (hz : regs 360 = 0)
    (htarget : regs 359 = if target then 1 else 0) :
    let actual := (rankFinish reader).eval memory ⟨regs, .running⟩
    let expected := match superWord, deltaWord, word with
      | some super, some delta, some bits => WordRAM.TraceResult.map
          (fun localRank => bitsToNatLE super + bitsToNatLE delta + localRank)
          (bpChunkedWordRankTraceResultAtSegmentWithStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21
            (packedFringeChunkBits shape.size) target bits (regs 361 - regs 362 * regs 354))
      | _, _, _ => WordRAM.TraceResult.pure 0
    actual.final.status = .running ∧ actual.final.regs 360 = expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  cases superWord <;> cases deltaWord <;> cases word
  all_goals dsimp only
  all_goals first
    | exact ⟨(rankFinish_zero_summary reader memory regs hz (Or.inl hs)).1,
        (rankFinish_zero_summary reader memory regs hz (Or.inl hs)).2.1,
        (rankFinish_zero_summary reader memory regs hz (Or.inl hs)).2.2,
        by intro event he; cases he⟩
    | exact ⟨(rankFinish_zero_summary reader memory regs hz (Or.inr (Or.inl hd))).1,
        (rankFinish_zero_summary reader memory regs hz (Or.inr (Or.inl hd))).2.1,
        (rankFinish_zero_summary reader memory regs hz (Or.inr (Or.inl hd))).2.2,
        by intro event he; cases he⟩
    | exact ⟨(rankFinish_zero_summary reader memory regs hz (Or.inr (Or.inr hw))).1,
        (rankFinish_zero_summary reader memory regs hz (Or.inr (Or.inr hw))).2.1,
        (rankFinish_zero_summary reader memory regs hz (Or.inr (Or.inr hw))).2.2,
        by intro event he; cases he⟩
    | skip
  rename_i super delta bits
  have h := rankFinish_present shape memory reader hreader hwrites regs hm
    (bitsToNatLE super) (bitsToNatLE delta) bits target hs hd hw hl hone htarget
  simpa only [WordRAM.TraceResult.map, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
    List.append_nil] using
    And.intro h.1 (And.intro h.2.1 (And.intro h.2.2
      (rankFold_readOnly (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21
        (packedFringeChunkBits shape.size) target bits
        (bpWordRankEffLimit bits (regs 361 - regs 362 * regs 354)) 0
        (bpWordChunkCount (packedFringeChunkBits shape.size)
          (bpWordRankEffLimit bits (regs 361 - regs 362 * regs 354))) 0)))

/-- Whole rank performs the three seed reads in order before inspecting presence.
The statement imposes no successful-read or positive-geometry condition. -/
theorem rankBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (target : Bool) (regs : Registers) (hm : MetadataMatches shape regs)
    (htarget : regs 359 = if target then 1 else 0) :
    let actual := (rankBlock reader).eval memory ⟨regs, .running⟩
    let expected := packedRankRead (regs 356) (regs 357) (regs 358) 21
      (packedFringeChunkBits shape.size) target
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (regs 353) (regs 354) (regs 355) (regs 352)
    actual.final.status = .running ∧ actual.final.regs 360 = expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hs := rankSeeds_source shape memory reader hreader hwrites regs hm
  have hsm := writes_metadata shape memory (rankSeeds reader) _ (rankSeeds_writes reader hwrites)
    (by intro r hlo hhi; omega) ⟨regs, .running⟩ hm
  have hsf (r : Nat) (ho : r < 360) := Block.eval_frame memory (rankSeeds reader) _
    (rankSeeds_writes reader hwrites) r (by omega) ⟨regs, .running⟩
  generalize heS : (rankSeeds reader).eval memory ⟨regs, .running⟩ = seeded at hs hsm hsf
  rcases seeded with ⟨⟨sr, sst⟩, str⟩
  dsimp only at hs hsm hsf
  obtain ⟨hss, hs0, hse, hsb, _hsi, hs1, hsuper, hdelta, hword, hlength, hsreads⟩ := hs
  subst sst
  have hf := rankFinish_options shape memory reader hreader hwrites sr hsm _ _ _ target
    hsuper hdelta hword hlength hs1 hs0 ((hsf 359 (by decide)).trans htarget)
  rw [hse, hsb, hsf 354 (by decide)] at hf
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let e := min (regs 352) (regs 353)
  let b := e / regs 354
  let s := b / regs 355
  cases hsw : store.readWord? (regs 356) s <;>
    cases hdw : store.readWord? (regs 357) b <;>
    cases hww : store.readWord? (regs 358) b
  all_goals
    simp only [store, s, b, e] at hsw hdw hww
    simp only [hsw, hdw, hww, WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.pure, List.append_nil] at hf
    have hj := eval_seq_summary memory (rankSeeds reader) (rankFinish reader) regs _ 360 _
      (by rw [heS]) (by
        simp only [heS]
        exact ⟨hf.1, hf.2.1, rfl⟩)
    dsimp only at hj
    simp only [rankBlock, packedRankRead, bpChunkReadTraceResult, bpWordReadTraceResult,
      WordRAM.TraceResult.bind, WordRAM.TraceResult.map, WordRAM.TraceResult.pure,
      hsw, hdw, hww, Option.map_some, Option.map_none] at hj ⊢
    refine ⟨hj.1, hj.2.1, ?_, ?_⟩
    · rw [hj.2.2, hsreads, hf.2.2.1]
      simp only [logicalTraceReads, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append,
        List.nil_append]
    · intro event he
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | he
      all_goals first | trivial | exact hf.2.2.2 event he


theorem rankLongBlock_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (rankLongBlock reader).WritesOnly RankWrapperWrites := by
  have hr : (rankBlock reader).WritesOnly RankWrapperWrites :=
    Block.WritesOnly.mono _ (rankBlock_writes reader hwrites) (by
      intro r h
      unfold RankWrites at h
      unfold RankWrapperWrites
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨by omega, h.2⟩)
      · exact Or.inr (Or.inr h))
  simpa [rankLongBlock, Block.sequence, Block.WritesOnly, Action.destination,
    RankWrapperWrites] using hr


private theorem rankLongPrefix_eval (memory : Memory) (tail : Block)
    (regs final : Registers) (receipts : List Receipt)
    (htail : tail.eval memory ⟨((((((regs.write 353 (regs 28)).write 354 (regs 30)).write 355 1).write
    356 9).write 357 10).write 358 11).write 359 1, .running⟩ =
      ⟨⟨final, .running⟩, receipts⟩) :
    (Block.sequence [.action (.move 353 28), .action (.move 354 30),
      .action (.constant 355 1), .action (.constant 356 9),
      .action (.constant 357 10), .action (.constant 358 11),
      .action (.constant 359 1), tail]).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, receipts⟩ := by
  simp [Block.sequence, Block.eval_seq, eval_move, eval_constant,
    eval_skip, Evaluation.bind, Registers.write, htail]



private theorem rankSparsePrefix_eval (memory : Memory) (tail : Block)
    (regs final : Registers) (receipts : List Receipt)
    (htail : tail.eval memory ⟨((((((regs.write 353 (regs 29)).write 354 (regs 31)).write 355 1).write
    356 13).write 357 14).write 358 15).write 359 1, .running⟩ =
      ⟨⟨final, .running⟩, receipts⟩) :
    (Block.sequence [.action (.move 353 29), .action (.move 354 31),
      .action (.constant 355 1), .action (.constant 356 13),
      .action (.constant 357 14), .action (.constant 358 15),
      .action (.constant 359 1), tail]).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, receipts⟩ := by
  simp [Block.sequence, Block.eval_seq, eval_move, eval_constant,
    eval_skip, Evaluation.bind, Registers.write, htail]



private theorem rankClosePrefix_eval (memory : Memory) (tail : Block)
    (regs final : Registers) (receipts : List Receipt)
    (htail : tail.eval memory ⟨(((((((regs.write 369 2).write 353 (regs 16 * 2)).write 354 (regs 32)).write
    355 (regs 32)).write 356 17).write 357 18).write 358 19).write 359 0, .running⟩ =
      ⟨⟨final, .running⟩, receipts⟩) :
    (Block.sequence [.action (.constant 369 2), .action (.arithmetic .mul 353 16 369),
      .action (.move 354 32), .action (.move 355 32),
      .action (.constant 356 17), .action (.constant 357 18),
      .action (.constant 358 19), .action (.constant 359 0), tail]).eval memory ⟨regs, .running⟩ =
      ⟨⟨final, .running⟩, receipts⟩ := by
  simp [Block.sequence, Block.eval_seq, eval_move, eval_constant, eval_arithmetic,
    eval_skip, Evaluation.bind, Arithmetic.eval, Registers.write, htail]


theorem rankLongBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (rankLongBlock reader).eval memory ⟨regs, .running⟩
    let expected := packedRankRead 9 10 11 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSuperSlots shape.size) (packedLongFlagWordSize shape.size) 1 (regs 352)
    actual.final.status = .running ∧ actual.final.regs 360 = expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let pr := ((((((regs.write 353 (regs 28)).write 354 (regs 30)).write 355 1).write
    356 9).write 357 10).write 358 11).write 359 1
  have hpframe (r : Nat) (hr : r < 353) : pr r = regs r := by
    simp only [pr, Registers.write, if_neg (show r ≠ 353 by omega),
      if_neg (show r ≠ 354 by omega), if_neg (show r ≠ 355 by omega),
      if_neg (show r ≠ 356 by omega), if_neg (show r ≠ 357 by omega),
      if_neg (show r ≠ 358 by omega), if_neg (show r ≠ 359 by omega)]
  have hpm : MetadataMatches shape pr := by
    intro i hi
    rw [hpframe (16 + i) (by omega)]
    exact hm i hi
  have hlen : regs 28 = packedSuperSlots shape.size := hm 12 (by decide)
  have hwidth : regs 30 = packedLongFlagWordSize shape.size := hm 14 (by decide)
  have hs := rankBlock_source shape memory reader hreader hwrites true pr hpm rfl
  generalize he : (rankBlock reader).eval memory ⟨pr, .running⟩ = ranked at hs
  simp only [pr, Registers.write, reduceIte, hlen, hwidth] at hs
  rcases ranked with ⟨⟨rr, rst⟩, receipts⟩
  dsimp only at hs
  obtain ⟨hst, hv, ht, hro⟩ := hs
  subst rst
  have heval : (rankLongBlock reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨rr, .running⟩, receipts⟩ :=
    rankLongPrefix_eval memory (rankBlock reader) regs rr receipts he
  rw [heval]
  exact ⟨rfl, hv, ht, hro⟩



theorem rankSparseBlock_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (rankSparseBlock reader).WritesOnly RankWrapperWrites := by
  have hr : (rankBlock reader).WritesOnly RankWrapperWrites :=
    Block.WritesOnly.mono _ (rankBlock_writes reader hwrites) (by
      intro r h
      unfold RankWrites at h
      unfold RankWrapperWrites
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨by omega, h.2⟩)
      · exact Or.inr (Or.inr h))
  simpa [rankSparseBlock, Block.sequence, Block.WritesOnly, Action.destination,
    RankWrapperWrites] using hr

theorem rankSparseBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (rankSparseBlock reader).eval memory ⟨regs, .running⟩
    let expected := packedRankRead 13 14 15 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSparseSlots shape.size) (packedSparseWordSize shape.size) 1 (regs 352)
    actual.final.status = .running ∧ actual.final.regs 360 = expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let pr := ((((((regs.write 353 (regs 29)).write 354 (regs 31)).write 355 1).write
    356 13).write 357 14).write 358 15).write 359 1
  have hpframe (r : Nat) (hr : r < 353) : pr r = regs r := by
    simp only [pr, Registers.write, if_neg (show r ≠ 353 by omega),
      if_neg (show r ≠ 354 by omega), if_neg (show r ≠ 355 by omega),
      if_neg (show r ≠ 356 by omega), if_neg (show r ≠ 357 by omega),
      if_neg (show r ≠ 358 by omega), if_neg (show r ≠ 359 by omega)]
  have hpm : MetadataMatches shape pr := by
    intro i hi
    rw [hpframe (16 + i) (by omega)]
    exact hm i hi
  have hlen : regs 29 = packedSparseSlots shape.size := hm 13 (by decide)
  have hwidth : regs 31 = packedSparseWordSize shape.size := hm 15 (by decide)
  have hs := rankBlock_source shape memory reader hreader hwrites true pr hpm rfl
  generalize he : (rankBlock reader).eval memory ⟨pr, .running⟩ = ranked at hs
  simp only [pr, Registers.write, reduceIte, hlen, hwidth] at hs
  rcases ranked with ⟨⟨rr, rst⟩, receipts⟩
  dsimp only at hs
  obtain ⟨hst, hv, ht, hro⟩ := hs
  subst rst
  have heval : (rankSparseBlock reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨rr, .running⟩, receipts⟩ :=
    rankSparsePrefix_eval memory (rankBlock reader) regs rr receipts he
  rw [heval]
  exact ⟨rfl, hv, ht, hro⟩


theorem rankCloseBlock_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (rankCloseBlock reader).WritesOnly RankWrapperWrites := by
  have hr : (rankBlock reader).WritesOnly RankWrapperWrites :=
    Block.WritesOnly.mono _ (rankBlock_writes reader hwrites) (by
      intro r h
      unfold RankWrites at h
      unfold RankWrapperWrites
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨by omega, h.2⟩)
      · exact Or.inr (Or.inr h))
  simpa [rankCloseBlock, Block.sequence, Block.WritesOnly, Action.destination,
    RankWrapperWrites] using hr

theorem rankCloseBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (rankCloseBlock reader).eval memory ⟨regs, .running⟩
    let expected := packedRankCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 352)
    actual.final.status = .running ∧ actual.final.regs 360 = expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let pr := (((((((regs.write 369 2).write 353 (regs 16 * 2)).write 354 (regs 32)).write
    355 (regs 32)).write 356 17).write 357 18).write 358 19).write 359 0
  have hpframe (r : Nat) (hr : r < 353) : pr r = regs r := by
    simp only [pr, Registers.write, if_neg (show r ≠ 353 by omega),
      if_neg (show r ≠ 354 by omega), if_neg (show r ≠ 355 by omega),
      if_neg (show r ≠ 356 by omega), if_neg (show r ≠ 357 by omega),
      if_neg (show r ≠ 358 by omega), if_neg (show r ≠ 359 by omega),
      if_neg (show r ≠ 369 by omega)]
  have hpm : MetadataMatches shape pr := by
    intro i hi
    rw [hpframe (16 + i) (by omega)]
    exact hm i hi
  have hn : regs 16 = shape.size := hm 0 (by decide)
  have hwidth : regs 32 = packedBpCodeWordWidth shape.size := hm 16 (by decide)
  have hs := rankBlock_source shape memory reader hreader hwrites false pr hpm rfl
  generalize he : (rankBlock reader).eval memory ⟨pr, .running⟩ = ranked at hs
  simp only [pr, Registers.write, reduceIte, hn, hwidth, Nat.mul_comm] at hs
  rcases ranked with ⟨⟨rr, rst⟩, receipts⟩
  dsimp only at hs
  obtain ⟨hst, hv, ht, hro⟩ := hs
  subst rst
  have heval : (rankCloseBlock reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨rr, .running⟩, receipts⟩ :=
    rankClosePrefix_eval memory (rankBlock reader) regs rr receipts he
  rw [heval]
  exact ⟨rfl, hv, ht, hro⟩


theorem rankBlock_machine (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (target : Bool) (regs : Registers) (hm : MetadataMatches shape regs)
    (htarget : regs 359 = if target then 1 else 0) :
    let expected := packedRankRead (regs 356) (regs 357) (regs 358) 21
      (packedFringeChunkBits shape.size) target
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (regs 353) (regs 354) (regs 355) (regs 352)
    let actual := run memory ((rankBlock reader).compileAt 0 ++ [.halt 360])
      (552 + 11 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧
    actual.steps ≤ 552 + 11 * reader.size ∧
    (∀ r, ¬ RankWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace := by
  have hs := rankBlock_source shape memory reader hreader hwrites target regs hm htarget
  have hc := rank_compile_with_halt (rankBlock reader) 360 memory regs _ _ RankWrites
    (rankBlock_writes reader hwrites) hs.1 hs.2.1 hs.2.2.1
  have hsize : (rankBlock reader).size + 1 = 552 + 11 * reader.size := by
    rw [rankBlock_size]; omega
  rw [hsize] at hc
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, hs.2.2.2⟩



@[simp] theorem rankLongBlock_size (reader : Block) :
    (rankLongBlock reader).size = 558 + 11 * reader.size := by
  simp [rankLongBlock, Block.sequence, Block.size, rankBlock_size]
  omega

theorem rankLongBlock_frame (reader : Block) (hwrites : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ RankWrapperWrites r) :
    ((rankLongBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (rankLongBlock_writes reader hwrites) r outside s


theorem rankLongBlock_machine (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
     (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedRankRead 9 10 11 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSuperSlots shape.size) (packedLongFlagWordSize shape.size) 1 (regs 352)
    let actual := run memory ((rankLongBlock reader).compileAt 0 ++ [.halt 360])
      (559 + 11 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧
    actual.steps ≤ 559 + 11 * reader.size ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace := by
  have hs := rankLongBlock_source shape memory reader hreader hwrites regs hm
  have hc := rank_compile_with_halt (rankLongBlock reader) 360 memory regs _ _ RankWrapperWrites
    (rankLongBlock_writes reader hwrites) hs.1 hs.2.1 hs.2.2.1
  have hsize : (rankLongBlock reader).size + 1 = 559 + 11 * reader.size := by
    rw [rankLongBlock_size]; omega
  rw [hsize] at hc
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, hs.2.2.2⟩



@[simp] theorem rankSparseBlock_size (reader : Block) :
    (rankSparseBlock reader).size = 558 + 11 * reader.size := by
  simp [rankSparseBlock, Block.sequence, Block.size, rankBlock_size]
  omega

theorem rankSparseBlock_frame (reader : Block) (hwrites : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ RankWrapperWrites r) :
    ((rankSparseBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (rankSparseBlock_writes reader hwrites) r outside s


theorem rankSparseBlock_machine (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
     (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedRankRead 13 14 15 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSparseSlots shape.size) (packedSparseWordSize shape.size) 1 (regs 352)
    let actual := run memory ((rankSparseBlock reader).compileAt 0 ++ [.halt 360])
      (559 + 11 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧
    actual.steps ≤ 559 + 11 * reader.size ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace := by
  have hs := rankSparseBlock_source shape memory reader hreader hwrites regs hm
  have hc := rank_compile_with_halt (rankSparseBlock reader) 360 memory regs _ _ RankWrapperWrites
    (rankSparseBlock_writes reader hwrites) hs.1 hs.2.1 hs.2.2.1
  have hsize : (rankSparseBlock reader).size + 1 = 559 + 11 * reader.size := by
    rw [rankSparseBlock_size]; omega
  rw [hsize] at hc
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, hs.2.2.2⟩



@[simp] theorem rankCloseBlock_size (reader : Block) :
    (rankCloseBlock reader).size = 559 + 11 * reader.size := by
  simp [rankCloseBlock, Block.sequence, Block.size, rankBlock_size]
  omega

theorem rankCloseBlock_frame (reader : Block) (hwrites : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ RankWrapperWrites r) :
    ((rankCloseBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (rankCloseBlock_writes reader hwrites) r outside s


theorem rankCloseBlock_machine (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
     (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedRankCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 352)
    let actual := run memory ((rankCloseBlock reader).compileAt 0 ++ [.halt 360])
      (560 + 11 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧
    actual.steps ≤ 560 + 11 * reader.size ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace := by
  have hs := rankCloseBlock_source shape memory reader hreader hwrites regs hm
  have hc := rank_compile_with_halt (rankCloseBlock reader) 360 memory regs _ _ RankWrapperWrites
    (rankCloseBlock_writes reader hwrites) hs.1 hs.2.1 hs.2.2.1
  have hsize : (rankCloseBlock reader).size + 1 = 560 + 11 * reader.size := by
    rw [rankCloseBlock_size]; omega
  rw [hsize] at hc
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, hs.2.2.2⟩


/-- Empty input and zero limit still issue the reference protocol's one
zero-length chunk lookup. False-bit rank is zero even if that lookup fails. -/
theorem rankWordBlock_empty (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs)
    (hword : regs 256 = 0) (hlength : regs 257 = 0)
    (hlimit : regs 258 = 0) (htarget : regs 259 = 0) :
    let actual := (rankWordBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 260 = 0 ∧
    actual.reads = readerReceipts shape memory 21 0 := by
  have h := rankWordBlock_source shape memory reader hreader hwrites [] false 0 regs
    hm hword hlength hlimit htarget
  have htrace := h.2.2.1
  have hvalue := h.2.1
  simp [bpChunkedWordRankTraceResultAtSegmentWithStore, bpWordRankEffLimit, bpWordChunkCount,
    bpChunkedWordRankTraceFromWithStore, bpChunkReadTraceResult,
    bpFringeChunkSlot, bpFringeWindowChunkValue, bpWordChunkSliceLen, bitsToNatLE,
    bpWordRankStepDecoded, bpChunkRankOfEntry, WordRAM.TraceResult.bind,
    WordRAM.TraceResult.pure, logicalTraceReads] at hvalue htrace
  exact ⟨h.1, hvalue, htrace⟩

/-- A concrete ragged word and an overlong limit consume the same public source
theorem, without a word-length divisibility premise. -/
theorem rankWordBlock_ragged (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs)
    (hword : regs 256 = 5) (hlength : regs 257 = 3)
    (hlimit : regs 258 = 5) (htarget : regs 259 = 1) :
    let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21
      (packedFringeChunkBits shape.size) true [true, false, true] 5
    let actual := run memory ((rankWordBlock reader).compileAt 0 ++ [.halt 260])
      (502 + 8 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧
    actual.steps ≤ 502 + 8 * reader.size ∧
    (∀ r, ¬ RankWordWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace :=
  rankWordBlock_machine shape memory reader hreader hwrites [true, false, true] true 5 regs
    hm hword hlength hlimit htarget

theorem packedRankRead_missing_reference (store : WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment c : Nat) (target : Bool)
    (bitLength wordSize blocksPerSuper pos : Nat)
    (hmissing : store.readWord? superSegment (min pos bitLength / wordSize / blocksPerSuper) = none ∨
      store.readWord? blockSegment (min pos bitLength / wordSize) = none ∨
      store.readWord? wordSegment (min pos bitLength / wordSize) = none) :
    let expected := packedRankRead superSegment blockSegment wordSegment chunkSegment c target
      store bitLength wordSize blocksPerSuper pos
    expected.value = 0 ∧ expected.trace = [
      .readWord superSegment (min pos bitLength / wordSize / blocksPerSuper)
        (store.readWord? superSegment (min pos bitLength / wordSize / blocksPerSuper)),
      .readWord blockSegment (min pos bitLength / wordSize)
        (store.readWord? blockSegment (min pos bitLength / wordSize)),
      .readWord wordSegment (min pos bitLength / wordSize)
        (store.readWord? wordSegment (min pos bitLength / wordSize))] := by
  cases hs : store.readWord? superSegment (min pos bitLength / wordSize / blocksPerSuper) <;>
    cases hd : store.readWord? blockSegment (min pos bitLength / wordSize) <;>
    cases hw : store.readWord? wordSegment (min pos bitLength / wordSize)
  all_goals simp only [hs, hd, hw, Option.some_ne_none, or_self] at hmissing
  all_goals first | contradiction | skip
  all_goals simp [packedRankRead, bpChunkReadTraceResult, bpWordReadTraceResult,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.pure, hs, hd, hw]

theorem rankBlock_missing_seed (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (target : Bool) (regs : Registers) (hm : MetadataMatches shape regs)
    (htarget : regs 359 = if target then 1 else 0)
    (hmissing :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? (regs 356)
        (min (regs 352) (regs 353) / regs 354 / regs 355) = none ∨
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? (regs 357)
        (min (regs 352) (regs 353) / regs 354) = none ∨
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? (regs 358)
        (min (regs 352) (regs 353) / regs 354) = none) :
    let actual := run memory ((rankBlock reader).compileAt 0 ++ [.halt 360])
      (552 + 11 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some 0 ∧ actual.final.status = .halted 0 ∧
    actual.reads = readerReceipts shape memory (regs 356)
        (min (regs 352) (regs 353) / regs 354 / regs 355) ++
      readerReceipts shape memory (regs 357) (min (regs 352) (regs 353) / regs 354) ++
      readerReceipts shape memory (regs 358) (min (regs 352) (regs 353) / regs 354) ∧
    actual.steps ≤ 552 + 11 * reader.size ∧
    (∀ r, ¬ RankWrites r → actual.final.regs r = regs r) := by
  have he := packedRankRead_missing_reference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (regs 356) (regs 357) (regs 358) 21 (packedFringeChunkBits shape.size) target
    (regs 353) (regs 354) (regs 355) (regs 352) hmissing
  have ha := rankBlock_machine shape memory reader hreader hwrites target regs hm htarget
  dsimp only at he ha
  rw [he.1, he.2] at ha
  refine ⟨ha.1, ha.2.1, ?_, ha.2.2.2.1, ha.2.2.2.2.1⟩
  simpa only [logicalTraceReads, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc] using ha.2.2.1

theorem rankWordRepeat_zero_count (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (word : List Bool) (target : Bool) (c e acc : Nat) (regs : Registers)
    (hm : MetadataMatches shape regs) (hs : RankFoldState word target c e 0 0 acc regs) :
    let actual := (Block.repeat 8 (rankWordBody reader)).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 260 = acc ∧ actual.reads = [] := by
  have h := rankWordRepeat_source shape memory reader hreader hwrites word target c e
    0 8 0 acc regs hm hs (by decide)
  simpa only [Nat.sub_zero, bpChunkedWordRankTraceFromWithStore,
    WordRAM.TraceResult.pure, logicalTraceReads, List.flatMap_nil] using h


theorem rankCloseBlock_metadata (shape : CartesianShape) (reader : Block)
    (hwrites : ReaderWrites reader) (memory : Memory) (s : Data)
    (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((rankCloseBlock reader).eval memory s).final.regs :=
  writes_metadata shape memory _ _ (rankCloseBlock_writes reader hwrites)
    (by intro r hlo hhi; unfold RankWrapperWrites; omega) s hm



theorem rankLongBlock_metadata (shape : CartesianShape) (reader : Block)
    (hwrites : ReaderWrites reader) (memory : Memory) (s : Data)
    (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((rankLongBlock reader).eval memory s).final.regs :=
  writes_metadata shape memory _ _ (rankLongBlock_writes reader hwrites)
    (by intro r hlo hhi; unfold RankWrapperWrites; omega) s hm



theorem rankSparseBlock_metadata (shape : CartesianShape) (reader : Block)
    (hwrites : ReaderWrites reader) (memory : Memory) (s : Data)
    (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((rankSparseBlock reader).eval memory s).final.regs :=
  writes_metadata shape memory _ _ (rankSparseBlock_writes reader hwrites)
    (by intro r hlo hhi; unfold RankWrapperWrites; omega) s hm


/-- Independent typed consumers pin each canonical wrapper to the counted allocation. -/
theorem rankCloseBlock_sameAllocation (shape : CartesianShape) (reader : Block)
    (hr : ReaderCorrect shape (shapeMemory shape) reader) (hw : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedRankCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 352)
    let actual := run (shapeMemory shape) ((rankCloseBlock reader).compileAt 0 ++ [.halt 360])
      (560 + 11 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 560 + 11 * reader.size ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace :=
  rankCloseBlock_machine shape (shapeMemory shape) reader hr hw regs hm

theorem rankLongBlock_sameAllocation (shape : CartesianShape) (reader : Block)
    (hr : ReaderCorrect shape (shapeMemory shape) reader) (hw : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedRankRead 9 10 11 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSuperSlots shape.size) (packedLongFlagWordSize shape.size) 1 (regs 352)
    let actual := run (shapeMemory shape) ((rankLongBlock reader).compileAt 0 ++ [.halt 360])
      (559 + 11 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 559 + 11 * reader.size ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace :=
  rankLongBlock_machine shape (shapeMemory shape) reader hr hw regs hm

theorem rankSparseBlock_sameAllocation (shape : CartesianShape) (reader : Block)
    (hr : ReaderCorrect shape (shapeMemory shape) reader) (hw : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedRankRead 13 14 15 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSparseSlots shape.size) (packedSparseWordSize shape.size) 1 (regs 352)
    let actual := run (shapeMemory shape) ((rankSparseBlock reader).compileAt 0 ++ [.halt 360])
      (559 + 11 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 559 + 11 * reader.size ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace :=
  rankSparseBlock_machine shape (shapeMemory shape) reader hr hw regs hm


end RMQ.SuccinctFinal.PackedWordRAM
