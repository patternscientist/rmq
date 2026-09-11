import RMQ.Core.WordRAM.Packed.WindowProof
import RMQ.Core.WordRAM.Packed.InteriorReadProof
import RMQ.Core.WordRAM.Packed.CandidateProof
import RMQ.Core.WordRAM.Packed.RankProof

/-! # The fixed scalar fringe fold on the four charged window reads -/

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

def FringeAddressWrites (r : Nat) : Prop :=
  (1117 ≤ r ∧ r < 1123) ∨ r = 1126 ∨ r = 1132 ∨ r = 8192 ∨ r = 8193

theorem fringeAddressBlock_writes : fringeAddressBlock.WritesOnly FringeAddressWrites := by
  simp [fringeAddressBlock, fringeAddressRangeBlock, fringeAddressSlotBlock,
    Block.sequence, Block.WritesOnly, Action.destination,
    FringeAddressWrites, natSubBlock, minBlock]

theorem fringeAddressBlock_frame (memory : Memory) (s : Data) (r : Nat)
    (outside : ¬ FringeAddressWrites r) :
    (fringeAddressBlock.eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ fringeAddressBlock_writes r outside s

theorem fringeAddressBlock_source (memory : Memory) (regs : Registers)
    (hone : regs 1127 = 1) (hradix : regs 1128 = regs 34 + 1) :
    let actual := fringeAddressBlock.eval memory ⟨regs, .running⟩
    let j := regs 1116
    let c := regs 34
    let lo := min (regs 1109 - j * c) c
    let hi := min (regs 1110 + 1) ((j + 1) * c) - j * c
    let chunk := regs 1064 / 2 ^ (j * c) % 2 ^ c
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 8192 = 21 ∧
      actual.final.regs 8193 = (chunk * (c + 1) + lo) * (c + 1) + hi ∧
      actual.final.regs 1117 = j * c ∧ actual.final.regs 1118 = lo ∧
      actual.final.regs 1120 = hi := by
  have hsub1 (r : Registers) := natSubBlock_source 1118 1109 1117 1132 memory r (by decide) (by decide)
  have hsub2 (r : Registers) := natSubBlock_source 1120 1119 1117 1132 memory r (by decide) (by decide)
  have hmin1 (r : Registers) := minBlock_source 1118 1118 34 1132 memory r (by decide) (by decide)
  have hmin2 (r : Registers) := minBlock_source 1119 1119 1126 1132 memory r (by decide) (by decide)
  have shiftLeft_numeric (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b
  have shiftRight_numeric (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b
  simp [fringeAddressBlock, fringeAddressRangeBlock, fringeAddressSlotBlock,
    Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_constant, eval_arithmetic, eval_skip, hsub1, hsub2, hmin1, hmin2,
    Registers.write, Arithmetic.eval, hone, hradix, shiftLeft_numeric, shiftRight_numeric]

theorem fringeConsiderBlock_writes : fringeConsiderBlock.WritesOnly
    (fun r => (1113 ≤ r ∧ r < 1116) ∨ r = 1124 ∨ r = 1125 ∨ r = 1130 ∨ r = 1132) := by
  simp [fringeConsiderBlock, fringeKeepBestBlock, Block.sequence, Block.WritesOnly,
    Action.destination, natSubBlock]

theorem fringeConsiderBlock_source (memory : Memory) (regs : Registers) :
    let actual := fringeConsiderBlock.eval memory ⟨regs, .running⟩
    let score := regs 1112 + regs 1123 / regs 1128 % regs 1129 - regs 34
    let position := regs 1117 + regs 1123 % regs 1128
    actual.final.status = .running ∧ actual.reads = [] ∧
      candidateOfRegs 1113 actual.final.regs =
        bpFringeMergeCand (candidateOfRegs 1113 regs) (some (score, position)) := by
  have hsub (r : Registers) := natSubBlock_source 1124 1124 34 1132 memory r (by decide) (by decide)
  by_cases hz : regs 1113 = 0
  · simp [fringeConsiderBlock, fringeKeepBestBlock, Block.sequence, Block.eval_seq,
      Evaluation.bind, eval_constant, eval_arithmetic, eval_move, eval_ifZero, eval_skip,
      Arithmetic.eval, Registers.write, hsub, candidateOfRegs, bpFringeMergeCand, hz]
  · by_cases hbetter : regs 1112 + regs 1123 / regs 1128 % regs 1129 - regs 34 < regs 1114
    all_goals simp [fringeConsiderBlock, fringeKeepBestBlock, Block.sequence, Block.eval_seq,
      Evaluation.bind, eval_arithmetic, eval_comparison, eval_move, eval_ifZero, eval_skip,
      Arithmetic.eval, Comparison.eval, Registers.write, hsub, candidateOfRegs, bpFringeMergeCand, hz, hbetter]

theorem fringeAdvanceBlock_writes : fringeAdvanceBlock.WritesOnly
    (fun r => r = 1112 ∨ r = 1116 ∨ r = 1126 ∨ r = 1132) := by
  simp [fringeAdvanceBlock, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]

theorem fringeAdvanceBlock_source (memory : Memory) (regs : Registers) (hone : regs 1127 = 1) :
    let actual := fringeAdvanceBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 1112 = regs 1112 + regs 1123 / (regs 1128 * regs 1129) - regs 34 ∧
      actual.final.regs 1116 = regs 1116 + 1 := by
  have hsub (r : Registers) := natSubBlock_source 1112 1112 34 1132 memory r (by decide) (by decide)
  simp [fringeAdvanceBlock, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_arithmetic, eval_skip, Arithmetic.eval, Registers.write, hsub, hone]

def FringeDecodeWrites (r : Nat) : Prop :=
  (1113 ≤ r ∧ r < 1116) ∨ (1123 ≤ r ∧ r < 1126) ∨ r = 1130 ∨ r = 1132

theorem fringeDecodeBlock_writes : fringeDecodeBlock.WritesOnly FringeDecodeWrites := by
  simp [fringeDecodeBlock, fringeConsiderBlock, fringeKeepBestBlock, Block.sequence,
    Block.WritesOnly, Action.destination, FringeDecodeWrites, natSubBlock]

theorem fringeDecodeBlock_frame (memory : Memory) (s : Data) (r : Nat)
    (outside : ¬ FringeDecodeWrites r) :
    (fringeDecodeBlock.eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ fringeDecodeBlock_writes r outside s

theorem fringeDecodeBlock_source (memory : Memory) (regs : Registers) (hone : regs 1127 = 1) :
    let actual := fringeDecodeBlock.eval memory ⟨regs, .running⟩
    let entry := regs 8194 - 1
    let score := regs 1112 + entry / regs 1128 % regs 1129 - regs 34
    let position := regs 1117 + entry % regs 1128
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 1123 = entry ∧
      candidateOfRegs 1113 actual.final.regs = bpFringeMergeCand (candidateOfRegs 1113 regs)
        (if regs 1118 < regs 1120 then some (score, position) else none) := by
  have hsub := natSubBlock_source 1123 8194 1127 1132 memory regs (by decide) (by decide)
  let prepared := ((regs.write 1132 (Comparison.le.eval 1 (regs 8194))).write 1123 (regs 8194 - 1)).write
    1130 (Comparison.lt.eval (regs 1118) (regs 1120))
  have hc := fringeConsiderBlock_source memory prepared
  have hf := Block.eval_frame memory fringeConsiderBlock _ fringeConsiderBlock_writes 1123
    (by simp) ⟨prepared, .running⟩
  generalize he : fringeConsiderBlock.eval memory ⟨prepared, .running⟩ = considered at hc hf
  rcases considered with ⟨⟨out, status⟩, reads⟩
  dsimp only at hc hf
  obtain ⟨hstatus, hreads, hbest⟩ := hc
  subst status
  subst reads
  simp [prepared, Registers.write, candidateOfRegs] at he hf hbest
  by_cases hgate : regs 1118 < regs 1120
  · simp only [Comparison.eval, if_pos hgate] at he
    simp [fringeDecodeBlock, Block.sequence, Block.eval_seq, Evaluation.bind,
      hsub, eval_comparison, eval_ifZero, eval_skip, Comparison.eval, Registers.write,
      hone, hgate, he, hf, candidateOfRegs, hbest]
  · simp [fringeDecodeBlock, Block.sequence, Block.eval_seq, Evaluation.bind,
      hsub, eval_comparison, eval_ifZero, eval_skip, Comparison.eval, Registers.write,
      hone, hgate, candidateOfRegs, bpFringeMergeCand]
    split <;> rfl

def FringeBodyWrites (r : Nat) : Prop :=
  (1112 ≤ r ∧ r < 1127) ∨ r = 1130 ∨ r = 1132 ∨ (8192 ≤ r ∧ r < 8271)

theorem fringeBody_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (fringeBody reader).WritesOnly FringeBodyWrites := by
  have hr : reader.WritesOnly FringeBodyWrites :=
    Block.WritesOnly.mono reader hwrites (by intro r h; unfold FringeBodyWrites; omega)
  simpa [fringeBody, fringeAddressBlock, fringeAddressRangeBlock, fringeAddressSlotBlock,
    fringeDecodeBlock, fringeConsiderBlock,
    fringeKeepBestBlock, fringeAdvanceBlock, Block.sequence, Block.WritesOnly,
    Action.destination, FringeBodyWrites, natSubBlock, minBlock] using hr

theorem fringeBody_frame (reader : Block) (hwrites : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ FringeBodyWrites r) :
    ((fringeBody reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (fringeBody_writes reader hwrites) r outside s

theorem fringeBody_metadata (shape : CartesianShape) (reader : Block)
    (hwrites : ReaderWrites reader) (memory : Memory) (s : Data) (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((fringeBody reader).eval memory s).final.regs := by
  intro i hi
  rw [fringeBody_frame reader hwrites memory s (16 + i) (by unfold FringeBodyWrites; omega)]
  exact hm i hi

theorem fringeBody_inactive (reader : Block) (memory : Memory) (regs : Registers)
    (hstop : regs 1111 ≤ regs 1116) :
    (fringeBody reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write 1130 0, .running⟩, []⟩ := by
  simp [fringeBody, Block.eval_seq, eval_comparison, eval_ifZero, eval_skip,
    Evaluation.bind, Comparison.eval, Registers.write, Nat.not_lt.mpr hstop]

theorem fringeAddressBlock_reference (memory : Memory) (regs : Registers) (window : List Bool)
    (hwindow : regs 1064 = bitsToNatLE window) (hone : regs 1127 = 1)
    (hradix : regs 1128 = regs 34 + 1) :
    let actual := fringeAddressBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 8192 = 21 ∧ actual.final.regs 8193 =
        bpFringeChunkSlotAt (regs 34) window (regs 1109) (regs 1110) (regs 1116) ∧
      actual.final.regs 1117 = regs 1116 * regs 34 ∧
      actual.final.regs 1118 = bpFringeChunkStartOff (regs 34) (regs 1109) (regs 1116) ∧
      actual.final.regs 1120 = bpFringeChunkEndOff (regs 34) (regs 1110) (regs 1116) := by
  have h := fringeAddressBlock_source memory regs hone hradix
  simpa only [hwindow, bpFringeChunkSlotAt, bpFringeChunkSlot,
    bpFringeWindowChunkValue_eq_div_mod, bpFringeChunkStartOff, max_sub_eq_sub,
    bpFringeChunkEndOff, Nat.min_comm] using h

theorem fringeBody_active (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (regs : Registers) (window : List Bool)
    (hm : MetadataMatches shape regs) (hwindow : regs 1064 = bitsToNatLE window)
    (hone : regs 1127 = 1) (hradix : regs 1128 = regs 34 + 1)
    (hradix2 : regs 1129 = 2 * regs 34 + 2) (hactive : regs 1116 < regs 1111) :
    let actual := (fringeBody reader).eval memory ⟨regs, .running⟩
    let slot := bpFringeChunkSlotAt (regs 34) window (regs 1109) (regs 1110) (regs 1116)
    let entry := ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21 slot).map bitsToNatLE
    actual.final.status = .running ∧ actual.reads = readerReceipts shape memory 21 slot ∧
      actual.final.regs 1116 = regs 1116 + 1 ∧
      (actual.final.regs 1112, candidateOfRegs 1113 actual.final.regs) =
        bpFringeChunkStepDecoded (regs 34) (regs 1109) (regs 1110) (regs 1116)
          (regs 1112, candidateOfRegs 1113 regs) entry := by
  let compared := regs.write 1130 1
  have hcomp (r : Nat) (hr : r ≠ 1130) : compared r = regs r := by simp [compared, Registers.write, hr]
  have ha := fringeAddressBlock_reference memory compared window
    ((hcomp _ (by decide)).trans hwindow) ((hcomp _ (by decide)).trans hone)
    (by rw [hcomp _ (by decide), hcomp _ (by decide)]; exact hradix)
  have haf (r : Nat) (ho : ¬ FringeAddressWrites r) :=
    fringeAddressBlock_frame memory ⟨compared, .running⟩ r ho
  generalize hea : fringeAddressBlock.eval memory ⟨compared, .running⟩ = addressed at ha haf
  rcases addressed with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha haf
  obtain ⟨hast, hareads, hsegment, hslot, hjc, hlo, hhi⟩ := ha
  subst ast
  subst areads
  have ham : MetadataMatches shape ar := by
    intro i hi
    rw [haf _ (by unfold FringeAddressWrites; omega), hcomp _ (by omega)]
    exact hm i hi
  have hb := hreader ar ham
  generalize heb : reader.eval memory ⟨ar, .running⟩ = loaded at hb
  rcases loaded with ⟨⟨br, bst⟩, breads⟩
  dsimp only at hb
  obtain ⟨hbst, hpacket, _hlength, hreads, hbf⟩ := hb
  subst bst
  have hbare (r : Nat) (hr : r < 8194) : br r = ar r := hbf r (Or.inl hr)
  have hf (r : Nat) (hr : r < 8192) (hne : r ≠ 1130) (ho : ¬ FringeAddressWrites r) : br r = regs r := by
    rw [hbare _ (by omega), haf _ ho, hcomp _ hne]
  have hbone : br 1127 = 1 := (hf _ (by decide) (by decide) (by simp [FringeAddressWrites])).trans hone
  have hc := fringeDecodeBlock_source memory br hbone
  have hcf (r : Nat) (ho : ¬ FringeDecodeWrites r) := fringeDecodeBlock_frame memory ⟨br, .running⟩ r ho
  generalize hec : fringeDecodeBlock.eval memory ⟨br, .running⟩ = decoded at hc hcf
  rcases decoded with ⟨⟨cr, cst⟩, creads⟩
  dsimp only at hc hcf
  obtain ⟨hcst, hcreads, hentry, hbest⟩ := hc
  subst cst
  subst creads
  have hd := fringeAdvanceBlock_source memory cr
    ((hcf 1127 (by simp [FringeDecodeWrites])).trans hbone)
  have hdf (r : Nat) (ho : r ≠ 1112 ∧ r ≠ 1116 ∧ r ≠ 1126 ∧ r ≠ 1132) :=
    Block.eval_frame memory fringeAdvanceBlock _ fringeAdvanceBlock_writes r (by omega) ⟨cr, .running⟩
  generalize hed : fringeAdvanceBlock.eval memory ⟨cr, .running⟩ = advanced at hd hdf
  rcases advanced with ⟨⟨dr, dst⟩, dreads⟩
  dsimp only at hd hdf
  obtain ⟨hdst, hdreads, hacc, hindex⟩ := hd
  subst dst
  subst dreads
  have heval : (fringeBody reader).eval memory ⟨regs, .running⟩ = ⟨⟨dr, .running⟩, breads⟩ := by
    have htail := eval_seq_of_results memory fringeDecodeBlock fringeAdvanceBlock
      ⟨br, .running⟩ ⟨⟨cr, .running⟩, []⟩ ⟨⟨dr, .running⟩, []⟩ hec hed
    have hread := eval_seq_of_results memory reader (.seq fringeDecodeBlock fringeAdvanceBlock)
      ⟨ar, .running⟩ ⟨⟨br, .running⟩, breads⟩ ⟨⟨dr, .running⟩, []⟩ heb htail
    simp only [List.append_nil] at hread
    have haddress := eval_seq_of_results memory fringeAddressBlock
      (.seq reader (.seq fringeDecodeBlock fringeAdvanceBlock))
      ⟨compared, .running⟩ ⟨⟨ar, .running⟩, []⟩ ⟨⟨dr, .running⟩, breads⟩ hea hread
    simp only [List.nil_append] at haddress
    have hgate : (Block.ifZero 1130 .skip
        (.seq fringeAddressBlock (.seq reader (.seq fringeDecodeBlock fringeAdvanceBlock)))).eval
        memory ⟨compared, .running⟩ = ⟨⟨dr, .running⟩, breads⟩ := by
      rw [eval_ifZero, if_neg (by simp [compared])]
      exact haddress
    dsimp only [compared] at hgate
    rw [fringeBody, Block.eval_seq, eval_comparison]
    have hcmp : Comparison.lt.eval (regs 1116) (regs 1111) = 1 := by simp [Comparison.eval, hactive]
    simp only [hcmp, Evaluation.bind, hgate, List.nil_append]
  rw [heval]
  dsimp only
  simp [hsegment, hslot, compared, Registers.write] at hpacket hreads
  have hkeep (r : Nat) (hr : r = 34 ∨ r = 1112 ∨ r = 1116 ∨ r = 1128 ∨ r = 1129) : cr r = regs r := by
    rw [hcf _ (by unfold FringeDecodeWrites; omega)]
    exact hf _ (by omega) (by omega) (by unfold FringeAddressWrites; omega)
  have hbestframe : candidateOfRegs 1113 dr = candidateOfRegs 1113 cr := by
    simp only [candidateOfRegs, hdf 1113 (by omega), hdf 1114 (by omega), hdf 1115 (by omega)]
  have hbeforebest : candidateOfRegs 1113 br = candidateOfRegs 1113 regs := by
    simp only [candidateOfRegs, hf 1113 (by decide) (by decide) (by simp [FringeAddressWrites]),
      hf 1114 (by decide) (by decide) (by simp [FringeAddressWrites]),
      hf 1115 (by decide) (by decide) (by simp [FringeAddressWrites])]
  refine ⟨rfl, hreads, ?_, ?_⟩
  · rw [hindex, hkeep 1116 (by simp)]
  · apply Prod.ext
    · dsimp only [bpFringeChunkStepDecoded]
      rw [hacc, hkeep 1112 (by simp), hentry, hpacket, logicalPacket_pred,
        hkeep 1128 (by simp), hkeep 1129 (by simp), hkeep 34 (by simp), hradix, hradix2]
    · dsimp only [bpFringeChunkStepDecoded]
      rw [hbestframe, hbest, hbeforebest, hpacket, logicalPacket_pred]
      rw [hf 1112 (by decide) (by decide) (by simp [FringeAddressWrites]),
        hf 1128 (by decide) (by decide) (by simp [FringeAddressWrites]),
        hf 1129 (by decide) (by decide) (by simp [FringeAddressWrites]),
        hf 34 (by decide) (by decide) (by simp [FringeAddressWrites]),
        hbare 1117 (by decide), hbare 1118 (by decide), hbare 1120 (by decide),
        hjc, hlo, hhi, hradix, hradix2]
      simp [compared, Registers.write]

structure FringeFoldState (c : Nat) (window : List Bool) (lo hi total j : Nat)
    (st : Nat × Option (Nat × Nat)) (regs : Registers) : Prop where
  chunk_eq : regs 34 = c
  window_eq : regs 1064 = bitsToNatLE window
  lo_eq : regs 1109 = lo
  hi_eq : regs 1110 = hi
  total_eq : regs 1111 = total
  index_eq : regs 1116 = j
  accumulator : regs 1112 = st.1
  best : candidateOfRegs 1113 regs = st.2
  one_eq : regs 1127 = 1
  radix_eq : regs 1128 = c + 1
  radix2_eq : regs 1129 = 2 * c + 2

theorem fringeRepeat_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (c : Nat) (window : List Bool) (lo hi total cycles j : Nat) (st : Nat × Option (Nat × Nat))
    (regs : Registers) (hm : MetadataMatches shape regs)
    (hs : FringeFoldState c window lo hi total j st regs) (hcover : total ≤ j + cycles) :
    let actual := (Block.repeat cycles (fringeBody reader)).eval memory ⟨regs, .running⟩
    let expected := (bpFringeChunkFoldComputationFrom c window lo hi j (total - j) st).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21)
    actual.final.status = .running ∧
      (actual.final.regs 1112, candidateOfRegs 1113 actual.final.regs) = expected.value ∧
      actual.reads = expected.reads.flatMap (fun read => readerReceipts shape memory 21 read.1) := by
  induction cycles generalizing j st regs with
  | zero =>
    have hz : total - j = 0 := by omega
    simp [Block.eval_repeat, iterate, hz, bpFringeChunkFoldComputationFrom,
      FlatStoreComputation.pure, hs.accumulator, hs.best]
  | succ cycles ih =>
    by_cases hactive : j < total
    · have hb := fringeBody_active shape memory reader hreader regs window hm hs.window_eq hs.one_eq
        (by rw [hs.chunk_eq]; exact hs.radix_eq) (by rw [hs.chunk_eq]; exact hs.radix2_eq)
        (by rw [hs.index_eq, hs.total_eq]; exact hactive)
      have hmeta := fringeBody_metadata shape reader hwrites memory ⟨regs, .running⟩ hm
      have hframe (r : Nat) (ho : ¬ FringeBodyWrites r) :=
        fringeBody_frame reader hwrites memory ⟨regs, .running⟩ r ho
      generalize he : (fringeBody reader).eval memory ⟨regs, .running⟩ = first at hb hmeta hframe
      rcases first with ⟨⟨fr, fst⟩, freceipts⟩
      dsimp only at hb hmeta hframe
      obtain ⟨hfst, hreads, hindex, hvalue⟩ := hb
      subst fst
      simp only [hs.chunk_eq, hs.lo_eq, hs.hi_eq, hs.index_eq, hs.accumulator, hs.best] at hreads hindex hvalue
      let next := bpFringeChunkStepDecoded c lo hi j st
        (((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          21 (bpFringeChunkSlotAt c window lo hi j)).map bitsToNatLE)
      have hnext : FringeFoldState c window lo hi total (j + 1) next fr := by
        constructor
        · rw [hframe 34 (by simp [FringeBodyWrites])]; exact hs.chunk_eq
        · rw [hframe 1064 (by simp [FringeBodyWrites])]; exact hs.window_eq
        · rw [hframe 1109 (by simp [FringeBodyWrites])]; exact hs.lo_eq
        · rw [hframe 1110 (by simp [FringeBodyWrites])]; exact hs.hi_eq
        · rw [hframe 1111 (by simp [FringeBodyWrites])]; exact hs.total_eq
        · exact hindex
        · exact congrArg Prod.fst hvalue
        · exact congrArg Prod.snd hvalue
        · rw [hframe 1127 (by simp [FringeBodyWrites])]; exact hs.one_eq
        · rw [hframe 1128 (by simp [FringeBodyWrites])]; exact hs.radix_eq
        · rw [hframe 1129 (by simp [FringeBodyWrites])]; exact hs.radix2_eq
      have ht := ih (j + 1) next fr hmeta hnext (by omega)
      have hremaining : total - j = (total - (j + 1)) + 1 := by omega
      rw [Block.eval_repeat_succ, he]
      dsimp only [Evaluation.bind]
      rw [hremaining, bpFringeChunkFoldComputationFrom]
      dsimp only [FlatStoreComputation.bind, FlatStoreComputation.read, FlatStoreExecution.append]
      refine ⟨ht.1, ht.2.1, ?_⟩
      rw [hreads, ht.2.2]
      simp only [List.cons_append, List.nil_append, List.flatMap_cons,
        bpFringeChunkSlotAt, next]
    · have hstop : regs 1111 ≤ regs 1116 := by rw [hs.total_eq, hs.index_eq]; omega
      have hnext : FringeFoldState c window lo hi total j st (regs.write 1130 0) := by
        constructor
        · exact hs.chunk_eq
        · exact hs.window_eq
        · exact hs.lo_eq
        · exact hs.hi_eq
        · exact hs.total_eq
        · exact hs.index_eq
        · exact hs.accumulator
        · simpa only [candidateOfRegs, Registers.write, reduceIte] using hs.best
        · exact hs.one_eq
        · exact hs.radix_eq
        · exact hs.radix2_eq
      have ht := ih j st (regs.write 1130 0)
        (MetadataMatches.write shape regs hm 1130 0 (Or.inr (by decide))) hnext (by omega)
      rw [Block.eval_repeat_succ, fringeBody_inactive reader memory regs hstop]
      simpa only [Evaluation.bind, List.nil_append] using ht

theorem fringeSeedAddressBlock_writes : fringeSeedAddressBlock.WritesOnly
    (fun r => r = 352 ∨ r = 1107 ∨ r = 1127 ∨ r = 1131) := by
  simp [fringeSeedAddressBlock, Block.sequence, Block.WritesOnly, Action.destination]

theorem fringeSeedAddressBlock_source (memory : Memory) (regs : Registers) :
    let actual := fringeSeedAddressBlock.eval memory ⟨regs, .running⟩
    let base := regs 1104 / regs 33 * regs 33 / regs 32 * regs 32
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 352 = base ∧
      actual.final.regs 1107 = base ∧ actual.final.regs 1127 = 1 ∧ actual.final.regs 1131 = 2 := by
  simp [fringeSeedAddressBlock, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_constant, eval_arithmetic, eval_move, eval_skip, Arithmetic.eval, Registers.write]

theorem fringeSeedDecodeBlock_writes : fringeSeedDecodeBlock.WritesOnly
    (fun r => r = 1024 ∨ r = 1108 ∨ r = 1132) := by
  simp [fringeSeedDecodeBlock, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]

theorem fringeSeedDecodeBlock_source (memory : Memory) (regs : Registers) (htwo : regs 1131 = 2) :
    let actual := fringeSeedDecodeBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 1108 = regs 1107 - 2 * regs 360 ∧ actual.final.regs 1024 = regs 1104 := by
  have hsub (r : Registers) := natSubBlock_source 1108 1107 1108 1132 memory r (by decide) (by decide)
  simp [fringeSeedDecodeBlock, Block.sequence, Block.eval_seq, Evaluation.bind, eval_arithmetic,
    eval_move, eval_skip, Arithmetic.eval, Registers.write, hsub, htwo, Nat.mul_comm]

theorem fringeFoldInit_writes : fringeFoldInit.WritesOnly
    (fun r => (1109 ≤ r ∧ r < 1117) ∨ r = 1128 ∨ r = 1129 ∨ r = 1130 ∨ r = 1132) := by
  simp [fringeFoldInit, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, minBlock]

theorem fringeFoldInit_source (memory : Memory) (regs : Registers)
    (hone : regs 1127 = 1) (htwo : regs 1131 = 2) :
    let actual := fringeFoldInit.eval memory ⟨regs, .running⟩
    let lo := regs 1105 - regs 1107
    let hi := regs 1105 + regs 1106 - 1 - regs 1107
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 1109 = lo ∧ actual.final.regs 1110 = hi ∧
      actual.final.regs 1111 = min (hi / regs 34 + 1) 33 ∧
      actual.final.regs 1112 = regs 1108 ∧ candidateOfRegs 1113 actual.final.regs = none ∧
      actual.final.regs 1116 = 0 ∧ actual.final.regs 1128 = regs 34 + 1 ∧
      actual.final.regs 1129 = 2 * regs 34 + 2 := by
  have hsub1 (r : Registers) := natSubBlock_source 1109 1105 1107 1132 memory r (by decide) (by decide)
  have hsub2 (r : Registers) := natSubBlock_source 1110 1110 1127 1132 memory r (by decide) (by decide)
  have hsub3 (r : Registers) := natSubBlock_source 1110 1110 1107 1132 memory r (by decide) (by decide)
  have hmin (r : Registers) := minBlock_source 1111 1111 1130 1132 memory r (by decide) (by decide)
  simp [fringeFoldInit, Block.sequence, Block.eval_seq, Evaluation.bind, eval_constant,
    eval_arithmetic, eval_move, eval_skip, Arithmetic.eval, Registers.write,
    hsub1, hsub2, hsub3, hmin, hone, htwo, candidateOfRegs, Nat.mul_add]

theorem fringeFinishBlock_writes : fringeFinishBlock.WritesOnly (fun r => 7000 ≤ r ∧ r < 7003) := by
  simp [fringeFinishBlock, Block.sequence, Block.WritesOnly, Action.destination]

theorem fringeFinishBlock_source (memory : Memory) (regs : Registers) :
    let actual := fringeFinishBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      candidateOfRegs 7000 actual.final.regs = bpFringeCandGlobal (regs 1107) (regs 1108)
        (regs 1105) (candidateOfRegs 1113 regs) := by
  by_cases hz : regs 1113 = 0 <;>
    simp [fringeFinishBlock, Block.sequence, Block.eval_seq, Evaluation.bind,
      eval_constant, eval_move, eval_arithmetic, eval_skip, eval_ifZero,
      Arithmetic.eval, Registers.write, candidateOfRegs, bpFringeCandGlobal, hz]

private theorem fringeFoldInitialized_source (shape : CartesianShape) (memory : Memory)
    (reader : Block) (copies : Nat) (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (window : List Bool)
    (hwindow : regs 1064 = bitsToNatLE window) (hone : regs 1127 = 1) (htwo : regs 1131 = 2)
    (hcover : min ((regs 1105 + regs 1106 - 1 - regs 1107) / regs 34 + 1) 33 ≤ copies) :
    let lo := regs 1105 - regs 1107
    let hi := regs 1105 + regs 1106 - 1 - regs 1107
    let expected := bpFringeChunkFoldTraceResultAtSegmentWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 (regs 34) window (regs 1108)
      lo hi (min (hi / regs 34 + 1) 33)
    let actual := (Block.seq fringeFoldInit (.seq (.repeat copies (fringeBody reader)) fringeFinishBlock)).eval
      memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs =
      bpFringeCandGlobal (regs 1107) (regs 1108) (regs 1105) expected.value.2 ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hi := fringeFoldInit_source memory regs hone htwo
  have hif (r : Nat) (hr : r < 1109 ∨ r = 1127 ∨ r = 1131 ∨ 1133 ≤ r) :=
    Block.eval_frame memory fringeFoldInit _ fringeFoldInit_writes r (by omega) ⟨regs, .running⟩
  generalize hei : fringeFoldInit.eval memory ⟨regs, .running⟩ = initialized at hi hif
  rcases initialized with ⟨⟨ir, ist⟩, ireads⟩
  dsimp only at hi hif
  obtain ⟨hist, hireads, hlo, hhi, htotal, hseed, hbest, hindex, hradix, hradix2⟩ := hi
  subst ist
  subst ireads
  let lo := regs 1105 - regs 1107
  let high := regs 1105 + regs 1106 - 1 - regs 1107
  let total := min (high / regs 34 + 1) 33
  have him : MetadataMatches shape ir := by
    intro i hi
    rw [hif _ (Or.inl (by omega))]
    exact hm i hi
  have hstate : FringeFoldState (regs 34) window lo high total 0 (regs 1108, none) ir :=
    ⟨hif 34 (Or.inl (by decide)), (hif 1064 (Or.inl (by decide))).trans hwindow,
      hlo, hhi, htotal, hindex, hseed, hbest,
      (hif 1127 (Or.inr (Or.inl rfl))).trans hone, hradix, hradix2⟩
  have hr := fringeRepeat_source shape memory reader hreader hwrites (regs 34) window lo high total
    copies 0 (regs 1108, none) ir him hstate (by simpa only [Nat.zero_add] using hcover)
  have hrf (r : Nat) (ho : ¬ FringeBodyWrites r) := Block.eval_frame memory
    (.repeat copies (fringeBody reader)) _ (fringeBody_writes reader hwrites) r ho ⟨ir, .running⟩
  generalize her : (Block.repeat copies (fringeBody reader)).eval memory ⟨ir, .running⟩ = repeated at hr hrf
  rcases repeated with ⟨⟨rr, rst⟩, rreads⟩
  dsimp only at hr hrf
  obtain ⟨hrst, hrvalue, hrreads⟩ := hr
  subst rst
  have hf := fringeFinishBlock_source memory rr
  generalize hef : fringeFinishBlock.eval memory ⟨rr, .running⟩ = finished at hf
  rcases finished with ⟨⟨fr, fst⟩, freads⟩
  dsimp only at hf
  obtain ⟨hfst, hfreads, hfvalue⟩ := hf
  subst fst
  subst freads
  have heval : (Block.seq fringeFoldInit (.seq (.repeat copies (fringeBody reader)) fringeFinishBlock)).eval
      memory ⟨regs, .running⟩ = ⟨⟨fr, .running⟩, rreads⟩ := by
    have htail := eval_seq_of_results memory (.repeat copies (fringeBody reader)) fringeFinishBlock
      ⟨ir, .running⟩ ⟨⟨rr, .running⟩, rreads⟩ ⟨⟨fr, .running⟩, []⟩ her hef
    simp only [List.append_nil] at htail
    have hwhole := eval_seq_of_results memory fringeFoldInit
      (.seq (.repeat copies (fringeBody reader)) fringeFinishBlock)
      ⟨regs, .running⟩ ⟨⟨ir, .running⟩, []⟩ ⟨⟨fr, .running⟩, rreads⟩ hei htail
    simpa only [List.nil_append] using hwhole
  rw [heval]
  dsimp only
  refine ⟨rfl, ?_, ?_, flatExecution_readOnly 21 _⟩
  · rw [hfvalue, hrf 1107 (by simp [FringeBodyWrites]), hrf 1108 (by simp [FringeBodyWrites]),
      hrf 1105 (by simp [FringeBodyWrites]), hif 1107 (Or.inl (by decide)),
      hif 1108 (Or.inl (by decide)), hif 1105 (Or.inl (by decide))]
    apply congrArg (bpFringeCandGlobal (regs 1107) (regs 1108) (regs 1105))
    simpa only [bpFringeChunkFoldTraceResultAtSegmentWithStore, bpFringeChunkFoldComputation,
      flatStoreExecutionTraceResultAtSegment, flatWordStoreOfReadStore, Nat.sub_zero]
      using congrArg Prod.snd hrvalue
  · rw [bpFringeChunkFoldTraceResultAtSegmentWithStore, logicalTraceReads_flatExecution]
    simpa only [bpFringeChunkFoldComputation, flatWordStoreOfReadStore, Nat.sub_zero] using hrreads

theorem fringeFoldBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (window : List Bool)
    (hwindow : regs 1064 = bitsToNatLE window) (hone : regs 1127 = 1) (htwo : regs 1131 = 2) :
    let lo := regs 1105 - regs 1107
    let hi := regs 1105 + regs 1106 - 1 - regs 1107
    let expected := bpFringeChunkFoldTraceResultAtSegmentWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21 (regs 34) window (regs 1108)
      lo hi (min (hi / regs 34 + 1) 33)
    let actual := (fringeFoldBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs =
      bpFringeCandGlobal (regs 1107) (regs 1108) (regs 1105) expected.value.2 ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace :=
  fringeFoldInitialized_source shape memory reader 33 hreader hwrites regs hm window hwindow hone htwo
    (Nat.min_le_right _ _)

def FringeSeedWrites (r : Nat) : Prop :=
  RankWrapperWrites r ∨ r = 352 ∨ r = 1024 ∨ r = 1107 ∨ r = 1108 ∨
    r = 1127 ∨ r = 1131 ∨ r = 1132

theorem fringeSeedBlock_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (fringeSeedBlock reader).WritesOnly FringeSeedWrites := by
  have ha : fringeSeedAddressBlock.WritesOnly FringeSeedWrites :=
    Block.WritesOnly.mono _ fringeSeedAddressBlock_writes (by
      intro r h; unfold FringeSeedWrites RankWrapperWrites; omega)
  have hr : (rankCloseBlock reader).WritesOnly FringeSeedWrites :=
    Block.WritesOnly.mono _ (rankCloseBlock_writes reader hwrites) (by intro r h; exact Or.inl h)
  have hd : fringeSeedDecodeBlock.WritesOnly FringeSeedWrites :=
    Block.WritesOnly.mono _ fringeSeedDecodeBlock_writes (by
      intro r h; unfold FringeSeedWrites RankWrapperWrites; omega)
  exact ⟨ha, hr, hd⟩

theorem fringeSeedBlock_frame (reader : Block) (hwrites : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (ho : ¬ FringeSeedWrites r) :
    ((fringeSeedBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (fringeSeedBlock_writes reader hwrites) r ho s

theorem fringeSeedBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let base := packedLocalBPWindowBase shape.size (packedInteriorLayout shape.size).blockSize (regs 1104)
    let expected := packedLocalBPSeed shape.size
      (packedRankCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size)
      (packedInteriorLayout shape.size).blockSize (regs 1104)
    let actual := (fringeSeedBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 1107 = base ∧
      actual.final.regs 1108 = expected.value ∧ actual.final.regs 1024 = regs 1104 ∧
      actual.final.regs 1127 = 1 ∧ actual.final.regs 1131 = 2 ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have ha := fringeSeedAddressBlock_source memory regs
  have haf (r : Nat) (hr : r ≠ 352 ∧ r ≠ 1107 ∧ r ≠ 1127 ∧ r ≠ 1131) :=
    Block.eval_frame memory _ _ fringeSeedAddressBlock_writes r (by omega) ⟨regs, .running⟩
  generalize hea : fringeSeedAddressBlock.eval memory ⟨regs, .running⟩ = addressed at ha haf
  rcases addressed with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha haf
  obtain ⟨hast, hareads, hpos, hbase, hone, htwo⟩ := ha
  subst ast
  subst areads
  have ham : MetadataMatches shape ar := by
    intro i hi
    rw [haf _ (by omega)]
    exact hm i hi
  have hr := rankCloseBlock_source shape memory reader hreader hwrites ar ham
  have hrf (r : Nat) (ho : ¬ RankWrapperWrites r) :=
    rankCloseBlock_frame reader hwrites memory ⟨ar, .running⟩ r ho
  generalize her : (rankCloseBlock reader).eval memory ⟨ar, .running⟩ = ranked at hr hrf
  rcases ranked with ⟨⟨rr, rst⟩, rreads⟩
  dsimp only at hr hrf
  obtain ⟨hrst, hrvalue, hrreads, hreadonly⟩ := hr
  subst rst
  have hd := fringeSeedDecodeBlock_source memory rr
    ((hrf 1131 (by simp [RankWrapperWrites])).trans htwo)
  have hdf (r : Nat) (ho : r ≠ 1024 ∧ r ≠ 1108 ∧ r ≠ 1132) :=
    Block.eval_frame memory _ _ fringeSeedDecodeBlock_writes r (by omega) ⟨rr, .running⟩
  generalize hed : fringeSeedDecodeBlock.eval memory ⟨rr, .running⟩ = decoded at hd hdf
  rcases decoded with ⟨⟨dr, dst⟩, dreads⟩
  dsimp only at hd hdf
  obtain ⟨hdst, hdreads, hdseed, hdclose⟩ := hd
  subst dst
  subst dreads
  have htail := eval_seq_of_results memory (rankCloseBlock reader) fringeSeedDecodeBlock
    ⟨ar, .running⟩ ⟨⟨rr, .running⟩, rreads⟩ ⟨⟨dr, .running⟩, []⟩ her hed
  simp only [List.append_nil] at htail
  have hwhole := eval_seq_of_results memory fringeSeedAddressBlock
    (.seq (rankCloseBlock reader) fringeSeedDecodeBlock) ⟨regs, .running⟩
    ⟨⟨ar, .running⟩, []⟩ ⟨⟨dr, .running⟩, rreads⟩ hea htail
  simp only [List.nil_append] at hwhole
  change (fringeSeedBlock reader).eval memory ⟨regs, .running⟩ = _ at hwhole
  rw [hwhole]
  dsimp only
  have hb : regs 33 = (packedInteriorLayout shape.size).blockSize := hm 17 (by decide)
  have hw : regs 32 = packedBpCodeWordWidth shape.size := hm 16 (by decide)
  have hbase' : regs 1104 / regs 33 * regs 33 / regs 32 * regs 32 =
      packedLocalBPWindowBase shape.size (packedInteriorLayout shape.size).blockSize (regs 1104) := by
    simp only [packedLocalBPWindowBase, blockStartOf, blockOfClose, hb, hw]
  have hpos' := hpos.trans hbase'
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdf 1107 (by decide), hrf 1107 (by simp [RankWrapperWrites]), hbase, hbase']
  · rw [hdseed, hrf 1107 (by simp [RankWrapperWrites]), hbase, hrvalue, hpos', hbase']
    rfl
  · rw [hdclose, hrf 1104 (by simp [RankWrapperWrites]), haf 1104 (by decide)]
  · rw [hdf 1127 (by decide), hrf 1127 (by simp [RankWrapperWrites]), hone]
  · rw [hdf 1131 (by decide), hrf 1131 (by simp [RankWrapperWrites]), htwo]
  · simpa only [packedLocalBPSeed, WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.pure, List.append_nil, hpos'] using hrreads
  · simpa only [packedLocalBPSeed, WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.pure, List.append_nil, hpos'] using hreadonly

def FringeFoldWrites (r : Nat) : Prop :=
  (1109 ≤ r ∧ r < 1133) ∨ (7000 ≤ r ∧ r < 7003) ∨ (8192 ≤ r ∧ r < 8271)

theorem fringeFoldBlock_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (fringeFoldBlock reader).WritesOnly FringeFoldWrites := by
  refine ⟨Block.WritesOnly.mono _ fringeFoldInit_writes ?_,
    Block.WritesOnly.mono _ (fringeBody_writes reader hwrites) ?_,
    Block.WritesOnly.mono _ fringeFinishBlock_writes ?_⟩
  · intro r h; unfold FringeFoldWrites; omega
  · intro r h; unfold FringeBodyWrites at h; unfold FringeFoldWrites; omega
  · intro r h; unfold FringeFoldWrites; omega

def FringeWindowWrites (r : Nat) : Prop := WindowWrites r ∨ FringeFoldWrites r

theorem fringeWindowFoldBlock_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (fringeWindowFoldBlock reader).WritesOnly FringeWindowWrites :=
  ⟨Block.WritesOnly.mono _ (loadWindowBlock_writes reader hwrites) (by intro r h; exact Or.inl h),
   Block.WritesOnly.mono _ (fringeFoldBlock_writes reader hwrites) (by intro r h; exact Or.inr h)⟩

/-- Proof-side reference composition of the existing window and fringe fold.
The source does not receive this function or its intermediate values. -/
def fringeWindowReference (store : WordRAM.ReadStore) (n close start span seed : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let layout := packedInteriorLayout n
  let base := packedLocalBPWindowBase n layout.blockSize close
  let lo := start - base
  let hi := start + span - 1 - base
  (packedLocalBPWindowBitsRead store n layout.blockSize close).bind fun window =>
    (bpFringeChunkFoldTraceResultAtSegmentWithStore store 21 (packedFringeChunkBits n)
      window seed lo hi (min (hi / packedFringeChunkBits n + 1) 33)).map
      (fun result => bpFringeCandGlobal base seed start result.2)

theorem fringeWindowFoldBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs)
    (hbase : regs 1107 = packedLocalBPWindowBase shape.size (packedInteriorLayout shape.size).blockSize (regs 1024))
    (hone : regs 1127 = 1) (htwo : regs 1131 = 2) :
    let expected := fringeWindowReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 1024) (regs 1105) (regs 1106) (regs 1108)
    let actual := (fringeWindowFoldBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hw := loadWindowBlock_reference shape memory reader hreader hwrites regs hm
  have hwf (r : Nat) (ho : ¬ WindowWrites r) :=
    loadWindowBlock_frame reader hwrites memory ⟨regs, .running⟩ r ho
  generalize hew : (loadWindowBlock reader).eval memory ⟨regs, .running⟩ = windowed at hw hwf
  rcases windowed with ⟨⟨wr, wst⟩, wreads⟩
  dsimp only at hw hwf
  obtain ⟨hwst, hwvalue, hwreads, hwreadonly⟩ := hw
  subst wst
  have hwm : MetadataMatches shape wr := by
    intro i hi
    rw [hwf _ (by unfold WindowWrites; omega)]
    exact hm i hi
  have hf := fringeFoldBlock_source shape memory reader hreader hwrites wr hwm
    (packedLocalBPWindowBitsRead (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (packedInteriorLayout shape.size).blockSize (regs 1024)).value hwvalue
    ((hwf 1127 (by simp [WindowWrites])).trans hone)
    ((hwf 1131 (by simp [WindowWrites])).trans htwo)
  generalize hef : (fringeFoldBlock reader).eval memory ⟨wr, .running⟩ = folded at hf
  rcases folded with ⟨⟨fr, fst⟩, freads⟩
  dsimp only at hf
  obtain ⟨hfst, hfvalue, hfreads, hfreadonly⟩ := hf
  subst fst
  have heval := eval_seq_of_results memory (loadWindowBlock reader) (fringeFoldBlock reader)
    ⟨regs, .running⟩ ⟨⟨wr, .running⟩, wreads⟩ ⟨⟨fr, .running⟩, freads⟩ hew hef
  change (fringeWindowFoldBlock reader).eval memory ⟨regs, .running⟩ = _ at heval
  rw [heval]
  dsimp only
  have hc : regs 34 = packedFringeChunkBits shape.size := hm 18 (by decide)
  simp only [hwf 34 (by simp [WindowWrites]), hwf 1105 (by simp [WindowWrites]),
    hwf 1106 (by simp [WindowWrites]), hwf 1107 (by simp [WindowWrites]),
    hwf 1108 (by simp [WindowWrites]), hbase, hc] at hfvalue hfreads hfreadonly
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact hfvalue
  · simp only [fringeWindowReference, WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, List.append_nil, rank_logicalTraceReads_append]
    rw [hwreads, hfreads]
  · simp only [fringeWindowReference, WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, List.append_nil, ReadOnlyTrace, List.mem_append]
    intro e he
    rcases he with he | he
    · exact hwreadonly e he
    · exact hfreadonly e he

def FringeWrites (r : Nat) : Prop := FringeSeedWrites r ∨ FringeWindowWrites r

theorem fringeBlock_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (fringeBlock reader).WritesOnly FringeWrites :=
  ⟨Block.WritesOnly.mono _ (fringeSeedBlock_writes reader hwrites) (by intro r h; exact Or.inl h),
   Block.WritesOnly.mono _ (fringeWindowFoldBlock_writes reader hwrites) (by intro r h; exact Or.inr h)⟩

theorem fringeBlock_frame (reader : Block) (hwrites : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (ho : ¬ FringeWrites r) :
    ((fringeBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (fringeBlock_writes reader hwrites) r ho s

def fringeReference (store : WordRAM.ReadStore) (n close start span : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  (packedLocalBPSeed n (packedRankCloseLeaf store n) (packedInteriorLayout n).blockSize close).bind
    (fringeWindowReference store n close start span)

theorem fringeBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := fringeReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 1104) (regs 1105) (regs 1106)
    let actual := (fringeBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hs := fringeSeedBlock_source shape memory reader hreader hwrites regs hm
  have hsf (r : Nat) (ho : ¬ FringeSeedWrites r) :=
    fringeSeedBlock_frame reader hwrites memory ⟨regs, .running⟩ r ho
  generalize hes : (fringeSeedBlock reader).eval memory ⟨regs, .running⟩ = seeded at hs hsf
  rcases seeded with ⟨⟨sr, sst⟩, sreads⟩
  dsimp only at hs hsf
  obtain ⟨hsst, hsbase, hsseed, hsclose, hsone, hstwo, hsreads, hsreadonly⟩ := hs
  subst sst
  have hsm : MetadataMatches shape sr := by
    intro i hi
    rw [hsf _ (by unfold FringeSeedWrites RankWrapperWrites; omega)]
    exact hm i hi
  have ht := fringeWindowFoldBlock_source shape memory reader hreader hwrites sr hsm
    (by rw [hsclose]; exact hsbase) hsone hstwo
  generalize het : (fringeWindowFoldBlock reader).eval memory ⟨sr, .running⟩ = tailed at ht
  rcases tailed with ⟨⟨tr, tst⟩, treads⟩
  dsimp only at ht
  obtain ⟨htst, htvalue, htreads, htreadonly⟩ := ht
  subst tst
  have heval := eval_seq_of_results memory (fringeSeedBlock reader) (fringeWindowFoldBlock reader)
    ⟨regs, .running⟩ ⟨⟨sr, .running⟩, sreads⟩ ⟨⟨tr, .running⟩, treads⟩ hes het
  change (fringeBlock reader).eval memory ⟨regs, .running⟩ = _ at heval
  rw [heval]
  dsimp only
  simp only [hsclose, hsseed, hsf 1105 (by simp [FringeSeedWrites, RankWrapperWrites]),
    hsf 1106 (by simp [FringeSeedWrites, RankWrapperWrites])] at htvalue htreads htreadonly
  refine ⟨rfl, htvalue, ?_, ?_⟩
  · simp only [fringeReference, WordRAM.TraceResult.bind, rank_logicalTraceReads_append]
    rw [hsreads, htreads]
  · simp only [fringeReference, WordRAM.TraceResult.bind, ReadOnlyTrace, List.mem_append]
    intro e he
    rcases he with he | he
    · exact hsreadonly e he
    · exact htreadonly e he

theorem fringeWindowReference_left (store : WordRAM.ReadStore) (n close seed : Nat) :
    fringeWindowReference store n close (close + 1)
      (close / (packedInteriorLayout n).blockSize * (packedInteriorLayout n).blockSize +
        (packedInteriorLayout n).blockSize - close) seed =
      packedLeftFringeCandidateRead store 21 n (packedInteriorLayout n).blockSize close seed := rfl

theorem fringeWindowReference_right (store : WordRAM.ReadStore) (n close seed : Nat) :
    fringeWindowReference store n close
      (close / (packedInteriorLayout n).blockSize * (packedInteriorLayout n).blockSize)
      (close - close / (packedInteriorLayout n).blockSize * (packedInteriorLayout n).blockSize + 2) seed =
      packedRightFringeCandidateRead store 21 n (packedInteriorLayout n).blockSize close seed := rfl

theorem fringeReference_sameBlock (store : WordRAM.ReadStore) (n left right : Nat) :
    (fringeReference store n left (left + 1) (right - left + 1)).map bpCandidateClose? =
      packedSameBlockCloseDecodedRead store (packedRankCloseLeaf store n) 21 n
        (packedInteriorLayout n).blockSize left right := by
  simp [fringeReference, fringeWindowReference, packedSameBlockCloseDecodedRead,
    packedSameBlockCloseSeededRead, WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
    WordRAM.TraceResult.pure]

theorem fringeBlock_metadata (shape : CartesianShape) (reader : Block)
    (hwrites : ReaderWrites reader) (memory : Memory) (s : Data)
    (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((fringeBlock reader).eval memory s).final.regs := by
  intro i hi
  rw [fringeBlock_frame reader hwrites memory s (16 + i) (by
    unfold FringeWrites FringeSeedWrites FringeWindowWrites FringeFoldWrites WindowWrites RankWrapperWrites
    omega)]
  exact hm i hi

end RMQ.SuccinctFinal.PackedWordRAM
