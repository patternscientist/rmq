import RMQ.Core.WordRAM.Packed.SelectProof
import RMQ.Core.WordRAM.Packed.ReaderSafety
import RMQ.Core.WordRAM.Packed.RankSafety

/-!
# Word safety of the fixed canonical select controller

Bounds below describe actual source registers. The source, memory and declared
word width are the same objects used by the select value and receipt theorems.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM
open Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

theorem select_constant_fit (n value : Nat) (small : value < 2 ^ 32) :
    value < 2 ^ wordWidth n :=
  Nat.lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) (by unfold wordWidth; omega))

theorem select_old_capacity_le_envelope (n : Nat) :
    2 ^ packedReviewerCellWidth n ≤ metadataEnvelope n := by
  have hp := Nat.two_pow_pos (packedReviewerCellWidth n)
  have h := Nat.le_mul_of_pos_right (2 ^ packedReviewerCellWidth n) hp
  unfold metadataEnvelope
  rw [Nat.pow_two]
  omega

theorem select_envelope_square_fit (n : Nat) :
    256 * (metadataEnvelope n * metadataEnvelope n) < 2 ^ wordWidth n := by
  have he : metadataEnvelope n = 2 ^ (6 + packedReviewerCellWidth n * 2) := by
    simp [metadataEnvelope, Nat.pow_add, Nat.pow_mul]
  rw [he]
  have hp : 256 * (2 ^ (6 + packedReviewerCellWidth n * 2) *
      2 ^ (6 + packedReviewerCellWidth n * 2)) =
      2 ^ (20 + packedReviewerCellWidth n * 4) := by
    change 2 ^ 8 * (2 ^ (6 + packedReviewerCellWidth n * 2) *
      2 ^ (6 + packedReviewerCellWidth n * 2)) = _
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  rw [hp]
  apply Nat.pow_lt_pow_right (by decide)
  unfold wordWidth
  omega

theorem select_logicalPacket_bound (shape : CartesianShape) (segment index : Nat) :
    logicalPacket ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
      segment index) ≤ 2 ^ packedReviewerCellWidth shape.size := by
  cases hr : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index with
  | none => simp [logicalPacket]
  | some bits =>
      have hf := packedReviewerGlobalReadStore_word_fits shape
        ⟨⟨.leftSelect, 0, 0⟩, .entryBaseOccurrence, segment, index⟩ bits hr
      have hv := hf.value_lt_two_pow
      simp only [logicalPacket]
      omega

private theorem select_safe_sequence (memory : Memory) (width : Nat) (blocks : List Block)
    (safe : ∀ block ∈ blocks, ∀ s, s.Fits width → block.Safe memory width s)
    (s : Data) (fit : s.Fits width) : (Block.sequence blocks).Safe memory width s := by
  induction blocks generalizing s with
  | nil => exact Block.safe_skip memory width s fit
  | cons block rest ih =>
      have head := safe block (by simp) s fit
      exact Block.safe_seq head (ih (by intro b hb; exact safe b (by simp [hb]))
        _ (Block.eval_fits _ _ _ _ head))

private theorem select_safe_branch (memory : Memory) (width condition : Nat)
    (zero nonzero : Block)
    (hz : ∀ s, s.Fits width → zero.Safe memory width s)
    (hn : ∀ s, s.Fits width → nonzero.Safe memory width s)
    (s : Data) (fit : s.Fits width) :
    (Block.ifZero condition zero nonzero).Safe memory width s := by
  apply Block.safe_ifZero fit
  split
  · exact hz s fit
  · exact hn s fit

theorem selectFieldRead_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderSafe shape memory reader) (segment indexReg destination : Nat)
    (hsegment : segment < 2 ^ wordWidth shape.size) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (selectFieldRead reader segment indexReg destination).Safe memory (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs
      subst status
      have first := Block.safe_action memory (wordWidth shape.size) (.constant 8192 segment)
        ⟨regs, .running⟩ fit hsegment
      have fp := Block.eval_fits _ _ _ _ first
      have second := Block.safe_action memory (wordWidth shape.size) (.move 8193 indexReg)
        _ fp (fp.1 indexReg)
      have fq := Block.eval_fits _ _ _ _ second
      have mp : MetadataMatches shape
          ((regs.write 8192 segment).write 8193 ((regs.write 8192 segment) indexReg)) :=
        MetadataMatches.write shape _
          (MetadataMatches.write shape regs hm 8192 segment (Or.inr (by decide)))
          8193 _ (Or.inr (by decide))
      have loadSafe := hreader _ fq mp
      have fr := Block.eval_fits _ _ _ _ loadSafe
      have tail := SimpleScalar.safe memory (wordWidth shape.size)
        (Block.sequence [.action (.move destination 8194)]) ⟨True.intro, True.intro⟩ _ fr
      exact Block.safe_seq first (Block.safe_seq second (Block.safe_seq loadSafe tail))
  · exact Block.safe_stopped memory _ _ s fit hs

theorem selectFieldsFrom_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderSafe shape memory reader) (hwrites : ReaderWrites reader)
    (segment indexReg destination count : Nat) (hd : 190 ≤ destination)
    (hsegments : segment + count ≤ 2 ^ wordWidth shape.size) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (selectFieldsFrom reader segment indexReg destination count).Safe memory (wordWidth shape.size) s := by
  induction count generalizing segment destination s with
  | zero => exact Block.safe_skip memory _ s fit
  | succ count ih =>
      have head := selectFieldRead_safe shape memory reader hreader segment indexReg destination
        (by omega) s fit hm
      have fp := Block.eval_fits _ _ _ _ head
      have mp := selectFieldRead_metadata shape reader hwrites segment indexReg destination hd memory s hm
      exact Block.safe_seq head (ih (segment + 1) (destination + 1) (by omega) (by omega) _ fp mp)

theorem selectEntryDecode_safe (base : Nat) (memory : Memory) (width : Nat)
    (one : 1 < 2 ^ width) (s : Data) (fit : s.Fits width) :
    (selectEntryDecode base).Safe memory width s := by
  have subSafe (i : Nat) (hi : i < 4) (s : Data) (fit : s.Fits width) :
      (natSubBlock (base + (i + 1)) (base + (i + 5)) (base + 9) (base + 10)).Safe
        memory width s :=
    natSubBlock_safe memory width _ _ _ _ s fit one (by omega) (by omega)
  have tail (s : Data) (fit : s.Fits width) :
      (Block.sequence [natSubBlock (base + 1) (base + 5) (base + 9) (base + 10),
        natSubBlock (base + 2) (base + 6) (base + 9) (base + 10),
        natSubBlock (base + 3) (base + 7) (base + 9) (base + 10),
        natSubBlock (base + 4) (base + 8) (base + 9) (base + 10),
        .action (.constant base 1)]).Safe memory width s := by
    apply select_safe_sequence memory width _ _ s fit
    intro block hb t ft
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with h | h | h | h | h <;> subst block
    · exact subSafe 0 (by decide) t ft
    · exact subSafe 1 (by decide) t ft
    · exact subSafe 2 (by decide) t ft
    · exact subSafe 3 (by decide) t ft
    · exact Block.safe_action memory width _ t ft one
  exact select_safe_branch memory width _ _ _ (Block.safe_skip memory width)
    (select_safe_branch memory width _ _ _ (Block.safe_skip memory width)
      (select_safe_branch memory width _ _ _ (Block.safe_skip memory width)
        (select_safe_branch memory width _ _ _ (Block.safe_skip memory width) tail))) s fit

theorem selectEntryBlock_safe (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderSafe shape memory reader) (hwrites : ReaderWrites reader)
    (segment indexReg base : Nat) (hb : 190 ≤ base)
    (hsegments : segment + 4 ≤ 2 ^ wordWidth shape.size) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (selectEntryBlock reader segment indexReg base).Safe memory (wordWidth shape.size) s := by
  have one := select_constant_fit shape.size 1 (by decide)
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs
      subst status
      have first := Block.safe_action memory (wordWidth shape.size) (.constant base 0)
        ⟨regs, .running⟩ fit (Nat.two_pow_pos _)
      have fp := Block.eval_fits _ _ _ _ first
      have second := Block.safe_action memory (wordWidth shape.size) (.constant (base + 9) 1)
        _ fp one
      have fq := Block.eval_fits _ _ _ _ second
      have mp : MetadataMatches shape ((regs.write base 0).write (base + 9) 1) :=
        MetadataMatches.write shape _ (MetadataMatches.write shape regs hm base 0 (Or.inr hb))
          (base + 9) 1 (Or.inr (by omega))
      have fields := selectFieldsFrom_safe shape memory reader hreader hwrites segment indexReg
        (base + 5) 4 (by omega) hsegments _ fq mp
      have fr := Block.eval_fits _ _ _ _ fields
      have decode := selectEntryDecode_safe base memory _ one _ fr
      exact Block.safe_seq first (Block.safe_seq second (Block.safe_seq fields
        (Block.safe_seq decode (Block.safe_skip memory _ _ (Block.eval_fits _ _ _ _ decode)))))
  · exact Block.safe_stopped memory _ _ s fit hs

theorem select_metadata_geometry (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    regs 16 = shape.size ∧ 0 < regs 25 ∧ 0 < regs 26 ∧ 0 < regs 32 ∧
      regs 32 ≤ packedReviewerCellWidth shape.size ∧ 0 < regs 34 ∧
      regs 34 ≤ packedReviewerCellWidth shape.size := by
  have h16 : regs 16 = shape.size := hm 0 (by decide)
  have h25 : regs 25 = packedSelectSuperStride shape.size := hm 9 (by decide)
  have h26 : regs 26 = packedSelectLocalStride shape.size := hm 10 (by decide)
  have h32 : regs 32 = packedBpCodeWordWidth shape.size := hm 16 (by decide)
  have h34 := metadata_chunkBits shape regs hm
  have hbp : packedBpCodeWordWidth shape.size ≤ packedReviewerCellWidth shape.size := by
    apply packedReviewerMachineWordBits_le_cellWidth
    have := packedTwoMul_le_reviewerBound shape.size
    omega
  have hc : packedFringeChunkBits shape.size ≤ packedBpCodeWordWidth shape.size := by
    have := Nat.div_le_self (Nat.log2 (2 * shape.size)) 8
    change Nat.log2 (2 * shape.size) / 8 + 1 ≤ Nat.log2 (2 * shape.size) + 1
    omega
  rw [h25, h26, h32, h34]
  exact ⟨h16, GenericSelect.superStride_pos _, GenericSelect.localStride_pos _,
    packedBpCodeWordWidth_pos _, hbp, by change 0 < Nat.log2 (2 * shape.size) / 8 + 1; omega,
    Nat.le_trans hc hbp⟩

theorem selectEntryOfPackets_bounds (q p0 p1 p2 p3 : Nat)
    (h0 : p0 ≤ q) (h1 : p1 ≤ q) (h2 : p2 ≤ q) (h3 : p3 ≤ q) :
    match selectEntryOfPackets p0 p1 p2 p3 with
    | none => True
    | some entry => entry.baseOccurrence ≤ q ∧ entry.baseWordIndex ≤ q ∧
        entry.rankBefore ≤ q ∧ entry.firstOffset ≤ q := by
  by_cases h : p0 = 0 ∨ p1 = 0 ∨ p2 = 0 ∨ p3 = 0
  · simp [selectEntryOfPackets, h]
  · simp [selectEntryOfPackets, h]
    omega

theorem selectEntryRead_bounds (shape : CartesianShape)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases) (index : Nat) :
    match (packedSelectEntryRead layout (concreteBPNativeSuccinctRMQGlobalReadStore shape) index).value with
    | none => True
    | some entry => entry.baseOccurrence ≤ 2 ^ packedReviewerCellWidth shape.size ∧
        entry.baseWordIndex ≤ 2 ^ packedReviewerCellWidth shape.size ∧
        entry.rankBefore ≤ 2 ^ packedReviewerCellWidth shape.size ∧
        entry.firstOffset ≤ 2 ^ packedReviewerCellWidth shape.size := by
  rw [selectEntryRead_value, ← selectEntryOfPackets_logicalPacket]
  exact selectEntryOfPackets_bounds _ _ _ _ _
    (select_logicalPacket_bound shape layout.baseOccurrence index)
    (select_logicalPacket_bound shape layout.baseWordIndex index)
    (select_logicalPacket_bound shape layout.rankBefore index)
    (select_logicalPacket_bound shape layout.firstOffset index)

theorem selectEntryBlock_present_bounds (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (segment indexReg base : Nat) (hb : 190 ≤ base) (hupper : base + 11 ≤ 8192)
    (hi : indexReg < 8192) (hout : indexReg < base ∨ base + 11 ≤ indexReg)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (selectEntryBlock reader segment indexReg base).eval memory ⟨regs, .running⟩
    actual.final.regs base ≠ 0 →
      actual.final.regs (base + 1) ≤ 2 ^ packedReviewerCellWidth shape.size ∧
      actual.final.regs (base + 2) ≤ 2 ^ packedReviewerCellWidth shape.size ∧
      actual.final.regs (base + 3) ≤ 2 ^ packedReviewerCellWidth shape.size ∧
      actual.final.regs (base + 4) ≤ 2 ^ packedReviewerCellWidth shape.size := by
  dsimp only
  have source := selectEntryBlock_source shape memory reader hreader hwrites segment indexReg base
    hb hupper hi hout regs hm
  have bounds := selectEntryRead_bounds shape (selectEntryLayout segment) (regs indexReg)
  cases he : (packedSelectEntryRead (selectEntryLayout segment)
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) (regs indexReg)).value with
  | none =>
      simp only [SelectEntryResult, he] at source
      exact fun h => (h source.1.2).elim
  | some entry =>
      simp only [SelectEntryResult, he] at source
      simp only [he] at bounds
      intro _
      rw [source.1.2.2.1, source.1.2.2.2.1, source.1.2.2.2.2.1, source.1.2.2.2.2.2]
      exact bounds

theorem selectWordAddress_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n) (hj : regs 404 < 8) :
    selectWordAddress.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have a := Block.safe_action memory (wordWidth n) (.move 280 400)
    ⟨regs, .running⟩ fit (fit.1 400)
  have fa := Block.eval_fits _ _ _ _ a
  have b := Block.safe_action memory (wordWidth n) (.move 281 34) _ fa (fa.1 34)
  have fb := Block.eval_fits _ _ _ _ b
  have c := Block.safe_action memory (wordWidth n) (.move 282 404) _ fb (fb.1 404)
  have fc := Block.eval_fits _ _ _ _ c
  have d := Block.safe_action memory (wordWidth n) (.move 283 401) _ fc (fc.1 401)
  have fd := Block.eval_fits _ _ _ _ d
  have slot := chunkSlotBlock_canonical_safe 280 n memory _ fd
    (by simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write] using hc)
    (by simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write] using hj)
  have fs := Block.eval_fits _ _ _ _ slot
  have tail := SimpleScalar.safe memory (wordWidth n)
    (Block.sequence [.action (.constant 8192 21), .action (.move 8193 286)])
    ⟨select_constant_fit n 21 (by decide), True.intro, True.intro⟩ _ fs
  exact Block.safe_seq a (Block.safe_seq b (Block.safe_seq c
    (Block.safe_seq d (Block.safe_seq slot tail))))

theorem selectWordDecode_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n) (hl : regs 284 ≤ regs 34) :
    selectWordDecode.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have a := Block.safe_action memory (wordWidth n) (.move 300 34)
    ⟨regs, .running⟩ fit (fit.1 34)
  have fa := Block.eval_fits _ _ _ _ a
  have b := Block.safe_action memory (wordWidth n) (.move 301 284) _ fa (fa.1 284)
  have fb := Block.eval_fits _ _ _ _ b
  have sub := natSubBlock_safe memory (wordWidth n) 302 8194 407 409 _ fb
    (select_constant_fit n 1 (by decide)) (by decide) (by decide)
  have fs := Block.eval_fits _ _ _ _ sub
  have zero := Block.safe_action memory (wordWidth n) (.constant 303 0) _ fs (Nat.two_pow_pos _)
  have fz := Block.eval_fits _ _ _ _ zero
  have hsub (r : Registers) := natSubBlock_source 302 8194 407 409 memory r (by decide) (by decide)
  have decode := chunkRankBlock_canonical_safe 300 n memory _ fz
    (by simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write, hsub] using hc)
    (by simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write, hsub] using hl)
  exact Block.safe_seq a (Block.safe_seq b (Block.safe_seq sub
    (Block.safe_seq zero (Block.safe_seq decode
      (Block.safe_skip memory _ _ (Block.eval_fits _ _ _ _ decode))))))

theorem selectWordMiss_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hj : regs 404 < 8) (hone : regs 407 = 1) :
    selectWordMiss.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  apply ScalarChecks_safe memory _ _ _ fit
  have cap := select_constant_fit n 9 (by decide)
  have hwne : wordWidth n ≠ 0 := by unfold wordWidth; omega
  have fk := fit.1 406
  dsimp only at fk
  by_cases hsub : regs 304 ≤ regs 406
  all_goals simp [ScalarChecks, selectWordMiss, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
    hsub, hone, hwne] <;> omega

theorem selectWordSelectAddress_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n) (hone : regs 407 = 1)
    (hvalue : regs 285 ≤ 2 ^ packedReviewerCellWidth n) (hk : regs 406 ≤ regs 34) :
    selectWordSelectAddress.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  let e := metadataEnvelope n
  have ep : 0 < e := metadataEnvelope_pos n
  have hw := Nat.lt_two_pow_self (n := packedReviewerCellWidth n)
  have hq := select_old_capacity_le_envelope n
  have cp : regs 34 + 1 ≤ e := by dsimp only [e]; omega
  have vp : regs 285 ≤ e := by dsimp only [e]; omega
  have kp : regs 406 ≤ e := by omega
  have hp := Nat.mul_le_mul vp cp
  have hsquare : e ≤ e * e := by
    simpa using Nat.mul_le_mul_left e (show 1 ≤ e by omega)
  have cap := select_envelope_square_fit n
  change 256 * (e * e) < _ at cap
  have const := select_constant_fit n 22 (by decide)
  apply ScalarChecks_safe memory _ _ _ fit
  simp [ScalarChecks, selectWordSelectAddress, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, hone]
  omega

theorem selectWordFinish_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs 34 ≤ packedReviewerCellWidth n) (hj : regs 404 < 8)
    (hone : regs 407 = 1) (hreply : regs 8194 ≤ 2 ^ packedReviewerCellWidth n) :
    selectWordFinish.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have hp := Nat.mul_le_mul (show regs 404 ≤ 7 by omega) hc
  have he := rank_output_envelope n
  have hq := Nat.two_pow_pos (packedReviewerCellWidth n)
  have cap := metadataEnvelope_lt_wordCapacity n
  have hwne : wordWidth n ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe memory _ _ _ fit
  by_cases hsub : 1 ≤ regs 8194
  all_goals simp [ScalarChecks, selectWordFinish, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
    hsub, hone, hwne] <;> omega

theorem selectWordInit_safe (n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : 0 < regs 34) (hl : regs 401 ≤ packedReviewerCellWidth n) :
    selectWordInit.Safe memory (wordWidth n) ⟨regs, .running⟩ := by
  have hdiv := Nat.div_le_self (regs 401 - 1) (regs 34)
  have hw := Nat.lt_two_pow_self (n := packedReviewerCellWidth n)
  have he := rank_output_envelope n
  have cap := metadataEnvelope_lt_wordCapacity n
  have const := select_constant_fit n 9 (by decide)
  have hk := fit.1 402
  dsimp only at hk
  have hwne : wordWidth n ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe memory _ _ _ fit
  by_cases hsub : 1 ≤ regs 401
  · by_cases hmin : (regs 401 - 1) / regs 34 + 1 ≤ 8
    all_goals simp [ScalarChecks, selectWordInit, Block.sequence, Block.eval,
      Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
      Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
      minBlock, hsub, hmin, hwne] <;> omega
  · have hz : regs 401 = 0 := by omega
    simp [ScalarChecks, selectWordInit, Block.sequence, Block.eval,
      Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
      Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
      minBlock, hz, hwne]
    omega

private theorem select_safe_follow {memory : Memory} {width : Nat}
    {first second : Block} {s : Data} (head : first.Safe memory width s)
    (tail : (first.eval memory s).final.Fits width →
      second.Safe memory width (first.eval memory s).final) :
    (Block.seq first second).Safe memory width s :=
  Block.safe_seq head (tail (first.eval_fits memory width s head))

private theorem select_follow_post {memory : Memory} {width : Nat}
    {first second : Block} {s : Data} (post : Data → Prop)
    (head : first.Safe memory width s)
    (tail : (first.eval memory s).final.Fits width →
      second.Safe memory width (first.eval memory s).final ∧
        post (second.eval memory (first.eval memory s).final).final) :
    (Block.seq first second).Safe memory width s ∧
      post ((Block.seq first second).eval memory s).final := by
  have next := tail (Block.eval_fits _ _ _ _ head)
  exact ⟨Block.safe_seq head next.1, by
    simpa only [Block.eval_seq, Evaluation.bind] using next.2⟩

private theorem select_metadata_frame (shape : CartesianShape) (memory : Memory)
    (block : Block) (allowed : Nat → Prop) (writes : block.WritesOnly allowed)
    (outside : ∀ r, 16 ≤ r → r < 190 → ¬ allowed r)
    (s : Data) (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape (block.eval memory s).final.regs := by
  intro i hi
  rw [Block.eval_frame memory block allowed writes _ (outside _ (by omega) (by omega))]
  exact hm i hi

private theorem select_data_running (s : Data) (hs : s.status = .running) :
    s = ⟨s.regs, .running⟩ := by cases s; simp_all

theorem select_decodedReply_bound (shape : CartesianShape) (segment index : Nat) :
    (((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index).map
      bitsToNatLE).getD 0 ≤ 2 ^ packedReviewerCellWidth shape.size := by
  have h := select_logicalPacket_bound shape segment index
  rw [← logicalPacket_pred]
  omega

theorem selectWordSelected_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hj : regs 404 < 8) (hone : regs 407 = 1)
    (hvalue : regs 285 ≤ 2 ^ packedReviewerCellWidth shape.size) (hk : regs 406 ≤ regs 34) :
    (selectWordSelected logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size)
      ⟨regs, .running⟩ := by
  have hc := (select_metadata_geometry shape regs hm).2.2.2.2.2.2
  have head := selectWordSelectAddress_safe shape.size (shapeMemory shape) regs fit hc hone hvalue hk
  refine select_safe_follow head (fun fa => ?_)
  have hw : selectWordSelectAddress.WritesOnly (fun r => r = 410 ∨ r = 8192 ∨ r = 8193) := by
    simp [selectWordSelectAddress, Block.sequence, Block.WritesOnly, Action.destination]
  have frame (r : Nat) (ho : r ≠ 410 ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    Block.eval_frame (shapeMemory shape) _ _ hw r (by omega) ⟨regs, .running⟩
  have metadataA := select_metadata_frame shape (shapeMemory shape) _ _ hw
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have src := selectWordSelectAddress_source (shapeMemory shape) regs
  generalize he : selectWordSelectAddress.eval (shapeMemory shape) ⟨regs, .running⟩ = addressed
    at src frame metadataA fa ⊢
  rcases addressed with ⟨⟨ar, ast⟩, ard⟩
  dsimp only at src frame metadataA fa
  have hs := src.1
  subst ast
  have loadSafe := logicalReadBlock_safe shape ⟨ar, .running⟩ fa metadataA
  refine select_safe_follow loadSafe (fun fb => ?_)
  have reader := logicalReadBlock_correct shape ar metadataA
  have bound := logicalReadBlock_output_bounds shape ar metadataA
  generalize heR : logicalReadBlock.eval (shapeMemory shape) ⟨ar, .running⟩ = loaded
    at reader bound fb ⊢
  rcases loaded with ⟨⟨br, bst⟩, brd⟩
  dsimp only at reader bound fb
  have hs := reader.1
  subst bst
  have finish := selectWordFinish_safe shape.size (shapeMemory shape) br fb
    (by rw [reader.2.2.2.2 34 (Or.inl (by decide)), frame 34 (by omega)]; exact hc)
    (by rw [reader.2.2.2.2 404 (Or.inl (by decide)), frame 404 (by omega)]; exact hj)
    (by rw [reader.2.2.2.2 407 (Or.inl (by decide)), frame 407 (by omega)]; exact hone)
    bound.1
  exact Block.safe_seq finish (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ finish))

theorem selectWordActive_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hj : regs 404 < 8) (hone : regs 407 = 1) :
    (selectWordActive logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size)
      ⟨regs, .running⟩ := by
  have hc := (select_metadata_geometry shape regs hm).2.2.2.2.2.2
  have first := selectWordAddress_safe shape.size (shapeMemory shape) regs fit hc hj
  refine select_safe_follow first (fun fa => ?_)
  have srcA := selectWordAddress_source (shapeMemory shape) regs
  have metaA := select_metadata_frame shape (shapeMemory shape) _ _ selectWordAddress_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frameA (r : Nat) (ho : (r < 280 ∨ 292 ≤ r) ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    selectWordAddress_frame (shapeMemory shape) ⟨regs, .running⟩ r ho
  generalize heA : selectWordAddress.eval (shapeMemory shape) ⟨regs, .running⟩ = addressed
    at srcA metaA frameA fa ⊢
  rcases addressed with ⟨⟨ar, ast⟩, ard⟩
  dsimp only at srcA metaA frameA fa
  have hs := srcA.1
  subst ast
  have loadSafe := logicalReadBlock_safe shape ⟨ar, .running⟩ fa metaA
  refine select_safe_follow loadSafe (fun fb => ?_)
  have srcB := logicalReadBlock_correct shape ar metaA
  generalize heB : logicalReadBlock.eval (shapeMemory shape) ⟨ar, .running⟩ = loaded
    at srcB fb ⊢
  rcases loaded with ⟨⟨br, bst⟩, brd⟩
  dsimp only at srcB fb
  have hs := srcB.1
  subst bst
  have frameB := srcB.2.2.2.2
  have metaB := frameB.metadata shape ar br metaA
  have cb : br 34 = regs 34 := by rw [frameB 34 (Or.inl (by decide)), frameA 34 (by omega)]
  have lb : br 284 ≤ br 34 := by
    rw [frameB 284 (Or.inl (by decide)), srcA.2.2.2.2.1, cb]
    exact Nat.min_le_left _ _
  have decode := selectWordDecode_safe shape.size (shapeMemory shape) br fb (by omega) lb
  refine select_safe_follow decode (fun fc => ?_)
  have srcC := selectWordDecode_source (shapeMemory shape) br
  have metaC := select_metadata_frame shape (shapeMemory shape) _ _ selectWordDecode_writes
    (by intro r h1 h2; omega) ⟨br, .running⟩ metaB
  have frameC (r : Nat) (ho : (r < 300 ∨ 311 ≤ r) ∧ r ≠ 409) :=
    Block.eval_frame (shapeMemory shape) _ _ selectWordDecode_writes r (by omega) ⟨br, .running⟩
  generalize heC : selectWordDecode.eval (shapeMemory shape) ⟨br, .running⟩ = decoded
    at srcC metaC frameC fc ⊢
  rcases decoded with ⟨⟨cr, cst⟩, crd⟩
  dsimp only at srcC metaC frameC fc
  have hs := srcC.1
  subst cst
  have kept (r : Nat) (hrange : r < 280 ∨ (311 ≤ r ∧ r < 8192)) (hne : r ≠ 409) :
      cr r = regs r := by
    rw [frameC r ⟨by omega, hne⟩, frameB r (Or.inl (by omega)), frameA r ⟨by omega, by omega, by omega⟩]
  have rankBound : cr 304 ≤ cr 34 := by
    rw [srcC.2.2, frameC 34 (by omega)]
    exact chunkRank_le_chunk _ _ _ _ lb
  have valueBound : cr 285 ≤ 2 ^ packedReviewerCellWidth shape.size := by
    rw [frameC 285 (by omega), frameB 285 (Or.inl (by decide)), srcA.2.2.2.2.2]
    exact Nat.le_trans (Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (Nat.pow_le_pow_right (by decide) hc)
  have compare := Block.safe_action (shapeMemory shape) (wordWidth shape.size)
    (.comparison .lt 408 406 304) ⟨cr, .running⟩ fc
    (by dsimp only [Action.LocalSafe, Comparison.eval]; split <;>
      exact select_constant_fit shape.size _ (by decide))
  refine select_safe_follow compare (fun ft => ?_)
  have testMeta := MetadataMatches.write shape cr metaC 408
    (Comparison.lt.eval (cr 406) (cr 304)) (Or.inr (by decide))
  by_cases active : cr 406 < cr 304
  · have selected := selectWordSelected_safe shape
      (cr.write 408 (Comparison.lt.eval (cr 406) (cr 304))) ft testMeta
      (by simpa [Registers.write, kept 404 (by omega) (by decide)] using hj)
      (by simpa [Registers.write, kept 407 (by omega) (by decide)] using hone)
      (by simpa [Registers.write] using valueBound)
      (by simpa [Registers.write] using Nat.le_trans (Nat.le_of_lt active) rankBound)
    have final := Block.safe_ifZero (condition := 408) (zero := selectWordMiss)
      (nonzero := selectWordSelected logicalReadBlock) ft (by
      simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
        Data.ofState, Registers.write, Comparison.eval, active] using selected)
    exact Block.safe_seq final (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ final))
  · have missed := selectWordMiss_safe shape.size (shapeMemory shape)
      (cr.write 408 (Comparison.lt.eval (cr 406) (cr 304))) ft
      (by simpa [Registers.write, kept 404 (by omega) (by decide)] using hj)
      (by simpa [Registers.write, kept 407 (by omega) (by decide)] using hone)
    have final := Block.safe_ifZero (condition := 408) (zero := selectWordMiss)
      (nonzero := selectWordSelected logicalReadBlock) ft (by
      simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
        Data.ofState, Registers.write, Comparison.eval, active] using missed)
    exact Block.safe_seq final (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ final))

theorem selectWordActive_output_bound (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (hj : regs 404 < 8) (hone : regs 407 = 1)
    (hout : regs 403 ≤ metadataEnvelope shape.size) :
    ((selectWordActive logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 403 ≤
      metadataEnvelope shape.size := by
  have source := selectWordActive_source shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm hone
  have hvalue := select_decodedReply_bound shape 22
    ((regs 400 / 2 ^ (regs 404 * regs 34) % 2 ^ regs 34) * (regs 34 + 1) + regs 406)
  have hc := (select_metadata_geometry shape regs hm).2.2.2.2.2.2
  have hp := Nat.mul_le_mul (show regs 404 ≤ 7 by omega) hc
  have he := rank_output_envelope shape.size
  have hq := Nat.two_pow_pos (packedReviewerCellWidth shape.size)
  dsimp only at source
  rw [source.2.1]
  split <;> omega

theorem selectWordBody_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs)
    (total : s.regs 405 ≤ 8) (hone : s.regs 407 = 1) :
    (selectWordBody logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs total hone
      subst status
      apply Block.safe_ifZero fit
      by_cases hfound : regs 403 = 0
      · simp only [hfound, if_pos]
        have compare := Block.safe_action (shapeMemory shape) (wordWidth shape.size)
          (.comparison .lt 408 404 405) ⟨regs, .running⟩ fit
          (by dsimp only [Action.LocalSafe, Comparison.eval]; split <;>
            exact select_constant_fit shape.size _ (by decide))
        refine select_safe_follow compare (fun fp => ?_)
        apply Block.safe_ifZero fp
        by_cases active : regs 404 < regs 405
        · have mp := MetadataMatches.write shape regs hm 408
            (Comparison.lt.eval (regs 404) (regs 405)) (Or.inr (by decide))
          have child := selectWordActive_safe shape
            (regs.write 408 (Comparison.lt.eval (regs 404) (regs 405))) fp mp
            (by simp [Registers.write]; omega) (by simpa [Registers.write] using hone)
          simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
            Data.ofState, Registers.write, Comparison.eval, active] using child
        · simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
            Data.ofState, Registers.write, Comparison.eval, active] using
            Block.safe_skip (shapeMemory shape) (wordWidth shape.size) _ fp
      · simpa [hfound] using Block.safe_skip (shapeMemory shape) (wordWidth shape.size) _ fit
  · exact Block.safe_stopped _ _ _ s fit hs

def SelectWordSafetyInv (shape : CartesianShape) (s : Data) : Prop :=
  s.Fits (wordWidth shape.size) ∧ MetadataMatches shape s.regs ∧
    s.regs 405 ≤ 8 ∧ s.regs 407 = 1 ∧ s.regs 403 ≤ metadataEnvelope shape.size

private theorem select_guard_active (memory : Memory) (body : Block) (regs : Registers)
    (found : regs 403 = 0) (active : regs 404 < regs 405) :
    (Block.ifZero 403 (.seq (.action (.comparison .lt 408 404 405))
      (.ifZero 408 .skip body)) .skip).eval memory ⟨regs, .running⟩ =
      body.eval memory ⟨regs.write 408 1, .running⟩ := by
  simp [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
    Data.ofState, Registers.write, Comparison.eval, found, active]

private theorem select_guard_active_bound (memory : Memory) (body : Block) (regs : Registers)
    (limit : Nat) (found : regs 403 = 0) (active : regs 404 < regs 405)
    (bound : (body.eval memory ⟨regs.write 408 1, .running⟩).final.regs 403 ≤ limit) :
    ((Block.ifZero 403 (.seq (.action (.comparison .lt 408 404 405))
      (.ifZero 408 .skip body)) .skip).eval memory ⟨regs, .running⟩).final.regs 403 ≤ limit := by
  rw [select_guard_active memory body regs found active]
  exact bound

private theorem select_guard_active_status (memory : Memory) (body : Block) (regs : Registers)
    (found : regs 403 = 0) (active : regs 404 < regs 405)
    (status : (body.eval memory ⟨regs.write 408 1, .running⟩).final.status = .running) :
    ((Block.ifZero 403 (.seq (.action (.comparison .lt 408 404 405))
      (.ifZero 408 .skip body)) .skip).eval memory ⟨regs, .running⟩).final.status = .running := by
  rw [select_guard_active memory body regs found active]
  exact status

theorem selectWordBody_running (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (hone : regs 407 = 1) :
    ((selectWordBody logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running := by
  by_cases found : regs 403 = 0
  · by_cases active : regs 404 < regs 405
    · have source := selectWordActive_source shape (shapeMemory shape) logicalReadBlock
        (logicalReadBlock_correct shape) logicalReadBlock_writesOnly (regs.write 408 1)
        (MetadataMatches.write shape regs hm 408 1 (Or.inr (by decide)))
        (by simpa [Registers.write] using hone)
      exact select_guard_active_status (shapeMemory shape) (selectWordActive logicalReadBlock)
        regs found active source.1
    · rw [selectWordBody_inactive logicalReadBlock (shapeMemory shape) regs found (by omega)]
  · rw [selectWordBody_found logicalReadBlock (shapeMemory shape) regs found]

theorem selectWordBody_safe_invariant (shape : CartesianShape) (s : Data)
    (inv : SelectWordSafetyInv shape s) :
    (selectWordBody logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s ∧
      SelectWordSafetyInv shape
        ((selectWordBody logicalReadBlock).eval (shapeMemory shape) s).final := by
  obtain ⟨fit, hm, total, hone, hout⟩ := inv
  have safe := selectWordBody_safe shape s fit hm total hone
  have fp := Block.eval_fits _ _ _ _ safe
  have mp := selectWordBody_metadata shape logicalReadBlock logicalReadBlock_writesOnly
    (shapeMemory shape) s hm
  have fr405 := selectWordBody_frame logicalReadBlock logicalReadBlock_writesOnly
    (shapeMemory shape) s 405 (by simp [SelectWordBodyWrites])
  have fr407 := selectWordBody_frame logicalReadBlock logicalReadBlock_writesOnly
    (shapeMemory shape) s 407 (by simp [SelectWordBodyWrites])
  refine ⟨safe, fp, mp, by omega, by omega, ?_⟩
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs total hone hout
      subst status
      by_cases found : regs 403 = 0
      · by_cases active : regs 404 < regs 405
        · let tested := regs.write 408 1
          have source := selectWordActive_output_bound shape tested
            (MetadataMatches.write shape regs hm 408 1 (Or.inr (by decide)))
            (by simp [tested, Registers.write]; omega)
            (by simpa [tested, Registers.write] using hone)
            (by simpa [tested, Registers.write] using hout)
          dsimp only [tested] at source
          exact select_guard_active_bound (shapeMemory shape) (selectWordActive logicalReadBlock)
            regs (metadataEnvelope shape.size) found active source
        · rw [selectWordBody_inactive logicalReadBlock (shapeMemory shape) regs found (by omega)]
          simpa [Registers.write] using hout
      · rw [selectWordBody_found logicalReadBlock (shapeMemory shape) regs found]
        exact hout
  · rw [Block.eval_stopped _ _ _ hs]
    exact hout

theorem selectWordBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs)
    (hl : s.regs 401 ≤ packedReviewerCellWidth shape.size) :
    (selectWordBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs hl
      subst status
      have hc := (select_metadata_geometry shape regs hm).2.2.2.2.2.1
      have initSafe := selectWordInit_safe shape.size (shapeMemory shape) regs fit hc hl
      refine select_safe_follow initSafe (fun fp => ?_)
      have source := selectWordInit_source (shapeMemory shape) regs
      have hw : selectWordInit.WritesOnly (fun r => 403 ≤ r ∧ r ≤ 409) := by
        simp [selectWordInit, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, minBlock]
      have mp := select_metadata_frame shape (shapeMemory shape) _ _ hw
        (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
      generalize he : selectWordInit.eval (shapeMemory shape) ⟨regs, .running⟩ = initialized
        at source mp fp ⊢
      rcases initialized with ⟨⟨ir, ist⟩, ireads⟩
      dsimp only at source mp fp
      have hs := source.1
      subst ist
      have inv : SelectWordSafetyInv shape ⟨ir, .running⟩ := by
        refine ⟨fp, mp, ?_, source.2.2.2.2.2.2, ?_⟩
        · dsimp only
          rw [source.2.2.2.2.1]
          exact Nat.min_le_right _ _
        · dsimp only
          rw [source.2.2.1]
          omega
      exact Block.safe_repeat fp (IterationsSafe.of_invariant _ (SelectWordSafetyInv shape)
        ((selectWordBody logicalReadBlock).eval (shapeMemory shape))
        (selectWordBody_safe_invariant shape) 8 _ inv)
  · exact Block.safe_stopped _ _ _ s fit hs

private theorem select_repeat_preserves (memory : Memory) (body : Block) (inv : Data → Prop)
    (preserve : ∀ s, inv s → inv (body.eval memory s).final)
    (count : Nat) (s : Data) (hs : inv s) :
    inv ((Block.repeat count body).eval memory s).final := by
  rw [Block.eval_repeat]
  induction count generalizing s with
  | zero => exact hs
  | succ count ih =>
      exact ih _ (preserve s hs)

private theorem select_init_repeat_bound (memory : Memory) (initializer body : Block)
    (inv : Data → Prop) (preserve : ∀ s, inv s → inv (body.eval memory s).final)
    (count : Nat) (s : Data) (initial : inv (initializer.eval memory s).final)
    (limit : Nat) (output : ∀ s, inv s → s.regs 403 ≤ limit)
    (program : Block) (program_eq : program = .seq initializer (.repeat count body)) :
    (program.eval memory s).final.regs 403 ≤ limit := by
  rw [program_eq, Block.eval_seq]
  exact output _ (select_repeat_preserves memory body inv preserve count _ initial)

private theorem select_init_repeat_property (memory : Memory) (initializer body : Block)
    (inv : Data → Prop) (preserve : ∀ s, inv s → inv (body.eval memory s).final)
    (count : Nat) (s : Data) (initial : inv (initializer.eval memory s).final)
    (property : Data → Prop) (conclude : ∀ s, inv s → property s)
    (program : Block) (program_eq : program = .seq initializer (.repeat count body)) :
    property (program.eval memory s).final := by
  rw [program_eq, Block.eval_seq]
  exact conclude _ (select_repeat_preserves memory body inv preserve count _ initial)

theorem selectWordBlock_running (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    ((selectWordBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running := by
  let inv (s : Data) := s.status = .running ∧ MetadataMatches shape s.regs ∧ s.regs 407 = 1
  have preserve (s : Data) (hs : inv s) : inv
      ((selectWordBody logicalReadBlock).eval (shapeMemory shape) s).final := by
    have running := select_data_running s hs.1
    have st := selectWordBody_running shape s.regs hs.2.1 hs.2.2
    have mp := selectWordBody_metadata shape logicalReadBlock logicalReadBlock_writesOnly
      (shapeMemory shape) s hs.2.1
    have one := selectWordBody_frame logicalReadBlock logicalReadBlock_writesOnly
      (shapeMemory shape) s 407 (by simp [SelectWordBodyWrites])
    exact ⟨by rw [running]; exact st, mp, one.trans hs.2.2⟩
  have source := selectWordInit_source (shapeMemory shape) regs
  have hw : selectWordInit.WritesOnly (fun r => 403 ≤ r ∧ r ≤ 409) := by
    simp [selectWordInit, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, minBlock]
  have mp := select_metadata_frame shape (shapeMemory shape) _ _ hw
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have initial : inv (selectWordInit.eval (shapeMemory shape) ⟨regs, .running⟩).final :=
    ⟨source.1, mp, source.2.2.2.2.2.2⟩
  exact select_init_repeat_property (shapeMemory shape) selectWordInit (selectWordBody logicalReadBlock)
    inv preserve 8 _ initial (fun s => s.status = .running) (fun _ h => h.1)
    (selectWordBlock logicalReadBlock) rfl

theorem selectWordBlock_output_bound (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hl : regs 401 ≤ packedReviewerCellWidth shape.size) :
    ((selectWordBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 403 ≤
      metadataEnvelope shape.size := by
  have hc := (select_metadata_geometry shape regs hm).2.2.2.2.2.1
  have initSafe := selectWordInit_safe shape.size (shapeMemory shape) regs fit hc hl
  have fp := Block.eval_fits _ _ _ _ initSafe
  have source := selectWordInit_source (shapeMemory shape) regs
  have hw : selectWordInit.WritesOnly (fun r => 403 ≤ r ∧ r ≤ 409) := by
    simp [selectWordInit, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, minBlock]
  have mp := select_metadata_frame shape (shapeMemory shape) _ _ hw
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have inv : SelectWordSafetyInv shape (selectWordInit.eval (shapeMemory shape) ⟨regs, .running⟩).final := by
    refine ⟨fp, mp, ?_, source.2.2.2.2.2.2, ?_⟩
    · rw [source.2.2.2.2.1]
      exact Nat.min_le_right _ _
    · rw [source.2.2.1]
      omega
  exact select_init_repeat_bound (shapeMemory shape) selectWordInit (selectWordBody logicalReadBlock)
    (SelectWordSafetyInv shape) (fun s hs => (selectWordBody_safe_invariant shape s hs).2)
    8 _ inv (metadataEnvelope shape.size) (fun _ h => h.2.2.2.2)
    (selectWordBlock logicalReadBlock) rfl

theorem selectLongAddress_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hrank : regs 360 ≤ metadataEnvelope shape.size)
    (hocc : regs 512 ≤ metadataEnvelope shape.size) :
    selectLongAddress.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  let e := metadataEnvelope shape.size
  have stride := hm.envelope shape regs 25 (by decide)
  have hp := Nat.mul_le_mul hrank stride
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e (metadataEnvelope_pos _)
  have cap := select_envelope_square_fit shape.size
  change 256 * (e * e) < _ at cap
  have one := select_constant_fit shape.size 12 (by decide)
  have hwne : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : regs 561 ≤ regs 512
  all_goals simp [ScalarChecks, selectLongAddress, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
    hsub, hwne] <;> dsimp only [e] at * <;> omega

theorem selectSparseAddress_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hrank : regs 360 ≤ metadataEnvelope shape.size)
    (hocc : regs 512 ≤ metadataEnvelope shape.size) :
    selectSparseAddress.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  let e := metadataEnvelope shape.size
  have stride := hm.envelope shape regs 26 (by decide)
  have hp := Nat.mul_le_mul hrank stride
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e (metadataEnvelope_pos _)
  have cap := select_envelope_square_fit shape.size
  change 256 * (e * e) < _ at cap
  have one := select_constant_fit shape.size 16 (by decide)
  have hwne : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : regs 521 ≤ regs 512
  all_goals simp [ScalarChecks, selectSparseAddress, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
    hsub, hwne] <;> dsimp only [e] at * <;> omega

theorem selectLongFinish_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hword : regs 562 ≤ metadataEnvelope shape.size)
    (hoffset : regs 564 ≤ metadataEnvelope shape.size)
    (hreply : regs 8194 ≤ metadataEnvelope shape.size) :
    selectLongFinish.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  let e := metadataEnvelope shape.size
  have word := hm.envelope shape regs 32 (by decide)
  have hp := Nat.mul_le_mul hword word
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e (metadataEnvelope_pos _)
  have cap := select_envelope_square_fit shape.size
  change 256 * (e * e) < _ at cap
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases absent : regs 8194 = 0
  all_goals simp [ScalarChecks, selectLongFinish, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, absent] <;> dsimp only [e] at * <;> omega

theorem selectSparseFinish_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hbase : regs 520 ≤ 3 * (metadataEnvelope shape.size * metadataEnvelope shape.size))
    (hreply : regs 8194 ≤ metadataEnvelope shape.size) :
    selectSparseFinish.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  let e := metadataEnvelope shape.size
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e (metadataEnvelope_pos _)
  have cap := select_envelope_square_fit shape.size
  change 256 * (e * e) < _ at cap
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases absent : regs 8194 = 0
  all_goals simp [ScalarChecks, selectSparseFinish, Action.LocalSafe,
    Arithmetic.eval, absent] <;> dsimp only [e] at * <;> omega

theorem selectLocalAddress_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hslot : regs 514 ≤ metadataEnvelope shape.size)
    (hocc : regs 512 ≤ metadataEnvelope shape.size) :
    selectLocalAddress.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  let e := metadataEnvelope shape.size
  have stride := hm.envelope shape regs 27 (by decide)
  have hp := Nat.mul_le_mul hslot stride
  have divisor := (select_metadata_geometry shape regs hm).2.2.1
  have hd := Nat.div_le_self (regs 512 - regs 561) (regs 26)
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e (metadataEnvelope_pos _)
  have cap := select_envelope_square_fit shape.size
  change 256 * (e * e) < _ at cap
  have hwne : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : regs 561 ≤ regs 512
  all_goals simp [ScalarChecks, selectLocalAddress, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
    hsub, hwne] <;> dsimp only [e] at * <;> omega

theorem selectLocalPrepare_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (h562 : regs 562 ≤ metadataEnvelope shape.size) (h592 : regs 592 ≤ metadataEnvelope shape.size)
    (h594 : regs 594 ≤ metadataEnvelope shape.size) (h561 : regs 561 ≤ metadataEnvelope shape.size)
    (h591 : regs 591 ≤ metadataEnvelope shape.size) :
    selectLocalPrepare.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  let e := metadataEnvelope shape.size
  have word := hm.envelope shape regs 32 (by decide)
  have hp := Nat.mul_le_mul (show regs 562 + regs 592 ≤ 2 * e by dsimp only [e]; omega) word
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e (metadataEnvelope_pos _)
  have cap := select_envelope_square_fit shape.size
  change 256 * (e * e) < _ at cap
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, selectLocalPrepare, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval]
  dsimp only [e] at *
  simp only [Nat.mul_assoc] at hp
  omega

theorem denseReadAddress_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    denseReadAddress.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have pos := (select_metadata_geometry shape regs hm).2.2.2.1
  have hp := Nat.div_le_self (regs 640) (regs 32)
  have fv := fit.1 640
  dsimp only at fv
  have one := select_constant_fit shape.size 1 (by decide)
  have hwne : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, denseReadAddress, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval]
  omega

theorem denseReadSave_safe (memory : Memory) (width : Nat) (s : Data) (fit : s.Fits width) :
    denseReadSave.Safe memory width s :=
  SimpleScalar.safe memory width denseReadSave ⟨True.intro, True.intro, True.intro⟩ s fit

theorem denseFirstPrepare_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hbefore : regs 648 ≤ metadataEnvelope shape.size)
    (hremain : regs 650 ≤ metadataEnvelope shape.size) :
    denseFirstPrepare.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have cap := reader_polynomial_fit shape.size
  have ep := metadataEnvelope_pos shape.size
  have hwne : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  have fw := fit.1 645
  have fl := fit.1 646
  dsimp only at fw fl
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : regs 659 ≤ regs 645
  all_goals simp [ScalarChecks, denseFirstPrepare, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
    hsub, hwne] <;> omega

theorem denseSecondPrepare_safe (memory : Memory) (width : Nat) (one : 1 < 2 ^ width)
    (s : Data) (fit : s.Fits width) : denseSecondPrepare.Safe memory width s := by
  apply select_safe_sequence memory width _ _ s fit
  intro block hb t ft
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h <;> subst block
  · exact natSubBlock_safe memory width _ _ _ _ t ft one (by decide) (by decide)
  · exact SimpleScalar.safe memory width (.action (.move 401 8195)) True.intro t ft
  · exact natSubBlock_safe memory width _ _ _ _ t ft one (by decide) (by decide)

theorem denseSecondAddress_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hindex : regs 644 ≤ 3 * (metadataEnvelope shape.size * metadataEnvelope shape.size))
    (hone : regs 659 = 1) :
    denseSecondAddress.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have ep := metadataEnvelope_pos shape.size
  have cap := select_envelope_square_fit shape.size
  have esq := Nat.mul_pos ep ep
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, denseSecondAddress, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, hone]
  omega

theorem denseWordFinish_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hindex : regs 644 ≤ 4 * (metadataEnvelope shape.size * metadataEnvelope shape.size))
    (hpacket : regs 403 ≤ metadataEnvelope shape.size) :
    denseWordFinish.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  let e := metadataEnvelope shape.size
  have ep : 0 < e := metadataEnvelope_pos shape.size
  have word := hm.envelope shape regs 32 (by decide)
  have hp := Nat.mul_le_mul hindex word
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e ep
  have ecube : e * e ≤ e * e * e := Nat.le_mul_of_pos_right (e * e) ep
  have cap := rank_polynomial_fit shape.size
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases absent : regs 403 = 0
  all_goals simp [ScalarChecks, denseWordFinish, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, absent] <;>
    dsimp only [e] at * <;> simp only [Nat.mul_assoc] at hp cap ecube <;> omega

theorem denseRankBeforePrepare_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hindex : regs 644 = regs 640 / regs 32) :
    denseRankBeforePrepare.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hp : regs 644 * regs 32 ≤ regs 640 := by
    rw [hindex]
    have h := Nat.mod_add_div (regs 640) (regs 32)
    rw [Nat.mul_comm] at h
    omega
  have fp := fit.1 640
  have fw := fit.1 645
  have fl := fit.1 646
  dsimp only at fp fw fl
  have one := select_constant_fit shape.size 1 (by decide)
  have hwne : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : regs 659 ≤ regs 645
  all_goals simp [ScalarChecks, denseRankBeforePrepare, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
    hp, hsub, hwne] <;> omega

theorem denseRankWholePrepare_safe (memory : Memory) (width : Nat) (one : 1 < 2 ^ width)
    (s : Data) (fit : s.Fits width) : denseRankWholePrepare.Safe memory width s := by
  apply select_safe_sequence memory width _ _ s fit
  intro block hb t ft
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h <;> subst block
  · exact SimpleScalar.safe memory width (.action (.move 648 260)) True.intro t ft
  · exact natSubBlock_safe memory width _ _ _ _ t ft one (by decide) (by decide)
  · exact SimpleScalar.safe memory width (.action (.move 257 646)) True.intro t ft
  · exact SimpleScalar.safe memory width (.action (.move 258 646)) True.intro t ft
  · exact SimpleScalar.safe memory width (.action (.constant 259 0)) (Nat.two_pow_pos _) t ft

theorem denseChoosePrepare_safe (memory : Memory) (width : Nat) (one : 1 < 2 ^ width)
    (s : Data) (fit : s.Fits width) : denseChoosePrepare.Safe memory width s := by
  apply select_safe_sequence memory width _ _ s fit
  intro block hb t ft
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h <;> subst block
  · exact SimpleScalar.safe memory width (.action (.move 649 260)) True.intro t ft
  · exact natSubBlock_safe memory width _ _ _ _ t ft one (by decide) (by decide)
  · exact natSubBlock_safe memory width _ _ _ _ t ft one (by decide) (by decide)
  · exact SimpleScalar.safe memory width (.action (.comparison .lt 652 650 651)) one t ft

theorem denseWordPrepared_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hl : regs 401 ≤ packedReviewerCellWidth shape.size)
    (hindex : regs 644 ≤ 4 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (Block.sequence [selectWordBlock logicalReadBlock, denseWordFinish]).Safe
      (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have selectSafe := selectWordBlock_safe shape ⟨regs, .running⟩ fit hm hl
  refine select_safe_follow selectSafe (fun fp => ?_)
  have running := selectWordBlock_running shape regs hm
  have bound := selectWordBlock_output_bound shape regs fit hm hl
  have frame (r : Nat) (hr : ¬ SelectWordWrites r) :=
    selectWordBlock_frame logicalReadBlock logicalReadBlock_writesOnly (shapeMemory shape)
      ⟨regs, .running⟩ r hr
  have mp := select_metadata_frame shape (shapeMemory shape) _ _
    (selectWordBlock_writes logicalReadBlock logicalReadBlock_writesOnly)
    (by intro r h1 h2; simp only [SelectWordWrites]; omega) ⟨regs, .running⟩ hm
  generalize he : (selectWordBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩ = selected
    at fp running bound frame mp ⊢
  rcases selected with ⟨⟨sr, status⟩, reads⟩
  dsimp only at fp running bound frame mp
  subst status
  have finish := denseWordFinish_safe shape sr fp mp
    (by rw [frame 644 (by simp [SelectWordWrites])]; exact hindex) bound
  exact Block.safe_seq finish (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ finish))

theorem denseFirstSelected_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hl : regs 646 ≤ packedReviewerCellWidth shape.size)
    (hbefore : regs 648 ≤ metadataEnvelope shape.size)
    (hremain : regs 650 ≤ metadataEnvelope shape.size)
    (hindex : regs 644 ≤ 4 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (denseFirstSelected logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size)
      ⟨regs, .running⟩ := by
  have prepare := denseFirstPrepare_safe shape regs fit hbefore hremain
  refine select_safe_follow prepare (fun fp => ?_)
  have source := denseFirstPrepare_source (shapeMemory shape) regs
  have mp := select_metadata_frame shape (shapeMemory shape) _ _ denseFirstPrepare_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frame := Block.eval_frame (shapeMemory shape) _ _ denseFirstPrepare_writes 644
    (by omega) ⟨regs, .running⟩
  generalize he : denseFirstPrepare.eval (shapeMemory shape) ⟨regs, .running⟩ = prepared
    at source mp frame fp ⊢
  rcases prepared with ⟨⟨pr, pst⟩, reads⟩
  dsimp only at source mp frame fp
  have hs := source.1
  subst pst
  exact denseWordPrepared_safe shape pr fp mp (by rw [source.2.2.2.1]; exact hl)
    (by rw [frame]; exact hindex)

theorem denseSecondPrepared_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hl : regs 8195 ≤ packedReviewerCellWidth shape.size)
    (hindex : regs 644 ≤ 4 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (Block.sequence [denseSecondPrepare, selectWordBlock logicalReadBlock, denseWordFinish]).Safe
      (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have prepare := denseSecondPrepare_safe (shapeMemory shape) (wordWidth shape.size)
    (select_constant_fit shape.size 1 (by decide)) ⟨regs, .running⟩ fit
  refine select_safe_follow prepare (fun fp => ?_)
  have source := denseSecondPrepare_source (shapeMemory shape) regs
  have mp := select_metadata_frame shape (shapeMemory shape) _ _ denseSecondPrepare_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frame := Block.eval_frame (shapeMemory shape) _ _ denseSecondPrepare_writes 644
    (by omega) ⟨regs, .running⟩
  generalize he : denseSecondPrepare.eval (shapeMemory shape) ⟨regs, .running⟩ = prepared
    at source mp frame fp ⊢
  rcases prepared with ⟨⟨pr, pst⟩, reads⟩
  dsimp only at source mp frame fp
  have hs := source.1
  subst pst
  exact denseWordPrepared_safe shape pr fp mp (by rw [source.2.2.2.1]; exact hl)
    (by rw [frame]; exact hindex)

theorem denseSecondSelected_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hindex : regs 644 ≤ 3 * (metadataEnvelope shape.size * metadataEnvelope shape.size))
    (hone : regs 659 = 1) :
    (denseSecondSelected logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size)
      ⟨regs, .running⟩ := by
  have address := denseSecondAddress_safe shape regs fit hindex hone
  refine select_safe_follow address (fun fp => ?_)
  have source := denseSecondAddress_source (shapeMemory shape) regs
  have mp := select_metadata_frame shape (shapeMemory shape) _ _ denseSecondAddress_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  generalize he : denseSecondAddress.eval (shapeMemory shape) ⟨regs, .running⟩ = addressed
    at source mp fp ⊢
  rcases addressed with ⟨⟨ar, ast⟩, reads⟩
  dsimp only at source mp fp
  have hs := source.1
  subst ast
  have loadSafe := logicalReadBlock_safe shape ⟨ar, .running⟩ fp mp
  refine select_safe_follow loadSafe (fun fl => ?_)
  have reader := logicalReadBlock_correct shape ar mp
  have bound := logicalReadBlock_output_bounds shape ar mp
  generalize heR : logicalReadBlock.eval (shapeMemory shape) ⟨ar, .running⟩ = loaded
    at reader bound fl ⊢
  rcases loaded with ⟨⟨lr, lst⟩, receipts⟩
  dsimp only at reader bound fl
  have hs := reader.1
  subst lst
  have ml := reader.2.2.2.2.metadata shape ar lr mp
  have hindex' : lr 644 ≤ 4 * (metadataEnvelope shape.size * metadataEnvelope shape.size) := by
    rw [reader.2.2.2.2 644 (Or.inl (by decide)), source.2.2.2.2, hone]
    have ep := metadataEnvelope_pos shape.size
    have esq := Nat.mul_pos ep ep
    omega
  have branch : (Block.ifZero 8194 .skip
      (Block.sequence [denseSecondPrepare, selectWordBlock logicalReadBlock, denseWordFinish])).Safe
        (shapeMemory shape) (wordWidth shape.size) ⟨lr, .running⟩ := by
    apply Block.safe_ifZero fl
    split
    · exact Block.safe_skip _ _ _ fl
    · exact denseSecondPrepared_safe shape lr fl ml bound.2 hindex'
  exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))

theorem denseRankBefore_safe_bound (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hl : regs 646 ≤ packedReviewerCellWidth shape.size)
    (hindex : regs 644 = regs 640 / regs 32) :
    (denseRankBefore logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((denseRankBefore logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running ∧
      ((denseRankBefore logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 260 ≤
        metadataEnvelope shape.size := by
  have prepare := denseRankBeforePrepare_safe shape regs fit hindex
  refine select_follow_post (fun s => s.status = .running ∧ s.regs 260 ≤ metadataEnvelope shape.size)
    prepare (fun fp => ?_)
  have source := denseRankBeforePrepare_source (shapeMemory shape) regs
  have mp := select_metadata_frame shape (shapeMemory shape) _ _ denseRankBeforePrepare_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  generalize he : denseRankBeforePrepare.eval (shapeMemory shape) ⟨regs, .running⟩ = prepared
    at source mp fp ⊢
  rcases prepared with ⟨⟨pr, pst⟩, reads⟩
  dsimp only at source mp fp
  have hs := source.1
  subst pst
  have length : pr 257 ≤ packedReviewerCellWidth shape.size := by rw [source.2.2.2.1]; exact hl
  have child := rankWordBlock_safe_invariant shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_readerSafe shape) (logicalReadBlock_correct shape)
    logicalReadBlock_writesOnly pr fp mp length
  have bound := rankWordBlock_output_bound shape pr fp mp length
  have env := rank_output_envelope shape.size
  exact ⟨child.1, child.2.running, by dsimp only; omega⟩

theorem denseRankWhole_safe_bound (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hl : regs 646 ≤ packedReviewerCellWidth shape.size) :
    (denseRankWhole logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((denseRankWhole logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running ∧
      ((denseRankWhole logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 260 ≤
        metadataEnvelope shape.size := by
  have prepare := denseRankWholePrepare_safe (shapeMemory shape) (wordWidth shape.size)
    (select_constant_fit shape.size 1 (by decide)) ⟨regs, .running⟩ fit
  refine select_follow_post (fun s => s.status = .running ∧ s.regs 260 ≤ metadataEnvelope shape.size)
    prepare (fun fp => ?_)
  have source := denseRankWholePrepare_source (shapeMemory shape) regs
  have mp := select_metadata_frame shape (shapeMemory shape) _ _ denseRankWholePrepare_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  generalize he : denseRankWholePrepare.eval (shapeMemory shape) ⟨regs, .running⟩ = prepared
    at source mp fp ⊢
  rcases prepared with ⟨⟨pr, pst⟩, reads⟩
  dsimp only at source mp fp
  have hs := source.1
  subst pst
  have length : pr 257 ≤ packedReviewerCellWidth shape.size := by rw [source.2.2.2.2.1]; exact hl
  have child := rankWordBlock_safe_invariant shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_readerSafe shape) (logicalReadBlock_correct shape)
    logicalReadBlock_writesOnly pr fp mp length
  have bound := rankWordBlock_output_bound shape pr fp mp length
  have env := rank_output_envelope shape.size
  exact ⟨child.1, child.2.running, by dsimp only; omega⟩

theorem densePresent_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hl : regs 646 ≤ packedReviewerCellWidth shape.size)
    (hdivision : regs 644 = regs 640 / regs 32)
    (hindex : regs 644 ≤ 3 * (metadataEnvelope shape.size * metadataEnvelope shape.size))
    (hocc : regs 642 ≤ metadataEnvelope shape.size) (hone : regs 659 = 1) :
    (densePresent logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have before := denseRankBefore_safe_bound shape regs fit hm hl hdivision
  refine select_safe_follow before.1 (fun fa => ?_)
  have metaA := select_metadata_frame shape (shapeMemory shape) _ _
    (denseRankBefore_writes logicalReadBlock logicalReadBlock_writesOnly)
    (by intro r h1 h2; simp only [DenseRankBeforeWrites]; omega) ⟨regs, .running⟩ hm
  have frameA (r : Nat) (ho : ¬ DenseRankBeforeWrites r) :=
    Block.eval_frame (shapeMemory shape) _ _
      (denseRankBefore_writes logicalReadBlock logicalReadBlock_writesOnly) r ho ⟨regs, .running⟩
  generalize heA : (denseRankBefore logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩ = beforeData
    at before metaA frameA fa ⊢
  rcases beforeData with ⟨⟨ar, ast⟩, readsA⟩
  dsimp only at before metaA frameA fa
  have hs := before.2.1
  subst ast
  have whole := denseRankWhole_safe_bound shape ar fa metaA
    (by rw [frameA 646 (by simp [DenseRankBeforeWrites])]; exact hl)
  refine select_safe_follow whole.1 (fun fb => ?_)
  have metaB := select_metadata_frame shape (shapeMemory shape) _ _
    (denseRankWhole_writes logicalReadBlock logicalReadBlock_writesOnly)
    (by intro r h1 h2; simp only [DenseRankWholeWrites]; omega) ⟨ar, .running⟩ metaA
  have frameB (r : Nat) (ho : ¬ DenseRankWholeWrites r) :=
    Block.eval_frame (shapeMemory shape) _ _
      (denseRankWhole_writes logicalReadBlock logicalReadBlock_writesOnly) r ho ⟨ar, .running⟩
  have saved := denseRankWhole_saved (shapeMemory shape) logicalReadBlock logicalReadBlock_writesOnly ar
  generalize heB : (denseRankWhole logicalReadBlock).eval (shapeMemory shape) ⟨ar, .running⟩ = wholeData
    at whole metaB frameB saved fb ⊢
  rcases wholeData with ⟨⟨br, bst⟩, readsB⟩
  dsimp only at whole metaB frameB saved fb
  have hs := whole.2.1
  subst bst
  have choose := denseChoosePrepare_safe (shapeMemory shape) (wordWidth shape.size)
    (select_constant_fit shape.size 1 (by decide)) ⟨br, .running⟩ fb
  refine select_safe_follow choose (fun fc => ?_)
  have sourceC := denseChoosePrepare_source (shapeMemory shape) br
  have metaC := select_metadata_frame shape (shapeMemory shape) _ _ denseChoosePrepare_writes
    (by intro r h1 h2; omega) ⟨br, .running⟩ metaB
  have frameC (r : Nat) (ho : ¬ ((649 ≤ r ∧ r < 653) ∨ r = 658)) :=
    Block.eval_frame (shapeMemory shape) _ _ denseChoosePrepare_writes r ho ⟨br, .running⟩
  generalize heC : denseChoosePrepare.eval (shapeMemory shape) ⟨br, .running⟩ = chosen
    at sourceC metaC frameC fc ⊢
  rcases chosen with ⟨⟨cr, cst⟩, readsC⟩
  dsimp only at sourceC metaC frameC fc
  have hs := sourceC.1
  subst cst
  have kept (r : Nat) (hr : r = 32 ∨ r = 640 ∨ r = 641 ∨ r = 642 ∨ r = 644 ∨ r = 646 ∨ r = 659) :
      cr r = regs r := by
    rw [frameC r (by omega), frameB r (by simp only [DenseRankWholeWrites]; omega),
      frameA r (by simp only [DenseRankBeforeWrites]; omega)]
  have chunkLen : cr 646 ≤ packedReviewerCellWidth shape.size := by rw [kept 646 (by omega)]; exact hl
  have indexBound : cr 644 ≤ 3 * (metadataEnvelope shape.size * metadataEnvelope shape.size) := by
    rw [kept 644 (by omega)]; exact hindex
  have one : cr 659 = 1 := (kept 659 (by omega)).trans hone
  have countBound : cr 648 ≤ metadataEnvelope shape.size := by
    rw [frameC 648 (by omega), saved]
    exact before.2.2
  have remainBound : cr 650 ≤ metadataEnvelope shape.size := by
    rw [sourceC.2.2.2.1, frameB 642 (by simp [DenseRankWholeWrites]),
      frameA 642 (by simp [DenseRankBeforeWrites])]
    omega
  have branch : (denseSelectBranch logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size)
      ⟨cr, .running⟩ := by
    apply Block.safe_ifZero fc
    split
    · exact denseSecondSelected_safe shape cr fc metaC indexBound one
    · exact denseFirstSelected_safe shape cr fc metaC chunkLen countBound remainBound (by omega)
  exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))

theorem denseSelectBlock_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (hbase : regs 640 ≤ 3 * (metadataEnvelope shape.size * metadataEnvelope shape.size))
    (hocc : regs 642 ≤ metadataEnvelope shape.size) :
    (denseSelectBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have address := denseReadAddress_safe shape regs fit hm
  refine select_safe_follow address (fun fa => ?_)
  have sourceA := denseReadAddress_source (shapeMemory shape) regs
  have metaA := select_metadata_frame shape (shapeMemory shape) _ _ denseReadAddress_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frameA (r : Nat) (ho : r ≠ 643 ∧ r ≠ 644 ∧ r ≠ 659 ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    Block.eval_frame (shapeMemory shape) _ _ denseReadAddress_writes r (by omega) ⟨regs, .running⟩
  generalize heA : denseReadAddress.eval (shapeMemory shape) ⟨regs, .running⟩ = addressed
    at sourceA metaA frameA fa ⊢
  rcases addressed with ⟨⟨ar, ast⟩, readsA⟩
  dsimp only at sourceA metaA frameA fa
  have hs := sourceA.1
  subst ast
  have loadSafe := logicalReadBlock_safe shape ⟨ar, .running⟩ fa metaA
  refine select_safe_follow loadSafe (fun fb => ?_)
  have reader := logicalReadBlock_correct shape ar metaA
  have bounds := logicalReadBlock_output_bounds shape ar metaA
  generalize heB : logicalReadBlock.eval (shapeMemory shape) ⟨ar, .running⟩ = loaded
    at reader bounds fb ⊢
  rcases loaded with ⟨⟨br, bst⟩, readsB⟩
  dsimp only at reader bounds fb
  have hs := reader.1
  subst bst
  have metaB := reader.2.2.2.2.metadata shape ar br metaA
  have saveSafe := denseReadSave_safe (shapeMemory shape) (wordWidth shape.size) ⟨br, .running⟩ fb
  refine select_safe_follow saveSafe (fun fc => ?_)
  have sourceC := denseReadSave_source (shapeMemory shape) br
  have metaC := select_metadata_frame shape (shapeMemory shape) _ _ denseReadSave_writes
    (by intro r h1 h2; omega) ⟨br, .running⟩ metaB
  have frameC (r : Nat) (ho : r ≠ 645 ∧ r ≠ 646) :=
    Block.eval_frame (shapeMemory shape) _ _ denseReadSave_writes r (by omega) ⟨br, .running⟩
  generalize heC : denseReadSave.eval (shapeMemory shape) ⟨br, .running⟩ = saved
    at sourceC metaC frameC fc ⊢
  rcases saved with ⟨⟨cr, cst⟩, readsC⟩
  dsimp only at sourceC metaC frameC fc
  have hs := sourceC.1
  subst cst
  have kept (r : Nat) (hr : r = 32 ∨ r = 640 ∨ r = 642) : cr r = regs r := by
    rw [frameC r (by omega), reader.2.2.2.2 r (Or.inl (by omega)), frameA r (by omega)]
  have indexEq : cr 644 = regs 640 / regs 32 := by
    rw [frameC 644 (by omega), reader.2.2.2.2 644 (Or.inl (by decide)), sourceA.2.2.2.2.1]
  have lenBound : cr 646 ≤ packedReviewerCellWidth shape.size := by rw [sourceC.2.2.2]; exact bounds.2
  have one : cr 659 = 1 := by
    rw [frameC 659 (by omega), reader.2.2.2.2 659 (Or.inl (by decide)), sourceA.2.2.2.1]
  have child := densePresent_safe shape cr fc metaC lenBound
    (by rw [indexEq, kept 640 (by omega), kept 32 (by omega)])
    (by rw [indexEq]; have hd := Nat.div_le_self (regs 640) (regs 32); omega)
    (by rw [kept 642 (by omega)]; exact hocc) one
  have branch : (Block.ifZero 645 .skip (densePresent logicalReadBlock)).Safe
      (shapeMemory shape) (wordWidth shape.size) ⟨cr, .running⟩ := by
    apply Block.safe_ifZero fc
    split
    · exact Block.safe_skip _ _ _ fc
    · exact child
  exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))

private theorem select_read_finish_safe (shape : CartesianShape) (finish : Block) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (finishSafe : ∀ out, (⟨out, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape out → ReaderFrame regs out →
      out 8194 ≤ 2 ^ packedReviewerCellWidth shape.size →
      finish.Safe (shapeMemory shape) (wordWidth shape.size) ⟨out, .running⟩) :
    (Block.sequence [logicalReadBlock, finish]).Safe (shapeMemory shape) (wordWidth shape.size)
      ⟨regs, .running⟩ := by
  have loadSafe := logicalReadBlock_safe shape ⟨regs, .running⟩ fit hm
  refine select_safe_follow loadSafe (fun fp => ?_)
  have source := logicalReadBlock_correct shape regs hm
  have bounds := logicalReadBlock_output_bounds shape regs hm
  generalize he : logicalReadBlock.eval (shapeMemory shape) ⟨regs, .running⟩ = loaded
    at source bounds fp ⊢
  rcases loaded with ⟨⟨lr, status⟩, reads⟩
  dsimp only at source bounds fp
  have hs := source.1
  subst status
  have tail := finishSafe lr fp (source.2.2.2.2.metadata shape regs lr hm) source.2.2.2.2 bounds.1
  exact Block.safe_seq tail (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ tail))

theorem selectLongTail_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hrank : regs 360 ≤ metadataEnvelope shape.size)
    (hocc : regs 512 ≤ metadataEnvelope shape.size)
    (hword : regs 562 ≤ metadataEnvelope shape.size) (hoffset : regs 564 ≤ metadataEnvelope shape.size) :
    (Block.sequence [selectLongAddress, logicalReadBlock, selectLongFinish]).Safe
      (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have address := selectLongAddress_safe shape regs fit hm hrank hocc
  refine select_safe_follow address (fun fp => ?_)
  have source := selectLongAddress_source (shapeMemory shape) regs
  have mp := select_metadata_frame shape (shapeMemory shape) _ _ selectLongAddress_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frame (r : Nat) (hr : r = 562 ∨ r = 564) :=
    Block.eval_frame (shapeMemory shape) _ _ selectLongAddress_writes r (by omega) ⟨regs, .running⟩
  generalize he : selectLongAddress.eval (shapeMemory shape) ⟨regs, .running⟩ = addressed
    at source mp frame fp ⊢
  rcases addressed with ⟨⟨ar, status⟩, reads⟩
  dsimp only at source mp frame fp
  have hs := source.1
  subst status
  apply select_read_finish_safe shape selectLongFinish ar fp mp
  intro out fo mo readerFrame reply
  exact selectLongFinish_safe shape out fo mo
    (by rw [readerFrame 562 (Or.inl (by decide)), frame 562 (by omega)]; exact hword)
    (by rw [readerFrame 564 (Or.inl (by decide)), frame 564 (by omega)]; exact hoffset)
    (Nat.le_trans reply (select_old_capacity_le_envelope _))

theorem selectSparseTail_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hrank : regs 360 ≤ metadataEnvelope shape.size)
    (hocc : regs 512 ≤ metadataEnvelope shape.size)
    (hbase : regs 520 ≤ 3 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (Block.sequence [selectSparseAddress, logicalReadBlock, selectSparseFinish]).Safe
      (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have address := selectSparseAddress_safe shape regs fit hm hrank hocc
  refine select_safe_follow address (fun fp => ?_)
  have source := selectSparseAddress_source (shapeMemory shape) regs
  have mp := select_metadata_frame shape (shapeMemory shape) _ _ selectSparseAddress_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frame := Block.eval_frame (shapeMemory shape) _ _ selectSparseAddress_writes 520
    (by omega) ⟨regs, .running⟩
  generalize he : selectSparseAddress.eval (shapeMemory shape) ⟨regs, .running⟩ = addressed
    at source mp frame fp ⊢
  rcases addressed with ⟨⟨ar, status⟩, reads⟩
  dsimp only at source mp frame fp
  have hs := source.1
  subst status
  apply select_read_finish_safe shape selectSparseFinish ar fp mp
  intro out fo mo readerFrame reply
  exact selectSparseFinish_safe shape out fo
    (by rw [readerFrame 520 (Or.inl (by decide)), frame]; exact hbase)
    (Nat.le_trans reply (select_old_capacity_le_envelope _))

private theorem select_rank_call_safe (shape : CartesianShape)
    (call tail program : Block) (input : Nat)
    (programEq : program = .seq (.action (.move 352 input)) (.seq call tail))
    (called : ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape regs →
      call.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
      (call.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running ∧
      (call.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 360 ≤ metadataEnvelope shape.size ∧
      (∀ r, ¬ RankWrapperWrites r →
        (call.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs r = regs r))
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs)
    (finish : ∀ out, (⟨out, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape out → out 360 ≤ metadataEnvelope shape.size →
      (∀ r, ¬ RankWrapperWrites r → r ≠ 352 → out r = regs r) →
      tail.Safe (shapeMemory shape) (wordWidth shape.size) ⟨out, .running⟩) :
    program.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  subst program
  have move := Block.safe_action (shapeMemory shape) (wordWidth shape.size) (.move 352 input)
    ⟨regs, .running⟩ fit (fit.1 input)
  refine select_safe_follow move (fun fp => ?_)
  let prepared := regs.write 352 (regs input)
  have mp := MetadataMatches.write shape regs hm 352 (regs input) (Or.inr (by decide))
  have callProof := called prepared fp mp
  refine select_safe_follow callProof.1 (fun fc => ?_)
  change (call.eval (shapeMemory shape) ⟨prepared, .running⟩).final.Fits (wordWidth shape.size) at fc
  change tail.Safe (shapeMemory shape) (wordWidth shape.size)
    (call.eval (shapeMemory shape) ⟨prepared, .running⟩).final
  generalize he : call.eval (shapeMemory shape) ⟨prepared, .running⟩ = result at callProof fc ⊢
  rcases result with ⟨⟨out, status⟩, reads⟩
  dsimp only at callProof fc
  have hs := callProof.2.1
  subst status
  have mo : MetadataMatches shape out := by
    intro i hi
    rw [callProof.2.2.2 (16 + i) (by simp only [RankWrapperWrites]; omega)]
    exact mp i hi
  exact finish out fc mo callProof.2.2.1 (by
    intro r hr hne
    rw [callProof.2.2.2 r hr]
    simp [prepared, Registers.write, hne])

theorem selectLongBlock_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hocc : regs 512 ≤ metadataEnvelope shape.size)
    (hword : regs 562 ≤ metadataEnvelope shape.size) (hoffset : regs 564 ≤ metadataEnvelope shape.size) :
    (selectLongBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  apply select_rank_call_safe shape (rankLongBlock logicalReadBlock)
    (Block.sequence [selectLongAddress, logicalReadBlock, selectLongFinish])
    (selectLongBlock logicalReadBlock) 514 rfl
    (fun rs fs ms => ⟨(rankLongBlock_safe_bound shape rs fs ms).1,
      (rankLongBlock_source shape (shapeMemory shape) logicalReadBlock
        (logicalReadBlock_correct shape) logicalReadBlock_writesOnly rs ms).1,
      (rankLongBlock_safe_bound shape rs fs ms).2,
      rankLongBlock_frame logicalReadBlock logicalReadBlock_writesOnly (shapeMemory shape) ⟨rs, .running⟩⟩)
    regs fit hm
  intro out fo mo bound frame
  exact selectLongTail_safe shape out fo mo bound
    (by rw [frame 512 (by simp [RankWrapperWrites]) (by decide)]; exact hocc)
    (by rw [frame 562 (by simp [RankWrapperWrites]) (by decide)]; exact hword)
    (by rw [frame 564 (by simp [RankWrapperWrites]) (by decide)]; exact hoffset)

theorem selectSparseBlock_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hocc : regs 512 ≤ metadataEnvelope shape.size)
    (hbase : regs 520 ≤ 3 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (selectSparseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  apply select_rank_call_safe shape (rankSparseBlock logicalReadBlock)
    (Block.sequence [selectSparseAddress, logicalReadBlock, selectSparseFinish])
    (selectSparseBlock logicalReadBlock) 515 rfl
    (fun rs fs ms => ⟨(rankSparseBlock_safe_bound shape rs fs ms).1,
      (rankSparseBlock_source shape (shapeMemory shape) logicalReadBlock
        (logicalReadBlock_correct shape) logicalReadBlock_writesOnly rs ms).1,
      (rankSparseBlock_safe_bound shape rs fs ms).2,
      rankSparseBlock_frame logicalReadBlock logicalReadBlock_writesOnly (shapeMemory shape) ⟨rs, .running⟩⟩)
    regs fit hm
  intro out fo mo bound frame
  exact selectSparseTail_safe shape out fo mo bound
    (by rw [frame 512 (by simp [RankWrapperWrites]) (by decide)]; exact hocc)
    (by rw [frame 520 (by simp [RankWrapperWrites]) (by decide)]; exact hbase)

theorem selectLocalDense_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hocc : regs 512 ≤ metadataEnvelope shape.size)
    (hbase : regs 520 ≤ 3 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (selectLocalDense logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have a := Block.safe_action (shapeMemory shape) (wordWidth shape.size) (.move 640 520)
    ⟨regs, .running⟩ fit (fit.1 520)
  have fa := Block.eval_fits _ _ _ _ a
  have b := Block.safe_action (shapeMemory shape) (wordWidth shape.size) (.move 641 521) _ fa (fa.1 521)
  have fb := Block.eval_fits _ _ _ _ b
  have c := Block.safe_action (shapeMemory shape) (wordWidth shape.size) (.move 642 512) _ fb (fb.1 512)
  have fc := Block.eval_fits _ _ _ _ c
  let prepared := ((regs.write 640 (regs 520)).write 641 (regs 521)).write 642 (regs 512)
  have mp : MetadataMatches shape prepared :=
    MetadataMatches.write shape _ (MetadataMatches.write shape _
      (MetadataMatches.write shape regs hm 640 (regs 520) (Or.inr (by decide)))
      641 (regs 521) (Or.inr (by decide))) 642 (regs 512) (Or.inr (by decide))
  have dense := denseSelectBlock_safe shape prepared fc mp
    (by simpa [prepared, Registers.write] using hbase)
    (by simpa [prepared, Registers.write] using hocc)
  have tail := SimpleScalar.safe (shapeMemory shape) (wordWidth shape.size)
    (Block.sequence [.action (.move 513 643)]) ⟨True.intro, True.intro⟩ _
    (Block.eval_fits _ _ _ _ dense)
  exact Block.safe_seq a (Block.safe_seq b (Block.safe_seq c (Block.safe_seq dense tail)))

theorem selectLocalPresent_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hocc : regs 512 ≤ metadataEnvelope shape.size)
    (h561 : regs 561 ≤ metadataEnvelope shape.size) (h562 : regs 562 ≤ metadataEnvelope shape.size)
    (h591 : regs 591 ≤ metadataEnvelope shape.size) (h592 : regs 592 ≤ metadataEnvelope shape.size)
    (h594 : regs 594 ≤ metadataEnvelope shape.size) :
    (selectLocalPresent logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have prepare := selectLocalPrepare_safe shape regs fit hm h562 h592 h594 h561 h591
  refine select_safe_follow prepare (fun fp => ?_)
  have source := selectLocalPrepare_source (shapeMemory shape) regs
  have mp := select_metadata_frame shape (shapeMemory shape) _ _ selectLocalPrepare_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frame := Block.eval_frame (shapeMemory shape) _ _ selectLocalPrepare_writes 512
    (by omega) ⟨regs, .running⟩
  generalize he : selectLocalPrepare.eval (shapeMemory shape) ⟨regs, .running⟩ = prepared
    at source mp frame fp ⊢
  rcases prepared with ⟨⟨pr, pst⟩, reads⟩
  dsimp only at source mp frame fp
  have hs := source.1
  subst pst
  have occ : pr 512 ≤ metadataEnvelope shape.size := by rw [frame]; exact hocc
  have base : pr 520 ≤ 3 * (metadataEnvelope shape.size * metadataEnvelope shape.size) := by
    rw [source.2.2.1]
    have word := hm.envelope shape regs 32 (by decide)
    have hp := Nat.mul_le_mul
      (show regs 562 + regs 592 ≤ 2 * metadataEnvelope shape.size by omega) word
    have ep := metadataEnvelope_pos shape.size
    have esq := Nat.le_mul_of_pos_right (metadataEnvelope shape.size) ep
    simp only [Nat.mul_assoc] at hp
    omega
  have branch : (Block.ifZero 593 (selectLocalDense logicalReadBlock)
      (selectSparseBlock logicalReadBlock)).Safe (shapeMemory shape) (wordWidth shape.size)
        ⟨pr, .running⟩ := by
    apply Block.safe_ifZero fp
    split
    · exact selectLocalDense_safe shape pr fp mp occ base
    · exact selectSparseBlock_safe shape pr fp mp occ base
  exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))

theorem selectLocalBlock_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hocc : regs 512 ≤ metadataEnvelope shape.size)
    (hslot : regs 514 ≤ metadataEnvelope shape.size)
    (h561 : regs 561 ≤ metadataEnvelope shape.size) (h562 : regs 562 ≤ metadataEnvelope shape.size) :
    (selectLocalBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have address := selectLocalAddress_safe shape regs fit hm hslot hocc
  refine select_safe_follow address (fun fa => ?_)
  have sourceA := selectLocalAddress_source (shapeMemory shape) regs
  have metaA := select_metadata_frame shape (shapeMemory shape) _ _ selectLocalAddress_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frameA (r : Nat) (hr : r = 512 ∨ r = 561 ∨ r = 562) :=
    Block.eval_frame (shapeMemory shape) _ _ selectLocalAddress_writes r (by omega) ⟨regs, .running⟩
  generalize heA : selectLocalAddress.eval (shapeMemory shape) ⟨regs, .running⟩ = addressed
    at sourceA metaA frameA fa ⊢
  rcases addressed with ⟨⟨ar, ast⟩, readsA⟩
  dsimp only at sourceA metaA frameA fa
  have hs := sourceA.1
  subst ast
  have entries := selectEntryBlock_safe shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_readerSafe shape) logicalReadBlock_writesOnly 5 515 590 (by decide)
    (by have := select_constant_fit shape.size 9 (by decide); omega) ⟨ar, .running⟩ fa metaA
  refine select_safe_follow entries (fun fb => ?_)
  have sourceB := selectEntryLocal_expectedType shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly ar metaA
  have bounds := selectEntryBlock_present_bounds shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly 5 515 590
    (by decide) (by decide) (by decide) (Or.inl (by decide)) ar metaA
  have metaB := selectEntryBlock_metadata shape logicalReadBlock logicalReadBlock_writesOnly
    5 515 590 (by decide) (shapeMemory shape) ⟨ar, .running⟩ metaA
  have frameB (r : Nat) (hr : r = 512 ∨ r = 561 ∨ r = 562) :=
    selectEntryBlock_frame logicalReadBlock logicalReadBlock_writesOnly 5 515 590
      (shapeMemory shape) ⟨ar, .running⟩ r (by simp only [SelectEntryWrites]; omega)
  generalize heB : (selectEntryBlock logicalReadBlock 5 515 590).eval (shapeMemory shape) ⟨ar, .running⟩ = fetched
    at sourceB bounds metaB frameB fb ⊢
  rcases fetched with ⟨⟨br, bst⟩, readsB⟩
  dsimp only at sourceB bounds metaB frameB fb
  have hs := sourceB.1
  subst bst
  have branch : (Block.ifZero 590 .skip (selectLocalPresent logicalReadBlock)).Safe
      (shapeMemory shape) (wordWidth shape.size) ⟨br, .running⟩ := by
    apply Block.safe_ifZero fb
    split
    · exact Block.safe_skip _ _ _ fb
    · rename_i present
      have hb := bounds present
      simp only [Nat.reduceAdd] at hb
      have eq := select_old_capacity_le_envelope shape.size
      exact selectLocalPresent_safe shape br fb metaB
        (by rw [frameB 512 (by omega), frameA 512 (by omega)]; exact hocc)
        (by rw [frameB 561 (by omega), frameA 561 (by omega)]; exact h561)
        (by rw [frameB 562 (by omega), frameA 562 (by omega)]; exact h562)
        (by omega) (by omega) (by omega)
  exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))

theorem selectSuperPresent_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hocc : regs 512 ≤ metadataEnvelope shape.size)
    (hslot : regs 514 ≤ metadataEnvelope shape.size)
    (h561 : regs 561 ≤ metadataEnvelope shape.size) (h562 : regs 562 ≤ metadataEnvelope shape.size)
    (h564 : regs 564 ≤ metadataEnvelope shape.size) :
    (selectSuperPresent logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  apply Block.safe_ifZero fit
  split
  · exact selectLocalBlock_safe shape regs fit hm hocc hslot h561 h562
  · exact selectLongBlock_safe shape regs fit hm hocc h562 h564

private theorem selectEligible_safe_aux (shape : CartesianShape) (entry tail program : Block)
    (programEq : program = .seq (.action (.arithmetic .div 514 512 25))
      (.seq entry (.seq (.ifZero 560 .skip tail) .skip)))
    (entrySpec : ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape regs →
      entry.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
      (entry.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running ∧
      MetadataMatches shape (entry.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs ∧
      (∀ r, r = 512 ∨ r = 514 → (entry.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs r = regs r) ∧
      ((entry.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 560 ≠ 0 →
        (entry.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 561 ≤ 2 ^ packedReviewerCellWidth shape.size ∧
        (entry.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 562 ≤ 2 ^ packedReviewerCellWidth shape.size ∧
        (entry.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 563 ≤ 2 ^ packedReviewerCellWidth shape.size ∧
        (entry.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 564 ≤ 2 ^ packedReviewerCellWidth shape.size))
    (tailSafe : ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) →
      MetadataMatches shape regs → regs 512 ≤ metadataEnvelope shape.size →
      regs 514 ≤ metadataEnvelope shape.size → regs 561 ≤ metadataEnvelope shape.size →
      regs 562 ≤ metadataEnvelope shape.size → regs 564 ≤ metadataEnvelope shape.size →
      tail.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hocc : regs 512 ≤ metadataEnvelope shape.size) :
    program.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  subst program
  have divisor := (select_metadata_geometry shape regs hm).2.1
  have hp := Nat.div_le_self (regs 512) (regs 25)
  have occFit : regs 512 < 2 ^ wordWidth shape.size := fit.1 512
  have divide := Block.safe_action (shapeMemory shape) (wordWidth shape.size)
    (.arithmetic .div 514 512 25) ⟨regs, .running⟩ fit
    (by simp [Action.LocalSafe, Arithmetic.eval]; omega)
  refine select_safe_follow divide (fun fp => ?_)
  let prepared := regs.write 514 (regs 512 / regs 25)
  have mp : MetadataMatches shape prepared := MetadataMatches.write shape regs hm 514 _ (Or.inr (by decide))
  have entries := entrySpec prepared fp mp
  refine select_safe_follow entries.1 (fun fe => ?_)
  change (entry.eval (shapeMemory shape) ⟨prepared, .running⟩).final.Fits (wordWidth shape.size) at fe
  change (Block.seq (.ifZero 560 .skip tail) .skip).Safe (shapeMemory shape) (wordWidth shape.size)
    (entry.eval (shapeMemory shape) ⟨prepared, .running⟩).final
  generalize he : entry.eval (shapeMemory shape) ⟨prepared, .running⟩ = fetched at entries fe ⊢
  rcases fetched with ⟨⟨er, est⟩, reads⟩
  dsimp only at entries fe
  have hs := entries.2.1
  subst est
  have branch : (Block.ifZero 560 .skip tail).Safe
      (shapeMemory shape) (wordWidth shape.size) ⟨er, .running⟩ := by
    apply Block.safe_ifZero fe
    split
    · exact Block.safe_skip _ _ _ fe
    · rename_i present
      have hb := entries.2.2.2.2 present
      have eq := select_old_capacity_le_envelope shape.size
      exact tailSafe er fe entries.2.2.1
        (by rw [entries.2.2.2.1 512 (by omega)]; simpa [prepared, Registers.write] using hocc)
        (by rw [entries.2.2.2.1 514 (by omega)]; simp [prepared]; omega)
        (by omega) (by omega) (by omega)
  exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))

private theorem selectSuperEntry_safe_spec (shape : CartesianShape) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe shape memory reader) (readerCorrect : ReaderCorrect shape memory reader)
    (readerWrites : ReaderWrites reader) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    let entry := selectEntryBlock reader 1 514 560
    let actual := entry.eval memory ⟨regs, .running⟩
    entry.Safe memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
    actual.final.status = .running ∧ MetadataMatches shape actual.final.regs ∧
    (∀ r, r = 512 ∨ r = 514 → actual.final.regs r = regs r) ∧
    (actual.final.regs 560 ≠ 0 → actual.final.regs 561 ≤ 2 ^ packedReviewerCellWidth shape.size ∧
      actual.final.regs 562 ≤ 2 ^ packedReviewerCellWidth shape.size ∧
      actual.final.regs 563 ≤ 2 ^ packedReviewerCellWidth shape.size ∧
      actual.final.regs 564 ≤ 2 ^ packedReviewerCellWidth shape.size) := by
  have safe := selectEntryBlock_safe shape memory reader
    readerSafe readerWrites 1 514 560 (by decide)
    (by have := select_constant_fit shape.size 5 (by decide); omega) ⟨regs, .running⟩ fit hm
  have source := selectEntrySuper_expectedType shape memory reader
    readerCorrect readerWrites regs hm
  have metadata := selectEntryBlock_metadata shape reader readerWrites
    1 514 560 (by decide) memory ⟨regs, .running⟩ hm
  have frame (r : Nat) (hr : r = 512 ∨ r = 514) :=
    selectEntryBlock_frame reader readerWrites 1 514 560
      memory ⟨regs, .running⟩ r (by simp only [SelectEntryWrites]; omega)
  have bounds := selectEntryBlock_present_bounds shape memory reader
    readerCorrect readerWrites 1 514 560
    (by decide) (by decide) (by decide) (Or.inl (by decide)) regs hm
  exact ⟨safe, source.1, metadata, frame, bounds⟩

theorem selectEligible_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hocc : regs 512 ≤ metadataEnvelope shape.size) :
    (selectEligible logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ :=
  selectEligible_safe_aux shape (selectEntryBlock logicalReadBlock 1 514 560)
    (selectSuperPresent logicalReadBlock) (selectEligible logicalReadBlock) rfl
    (selectSuperEntry_safe_spec shape (shapeMemory shape) logicalReadBlock
      (logicalReadBlock_readerSafe shape) (logicalReadBlock_correct shape) logicalReadBlock_writesOnly)
    (selectSuperPresent_safe shape) regs fit hm hocc

theorem selectCloseBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (selectCloseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs
      subst status
      have zero := Block.safe_action (shapeMemory shape) (wordWidth shape.size) (.constant 513 0)
        ⟨regs, .running⟩ fit (Nat.two_pow_pos _)
      refine select_safe_follow zero (fun fp => ?_)
      let prepared := regs.write 513 0
      have mp := MetadataMatches.write shape regs hm 513 0 (Or.inr (by decide))
      have compare := Block.safe_action (shapeMemory shape) (wordWidth shape.size)
        (.comparison .lt 550 512 16) ⟨prepared, .running⟩ fp
        (by dsimp only [Action.LocalSafe, Comparison.eval]; split <;>
          exact select_constant_fit shape.size _ (by decide))
      refine select_safe_follow compare (fun ft => ?_)
      have mt := MetadataMatches.write shape prepared mp 550
        (Comparison.lt.eval (prepared 512) (prepared 16)) (Or.inr (by decide))
      have sizeBound := hm.envelope shape regs 16 (by decide)
      have ft' : (⟨prepared.write 550 (Comparison.lt.eval (prepared 512) (prepared 16)), .running⟩ : Data).Fits
          (wordWidth shape.size) := ft
      have branch : (Block.ifZero 550 .skip (selectEligible logicalReadBlock)).Safe
          (shapeMemory shape) (wordWidth shape.size)
          ⟨prepared.write 550 (Comparison.lt.eval (prepared 512) (prepared 16)), .running⟩ := by
        apply Block.safe_ifZero ft'
        by_cases active : regs 512 < regs 16
        · have child := selectEligible_safe shape
            (prepared.write 550 (Comparison.lt.eval (prepared 512) (prepared 16))) ft' mt
            (by simp [prepared, Registers.write]; omega)
          simpa [prepared, Registers.write, Comparison.eval, active] using child
        · simpa [prepared, Registers.write, Comparison.eval, active] using
            Block.safe_skip (shapeMemory shape) (wordWidth shape.size) _ ft'
      exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))
  · exact Block.safe_stopped _ _ _ s fit hs


theorem selectWordBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (selectWordBlock reader).FieldsFit width := by
  have hwne : width ≠ 0 := by intro h; simp [h] at cap
  simp [selectWordBlock, selectWordInit, selectWordBody, selectWordActive,
    selectWordAddress, selectWordDecode, selectWordMiss, selectWordSelected,
    selectWordSelectAddress, selectWordFinish, chunkSlotBlock, chunkRankBlock,
    natSubBlock, minBlock, Block.sequence, Block.FieldsFit, Action.instruction,
    Instruction.Fits, Instruction.encoding, Instruction.operands, Arithmetic.code,
    Comparison.code, readerFields, hwne]
  omega

theorem denseSelectBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (denseSelectBlock reader).FieldsFit width := by
  have hwne : width ≠ 0 := by intro h; simp [h] at cap
  have wordFields := selectWordBlock_fieldsFit width reader readerFields cap
  have rankFields := rankWordBlock_fieldsFit width reader readerFields cap
  simp [denseSelectBlock, denseReadAddress, denseReadSave, densePresent,
    denseRankBefore, denseRankWhole, denseRankBeforePrepare, denseRankWholePrepare,
    denseChoosePrepare, denseSelectBranch, denseFirstSelected, denseSecondSelected,
    denseFirstPrepare, denseSecondAddress, denseSecondPrepare, denseWordFinish,
    natSubBlock, Block.sequence, Block.FieldsFit, Action.instruction,
    Instruction.Fits, Instruction.encoding, Instruction.operands, Arithmetic.code,
    Comparison.code, wordFields, rankFields, readerFields, hwne]
  omega


theorem selectEntryBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width)
    (segment indexReg base : Nat) (hs : segment + 4 ≤ 8280)
    (hi : indexReg ≤ 8280) (hb : base + 11 ≤ 8280) :
    (selectEntryBlock reader segment indexReg base).FieldsFit width := by
  have hwne : width ≠ 0 := by intro h; simp [h] at cap
  simp [selectEntryBlock, selectEntryFields, selectFieldsFrom, selectFieldRead,
    selectEntryDecode, natSubBlock, Block.sequence, Block.FieldsFit, Action.instruction,
    Instruction.Fits, Instruction.encoding, Instruction.operands, Arithmetic.code,
    Comparison.code, readerFields, hwne]
  omega

theorem selectCloseBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (selectCloseBlock reader).FieldsFit width := by
  have hwne : width ≠ 0 := by intro h; simp [h] at cap
  have denseFields := denseSelectBlock_fieldsFit width reader readerFields cap
  have longFields := rankLongBlock_fieldsFit width reader readerFields cap
  have sparseFields := rankSparseBlock_fieldsFit width reader readerFields cap
  have superFields := selectEntryBlock_fieldsFit width reader readerFields cap 1 514 560
    (by decide) (by decide) (by decide)
  have localFields := selectEntryBlock_fieldsFit width reader readerFields cap 5 515 590
    (by decide) (by decide) (by decide)
  simp [selectCloseBlock, selectEligible, selectSuperPresent, selectLocalBlock,
    selectLocalAddress, selectLocalPresent, selectLocalPrepare,
    selectLocalDense, selectLongBlock, selectLongAddress, selectLongFinish,
    selectSparseBlock, selectSparseAddress, selectSparseFinish, natSubBlock,
    Block.sequence, Block.FieldsFit, Action.instruction, Instruction.Fits,
    Instruction.encoding, Instruction.operands, Arithmetic.code, Comparison.code,
    denseFields, longFields, sparseFields, superFields, localFields, readerFields, hwne]
  omega

theorem selectCloseProgram_fieldsFit (n : Nat) :
    ∀ instruction ∈ selectCloseProgram, instruction.Fits (wordWidth n) := by
  have cap := select_constant_fit n 91243 (by decide)
  have fields := (selectCloseBlock logicalReadBlock).compile_fits (wordWidth n) 0
    (selectCloseBlock_fieldsFit _ _ (logicalReadBlock_fieldsFit _ (by omega)) (by omega))
    (by simp only [selectCloseBlock_size, logicalReadBlock_size, locateBlock_size]; omega)
  intro instruction hi
  rcases List.mem_append.mp hi with hi | hi
  · exact fields instruction hi
  · simp only [List.mem_singleton] at hi
    subst instruction
    simp [Instruction.Fits, Instruction.encoding, Instruction.operands]
    omega


theorem selectCloseBlock_output_position_bound (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    ((selectCloseBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 513 ≤
      2 * shape.size := by
  have source := selectCloseBlock_canonical shape regs hm
  rw [source.2.1, packedSelectCloseLeaf_global_value_eq_reference]
  cases selected : bpCloseOfInorder? shape (regs 512) with
  | none => simp [optionNatPacket]
  | some close =>
      have bound := bpCloseOfInorder?_bounds shape selected
      rw [CartesianShape.bpCode_length] at bound
      simp only [optionNatPacket, Option.map_some, Option.getD_some]
      omega

theorem selectCloseBlock_output_envelope (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    ((selectCloseBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 513 ≤
      metadataEnvelope shape.size := by
  have bound := selectCloseBlock_output_position_bound shape regs hm
  have size := packedReviewerInputSize_lt_two_pow_cellWidth shape.size
  have envelope := rank_output_envelope shape.size
  omega

theorem selectCloseBlock_output_bound (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    ((selectCloseBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 513 <
      2 ^ wordWidth shape.size :=
  ((selectCloseBlock logicalReadBlock).eval_fits _ _ _ (selectCloseBlock_safe shape _ fit hm)).1 513


theorem selectWordBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (length : regs 401 ≤ packedReviewerCellWidth shape.size) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((selectWordBlock logicalReadBlock).compileAt 0 ++ [.halt 403])
      17754 ⟨regs, 0, .running⟩ := by
  have cap := select_constant_fit shape.size 17754 (by decide)
  exact rank_compiled_safety (shapeMemory shape) (wordWidth shape.size)
    (selectWordBlock logicalReadBlock) 403 17754 regs
    (by simp only [selectWordBlock_size, logicalReadBlock_size, locateBlock_size])
    cap (selectWordBlock_fieldsFit _ _ (logicalReadBlock_fieldsFit _ (by omega)) (by omega))
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega)
    fit (selectWordBlock_safe shape _ fit hm length)

theorem selectCloseBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      selectCloseProgram 91243 ⟨regs, 0, .running⟩ := by
  have cap := select_constant_fit shape.size 91243 (by decide)
  exact rank_compiled_safety (shapeMemory shape) (wordWidth shape.size)
    (selectCloseBlock logicalReadBlock) 513 91243 regs
    (by simp only [selectCloseBlock_size, logicalReadBlock_size, locateBlock_size])
    cap (selectCloseBlock_fieldsFit _ _ (logicalReadBlock_fieldsFit _ (by omega)) (by omega))
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega)
    fit (selectCloseBlock_safe shape _ fit hm)

/-- Value, receipt order and every machine safety observation refer to one
fixed compiled select run on the counted allocation. -/
theorem selectCloseRun_safe (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size) :
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 512)
    let actual := selectCloseRun (shapeMemory shape) regs
    actual.result = some (optionNatPacket expected.value) ∧
    actual.final.status = .halted (optionNatPacket expected.value) ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 91243 ∧
    (∀ r, ¬ SelectWrites r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace ∧
    optionNatPacket expected.value < 2 ^ wordWidth shape.size ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      selectCloseProgram 91243 ⟨regs, 0, .running⟩ := by
  have sourceFit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) :=
    ⟨fit, fun _ h => Status.noConfusion h⟩
  have semantic := selectCloseRun_canonical shape regs hm
  have bound := selectCloseBlock_output_bound shape regs sourceFit hm
  have source := selectCloseBlock_canonical shape regs hm
  rw [source.2.1] at bound
  exact ⟨semantic.1, semantic.2.1, semantic.2.2.1, semantic.2.2.2.1,
    semantic.2.2.2.2.1, semantic.2.2.2.2.2, bound,
    selectCloseBlock_execution_safe shape regs sourceFit hm⟩

theorem selectCloseRun_sameAllocation (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size) :
    (shapeMemory shape).length * wordWidth shape.size ≤
      2 * shape.size + allocationRho shape.size ∧
    wordWidth shape.size ≤ 192 * (Nat.log2 (shape.size + 2) + 1) ∧
    (∀ value ∈ shapeMemory shape, value < 2 ^ wordWidth shape.size) ∧
    (selectCloseRun (shapeMemory shape) regs).result =
      some (optionNatPacket (packedSelectCloseLeaf
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 512)).value) ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      selectCloseProgram 91243 ⟨regs, 0, .running⟩ := by
  have h := selectCloseRun_safe shape regs hm fit
  exact ⟨shapeMemory_capacity_le shape, wordWidth_le_log shape.size,
    shapeMemory_words_fit shape, h.1, h.2.2.2.2.2.2.2⟩


namespace SelectSafetyConsumers

/-- This consumer spells the source boundary independently of helper predicates. -/
theorem source_expectedType (shape : CartesianShape) (regs : Registers) (status : Status)
    (registers : ∀ r, regs r < 2 ^ wordWidth shape.size)
    (halted : ∀ value, status = .halted value → value < 2 ^ wordWidth shape.size)
    (metadata : ∀ i < 174, regs (16 + i) = ((metadata shape)[i]?).getD 0)
    (_occurrence : regs 512 ≤ shape.size) :
    (selectCloseBlock logicalReadBlock).Safe (shapeMemory shape)
      (wordWidth shape.size) ⟨regs, status⟩ :=
  selectCloseBlock_safe shape _ ⟨registers, halted⟩ metadata

theorem word_expectedType (shape : CartesianShape) (regs : Registers)
    (registers : ∀ r, regs r < 2 ^ wordWidth shape.size)
    (metadata : ∀ i < 174, regs (16 + i) = ((metadata shape)[i]?).getD 0)
    (_word : regs 400 ≤ 2 ^ packedReviewerCellWidth shape.size)
    (length : regs 401 ≤ packedReviewerCellWidth shape.size)
    (_occurrence : regs 402 ≤ metadataEnvelope shape.size) :
    (selectWordBlock logicalReadBlock).Safe (shapeMemory shape)
      (wordWidth shape.size) ⟨regs, .running⟩ ∧
    ((selectWordBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 403 ≤
      metadataEnvelope shape.size := by
  have fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) :=
    ⟨registers, fun _ h => Status.noConfusion h⟩
  exact ⟨selectWordBlock_safe shape _ fit metadata length,
    selectWordBlock_output_bound shape regs fit metadata length⟩

theorem run_expectedType (shape : CartesianShape) (regs : Registers)
    (metadata : ∀ i < 174, regs (16 + i) = ((metadata shape)[i]?).getD 0)
    (fit : ∀ r, regs r < 2 ^ wordWidth shape.size) :
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 512)
    let program := (selectCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 513]
    let actual := run (shapeMemory shape) program 91243 ⟨regs, 0, .running⟩
    actual.result = some ((expected.value.map (fun position => position + 1)).getD 0) ∧
    actual.final.status = .halted ((expected.value.map (fun position => position + 1)).getD 0) ∧
    actual.reads = expected.trace.flatMap (fun event => match event with
      | .readWord segment index _ => readerReceipts shape (shapeMemory shape) segment index
      | _ => []) ∧ actual.steps ≤ 91243 ∧
    (∀ r, ¬ ((256 ≤ r ∧ r < 311) ∨ (352 ≤ r ∧ r < 371) ∨ (400 ≤ r ∧ r < 412) ∨
      (513 ≤ r ∧ r < 551) ∨ (560 ≤ r ∧ r < 571) ∨ (590 ≤ r ∧ r < 601) ∨
      (640 ≤ r ∧ r < 660) ∨ (8192 ≤ r ∧ r < 8271)) → actual.final.regs r = regs r) ∧
    (∀ event ∈ expected.trace, event.isReadWord) ∧
    ((expected.value.map (fun position => position + 1)).getD 0) < 2 ^ wordWidth shape.size ∧
    (∀ instruction ∈ program, instruction.Fits (wordWidth shape.size)) ∧
    actual.final.Fits (wordWidth shape.size) ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe (wordWidth shape.size) t.before t.instruction ∧
        t.after.Fits (wordWidth shape.size)) ∧
    (∀ index, index ≤ 91243 →
      (run (shapeMemory shape) program index ⟨regs, 0, .running⟩).final.Fits (wordWidth shape.size)) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      actual.transitions[index]? = some t → t.receipt = some receipt →
      receipt.address < 2 ^ wordWidth shape.size ∧ receipt.reply = (shapeMemory shape)[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ wordWidth shape.size)) := by
  simpa only [selectCloseRun, selectCloseProgram, optionNatPacket, logicalTraceReads,
    SelectWrites, ReadOnlyTrace, RankExecutionSafety] using selectCloseRun_safe shape regs metadata fit

theorem canonical_boundary (shape : CartesianShape) (regs : Registers)
    (metadata : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size)
    (boundary : regs 512 = shape.size) :
    (selectCloseRun (shapeMemory shape) regs).result = some 0 ∧
    (selectCloseRun (shapeMemory shape) regs).reads = [] ∧
    (∀ index, index ≤ 91243 → (run (shapeMemory shape) selectCloseProgram index
      ⟨regs, 0, .running⟩).final.Fits (wordWidth shape.size)) := by
  have absent := selectCloseRun_invalid shape regs metadata (by omega)
  have safe := selectCloseBlock_execution_safe shape regs
    ⟨fit, fun _ h => Status.noConfusion h⟩ metadata
  exact ⟨absent.1, absent.2, safe.2.2.2.1⟩

theorem empty_shape (shape : CartesianShape) (regs : Registers)
    (empty : shape.size = 0) (metadata : MetadataMatches shape regs)
    (fit : ∀ r, regs r < 2 ^ wordWidth shape.size) :
    (selectCloseRun (shapeMemory shape) regs).result = some 0 ∧
    (selectCloseRun (shapeMemory shape) regs).reads = [] ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      selectCloseProgram 91243 ⟨regs, 0, .running⟩ := by
  have absent := selectCloseRun_invalid shape regs metadata (by omega)
  exact ⟨absent.1, absent.2, selectCloseBlock_execution_safe shape regs
    ⟨fit, fun _ h => Status.noConfusion h⟩ metadata⟩

/-- Universal symbolic rare paths retain arbitrary canonical long/sparse counts;
only the decoded caller fields needed by their actual arithmetic are bounded. -/
theorem symbolic_rare_paths (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (metadata : MetadataMatches shape regs) (occurrence : regs 512 ≤ metadataEnvelope shape.size)
    (word : regs 562 ≤ metadataEnvelope shape.size) (offset : regs 564 ≤ metadataEnvelope shape.size)
    (base : regs 520 ≤ 3 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (selectLongBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
    (selectSparseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ :=
  ⟨selectLongBlock_safe shape regs fit metadata occurrence word offset,
    selectSparseBlock_safe shape regs fit metadata occurrence base⟩

end SelectSafetyConsumers

end RMQ.SuccinctFinal.PackedWordRAM
