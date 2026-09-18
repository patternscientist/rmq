import RMQ.Core.WordRAM.Bitvector.GenericSelectProof
import RMQ.Core.WordRAM.Bitvector.GenericRankSafety
import RMQ.Core.WordRAM.Bitvector.NumericReader
import RMQ.Core.WordRAM.Packed.SelectSafety

/-! # Numerical safety of the shared generic select controller

All executable blocks are the existing Packed blocks. The local context below
only packages the explicit reader and numerical proof parameters.
-/

namespace RMQ.PackedBitvector.Controller
open SuccinctFinal SuccinctFinal.PackedWordRAM Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

namespace SelectSafety

structure Context where
  model : ControllerModel
  limits : SafetyLimits
  bounds : ControllerSafetyBounds model limits
  memory : Memory
  reader : Block
  safe : ReaderSafe model limits.width memory reader
  correct : ReaderSimulation model memory reader
  writes : ReaderWrites reader

theorem reader_output_bounds (ctx : Context) (regs : Registers)
    (hm : MetadataMatches ctx.model regs) :
    (ctx.reader.eval ctx.memory ⟨regs, .running⟩).final.regs 8194 ≤ ctx.limits.packetBound ∧
    (regs 8192 = 0 ∨ regs 8192 = 11 ∨ regs 8192 = 15 →
      (ctx.reader.eval ctx.memory ⟨regs, .running⟩).final.regs 8195 ≤ ctx.limits.rawWidth) := by
  have h := ctx.correct regs hm
  refine ⟨?_, ?_⟩
  · rw [h.2.1]
    exact logicalPacket_bound ctx.model ctx.limits ctx.bounds _ _
  · intro hr
    rw [h.2.2.1]
    exact ctx.bounds.raw_length _ _ hr

theorem selectEntrySuper_expectedType (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches model regs) :
    let actual := (selectEntryBlock reader 1 514 560).eval memory ⟨regs, .running⟩
    let expected := packedSelectEntryRead ⟨1, 2, 3, 4, 29⟩
      model.store (regs 514)
    actual.final.status = .running ∧
      (match expected.value with
        | none => actual.final.regs 560 = 0
        | some entry => actual.final.regs 560 = 1 ∧
            actual.final.regs 561 = entry.baseOccurrence ∧ actual.final.regs 562 = entry.baseWordIndex ∧
            actual.final.regs 563 = entry.rankBefore ∧ actual.final.regs 564 = entry.firstOffset) ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have h := selectEntryBlock_source model memory reader hreader hwrites 1 514 560
    (by decide) (by decide) (by decide) (Or.inl (by decide)) regs hm
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

theorem selectEntryLocal_expectedType (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches model regs) :
    let actual := (selectEntryBlock reader 5 515 590).eval memory ⟨regs, .running⟩
    let expected := packedSelectEntryRead ⟨5, 6, 7, 8, 29⟩
      model.store (regs 515)
    actual.final.status = .running ∧
      (match expected.value with
        | none => actual.final.regs 590 = 0
        | some entry => actual.final.regs 590 = 1 ∧
            actual.final.regs 591 = entry.baseOccurrence ∧ actual.final.regs 592 = entry.baseWordIndex ∧
            actual.final.regs 593 = entry.rankBefore ∧ actual.final.regs 594 = entry.firstOffset) ∧
      actual.reads = logicalTraceReads model memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have h := selectEntryBlock_source model memory reader hreader hwrites 5 515 590
    (by decide) (by decide) (by decide) (Or.inl (by decide)) regs hm
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

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

theorem selectFieldRead_safe (ctx : Context) (memory : Memory) (reader : Block)
    (hreader : ReaderSafe ctx.model ctx.limits.width memory reader) (segment indexReg destination : Nat)
    (hsegment : segment < 2 ^ ctx.limits.width) (s : Data)
    (fit : s.Fits (ctx.limits.width)) (hm : MetadataMatches ctx.model s.regs) :
    (selectFieldRead reader segment indexReg destination).Safe memory (ctx.limits.width) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs
      subst status
      have first := Block.safe_action memory (ctx.limits.width) (.constant 8192 segment)
        ⟨regs, .running⟩ fit hsegment
      have fp := Block.eval_fits _ _ _ _ first
      have second := Block.safe_action memory (ctx.limits.width) (.move 8193 indexReg)
        _ fp (fp.1 indexReg)
      have fq := Block.eval_fits _ _ _ _ second
      have mp : MetadataMatches ctx.model
          ((regs.write 8192 segment).write 8193 ((regs.write 8192 segment) indexReg)) :=
        MetadataMatches.write ctx.model _
          (MetadataMatches.write ctx.model regs hm 8192 segment (Or.inr (by decide)))
          8193 _ (Or.inr (by decide))
      have loadSafe := hreader _ fq mp
      have fr := Block.eval_fits _ _ _ _ loadSafe
      have tail := SimpleScalar.safe memory (ctx.limits.width)
        (Block.sequence [.action (.move destination 8194)]) ⟨True.intro, True.intro⟩ _ fr
      exact Block.safe_seq first (Block.safe_seq second (Block.safe_seq loadSafe tail))
  · exact Block.safe_stopped memory _ _ s fit hs

theorem selectFieldsFrom_safe (ctx : Context) (memory : Memory) (reader : Block)
    (hreader : ReaderSafe ctx.model ctx.limits.width memory reader) (hwrites : ReaderWrites reader)
    (segment indexReg destination count : Nat) (hd : 190 ≤ destination)
    (hsegments : segment + count ≤ 2 ^ ctx.limits.width) (s : Data)
    (fit : s.Fits (ctx.limits.width)) (hm : MetadataMatches ctx.model s.regs) :
    (selectFieldsFrom reader segment indexReg destination count).Safe memory (ctx.limits.width) s := by
  induction count generalizing segment destination s with
  | zero => exact Block.safe_skip memory _ s fit
  | succ count ih =>
      have head := selectFieldRead_safe ctx memory reader hreader segment indexReg destination
        (by omega) s fit hm
      have fp := Block.eval_fits _ _ _ _ head
      have mp := selectFieldRead_metadata ctx.model reader hwrites segment indexReg destination hd memory s hm
      exact Block.safe_seq head (ih (segment + 1) (destination + 1) (by omega) (by omega) _ fp mp)

theorem selectEntryBlock_safe (ctx : Context) (memory : Memory) (reader : Block)
    (hreader : ReaderSafe ctx.model ctx.limits.width memory reader) (hwrites : ReaderWrites reader)
    (segment indexReg base : Nat) (hb : 190 ≤ base)
    (hsegments : segment + 4 ≤ 2 ^ ctx.limits.width) (s : Data)
    (fit : s.Fits (ctx.limits.width)) (hm : MetadataMatches ctx.model s.regs) :
    (selectEntryBlock reader segment indexReg base).Safe memory (ctx.limits.width) s := by
  have one := ctx.limits.constant_fit 1 (by decide)
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs
      subst status
      have first := Block.safe_action memory (ctx.limits.width) (.constant base 0)
        ⟨regs, .running⟩ fit (Nat.two_pow_pos _)
      have fp := Block.eval_fits _ _ _ _ first
      have second := Block.safe_action memory (ctx.limits.width) (.constant (base + 9) 1)
        _ fp one
      have fq := Block.eval_fits _ _ _ _ second
      have mp : MetadataMatches ctx.model ((regs.write base 0).write (base + 9) 1) :=
        MetadataMatches.write ctx.model _ (MetadataMatches.write ctx.model regs hm base 0 (Or.inr hb))
          (base + 9) 1 (Or.inr (by omega))
      have fields := selectFieldsFrom_safe ctx memory reader hreader hwrites segment indexReg
        (base + 5) 4 (by omega) hsegments _ fq mp
      have fr := Block.eval_fits _ _ _ _ fields
      have decode := selectEntryDecode_safe base memory _ one _ fr
      exact Block.safe_seq first (Block.safe_seq second (Block.safe_seq fields
        (Block.safe_seq decode (Block.safe_skip memory _ _ (Block.eval_fits _ _ _ _ decode)))))
  · exact Block.safe_stopped memory _ _ s fit hs

theorem select_metadata_geometry (ctx : Context) (regs : Registers)
    (hm : MetadataMatches ctx.model regs) :
    regs 16 = ctx.model.metadata 16 ∧ 0 < regs 25 ∧ 0 < regs 26 ∧ 0 < regs 32 ∧
      regs 32 ≤ ctx.limits.rawWidth ∧ 0 < regs 34 ∧ regs 34 ≤ ctx.limits.rawWidth := by
  rw [hm 16 (by decide), hm 25 (by decide), hm 26 (by decide),
    hm 32 (by decide), hm 34 (by decide)]
  exact ⟨rfl, ctx.bounds.super_stride_pos, ctx.bounds.local_stride_pos,
    ctx.bounds.word_pos, ctx.bounds.word_le, ctx.bounds.chunk_pos, ctx.bounds.chunk_le⟩

theorem selectEntryRead_bounds (ctx : Context)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases) (index : Nat) :
    match (packedSelectEntryRead layout ctx.model.store index).value with
    | none => True
    | some entry => entry.baseOccurrence ≤ ctx.limits.packetBound ∧
        entry.baseWordIndex ≤ ctx.limits.packetBound ∧
        entry.rankBefore ≤ ctx.limits.packetBound ∧
        entry.firstOffset ≤ ctx.limits.packetBound := by
  rw [selectEntryRead_value, ← selectEntryOfPackets_logicalPacket]
  exact selectEntryOfPackets_bounds _ _ _ _ _
    (logicalPacket_bound ctx.model ctx.limits ctx.bounds layout.baseOccurrence index)
    (logicalPacket_bound ctx.model ctx.limits ctx.bounds layout.baseWordIndex index)
    (logicalPacket_bound ctx.model ctx.limits ctx.bounds layout.rankBefore index)
    (logicalPacket_bound ctx.model ctx.limits ctx.bounds layout.firstOffset index)

theorem selectEntryBlock_present_bounds (ctx : Context) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation ctx.model memory reader) (hwrites : ReaderWrites reader)
    (segment indexReg base : Nat) (hb : 190 ≤ base) (hupper : base + 11 ≤ 8192)
    (hi : indexReg < 8192) (hout : indexReg < base ∨ base + 11 ≤ indexReg)
    (regs : Registers) (hm : MetadataMatches ctx.model regs) :
    let actual := (selectEntryBlock reader segment indexReg base).eval memory ⟨regs, .running⟩
    actual.final.regs base ≠ 0 →
      actual.final.regs (base + 1) ≤ ctx.limits.packetBound ∧
      actual.final.regs (base + 2) ≤ ctx.limits.packetBound ∧
      actual.final.regs (base + 3) ≤ ctx.limits.packetBound ∧
      actual.final.regs (base + 4) ≤ ctx.limits.packetBound := by
  dsimp only
  have source := selectEntryBlock_source ctx.model memory reader hreader hwrites segment indexReg base
    hb hupper hi hout regs hm
  have bounds := selectEntryRead_bounds ctx (selectEntryLayout segment) (regs indexReg)
  cases he : (packedSelectEntryRead (selectEntryLayout segment)
      ctx.model.store (regs indexReg)).value with
  | none =>
      simp only [SelectEntryResult, he] at source
      exact fun h => (h source.1.2).elim
  | some entry =>
      simp only [SelectEntryResult, he] at source
      simp only [he] at bounds
      intro _
      rw [source.1.2.2.1, source.1.2.2.2.1, source.1.2.2.2.2.1, source.1.2.2.2.2.2]
      exact bounds

theorem selectWordAddress_safe (limits : SafetyLimits) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hc : regs 34 ≤ limits.rawWidth) (hj : regs 404 < 8) :
    selectWordAddress.Safe memory (limits.width) ⟨regs, .running⟩ := by
  have a := Block.safe_action memory (limits.width) (.move 280 400)
    ⟨regs, .running⟩ fit (fit.1 400)
  have fa := Block.eval_fits _ _ _ _ a
  have b := Block.safe_action memory (limits.width) (.move 281 34) _ fa (fa.1 34)
  have fb := Block.eval_fits _ _ _ _ b
  have c := Block.safe_action memory (limits.width) (.move 282 404) _ fb (fb.1 404)
  have fc := Block.eval_fits _ _ _ _ c
  have d := Block.safe_action memory (limits.width) (.move 283 401) _ fc (fc.1 401)
  have fd := Block.eval_fits _ _ _ _ d
  have slot := chunkSlotBlock_canonical_safe 280 limits memory _ fd
    (by simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write] using hc)
    (by simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write] using hj)
  have fs := Block.eval_fits _ _ _ _ slot
  have tail := SimpleScalar.safe memory (limits.width)
    (Block.sequence [.action (.constant 8192 21), .action (.move 8193 286)])
    ⟨limits.constant_fit 21 (by decide), True.intro, True.intro⟩ _ fs
  exact Block.safe_seq a (Block.safe_seq b (Block.safe_seq c
    (Block.safe_seq d (Block.safe_seq slot tail))))

theorem selectWordDecode_safe (limits : SafetyLimits) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hc : regs 34 ≤ limits.rawWidth) (hl : regs 284 ≤ regs 34) :
    selectWordDecode.Safe memory (limits.width) ⟨regs, .running⟩ := by
  have a := Block.safe_action memory (limits.width) (.move 300 34)
    ⟨regs, .running⟩ fit (fit.1 34)
  have fa := Block.eval_fits _ _ _ _ a
  have b := Block.safe_action memory (limits.width) (.move 301 284) _ fa (fa.1 284)
  have fb := Block.eval_fits _ _ _ _ b
  have sub := natSubBlock_safe memory (limits.width) 302 8194 407 409 _ fb
    (limits.constant_fit 1 (by decide)) (by decide) (by decide)
  have fs := Block.eval_fits _ _ _ _ sub
  have zero := Block.safe_action memory (limits.width) (.constant 303 0) _ fs (Nat.two_pow_pos _)
  have fz := Block.eval_fits _ _ _ _ zero
  have hsub (r : Registers) := natSubBlock_source 302 8194 407 409 memory r (by decide) (by decide)
  have decode := chunkRankBlock_canonical_safe 300 limits memory _ fz
    (by simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write, hsub] using hc)
    (by simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
      Data.ofState, Registers.write, hsub] using hl)
  exact Block.safe_seq a (Block.safe_seq b (Block.safe_seq sub
    (Block.safe_seq zero (Block.safe_seq decode
      (Block.safe_skip memory _ _ (Block.eval_fits _ _ _ _ decode))))))

theorem selectWordMiss_safe (limits : SafetyLimits) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hj : regs 404 < 8) (hone : regs 407 = 1) :
    selectWordMiss.Safe memory (limits.width) ⟨regs, .running⟩ := by
  apply ScalarChecks_safe memory _ _ _ fit
  have cap := limits.constant_fit 9 (by decide)
  have hwne : limits.width ≠ 0 := by have := limits.width32; omega
  have fk := fit.1 406
  dsimp only at fk
  by_cases hsub : regs 304 ≤ regs 406
  all_goals simp [ScalarChecks, selectWordMiss, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
    hsub, hone, hwne] <;> omega

theorem selectWordSelectAddress_safe (limits : SafetyLimits) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hc : regs 34 ≤ limits.rawWidth) (hone : regs 407 = 1)
    (hvalue : regs 285 ≤ limits.packetBound) (hk : regs 406 ≤ regs 34) :
    selectWordSelectAddress.Safe memory (limits.width) ⟨regs, .running⟩ := by
  let e := limits.envelope
  have ep : 0 < e := limits.envelope_pos
  have hw := limits.raw_lt_packet
  have hq := limits.packet_le_envelope
  have cp : regs 34 + 1 ≤ e := by dsimp only [e]; omega
  have vp : regs 285 ≤ e := by dsimp only [e]; omega
  have kp : regs 406 ≤ e := by omega
  have hp := Nat.mul_le_mul vp cp
  have hsquare : e ≤ e * e := by
    simpa using Nat.mul_le_mul_left e (show 1 ≤ e by omega)
  have cap := limits.square
  change 256 * (e * e) < _ at cap
  have const := limits.constant_fit 22 (by decide)
  apply ScalarChecks_safe memory _ _ _ fit
  simp [ScalarChecks, selectWordSelectAddress, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, hone]
  omega

theorem selectWordFinish_safe (limits : SafetyLimits) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hc : regs 34 ≤ limits.rawWidth) (hj : regs 404 < 8)
    (hone : regs 407 = 1) (hreply : regs 8194 ≤ limits.packetBound) :
    selectWordFinish.Safe memory (limits.width) ⟨regs, .running⟩ := by
  have hp := Nat.mul_le_mul (show regs 404 ≤ 7 by omega) hc
  have he := limits.output_bound
  have hq := limits.packet_pos
  have cap := limits.envelope_lt_capacity
  have hwne : limits.width ≠ 0 := by have := limits.width32; omega
  apply ScalarChecks_safe memory _ _ _ fit
  by_cases hsub : 1 ≤ regs 8194
  all_goals simp [ScalarChecks, selectWordFinish, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
    hsub, hone, hwne] <;> omega

theorem selectWordInit_safe (limits : SafetyLimits) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (limits.width))
    (hc : 0 < regs 34) (hl : regs 401 ≤ limits.rawWidth) :
    selectWordInit.Safe memory (limits.width) ⟨regs, .running⟩ := by
  have hdiv := Nat.div_le_self (regs 401 - 1) (regs 34)
  have hw := limits.raw_lt_packet
  have he := limits.output_bound
  have cap := limits.envelope_lt_capacity
  have const := limits.constant_fit 9 (by decide)
  have hk := fit.1 402
  dsimp only at hk
  have hwne : limits.width ≠ 0 := by have := limits.width32; omega
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

private theorem select_metadata_frame (ctx : Context) (memory : Memory)
    (block : Block) (allowed : Nat → Prop) (writes : block.WritesOnly allowed)
    (outside : ∀ r, 0 ≤ r → r < 190 → ¬ allowed r)
    (s : Data) (hm : MetadataMatches ctx.model s.regs) :
    MetadataMatches ctx.model (block.eval memory s).final.regs := by
  intro i hi
  rw [Block.eval_frame memory block allowed writes _ (outside _ (by omega) (by omega))]
  exact hm i hi

private theorem select_data_running (s : Data) (hs : s.status = .running) :
    s = ⟨s.regs, .running⟩ := by cases s; simp_all

theorem select_decodedReply_bound (ctx : Context) (segment index : Nat) :
    ((ctx.model.store.readWord? segment index).map
      bitsToNatLE).getD 0 ≤ ctx.limits.packetBound := by
  have h := logicalPacket_bound ctx.model ctx.limits ctx.bounds segment index
  rw [← logicalPacket_pred]
  omega

theorem selectWordSelected_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hj : regs 404 < 8) (hone : regs 407 = 1)
    (hvalue : regs 285 ≤ ctx.limits.packetBound) (hk : regs 406 ≤ regs 34) :
    (selectWordSelected ctx.reader).Safe ctx.memory (ctx.limits.width)
      ⟨regs, .running⟩ := by
  have hc := (select_metadata_geometry ctx regs hm).2.2.2.2.2.2
  have head := selectWordSelectAddress_safe ctx.limits ctx.memory regs fit hc hone hvalue hk
  refine select_safe_follow head (fun fa => ?_)
  have hw : selectWordSelectAddress.WritesOnly (fun r => r = 410 ∨ r = 8192 ∨ r = 8193) := by
    simp [selectWordSelectAddress, Block.sequence, Block.WritesOnly, Action.destination]
  have frame (r : Nat) (ho : r ≠ 410 ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    Block.eval_frame ctx.memory _ _ hw r (by omega) ⟨regs, .running⟩
  have metadataA := select_metadata_frame ctx ctx.memory _ _ hw
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have src := selectWordSelectAddress_source ctx.memory regs
  generalize he : selectWordSelectAddress.eval ctx.memory ⟨regs, .running⟩ = addressed
    at src frame metadataA fa ⊢
  rcases addressed with ⟨⟨ar, ast⟩, ard⟩
  dsimp only at src frame metadataA fa
  have hs := src.1
  subst ast
  have loadSafe := ctx.safe ⟨ar, .running⟩ fa metadataA
  refine select_safe_follow loadSafe (fun fb => ?_)
  have reader := ctx.correct ar metadataA
  have bound := reader_output_bounds ctx ar metadataA
  generalize heR : ctx.reader.eval ctx.memory ⟨ar, .running⟩ = loaded
    at reader bound fb ⊢
  rcases loaded with ⟨⟨br, bst⟩, brd⟩
  dsimp only at reader bound fb
  have hs := reader.1
  subst bst
  have finish := selectWordFinish_safe ctx.limits ctx.memory br fb
    (by rw [reader.2.2.2.2 34 (Or.inl (by decide)), frame 34 (by omega)]; exact hc)
    (by rw [reader.2.2.2.2 404 (Or.inl (by decide)), frame 404 (by omega)]; exact hj)
    (by rw [reader.2.2.2.2 407 (Or.inl (by decide)), frame 407 (by omega)]; exact hone)
    bound.1
  exact Block.safe_seq finish (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ finish))

theorem selectWordActive_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hj : regs 404 < 8) (hone : regs 407 = 1) :
    (selectWordActive ctx.reader).Safe ctx.memory (ctx.limits.width)
      ⟨regs, .running⟩ := by
  have hc := (select_metadata_geometry ctx regs hm).2.2.2.2.2.2
  have first := selectWordAddress_safe ctx.limits ctx.memory regs fit hc hj
  refine select_safe_follow first (fun fa => ?_)
  have srcA := selectWordAddress_source ctx.memory regs
  have metaA := select_metadata_frame ctx ctx.memory _ _ selectWordAddress_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frameA (r : Nat) (ho : (r < 280 ∨ 292 ≤ r) ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    selectWordAddress_frame ctx.memory ⟨regs, .running⟩ r ho
  generalize heA : selectWordAddress.eval ctx.memory ⟨regs, .running⟩ = addressed
    at srcA metaA frameA fa ⊢
  rcases addressed with ⟨⟨ar, ast⟩, ard⟩
  dsimp only at srcA metaA frameA fa
  have hs := srcA.1
  subst ast
  have loadSafe := ctx.safe ⟨ar, .running⟩ fa metaA
  refine select_safe_follow loadSafe (fun fb => ?_)
  have srcB := ctx.correct ar metaA
  generalize heB : ctx.reader.eval ctx.memory ⟨ar, .running⟩ = loaded
    at srcB fb ⊢
  rcases loaded with ⟨⟨br, bst⟩, brd⟩
  dsimp only at srcB fb
  have hs := srcB.1
  subst bst
  have frameB := srcB.2.2.2.2
  have metaB := readerFrame_metadata ctx.model ar br frameB metaA
  have cb : br 34 = regs 34 := by rw [frameB 34 (Or.inl (by decide)), frameA 34 (by omega)]
  have lb : br 284 ≤ br 34 := by
    rw [frameB 284 (Or.inl (by decide)), srcA.2.2.2.2.1, cb]
    exact Nat.min_le_left _ _
  have decode := selectWordDecode_safe ctx.limits ctx.memory br fb (by omega) lb
  refine select_safe_follow decode (fun fc => ?_)
  have srcC := selectWordDecode_source ctx.memory br
  have metaC := select_metadata_frame ctx ctx.memory _ _ selectWordDecode_writes
    (by intro r h1 h2; omega) ⟨br, .running⟩ metaB
  have frameC (r : Nat) (ho : (r < 300 ∨ 311 ≤ r) ∧ r ≠ 409) :=
    Block.eval_frame ctx.memory _ _ selectWordDecode_writes r (by omega) ⟨br, .running⟩
  generalize heC : selectWordDecode.eval ctx.memory ⟨br, .running⟩ = decoded
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
  have valueBound : cr 285 ≤ ctx.limits.packetBound := by
    rw [frameC 285 (by omega), frameB 285 (Or.inl (by decide)), srcA.2.2.2.2.2]
    exact Nat.le_trans (Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (Nat.le_trans (Nat.pow_le_pow_right (by decide) hc)
        (Nat.le_trans ctx.limits.rawCapacity (Nat.le_max_left _ _)))
  have compare := Block.safe_action ctx.memory (ctx.limits.width)
    (.comparison .lt 408 406 304) ⟨cr, .running⟩ fc
    (by dsimp only [Action.LocalSafe, Comparison.eval]; split <;>
      exact ctx.limits.constant_fit _ (by decide))
  refine select_safe_follow compare (fun ft => ?_)
  have testMeta := MetadataMatches.write ctx.model cr metaC 408
    (Comparison.lt.eval (cr 406) (cr 304)) (Or.inr (by decide))
  by_cases active : cr 406 < cr 304
  · have selected := selectWordSelected_safe ctx
      (cr.write 408 (Comparison.lt.eval (cr 406) (cr 304))) ft testMeta
      (by simpa [Registers.write, kept 404 (by omega) (by decide)] using hj)
      (by simpa [Registers.write, kept 407 (by omega) (by decide)] using hone)
      (by simpa [Registers.write] using valueBound)
      (by simpa [Registers.write] using Nat.le_trans (Nat.le_of_lt active) rankBound)
    have final := Block.safe_ifZero (condition := 408) (zero := selectWordMiss)
      (nonzero := selectWordSelected ctx.reader) ft (by
      simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
        Data.ofState, Registers.write, Comparison.eval, active] using selected)
    exact Block.safe_seq final (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ final))
  · have missed := selectWordMiss_safe ctx.limits ctx.memory
      (cr.write 408 (Comparison.lt.eval (cr 406) (cr 304))) ft
      (by simpa [Registers.write, kept 404 (by omega) (by decide)] using hj)
      (by simpa [Registers.write, kept 407 (by omega) (by decide)] using hone)
    have final := Block.safe_ifZero (condition := 408) (zero := selectWordMiss)
      (nonzero := selectWordSelected ctx.reader) ft (by
      simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
        Data.ofState, Registers.write, Comparison.eval, active] using missed)
    exact Block.safe_seq final (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ final))

theorem selectWordActive_output_bound (ctx : Context) (regs : Registers)
    (hm : MetadataMatches ctx.model regs) (hj : regs 404 < 8) (hone : regs 407 = 1)
    (hout : regs 403 ≤ ctx.limits.envelope) :
    ((selectWordActive ctx.reader).eval ctx.memory ⟨regs, .running⟩).final.regs 403 ≤
      ctx.limits.envelope := by
  have source := selectWordActive_source ctx.model ctx.memory ctx.reader
    ctx.correct ctx.writes regs hm hone
  have hvalue := select_decodedReply_bound ctx 22
    ((regs 400 / 2 ^ (regs 404 * regs 34) % 2 ^ regs 34) * (regs 34 + 1) + regs 406)
  have hc := (select_metadata_geometry ctx regs hm).2.2.2.2.2.2
  have hp := Nat.mul_le_mul (show regs 404 ≤ 7 by omega) hc
  have he := ctx.limits.output_bound
  have hq := ctx.limits.packet_pos
  dsimp only at source
  rw [source.2.1]
  split <;> omega

theorem selectWordBody_safe (ctx : Context) (s : Data)
    (fit : s.Fits (ctx.limits.width)) (hm : MetadataMatches ctx.model s.regs)
    (total : s.regs 405 ≤ 8) (hone : s.regs 407 = 1) :
    (selectWordBody ctx.reader).Safe ctx.memory (ctx.limits.width) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs total hone
      subst status
      apply Block.safe_ifZero fit
      by_cases hfound : regs 403 = 0
      · simp only [hfound, if_pos]
        have compare := Block.safe_action ctx.memory (ctx.limits.width)
          (.comparison .lt 408 404 405) ⟨regs, .running⟩ fit
          (by dsimp only [Action.LocalSafe, Comparison.eval]; split <;>
            exact ctx.limits.constant_fit _ (by decide))
        refine select_safe_follow compare (fun fp => ?_)
        apply Block.safe_ifZero fp
        by_cases active : regs 404 < regs 405
        · have mp := MetadataMatches.write ctx.model regs hm 408
            (Comparison.lt.eval (regs 404) (regs 405)) (Or.inr (by decide))
          have child := selectWordActive_safe ctx
            (regs.write 408 (Comparison.lt.eval (regs 404) (regs 405))) fp mp
            (by simp [Registers.write]; omega) (by simpa [Registers.write] using hone)
          simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
            Data.ofState, Registers.write, Comparison.eval, active] using child
        · simpa [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
            Data.ofState, Registers.write, Comparison.eval, active] using
            Block.safe_skip ctx.memory (ctx.limits.width) _ fp
      · simpa [hfound] using Block.safe_skip ctx.memory (ctx.limits.width) _ fit
  · exact Block.safe_stopped _ _ _ s fit hs

def SelectWordSafetyInv (ctx : Context) (s : Data) : Prop :=
  s.Fits (ctx.limits.width) ∧ MetadataMatches ctx.model s.regs ∧
    s.regs 405 ≤ 8 ∧ s.regs 407 = 1 ∧ s.regs 403 ≤ ctx.limits.envelope

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

theorem selectWordBody_running (ctx : Context) (regs : Registers)
    (hm : MetadataMatches ctx.model regs) (hone : regs 407 = 1) :
    ((selectWordBody ctx.reader).eval ctx.memory ⟨regs, .running⟩).final.status = .running := by
  by_cases found : regs 403 = 0
  · by_cases active : regs 404 < regs 405
    · have source := selectWordActive_source ctx.model ctx.memory ctx.reader
        ctx.correct ctx.writes (regs.write 408 1)
        (MetadataMatches.write ctx.model regs hm 408 1 (Or.inr (by decide)))
        (by simpa [Registers.write] using hone)
      exact select_guard_active_status ctx.memory (selectWordActive ctx.reader)
        regs found active source.1
    · rw [selectWordBody_inactive ctx.reader ctx.memory regs found (by omega)]
  · rw [selectWordBody_found ctx.reader ctx.memory regs found]

theorem selectWordBody_safe_invariant (ctx : Context) (s : Data)
    (inv : SelectWordSafetyInv ctx s) :
    (selectWordBody ctx.reader).Safe ctx.memory (ctx.limits.width) s ∧
      SelectWordSafetyInv ctx
        ((selectWordBody ctx.reader).eval ctx.memory s).final := by
  obtain ⟨fit, hm, total, hone, hout⟩ := inv
  have safe := selectWordBody_safe ctx s fit hm total hone
  have fp := Block.eval_fits _ _ _ _ safe
  have mp := selectWordBody_metadata ctx.model ctx.reader ctx.writes
    ctx.memory s hm
  have fr405 := selectWordBody_frame ctx.reader ctx.writes
    ctx.memory s 405 (by simp [SelectWordBodyWrites])
  have fr407 := selectWordBody_frame ctx.reader ctx.writes
    ctx.memory s 407 (by simp [SelectWordBodyWrites])
  refine ⟨safe, fp, mp, by omega, by omega, ?_⟩
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs total hone hout
      subst status
      by_cases found : regs 403 = 0
      · by_cases active : regs 404 < regs 405
        · let tested := regs.write 408 1
          have source := selectWordActive_output_bound ctx tested
            (MetadataMatches.write ctx.model regs hm 408 1 (Or.inr (by decide)))
            (by simp [tested, Registers.write]; omega)
            (by simpa [tested, Registers.write] using hone)
            (by simpa [tested, Registers.write] using hout)
          dsimp only [tested] at source
          exact select_guard_active_bound ctx.memory (selectWordActive ctx.reader)
            regs (ctx.limits.envelope) found active source
        · rw [selectWordBody_inactive ctx.reader ctx.memory regs found (by omega)]
          simpa [Registers.write] using hout
      · rw [selectWordBody_found ctx.reader ctx.memory regs found]
        exact hout
  · rw [Block.eval_stopped _ _ _ hs]
    exact hout

theorem selectWordBlock_safe (ctx : Context) (s : Data)
    (fit : s.Fits (ctx.limits.width)) (hm : MetadataMatches ctx.model s.regs)
    (hl : s.regs 401 ≤ ctx.limits.rawWidth) :
    (selectWordBlock ctx.reader).Safe ctx.memory (ctx.limits.width) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs hl
      subst status
      have hc := (select_metadata_geometry ctx regs hm).2.2.2.2.2.1
      have initSafe := selectWordInit_safe ctx.limits ctx.memory regs fit hc hl
      refine select_safe_follow initSafe (fun fp => ?_)
      have source := selectWordInit_source ctx.memory regs
      have hw : selectWordInit.WritesOnly (fun r => 403 ≤ r ∧ r ≤ 409) := by
        simp [selectWordInit, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, minBlock]
      have mp := select_metadata_frame ctx ctx.memory _ _ hw
        (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
      generalize he : selectWordInit.eval ctx.memory ⟨regs, .running⟩ = initialized
        at source mp fp ⊢
      rcases initialized with ⟨⟨ir, ist⟩, ireads⟩
      dsimp only at source mp fp
      have hs := source.1
      subst ist
      have inv : SelectWordSafetyInv ctx ⟨ir, .running⟩ := by
        refine ⟨fp, mp, ?_, source.2.2.2.2.2.2, ?_⟩
        · dsimp only
          rw [source.2.2.2.2.1]
          exact Nat.min_le_right _ _
        · dsimp only
          rw [source.2.2.1]
          omega
      exact Block.safe_repeat fp (IterationsSafe.of_invariant _ (SelectWordSafetyInv ctx)
        ((selectWordBody ctx.reader).eval ctx.memory)
        (selectWordBody_safe_invariant ctx) 8 _ inv)
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

theorem selectWordBlock_running (ctx : Context) (regs : Registers)
    (hm : MetadataMatches ctx.model regs) :
    ((selectWordBlock ctx.reader).eval ctx.memory ⟨regs, .running⟩).final.status = .running := by
  let inv (s : Data) := s.status = .running ∧ MetadataMatches ctx.model s.regs ∧ s.regs 407 = 1
  have preserve (s : Data) (hs : inv s) : inv
      ((selectWordBody ctx.reader).eval ctx.memory s).final := by
    have running := select_data_running s hs.1
    have st := selectWordBody_running ctx s.regs hs.2.1 hs.2.2
    have mp := selectWordBody_metadata ctx.model ctx.reader ctx.writes
      ctx.memory s hs.2.1
    have one := selectWordBody_frame ctx.reader ctx.writes
      ctx.memory s 407 (by simp [SelectWordBodyWrites])
    exact ⟨by rw [running]; exact st, mp, one.trans hs.2.2⟩
  have source := selectWordInit_source ctx.memory regs
  have hw : selectWordInit.WritesOnly (fun r => 403 ≤ r ∧ r ≤ 409) := by
    simp [selectWordInit, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, minBlock]
  have mp := select_metadata_frame ctx ctx.memory _ _ hw
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have initial : inv (selectWordInit.eval ctx.memory ⟨regs, .running⟩).final :=
    ⟨source.1, mp, source.2.2.2.2.2.2⟩
  exact select_init_repeat_property ctx.memory selectWordInit (selectWordBody ctx.reader)
    inv preserve 8 _ initial (fun s => s.status = .running) (fun _ h => h.1)
    (selectWordBlock ctx.reader) rfl

theorem selectWordBlock_output_bound (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hl : regs 401 ≤ ctx.limits.rawWidth) :
    ((selectWordBlock ctx.reader).eval ctx.memory ⟨regs, .running⟩).final.regs 403 ≤
      ctx.limits.envelope := by
  have hc := (select_metadata_geometry ctx regs hm).2.2.2.2.2.1
  have initSafe := selectWordInit_safe ctx.limits ctx.memory regs fit hc hl
  have fp := Block.eval_fits _ _ _ _ initSafe
  have source := selectWordInit_source ctx.memory regs
  have hw : selectWordInit.WritesOnly (fun r => 403 ≤ r ∧ r ≤ 409) := by
    simp [selectWordInit, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, minBlock]
  have mp := select_metadata_frame ctx ctx.memory _ _ hw
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have inv : SelectWordSafetyInv ctx (selectWordInit.eval ctx.memory ⟨regs, .running⟩).final := by
    refine ⟨fp, mp, ?_, source.2.2.2.2.2.2, ?_⟩
    · rw [source.2.2.2.2.1]
      exact Nat.min_le_right _ _
    · rw [source.2.2.1]
      omega
  exact select_init_repeat_bound ctx.memory selectWordInit (selectWordBody ctx.reader)
    (SelectWordSafetyInv ctx) (fun s hs => (selectWordBody_safe_invariant ctx s hs).2)
    8 _ inv (ctx.limits.envelope) (fun _ h => h.2.2.2.2)
    (selectWordBlock ctx.reader) rfl

theorem selectLongAddress_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs)
    (hrank : regs 360 ≤ ctx.limits.envelope)
    (hocc : regs 512 ≤ ctx.limits.envelope) :
    selectLongAddress.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  let e := ctx.limits.envelope
  have stride := metadata_envelope ctx.model ctx.limits ctx.bounds regs hm 25 (by decide)
  have hp := Nat.mul_le_mul hrank stride
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e (ctx.limits.envelope_pos)
  have cap := ctx.limits.square
  change 256 * (e * e) < _ at cap
  have one := ctx.limits.constant_fit 12 (by decide)
  have hwne : ctx.limits.width ≠ 0 := by have := ctx.limits.width32; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : regs 561 ≤ regs 512
  all_goals simp [ScalarChecks, selectLongAddress, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
    hsub, hwne] <;> dsimp only [e] at * <;> omega

theorem selectSparseAddress_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs)
    (hrank : regs 360 ≤ ctx.limits.envelope)
    (hocc : regs 512 ≤ ctx.limits.envelope) :
    selectSparseAddress.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  let e := ctx.limits.envelope
  have stride := metadata_envelope ctx.model ctx.limits ctx.bounds regs hm 26 (by decide)
  have hp := Nat.mul_le_mul hrank stride
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e (ctx.limits.envelope_pos)
  have cap := ctx.limits.square
  change 256 * (e * e) < _ at cap
  have one := ctx.limits.constant_fit 16 (by decide)
  have hwne : ctx.limits.width ≠ 0 := by have := ctx.limits.width32; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : regs 521 ≤ regs 512
  all_goals simp [ScalarChecks, selectSparseAddress, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
    hsub, hwne] <;> dsimp only [e] at * <;> omega

theorem selectLongFinish_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs)
    (hword : regs 562 ≤ ctx.limits.envelope)
    (hoffset : regs 564 ≤ ctx.limits.envelope)
    (hreply : regs 8194 ≤ ctx.limits.envelope) :
    selectLongFinish.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  let e := ctx.limits.envelope
  have word := metadata_envelope ctx.model ctx.limits ctx.bounds regs hm 32 (by decide)
  have hp := Nat.mul_le_mul hword word
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e (ctx.limits.envelope_pos)
  have cap := ctx.limits.square
  change 256 * (e * e) < _ at cap
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases absent : regs 8194 = 0
  all_goals simp [ScalarChecks, selectLongFinish, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, absent] <;> dsimp only [e] at * <;> omega

theorem selectSparseFinish_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hbase : regs 520 ≤ 3 * (ctx.limits.envelope * ctx.limits.envelope))
    (hreply : regs 8194 ≤ ctx.limits.envelope) :
    selectSparseFinish.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  let e := ctx.limits.envelope
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e (ctx.limits.envelope_pos)
  have cap := ctx.limits.square
  change 256 * (e * e) < _ at cap
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases absent : regs 8194 = 0
  all_goals simp [ScalarChecks, selectSparseFinish, Action.LocalSafe,
    Arithmetic.eval, absent] <;> dsimp only [e] at * <;> omega

theorem selectLocalAddress_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs)
    (hslot : regs 514 ≤ ctx.limits.envelope)
    (hocc : regs 512 ≤ ctx.limits.envelope) :
    selectLocalAddress.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  let e := ctx.limits.envelope
  have stride := metadata_envelope ctx.model ctx.limits ctx.bounds regs hm 27 (by decide)
  have hp := Nat.mul_le_mul hslot stride
  have divisor := (select_metadata_geometry ctx regs hm).2.2.1
  have hd := Nat.div_le_self (regs 512 - regs 561) (regs 26)
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e (ctx.limits.envelope_pos)
  have cap := ctx.limits.square
  change 256 * (e * e) < _ at cap
  have hwne : ctx.limits.width ≠ 0 := by have := ctx.limits.width32; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : regs 561 ≤ regs 512
  all_goals simp [ScalarChecks, selectLocalAddress, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock,
    hsub, hwne] <;> dsimp only [e] at * <;> omega

theorem selectLocalPrepare_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs)
    (h562 : regs 562 ≤ ctx.limits.envelope) (h592 : regs 592 ≤ ctx.limits.envelope)
    (h594 : regs 594 ≤ ctx.limits.envelope) (h561 : regs 561 ≤ ctx.limits.envelope)
    (h591 : regs 591 ≤ ctx.limits.envelope) :
    selectLocalPrepare.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  let e := ctx.limits.envelope
  have word := metadata_envelope ctx.model ctx.limits ctx.bounds regs hm 32 (by decide)
  have hp := Nat.mul_le_mul (show regs 562 + regs 592 ≤ 2 * e by dsimp only [e]; omega) word
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e (ctx.limits.envelope_pos)
  have cap := ctx.limits.square
  change 256 * (e * e) < _ at cap
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, selectLocalPrepare, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval]
  dsimp only [e] at *
  simp only [Nat.mul_assoc] at hp
  omega

theorem denseReadAddress_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) :
    denseReadAddress.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  have pos := (select_metadata_geometry ctx regs hm).2.2.2.1
  have hp := Nat.div_le_self (regs 640) (regs 32)
  have fv := fit.1 640
  dsimp only at fv
  have one := ctx.limits.constant_fit 1 (by decide)
  have hwne : ctx.limits.width ≠ 0 := by have := ctx.limits.width32; omega
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, denseReadAddress, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval]
  omega

theorem denseReadSave_safe (memory : Memory) (width : Nat) (s : Data) (fit : s.Fits width) :
    denseReadSave.Safe memory width s :=
  SimpleScalar.safe memory width denseReadSave ⟨True.intro, True.intro, True.intro⟩ s fit

theorem denseFirstPrepare_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hbefore : regs 648 ≤ ctx.limits.envelope)
    (hremain : regs 650 ≤ ctx.limits.envelope) :
    denseFirstPrepare.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  have cap := ctx.limits.reader_polynomial_fit
  have ep := ctx.limits.envelope_pos
  have hwne : ctx.limits.width ≠ 0 := by have := ctx.limits.width32; omega
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

theorem denseSecondAddress_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hindex : regs 644 ≤ 3 * (ctx.limits.envelope * ctx.limits.envelope))
    (hone : regs 659 = 1) :
    denseSecondAddress.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  have ep := ctx.limits.envelope_pos
  have cap := ctx.limits.square
  have esq := Nat.mul_pos ep ep
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, denseSecondAddress, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, hone]
  omega

theorem denseWordFinish_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs)
    (hindex : regs 644 ≤ 4 * (ctx.limits.envelope * ctx.limits.envelope))
    (hpacket : regs 403 ≤ ctx.limits.envelope) :
    denseWordFinish.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  let e := ctx.limits.envelope
  have ep : 0 < e := ctx.limits.envelope_pos
  have word := metadata_envelope ctx.model ctx.limits ctx.bounds regs hm 32 (by decide)
  have hp := Nat.mul_le_mul hindex word
  have esq : e ≤ e * e := Nat.le_mul_of_pos_right e ep
  have ecube : e * e ≤ e * e * e := Nat.le_mul_of_pos_right (e * e) ep
  have cap := ctx.limits.cubic
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases absent : regs 403 = 0
  all_goals simp [ScalarChecks, denseWordFinish, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, absent] <;>
    dsimp only [e] at * <;> simp only [Nat.mul_assoc] at hp cap ecube <;> omega

theorem denseRankBeforePrepare_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hindex : regs 644 = regs 640 / regs 32) :
    denseRankBeforePrepare.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  have hp : regs 644 * regs 32 ≤ regs 640 := by
    rw [hindex]
    have h := Nat.mod_add_div (regs 640) (regs 32)
    rw [Nat.mul_comm] at h
    omega
  have fp := fit.1 640
  have fw := fit.1 645
  have fl := fit.1 646
  dsimp only at fp fw fl
  have one := ctx.limits.constant_fit 1 (by decide)
  have hwne : ctx.limits.width ≠ 0 := by have := ctx.limits.width32; omega
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

theorem denseWordPrepared_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hl : regs 401 ≤ ctx.limits.rawWidth)
    (hindex : regs 644 ≤ 4 * (ctx.limits.envelope * ctx.limits.envelope)) :
    (Block.sequence [selectWordBlock ctx.reader, denseWordFinish]).Safe
      ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  have selectSafe := selectWordBlock_safe ctx ⟨regs, .running⟩ fit hm hl
  refine select_safe_follow selectSafe (fun fp => ?_)
  have running := selectWordBlock_running ctx regs hm
  have bound := selectWordBlock_output_bound ctx regs fit hm hl
  have frame (r : Nat) (hr : ¬ SelectWordWrites r) :=
    selectWordBlock_frame ctx.reader ctx.writes ctx.memory
      ⟨regs, .running⟩ r hr
  have mp := select_metadata_frame ctx ctx.memory _ _
    (selectWordBlock_writes ctx.reader ctx.writes)
    (by intro r h1 h2; simp only [SelectWordWrites]; omega) ⟨regs, .running⟩ hm
  generalize he : (selectWordBlock ctx.reader).eval ctx.memory ⟨regs, .running⟩ = selected
    at fp running bound frame mp ⊢
  rcases selected with ⟨⟨sr, status⟩, reads⟩
  dsimp only at fp running bound frame mp
  subst status
  have finish := denseWordFinish_safe ctx sr fp mp
    (by rw [frame 644 (by simp [SelectWordWrites])]; exact hindex) bound
  exact Block.safe_seq finish (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ finish))

theorem denseFirstSelected_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hl : regs 646 ≤ ctx.limits.rawWidth)
    (hbefore : regs 648 ≤ ctx.limits.envelope)
    (hremain : regs 650 ≤ ctx.limits.envelope)
    (hindex : regs 644 ≤ 4 * (ctx.limits.envelope * ctx.limits.envelope)) :
    (denseFirstSelected ctx.reader).Safe ctx.memory (ctx.limits.width)
      ⟨regs, .running⟩ := by
  have prepare := denseFirstPrepare_safe ctx regs fit hbefore hremain
  refine select_safe_follow prepare (fun fp => ?_)
  have source := denseFirstPrepare_source ctx.memory regs
  have mp := select_metadata_frame ctx ctx.memory _ _ denseFirstPrepare_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frame := Block.eval_frame ctx.memory _ _ denseFirstPrepare_writes 644
    (by omega) ⟨regs, .running⟩
  generalize he : denseFirstPrepare.eval ctx.memory ⟨regs, .running⟩ = prepared
    at source mp frame fp ⊢
  rcases prepared with ⟨⟨pr, pst⟩, reads⟩
  dsimp only at source mp frame fp
  have hs := source.1
  subst pst
  exact denseWordPrepared_safe ctx pr fp mp (by rw [source.2.2.2.1]; exact hl)
    (by rw [frame]; exact hindex)

theorem denseSecondPrepared_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hl : regs 8195 ≤ ctx.limits.rawWidth)
    (hindex : regs 644 ≤ 4 * (ctx.limits.envelope * ctx.limits.envelope)) :
    (Block.sequence [denseSecondPrepare, selectWordBlock ctx.reader, denseWordFinish]).Safe
      ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  have prepare := denseSecondPrepare_safe ctx.memory (ctx.limits.width)
    (ctx.limits.constant_fit 1 (by decide)) ⟨regs, .running⟩ fit
  refine select_safe_follow prepare (fun fp => ?_)
  have source := denseSecondPrepare_source ctx.memory regs
  have mp := select_metadata_frame ctx ctx.memory _ _ denseSecondPrepare_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frame := Block.eval_frame ctx.memory _ _ denseSecondPrepare_writes 644
    (by omega) ⟨regs, .running⟩
  generalize he : denseSecondPrepare.eval ctx.memory ⟨regs, .running⟩ = prepared
    at source mp frame fp ⊢
  rcases prepared with ⟨⟨pr, pst⟩, reads⟩
  dsimp only at source mp frame fp
  have hs := source.1
  subst pst
  exact denseWordPrepared_safe ctx pr fp mp (by rw [source.2.2.2.1]; exact hl)
    (by rw [frame]; exact hindex)

theorem denseSecondSelected_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs)
    (hindex : regs 644 ≤ 3 * (ctx.limits.envelope * ctx.limits.envelope))
    (hone : regs 659 = 1) :
    (denseSecondSelected ctx.reader).Safe ctx.memory (ctx.limits.width)
      ⟨regs, .running⟩ := by
  have address := denseSecondAddress_safe ctx regs fit hindex hone
  refine select_safe_follow address (fun fp => ?_)
  have source := denseSecondAddress_source ctx.memory regs
  have mp := select_metadata_frame ctx ctx.memory _ _ denseSecondAddress_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  generalize he : denseSecondAddress.eval ctx.memory ⟨regs, .running⟩ = addressed
    at source mp fp ⊢
  rcases addressed with ⟨⟨ar, ast⟩, reads⟩
  dsimp only at source mp fp
  have hs := source.1
  subst ast
  have loadSafe := ctx.safe ⟨ar, .running⟩ fp mp
  refine select_safe_follow loadSafe (fun fl => ?_)
  have reader := ctx.correct ar mp
  have bound := reader_output_bounds ctx ar mp
  generalize heR : ctx.reader.eval ctx.memory ⟨ar, .running⟩ = loaded
    at reader bound fl ⊢
  rcases loaded with ⟨⟨lr, lst⟩, receipts⟩
  dsimp only at reader bound fl
  have hs := reader.1
  subst lst
  have ml := readerFrame_metadata ctx.model ar lr reader.2.2.2.2 mp
  have hindex' : lr 644 ≤ 4 * (ctx.limits.envelope * ctx.limits.envelope) := by
    rw [reader.2.2.2.2 644 (Or.inl (by decide)), source.2.2.2.2, hone]
    have ep := ctx.limits.envelope_pos
    have esq := Nat.mul_pos ep ep
    omega
  have branch : (Block.ifZero 8194 .skip
      (Block.sequence [denseSecondPrepare, selectWordBlock ctx.reader, denseWordFinish])).Safe
        ctx.memory (ctx.limits.width) ⟨lr, .running⟩ := by
    apply Block.safe_ifZero fl
    split
    · exact Block.safe_skip _ _ _ fl
    · exact denseSecondPrepared_safe ctx lr fl ml (bound.2 (Or.inl source.2.2.1)) hindex'
  exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))

theorem denseRankBefore_safe_bound (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hl : regs 646 ≤ ctx.limits.rawWidth)
    (hindex : regs 644 = regs 640 / regs 32) :
    (denseRankBefore ctx.reader).Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ ∧
      ((denseRankBefore ctx.reader).eval ctx.memory ⟨regs, .running⟩).final.status = .running ∧
      ((denseRankBefore ctx.reader).eval ctx.memory ⟨regs, .running⟩).final.regs 260 ≤
        ctx.limits.envelope := by
  have prepare := denseRankBeforePrepare_safe ctx regs fit hindex
  refine select_follow_post (fun s => s.status = .running ∧ s.regs 260 ≤ ctx.limits.envelope)
    prepare (fun fp => ?_)
  have source := denseRankBeforePrepare_source ctx.memory regs
  have mp := select_metadata_frame ctx ctx.memory _ _ denseRankBeforePrepare_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  generalize he : denseRankBeforePrepare.eval ctx.memory ⟨regs, .running⟩ = prepared
    at source mp fp ⊢
  rcases prepared with ⟨⟨pr, pst⟩, reads⟩
  dsimp only at source mp fp
  have hs := source.1
  subst pst
  have length : pr 257 ≤ ctx.limits.rawWidth := by rw [source.2.2.2.1]; exact hl
  have child := rankWordBlock_safe_invariant ctx.model ctx.limits ctx.bounds ctx.memory ctx.reader
    ctx.safe ctx.correct
    ctx.writes pr fp mp length
  have bound := rankWordBlock_output_bound ctx.model ctx.limits ctx.bounds ctx.memory ctx.reader ctx.safe ctx.correct ctx.writes pr fp mp length
  have env := ctx.limits.output_bound
  exact ⟨child.1, child.2.running, by dsimp only; omega⟩

theorem denseRankWhole_safe_bound (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hl : regs 646 ≤ ctx.limits.rawWidth) :
    (denseRankWhole ctx.reader).Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ ∧
      ((denseRankWhole ctx.reader).eval ctx.memory ⟨regs, .running⟩).final.status = .running ∧
      ((denseRankWhole ctx.reader).eval ctx.memory ⟨regs, .running⟩).final.regs 260 ≤
        ctx.limits.envelope := by
  have prepare := denseRankWholePrepare_safe ctx.memory (ctx.limits.width)
    (ctx.limits.constant_fit 1 (by decide)) ⟨regs, .running⟩ fit
  refine select_follow_post (fun s => s.status = .running ∧ s.regs 260 ≤ ctx.limits.envelope)
    prepare (fun fp => ?_)
  have source := denseRankWholePrepare_source ctx.memory regs
  have mp := select_metadata_frame ctx ctx.memory _ _ denseRankWholePrepare_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  generalize he : denseRankWholePrepare.eval ctx.memory ⟨regs, .running⟩ = prepared
    at source mp fp ⊢
  rcases prepared with ⟨⟨pr, pst⟩, reads⟩
  dsimp only at source mp fp
  have hs := source.1
  subst pst
  have length : pr 257 ≤ ctx.limits.rawWidth := by rw [source.2.2.2.2.1]; exact hl
  have child := rankWordBlock_safe_invariant ctx.model ctx.limits ctx.bounds ctx.memory ctx.reader
    ctx.safe ctx.correct
    ctx.writes pr fp mp length
  have bound := rankWordBlock_output_bound ctx.model ctx.limits ctx.bounds ctx.memory ctx.reader ctx.safe ctx.correct ctx.writes pr fp mp length
  have env := ctx.limits.output_bound
  exact ⟨child.1, child.2.running, by dsimp only; omega⟩

theorem densePresent_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hl : regs 646 ≤ ctx.limits.rawWidth)
    (hdivision : regs 644 = regs 640 / regs 32)
    (hindex : regs 644 ≤ 3 * (ctx.limits.envelope * ctx.limits.envelope))
    (hocc : regs 642 ≤ ctx.limits.envelope) (hone : regs 659 = 1) :
    (densePresent ctx.reader).Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  have before := denseRankBefore_safe_bound ctx regs fit hm hl hdivision
  refine select_safe_follow before.1 (fun fa => ?_)
  have metaA := select_metadata_frame ctx ctx.memory _ _
    (denseRankBefore_writes ctx.reader ctx.writes)
    (by intro r h1 h2; simp only [DenseRankBeforeWrites]; omega) ⟨regs, .running⟩ hm
  have frameA (r : Nat) (ho : ¬ DenseRankBeforeWrites r) :=
    Block.eval_frame ctx.memory _ _
      (denseRankBefore_writes ctx.reader ctx.writes) r ho ⟨regs, .running⟩
  generalize heA : (denseRankBefore ctx.reader).eval ctx.memory ⟨regs, .running⟩ = beforeData
    at before metaA frameA fa ⊢
  rcases beforeData with ⟨⟨ar, ast⟩, readsA⟩
  dsimp only at before metaA frameA fa
  have hs := before.2.1
  subst ast
  have whole := denseRankWhole_safe_bound ctx ar fa metaA
    (by rw [frameA 646 (by simp [DenseRankBeforeWrites])]; exact hl)
  refine select_safe_follow whole.1 (fun fb => ?_)
  have metaB := select_metadata_frame ctx ctx.memory _ _
    (denseRankWhole_writes ctx.reader ctx.writes)
    (by intro r h1 h2; simp only [DenseRankWholeWrites]; omega) ⟨ar, .running⟩ metaA
  have frameB (r : Nat) (ho : ¬ DenseRankWholeWrites r) :=
    Block.eval_frame ctx.memory _ _
      (denseRankWhole_writes ctx.reader ctx.writes) r ho ⟨ar, .running⟩
  have saved := denseRankWhole_saved ctx.memory ctx.reader ctx.writes ar
  generalize heB : (denseRankWhole ctx.reader).eval ctx.memory ⟨ar, .running⟩ = wholeData
    at whole metaB frameB saved fb ⊢
  rcases wholeData with ⟨⟨br, bst⟩, readsB⟩
  dsimp only at whole metaB frameB saved fb
  have hs := whole.2.1
  subst bst
  have choose := denseChoosePrepare_safe ctx.memory (ctx.limits.width)
    (ctx.limits.constant_fit 1 (by decide)) ⟨br, .running⟩ fb
  refine select_safe_follow choose (fun fc => ?_)
  have sourceC := denseChoosePrepare_source ctx.memory br
  have metaC := select_metadata_frame ctx ctx.memory _ _ denseChoosePrepare_writes
    (by intro r h1 h2; omega) ⟨br, .running⟩ metaB
  have frameC (r : Nat) (ho : ¬ ((649 ≤ r ∧ r < 653) ∨ r = 658)) :=
    Block.eval_frame ctx.memory _ _ denseChoosePrepare_writes r ho ⟨br, .running⟩
  generalize heC : denseChoosePrepare.eval ctx.memory ⟨br, .running⟩ = chosen
    at sourceC metaC frameC fc ⊢
  rcases chosen with ⟨⟨cr, cst⟩, readsC⟩
  dsimp only at sourceC metaC frameC fc
  have hs := sourceC.1
  subst cst
  have kept (r : Nat) (hr : r = 32 ∨ r = 640 ∨ r = 641 ∨ r = 642 ∨ r = 644 ∨ r = 646 ∨ r = 659) :
      cr r = regs r := by
    rw [frameC r (by omega), frameB r (by simp only [DenseRankWholeWrites]; omega),
      frameA r (by simp only [DenseRankBeforeWrites]; omega)]
  have chunkLen : cr 646 ≤ ctx.limits.rawWidth := by rw [kept 646 (by omega)]; exact hl
  have indexBound : cr 644 ≤ 3 * (ctx.limits.envelope * ctx.limits.envelope) := by
    rw [kept 644 (by omega)]; exact hindex
  have one : cr 659 = 1 := (kept 659 (by omega)).trans hone
  have countBound : cr 648 ≤ ctx.limits.envelope := by
    rw [frameC 648 (by omega), saved]
    exact before.2.2
  have remainBound : cr 650 ≤ ctx.limits.envelope := by
    rw [sourceC.2.2.2.1, frameB 642 (by simp [DenseRankWholeWrites]),
      frameA 642 (by simp [DenseRankBeforeWrites])]
    omega
  have branch : (denseSelectBranch ctx.reader).Safe ctx.memory (ctx.limits.width)
      ⟨cr, .running⟩ := by
    apply Block.safe_ifZero fc
    split
    · exact denseSecondSelected_safe ctx cr fc metaC indexBound one
    · exact denseFirstSelected_safe ctx cr fc metaC chunkLen countBound remainBound (by omega)
  exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))

theorem denseSelectBlock_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs)
    (hbase : regs 640 ≤ 3 * (ctx.limits.envelope * ctx.limits.envelope))
    (hocc : regs 642 ≤ ctx.limits.envelope) :
    (denseSelectBlock ctx.reader).Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  have address := denseReadAddress_safe ctx regs fit hm
  refine select_safe_follow address (fun fa => ?_)
  have sourceA := denseReadAddress_source ctx.memory regs
  have metaA := select_metadata_frame ctx ctx.memory _ _ denseReadAddress_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frameA (r : Nat) (ho : r ≠ 643 ∧ r ≠ 644 ∧ r ≠ 659 ∧ r ≠ 8192 ∧ r ≠ 8193) :=
    Block.eval_frame ctx.memory _ _ denseReadAddress_writes r (by omega) ⟨regs, .running⟩
  generalize heA : denseReadAddress.eval ctx.memory ⟨regs, .running⟩ = addressed
    at sourceA metaA frameA fa ⊢
  rcases addressed with ⟨⟨ar, ast⟩, readsA⟩
  dsimp only at sourceA metaA frameA fa
  have hs := sourceA.1
  subst ast
  have loadSafe := ctx.safe ⟨ar, .running⟩ fa metaA
  refine select_safe_follow loadSafe (fun fb => ?_)
  have reader := ctx.correct ar metaA
  have bounds := reader_output_bounds ctx ar metaA
  generalize heB : ctx.reader.eval ctx.memory ⟨ar, .running⟩ = loaded
    at reader bounds fb ⊢
  rcases loaded with ⟨⟨br, bst⟩, readsB⟩
  dsimp only at reader bounds fb
  have hs := reader.1
  subst bst
  have metaB := readerFrame_metadata ctx.model ar br reader.2.2.2.2 metaA
  have saveSafe := denseReadSave_safe ctx.memory (ctx.limits.width) ⟨br, .running⟩ fb
  refine select_safe_follow saveSafe (fun fc => ?_)
  have sourceC := denseReadSave_source ctx.memory br
  have metaC := select_metadata_frame ctx ctx.memory _ _ denseReadSave_writes
    (by intro r h1 h2; omega) ⟨br, .running⟩ metaB
  have frameC (r : Nat) (ho : r ≠ 645 ∧ r ≠ 646) :=
    Block.eval_frame ctx.memory _ _ denseReadSave_writes r (by omega) ⟨br, .running⟩
  generalize heC : denseReadSave.eval ctx.memory ⟨br, .running⟩ = saved
    at sourceC metaC frameC fc ⊢
  rcases saved with ⟨⟨cr, cst⟩, readsC⟩
  dsimp only at sourceC metaC frameC fc
  have hs := sourceC.1
  subst cst
  have kept (r : Nat) (hr : r = 32 ∨ r = 640 ∨ r = 642) : cr r = regs r := by
    rw [frameC r (by omega), reader.2.2.2.2 r (Or.inl (by omega)), frameA r (by omega)]
  have indexEq : cr 644 = regs 640 / regs 32 := by
    rw [frameC 644 (by omega), reader.2.2.2.2 644 (Or.inl (by decide)), sourceA.2.2.2.2.1]
  have lenBound : cr 646 ≤ ctx.limits.rawWidth := by
    rw [sourceC.2.2.2]
    exact bounds.2 (Or.inl sourceA.2.2.2.2.2.1)
  have one : cr 659 = 1 := by
    rw [frameC 659 (by omega), reader.2.2.2.2 659 (Or.inl (by decide)), sourceA.2.2.2.1]
  have child := densePresent_safe ctx cr fc metaC lenBound
    (by rw [indexEq, kept 640 (by omega), kept 32 (by omega)])
    (by rw [indexEq]; have hd := Nat.div_le_self (regs 640) (regs 32); omega)
    (by rw [kept 642 (by omega)]; exact hocc) one
  have branch : (Block.ifZero 645 .skip (densePresent ctx.reader)).Safe
      ctx.memory (ctx.limits.width) ⟨cr, .running⟩ := by
    apply Block.safe_ifZero fc
    split
    · exact Block.safe_skip _ _ _ fc
    · exact child
  exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))

private theorem select_read_finish_safe (ctx : Context) (finish : Block) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs)
    (finishSafe : ∀ out, (⟨out, .running⟩ : Data).Fits (ctx.limits.width) →
      MetadataMatches ctx.model out → ReaderFrame regs out →
      out 8194 ≤ ctx.limits.packetBound →
      finish.Safe ctx.memory (ctx.limits.width) ⟨out, .running⟩) :
    (Block.sequence [ctx.reader, finish]).Safe ctx.memory (ctx.limits.width)
      ⟨regs, .running⟩ := by
  have loadSafe := ctx.safe ⟨regs, .running⟩ fit hm
  refine select_safe_follow loadSafe (fun fp => ?_)
  have source := ctx.correct regs hm
  have bounds := reader_output_bounds ctx regs hm
  generalize he : ctx.reader.eval ctx.memory ⟨regs, .running⟩ = loaded
    at source bounds fp ⊢
  rcases loaded with ⟨⟨lr, status⟩, reads⟩
  dsimp only at source bounds fp
  have hs := source.1
  subst status
  have tail := finishSafe lr fp (readerFrame_metadata ctx.model regs lr source.2.2.2.2 hm) source.2.2.2.2 bounds.1
  exact Block.safe_seq tail (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ tail))

theorem selectLongTail_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hrank : regs 360 ≤ ctx.limits.envelope)
    (hocc : regs 512 ≤ ctx.limits.envelope)
    (hword : regs 562 ≤ ctx.limits.envelope) (hoffset : regs 564 ≤ ctx.limits.envelope) :
    (Block.sequence [selectLongAddress, ctx.reader, selectLongFinish]).Safe
      ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  have address := selectLongAddress_safe ctx regs fit hm hrank hocc
  refine select_safe_follow address (fun fp => ?_)
  have source := selectLongAddress_source ctx.memory regs
  have mp := select_metadata_frame ctx ctx.memory _ _ selectLongAddress_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frame (r : Nat) (hr : r = 562 ∨ r = 564) :=
    Block.eval_frame ctx.memory _ _ selectLongAddress_writes r (by omega) ⟨regs, .running⟩
  generalize he : selectLongAddress.eval ctx.memory ⟨regs, .running⟩ = addressed
    at source mp frame fp ⊢
  rcases addressed with ⟨⟨ar, status⟩, reads⟩
  dsimp only at source mp frame fp
  have hs := source.1
  subst status
  apply select_read_finish_safe ctx selectLongFinish ar fp mp
  intro out fo mo readerFrame reply
  exact selectLongFinish_safe ctx out fo mo
    (by rw [readerFrame 562 (Or.inl (by decide)), frame 562 (by omega)]; exact hword)
    (by rw [readerFrame 564 (Or.inl (by decide)), frame 564 (by omega)]; exact hoffset)
    (Nat.le_trans reply (ctx.limits.packet_le_envelope))

theorem selectSparseTail_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hrank : regs 360 ≤ ctx.limits.envelope)
    (hocc : regs 512 ≤ ctx.limits.envelope)
    (hbase : regs 520 ≤ 3 * (ctx.limits.envelope * ctx.limits.envelope)) :
    (Block.sequence [selectSparseAddress, ctx.reader, selectSparseFinish]).Safe
      ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  have address := selectSparseAddress_safe ctx regs fit hm hrank hocc
  refine select_safe_follow address (fun fp => ?_)
  have source := selectSparseAddress_source ctx.memory regs
  have mp := select_metadata_frame ctx ctx.memory _ _ selectSparseAddress_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frame := Block.eval_frame ctx.memory _ _ selectSparseAddress_writes 520
    (by omega) ⟨regs, .running⟩
  generalize he : selectSparseAddress.eval ctx.memory ⟨regs, .running⟩ = addressed
    at source mp frame fp ⊢
  rcases addressed with ⟨⟨ar, status⟩, reads⟩
  dsimp only at source mp frame fp
  have hs := source.1
  subst status
  apply select_read_finish_safe ctx selectSparseFinish ar fp mp
  intro out fo mo readerFrame reply
  exact selectSparseFinish_safe ctx out fo
    (by rw [readerFrame 520 (Or.inl (by decide)), frame]; exact hbase)
    (Nat.le_trans reply (ctx.limits.packet_le_envelope))

private theorem select_rank_call_safe (ctx : Context)
    (call tail program : Block) (input : Nat)
    (programEq : program = .seq (.action (.move 352 input)) (.seq call tail))
    (called : ∀ regs, (⟨regs, .running⟩ : Data).Fits (ctx.limits.width) →
      MetadataMatches ctx.model regs →
      call.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ ∧
      (call.eval ctx.memory ⟨regs, .running⟩).final.status = .running ∧
      (call.eval ctx.memory ⟨regs, .running⟩).final.regs 360 ≤ ctx.limits.envelope ∧
      (∀ r, ¬ RankWrapperWrites r →
        (call.eval ctx.memory ⟨regs, .running⟩).final.regs r = regs r))
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs)
    (finish : ∀ out, (⟨out, .running⟩ : Data).Fits (ctx.limits.width) →
      MetadataMatches ctx.model out → out 360 ≤ ctx.limits.envelope →
      (∀ r, ¬ RankWrapperWrites r → r ≠ 352 → out r = regs r) →
      tail.Safe ctx.memory (ctx.limits.width) ⟨out, .running⟩) :
    program.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  subst program
  have move := Block.safe_action ctx.memory (ctx.limits.width) (.move 352 input)
    ⟨regs, .running⟩ fit (fit.1 input)
  refine select_safe_follow move (fun fp => ?_)
  let prepared := regs.write 352 (regs input)
  have mp := MetadataMatches.write ctx.model regs hm 352 (regs input) (Or.inr (by decide))
  have callProof := called prepared fp mp
  refine select_safe_follow callProof.1 (fun fc => ?_)
  change (call.eval ctx.memory ⟨prepared, .running⟩).final.Fits (ctx.limits.width) at fc
  change tail.Safe ctx.memory (ctx.limits.width)
    (call.eval ctx.memory ⟨prepared, .running⟩).final
  generalize he : call.eval ctx.memory ⟨prepared, .running⟩ = result at callProof fc ⊢
  rcases result with ⟨⟨out, status⟩, reads⟩
  dsimp only at callProof fc
  have hs := callProof.2.1
  subst status
  have mo : MetadataMatches ctx.model out := by
    intro i hi
    rw [callProof.2.2.2 i (by simp only [RankWrapperWrites]; omega)]
    exact mp i hi
  exact finish out fc mo callProof.2.2.1 (by
    intro r hr hne
    rw [callProof.2.2.2 r hr]
    simp [prepared, Registers.write, hne])

theorem selectLongBlock_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hocc : regs 512 ≤ ctx.limits.envelope)
    (hword : regs 562 ≤ ctx.limits.envelope) (hoffset : regs 564 ≤ ctx.limits.envelope) :
    (selectLongBlock ctx.reader).Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  apply select_rank_call_safe ctx (rankLongBlock ctx.reader)
    (Block.sequence [selectLongAddress, ctx.reader, selectLongFinish])
    (selectLongBlock ctx.reader) 514 rfl
    (fun rs fs ms => ⟨(rankLongBlock_safe_bound ctx.model ctx.limits ctx.bounds ctx.memory ctx.reader ctx.safe ctx.correct ctx.writes rs fs ms).1,
      (rankLongBlock_source ctx.model ctx.memory ctx.reader
        ctx.correct ctx.writes rs ms).1,
      (rankLongBlock_safe_bound ctx.model ctx.limits ctx.bounds ctx.memory ctx.reader ctx.safe ctx.correct ctx.writes rs fs ms).2,
      rankLongBlock_frame ctx.reader ctx.writes ctx.memory ⟨rs, .running⟩⟩)
    regs fit hm
  intro out fo mo bound frame
  exact selectLongTail_safe ctx out fo mo bound
    (by rw [frame 512 (by simp [RankWrapperWrites]) (by decide)]; exact hocc)
    (by rw [frame 562 (by simp [RankWrapperWrites]) (by decide)]; exact hword)
    (by rw [frame 564 (by simp [RankWrapperWrites]) (by decide)]; exact hoffset)

theorem selectSparseBlock_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hocc : regs 512 ≤ ctx.limits.envelope)
    (hbase : regs 520 ≤ 3 * (ctx.limits.envelope * ctx.limits.envelope)) :
    (selectSparseBlock ctx.reader).Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  apply select_rank_call_safe ctx (rankSparseBlock ctx.reader)
    (Block.sequence [selectSparseAddress, ctx.reader, selectSparseFinish])
    (selectSparseBlock ctx.reader) 515 rfl
    (fun rs fs ms => ⟨(rankSparseBlock_safe_bound ctx.model ctx.limits ctx.bounds ctx.memory ctx.reader ctx.safe ctx.correct ctx.writes rs fs ms).1,
      (rankSparseBlock_source ctx.model ctx.memory ctx.reader
        ctx.correct ctx.writes rs ms).1,
      (rankSparseBlock_safe_bound ctx.model ctx.limits ctx.bounds ctx.memory ctx.reader ctx.safe ctx.correct ctx.writes rs fs ms).2,
      rankSparseBlock_frame ctx.reader ctx.writes ctx.memory ⟨rs, .running⟩⟩)
    regs fit hm
  intro out fo mo bound frame
  exact selectSparseTail_safe ctx out fo mo bound
    (by rw [frame 512 (by simp [RankWrapperWrites]) (by decide)]; exact hocc)
    (by rw [frame 520 (by simp [RankWrapperWrites]) (by decide)]; exact hbase)

theorem selectLocalDense_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hocc : regs 512 ≤ ctx.limits.envelope)
    (hbase : regs 520 ≤ 3 * (ctx.limits.envelope * ctx.limits.envelope)) :
    (selectLocalDense ctx.reader).Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  have a := Block.safe_action ctx.memory (ctx.limits.width) (.move 640 520)
    ⟨regs, .running⟩ fit (fit.1 520)
  have fa := Block.eval_fits _ _ _ _ a
  have b := Block.safe_action ctx.memory (ctx.limits.width) (.move 641 521) _ fa (fa.1 521)
  have fb := Block.eval_fits _ _ _ _ b
  have c := Block.safe_action ctx.memory (ctx.limits.width) (.move 642 512) _ fb (fb.1 512)
  have fc := Block.eval_fits _ _ _ _ c
  let prepared := ((regs.write 640 (regs 520)).write 641 (regs 521)).write 642 (regs 512)
  have mp : MetadataMatches ctx.model prepared :=
    MetadataMatches.write ctx.model _ (MetadataMatches.write ctx.model _
      (MetadataMatches.write ctx.model regs hm 640 (regs 520) (Or.inr (by decide)))
      641 (regs 521) (Or.inr (by decide))) 642 (regs 512) (Or.inr (by decide))
  have dense := denseSelectBlock_safe ctx prepared fc mp
    (by simpa [prepared, Registers.write] using hbase)
    (by simpa [prepared, Registers.write] using hocc)
  have tail := SimpleScalar.safe ctx.memory (ctx.limits.width)
    (Block.sequence [.action (.move 513 643)]) ⟨True.intro, True.intro⟩ _
    (Block.eval_fits _ _ _ _ dense)
  exact Block.safe_seq a (Block.safe_seq b (Block.safe_seq c (Block.safe_seq dense tail)))

theorem selectLocalPresent_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hocc : regs 512 ≤ ctx.limits.envelope)
    (h561 : regs 561 ≤ ctx.limits.envelope) (h562 : regs 562 ≤ ctx.limits.envelope)
    (h591 : regs 591 ≤ ctx.limits.envelope) (h592 : regs 592 ≤ ctx.limits.envelope)
    (h594 : regs 594 ≤ ctx.limits.envelope) :
    (selectLocalPresent ctx.reader).Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  have prepare := selectLocalPrepare_safe ctx regs fit hm h562 h592 h594 h561 h591
  refine select_safe_follow prepare (fun fp => ?_)
  have source := selectLocalPrepare_source ctx.memory regs
  have mp := select_metadata_frame ctx ctx.memory _ _ selectLocalPrepare_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frame := Block.eval_frame ctx.memory _ _ selectLocalPrepare_writes 512
    (by omega) ⟨regs, .running⟩
  generalize he : selectLocalPrepare.eval ctx.memory ⟨regs, .running⟩ = prepared
    at source mp frame fp ⊢
  rcases prepared with ⟨⟨pr, pst⟩, reads⟩
  dsimp only at source mp frame fp
  have hs := source.1
  subst pst
  have occ : pr 512 ≤ ctx.limits.envelope := by rw [frame]; exact hocc
  have base : pr 520 ≤ 3 * (ctx.limits.envelope * ctx.limits.envelope) := by
    rw [source.2.2.1]
    have word := metadata_envelope ctx.model ctx.limits ctx.bounds regs hm 32 (by decide)
    have hp := Nat.mul_le_mul
      (show regs 562 + regs 592 ≤ 2 * ctx.limits.envelope by omega) word
    have ep := ctx.limits.envelope_pos
    have esq := Nat.le_mul_of_pos_right (ctx.limits.envelope) ep
    simp only [Nat.mul_assoc] at hp
    omega
  have branch : (Block.ifZero 593 (selectLocalDense ctx.reader)
      (selectSparseBlock ctx.reader)).Safe ctx.memory (ctx.limits.width)
        ⟨pr, .running⟩ := by
    apply Block.safe_ifZero fp
    split
    · exact selectLocalDense_safe ctx pr fp mp occ base
    · exact selectSparseBlock_safe ctx pr fp mp occ base
  exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))

theorem selectLocalBlock_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hocc : regs 512 ≤ ctx.limits.envelope)
    (hslot : regs 514 ≤ ctx.limits.envelope)
    (h561 : regs 561 ≤ ctx.limits.envelope) (h562 : regs 562 ≤ ctx.limits.envelope) :
    (selectLocalBlock ctx.reader).Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  have address := selectLocalAddress_safe ctx regs fit hm hslot hocc
  refine select_safe_follow address (fun fa => ?_)
  have sourceA := selectLocalAddress_source ctx.memory regs
  have metaA := select_metadata_frame ctx ctx.memory _ _ selectLocalAddress_writes
    (by intro r h1 h2; omega) ⟨regs, .running⟩ hm
  have frameA (r : Nat) (hr : r = 512 ∨ r = 561 ∨ r = 562) :=
    Block.eval_frame ctx.memory _ _ selectLocalAddress_writes r (by omega) ⟨regs, .running⟩
  generalize heA : selectLocalAddress.eval ctx.memory ⟨regs, .running⟩ = addressed
    at sourceA metaA frameA fa ⊢
  rcases addressed with ⟨⟨ar, ast⟩, readsA⟩
  dsimp only at sourceA metaA frameA fa
  have hs := sourceA.1
  subst ast
  have entries := selectEntryBlock_safe ctx ctx.memory ctx.reader
    ctx.safe ctx.writes 5 515 590 (by decide)
    (by have := ctx.limits.constant_fit 9 (by decide); omega) ⟨ar, .running⟩ fa metaA
  refine select_safe_follow entries (fun fb => ?_)
  have sourceB := selectEntryLocal_expectedType ctx.model ctx.memory ctx.reader
    ctx.correct ctx.writes ar metaA
  have bounds := selectEntryBlock_present_bounds ctx ctx.memory ctx.reader
    ctx.correct ctx.writes 5 515 590
    (by decide) (by decide) (by decide) (Or.inl (by decide)) ar metaA
  have metaB := selectEntryBlock_metadata ctx.model ctx.reader ctx.writes
    5 515 590 (by decide) ctx.memory ⟨ar, .running⟩ metaA
  have frameB (r : Nat) (hr : r = 512 ∨ r = 561 ∨ r = 562) :=
    selectEntryBlock_frame ctx.reader ctx.writes 5 515 590
      ctx.memory ⟨ar, .running⟩ r (by simp only [SelectEntryWrites]; omega)
  generalize heB : (selectEntryBlock ctx.reader 5 515 590).eval ctx.memory ⟨ar, .running⟩ = fetched
    at sourceB bounds metaB frameB fb ⊢
  rcases fetched with ⟨⟨br, bst⟩, readsB⟩
  dsimp only at sourceB bounds metaB frameB fb
  have hs := sourceB.1
  subst bst
  have branch : (Block.ifZero 590 .skip (selectLocalPresent ctx.reader)).Safe
      ctx.memory (ctx.limits.width) ⟨br, .running⟩ := by
    apply Block.safe_ifZero fb
    split
    · exact Block.safe_skip _ _ _ fb
    · rename_i present
      have hb := bounds present
      simp only [Nat.reduceAdd] at hb
      have eq := ctx.limits.packet_le_envelope
      exact selectLocalPresent_safe ctx br fb metaB
        (by rw [frameB 512 (by omega), frameA 512 (by omega)]; exact hocc)
        (by rw [frameB 561 (by omega), frameA 561 (by omega)]; exact h561)
        (by rw [frameB 562 (by omega), frameA 562 (by omega)]; exact h562)
        (by omega) (by omega) (by omega)
  exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))

theorem selectSuperPresent_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hocc : regs 512 ≤ ctx.limits.envelope)
    (hslot : regs 514 ≤ ctx.limits.envelope)
    (h561 : regs 561 ≤ ctx.limits.envelope) (h562 : regs 562 ≤ ctx.limits.envelope)
    (h564 : regs 564 ≤ ctx.limits.envelope) :
    (selectSuperPresent ctx.reader).Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  apply Block.safe_ifZero fit
  split
  · exact selectLocalBlock_safe ctx regs fit hm hocc hslot h561 h562
  · exact selectLongBlock_safe ctx regs fit hm hocc h562 h564

private theorem selectEligible_safe_aux (ctx : Context) (entry tail program : Block)
    (programEq : program = .seq (.action (.arithmetic .div 514 512 25))
      (.seq entry (.seq (.ifZero 560 .skip tail) .skip)))
    (entrySpec : ∀ regs, (⟨regs, .running⟩ : Data).Fits (ctx.limits.width) →
      MetadataMatches ctx.model regs →
      entry.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ ∧
      (entry.eval ctx.memory ⟨regs, .running⟩).final.status = .running ∧
      MetadataMatches ctx.model (entry.eval ctx.memory ⟨regs, .running⟩).final.regs ∧
      (∀ r, r = 512 ∨ r = 514 → (entry.eval ctx.memory ⟨regs, .running⟩).final.regs r = regs r) ∧
      ((entry.eval ctx.memory ⟨regs, .running⟩).final.regs 560 ≠ 0 →
        (entry.eval ctx.memory ⟨regs, .running⟩).final.regs 561 ≤ ctx.limits.packetBound ∧
        (entry.eval ctx.memory ⟨regs, .running⟩).final.regs 562 ≤ ctx.limits.packetBound ∧
        (entry.eval ctx.memory ⟨regs, .running⟩).final.regs 563 ≤ ctx.limits.packetBound ∧
        (entry.eval ctx.memory ⟨regs, .running⟩).final.regs 564 ≤ ctx.limits.packetBound))
    (tailSafe : ∀ regs, (⟨regs, .running⟩ : Data).Fits (ctx.limits.width) →
      MetadataMatches ctx.model regs → regs 512 ≤ ctx.limits.envelope →
      regs 514 ≤ ctx.limits.envelope → regs 561 ≤ ctx.limits.envelope →
      regs 562 ≤ ctx.limits.envelope → regs 564 ≤ ctx.limits.envelope →
      tail.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hocc : regs 512 ≤ ctx.limits.envelope) :
    program.Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ := by
  subst program
  have divisor := (select_metadata_geometry ctx regs hm).2.1
  have hp := Nat.div_le_self (regs 512) (regs 25)
  have occFit : regs 512 < 2 ^ ctx.limits.width := fit.1 512
  have divide := Block.safe_action ctx.memory (ctx.limits.width)
    (.arithmetic .div 514 512 25) ⟨regs, .running⟩ fit
    (by simp [Action.LocalSafe, Arithmetic.eval]; omega)
  refine select_safe_follow divide (fun fp => ?_)
  let prepared := regs.write 514 (regs 512 / regs 25)
  have mp : MetadataMatches ctx.model prepared := MetadataMatches.write ctx.model regs hm 514 _ (Or.inr (by decide))
  have entries := entrySpec prepared fp mp
  refine select_safe_follow entries.1 (fun fe => ?_)
  change (entry.eval ctx.memory ⟨prepared, .running⟩).final.Fits (ctx.limits.width) at fe
  change (Block.seq (.ifZero 560 .skip tail) .skip).Safe ctx.memory (ctx.limits.width)
    (entry.eval ctx.memory ⟨prepared, .running⟩).final
  generalize he : entry.eval ctx.memory ⟨prepared, .running⟩ = fetched at entries fe ⊢
  rcases fetched with ⟨⟨er, est⟩, reads⟩
  dsimp only at entries fe
  have hs := entries.2.1
  subst est
  have branch : (Block.ifZero 560 .skip tail).Safe
      ctx.memory (ctx.limits.width) ⟨er, .running⟩ := by
    apply Block.safe_ifZero fe
    split
    · exact Block.safe_skip _ _ _ fe
    · rename_i present
      have hb := entries.2.2.2.2 present
      have eq := ctx.limits.packet_le_envelope
      exact tailSafe er fe entries.2.2.1
        (by rw [entries.2.2.2.1 512 (by omega)]; simpa [prepared, Registers.write] using hocc)
        (by rw [entries.2.2.2.1 514 (by omega)]; simp [prepared]; omega)
        (by omega) (by omega) (by omega)
  exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))

private theorem selectSuperEntry_safe_spec (ctx : Context) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe ctx.model ctx.limits.width memory reader) (readerCorrect : ReaderSimulation ctx.model memory reader)
    (readerWrites : ReaderWrites reader) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width)) (hm : MetadataMatches ctx.model regs) :
    let entry := selectEntryBlock reader 1 514 560
    let actual := entry.eval memory ⟨regs, .running⟩
    entry.Safe memory (ctx.limits.width) ⟨regs, .running⟩ ∧
    actual.final.status = .running ∧ MetadataMatches ctx.model actual.final.regs ∧
    (∀ r, r = 512 ∨ r = 514 → actual.final.regs r = regs r) ∧
    (actual.final.regs 560 ≠ 0 → actual.final.regs 561 ≤ ctx.limits.packetBound ∧
      actual.final.regs 562 ≤ ctx.limits.packetBound ∧
      actual.final.regs 563 ≤ ctx.limits.packetBound ∧
      actual.final.regs 564 ≤ ctx.limits.packetBound) := by
  have safe := selectEntryBlock_safe ctx memory reader
    readerSafe readerWrites 1 514 560 (by decide)
    (by have := ctx.limits.constant_fit 5 (by decide); omega) ⟨regs, .running⟩ fit hm
  have source := selectEntrySuper_expectedType ctx.model memory reader
    readerCorrect readerWrites regs hm
  have metadata := selectEntryBlock_metadata ctx.model reader readerWrites
    1 514 560 (by decide) memory ⟨regs, .running⟩ hm
  have frame (r : Nat) (hr : r = 512 ∨ r = 514) :=
    selectEntryBlock_frame reader readerWrites 1 514 560
      memory ⟨regs, .running⟩ r (by simp only [SelectEntryWrites]; omega)
  have bounds := selectEntryBlock_present_bounds ctx memory reader
    readerCorrect readerWrites 1 514 560
    (by decide) (by decide) (by decide) (Or.inl (by decide)) regs hm
  exact ⟨safe, source.1, metadata, frame, bounds⟩

theorem selectEligible_safe (ctx : Context) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (ctx.limits.width))
    (hm : MetadataMatches ctx.model regs) (hocc : regs 512 ≤ ctx.limits.envelope) :
    (selectEligible ctx.reader).Safe ctx.memory (ctx.limits.width) ⟨regs, .running⟩ :=
  selectEligible_safe_aux ctx (selectEntryBlock ctx.reader 1 514 560)
    (selectSuperPresent ctx.reader) (selectEligible ctx.reader) rfl
    (selectSuperEntry_safe_spec ctx ctx.memory ctx.reader
      ctx.safe ctx.correct ctx.writes)
    (selectSuperPresent_safe ctx) regs fit hm hocc

theorem selectCloseBlock_safe (ctx : Context) (s : Data)
    (fit : s.Fits (ctx.limits.width)) (hm : MetadataMatches ctx.model s.regs) :
    (selectCloseBlock ctx.reader).Safe ctx.memory (ctx.limits.width) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs
      subst status
      have zero := Block.safe_action ctx.memory (ctx.limits.width) (.constant 513 0)
        ⟨regs, .running⟩ fit (Nat.two_pow_pos _)
      refine select_safe_follow zero (fun fp => ?_)
      let prepared := regs.write 513 0
      have mp := MetadataMatches.write ctx.model regs hm 513 0 (Or.inr (by decide))
      have compare := Block.safe_action ctx.memory (ctx.limits.width)
        (.comparison .lt 550 512 16) ⟨prepared, .running⟩ fp
        (by dsimp only [Action.LocalSafe, Comparison.eval]; split <;>
          exact ctx.limits.constant_fit _ (by decide))
      refine select_safe_follow compare (fun ft => ?_)
      have mt := MetadataMatches.write ctx.model prepared mp 550
        (Comparison.lt.eval (prepared 512) (prepared 16)) (Or.inr (by decide))
      have sizeBound := metadata_envelope ctx.model ctx.limits ctx.bounds regs hm 16 (by decide)
      have ft' : (⟨prepared.write 550 (Comparison.lt.eval (prepared 512) (prepared 16)), .running⟩ : Data).Fits
          (ctx.limits.width) := ft
      have branch : (Block.ifZero 550 .skip (selectEligible ctx.reader)).Safe
          ctx.memory (ctx.limits.width)
          ⟨prepared.write 550 (Comparison.lt.eval (prepared 512) (prepared 16)), .running⟩ := by
        apply Block.safe_ifZero ft'
        by_cases active : regs 512 < regs 16
        · have child := selectEligible_safe ctx
            (prepared.write 550 (Comparison.lt.eval (prepared 512) (prepared 16))) ft' mt
            (by simp [prepared, Registers.write]; omega)
          simpa [prepared, Registers.write, Comparison.eval, active] using child
        · simpa [prepared, Registers.write, Comparison.eval, active] using
            Block.safe_skip ctx.memory (ctx.limits.width) _ ft'
      exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))
  · exact Block.safe_stopped _ _ _ s fit hs



end SelectSafety

/-- Every primitive in the actual shared select controller is safe on entry
registers matching the supplied numerical model. Its own guard handles invalid
occurrences, so no additional request bound is necessary. -/
theorem selectCloseBlock_safe (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader)
    (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
    (s : Data) (fit : s.Fits limits.width) (hm : MetadataMatches model s.regs) :
    (selectCloseBlock reader).Safe memory limits.width s :=
  SelectSafety.selectCloseBlock_safe
    ⟨model, limits, bounds, memory, reader, readerSafe, readerCorrect, readerWrites⟩ s fit hm

theorem selectCloseBlock_output_bound (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader)
    (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits limits.width)
    (hm : MetadataMatches model regs) :
    ((selectCloseBlock reader).eval memory ⟨regs, .running⟩).final.regs 513 < 2 ^ limits.width :=
  ((selectCloseBlock reader).eval_fits memory limits.width _
    (selectCloseBlock_safe model limits bounds memory reader readerSafe readerCorrect readerWrites
      ⟨regs, .running⟩ fit hm)).1 513

/-- The existing compiler safety predicate, named for its select consumer. -/
abbrev SelectExecutionSafety := RankExecutionSafety

theorem selectCloseBlock_execution_safe (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (readerSafe : ReaderSafe model limits.width memory reader)
    (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
    (readerFields : reader.FieldsFit limits.width)
    (budget : 3667 + 82 * reader.size < 2 ^ limits.width)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits limits.width)
    (hm : MetadataMatches model regs) :
    SelectExecutionSafety memory limits.width ((selectCloseBlock reader).compileAt 0 ++ [.halt 513])
      (3667 + 82 * reader.size) ⟨regs, 0, .running⟩ := by
  have cap := limits.constant_fit 8280 (by decide)
  exact rank_compiled_safety memory limits.width (selectCloseBlock reader) 513 _ regs
    (by rw [selectCloseBlock_size]; omega) budget
    (selectCloseBlock_fieldsFit _ _ readerFields cap)
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega) fit
    (selectCloseBlock_safe model limits bounds memory reader readerSafe readerCorrect readerWrites
      ⟨regs, .running⟩ fit hm)

theorem physicalReader_fieldsFit (limits : SafetyLimits) :
    Experiment.physicalReader.FieldsFit limits.width := by
  have cap := limits.constant_fit 8280 (by decide)
  have locate := regularLocateBlock_fieldsFit 8200 limits.width (by omega)
  have span := spanBlock_fieldsFit 8256 limits.width (by omega)
  have hwne : limits.width ≠ 0 := by have := limits.width32; omega
  simp [Experiment.physicalReader, Experiment.descriptorLoads, Experiment.finishPacket,
    Block.sequence, Block.FieldsFit, Action.instruction, Instruction.Fits, Instruction.encoding,
    Instruction.operands, Arithmetic.code, Comparison.code, locate, span, hwne]
  omega

theorem physicalSelect_safe (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory)
    (readerSafe : ReaderSafe model limits.width memory Experiment.physicalReader)
    (readerCorrect : ReaderSimulation model memory Experiment.physicalReader)
    (s : Data) (fit : s.Fits limits.width) (hm : MetadataMatches model s.regs) :
    (selectCloseBlock Experiment.physicalReader).Safe memory limits.width s :=
  selectCloseBlock_safe model limits bounds memory Experiment.physicalReader readerSafe readerCorrect
    physicalReader_writes s fit hm

theorem physicalSelect_execution_safe (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory)
    (readerSafe : ReaderSafe model limits.width memory Experiment.physicalReader)
    (readerCorrect : ReaderSimulation model memory Experiment.physicalReader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits limits.width)
    (hm : MetadataMatches model regs) :
    SelectExecutionSafety memory limits.width
      ((selectCloseBlock Experiment.physicalReader).compileAt 0 ++ [.halt 513])
      9981 ⟨regs, 0, .running⟩ := by
  have cap := limits.constant_fit 9981 (by decide)
  simpa only [physicalReader_size, Nat.reduceMul, Nat.reduceAdd] using
    selectCloseBlock_execution_safe model limits bounds memory Experiment.physicalReader
      readerSafe readerCorrect physicalReader_writes (physicalReader_fieldsFit limits)
      (by simpa only [physicalReader_size, Nat.reduceMul, Nat.reduceAdd] using cap) regs fit hm

/-- This consumer expands every observation of the same compiled physical-reader
run, retaining the producing transition index for each receipt. -/
theorem physicalSelect_execution_safe_expectedType
    (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory)
    (readerSafe : ReaderSafe model limits.width memory Experiment.physicalReader)
    (readerCorrect : ReaderSimulation model memory Experiment.physicalReader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits limits.width)
    (hm : MetadataMatches model regs) :
    let program := (selectCloseBlock Experiment.physicalReader).compileAt 0 ++ [.halt 513]
    let actual := run memory program 9981 ⟨regs, 0, .running⟩
    (∀ instruction ∈ program, instruction.Fits limits.width) ∧
    actual.final.Fits limits.width ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe limits.width t.before t.instruction ∧ t.after.Fits limits.width) ∧
    (∀ index, index ≤ 9981 →
      (run memory program index ⟨regs, 0, .running⟩).final.Fits limits.width) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      actual.transitions[index]? = some t → t.receipt = some receipt →
      receipt.address < 2 ^ limits.width ∧ receipt.reply = memory[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ limits.width)) :=
  physicalSelect_execution_safe model limits bounds memory readerSafe readerCorrect regs fit hm

end RMQ.PackedBitvector.Controller
