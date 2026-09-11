import RMQ.Core.WordRAM.Packed.ScalarSafety
import RMQ.Core.WordRAM.Packed.LoadSafety
import RMQ.Core.WordRAM.Packed.PhysicalRead
import RMQ.Core.WordRAM.Packed.Guard

/-!+# Scalar and actual-run safety of the canonical physical reader

All geometric bounds below are derived from the numeric metadata installed by
charged setup. They are proof bounds, not additional source inputs.
-/
namespace RMQ.SuccinctFinal.PackedWordRAM
open Cartesian PackedCellProbe Structured

theorem metadataEnvelope_pos (n : Nat) : 0 < metadataEnvelope n := by
  unfold metadataEnvelope
  exact Nat.mul_pos (by decide) (Nat.pow_pos (Nat.two_pow_pos _))

theorem reader_polynomial_fit (n : Nat) :
    175 * metadataEnvelope n + 2 * (metadataEnvelope n * metadataEnvelope n) <
      2 ^ wordWidth n := by
  let e := metadataEnvelope n
  have ep : 0 < e := metadataEnvelope_pos n
  have square : e ≤ e * e := by
    simpa using Nat.mul_le_mul_left e (show 1 ≤ e by omega)
  have bound : 256 * (e * e) < 2 ^ wordWidth n := by
    have heq : 256 * (e * e) = 2 ^ (20 + packedReviewerCellWidth n * 4) := by
      have he : e = 2 ^ (6 + packedReviewerCellWidth n * 2) := by
        simp [e, metadataEnvelope, Nat.pow_add, Nat.pow_mul]
      rw [he]
      change 2 ^ 8 * (2 ^ (6 + packedReviewerCellWidth n * 2) *
        2 ^ (6 + packedReviewerCellWidth n * 2)) = _
      rw [← Nat.pow_add, ← Nat.pow_add]
      congr 1
      omega
    rw [heq]
    apply Nat.pow_lt_pow_right (by decide)
    unfold wordWidth
    omega
  change 175 * e + 2 * (e * e) < _
  omega

theorem MetadataMatches.envelope (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (r : Nat) (hr : 16 ≤ r ∧ r < 190) :
    regs r ≤ metadataEnvelope shape.size := by
  have hi : r - 16 < 174 := by omega
  have h := hm (r - 16) hi
  rw [show 16 + (r - 16) = r by omega] at h
  rw [h]
  cases hv : (metadata shape)[r - 16]? with
  | none => simp
  | some value =>
      exact metadata_words_le_envelope shape value (List.mem_of_getElem? hv)

theorem MetadataMatches.interior_chunks_pos (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (component : PackedReviewerInteriorComponentTag) :
    0 < regs (150 + 5 * interiorComponentIndex component + 4) := by
  have hc := interiorComponentIndex_lt component
  have h := hm (134 + 5 * interiorComponentIndex component + 4) (by omega)
  rw [metadata_interior_field shape component 4 (by decide)] at h
  have hp := packedReviewerInteriorEntryWidth_pos shape component
  have hb := packedBpCodeWordWidth_pos shape.size
  have hg := GenericSelect.selectCeilDiv_mul_ge_of_pos
    (n := packedReviewerInteriorEntryWidth shape.size component) hb
  simp only [interiorDescriptor, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some] at h
  have heq : 16 + (134 + 5 * interiorComponentIndex component + 4) =
      150 + 5 * interiorComponentIndex component + 4 := by omega
  rw [heq] at h
  rw [h]
  by_cases hz : 0 < GenericSelect.selectCeilDiv (packedReviewerInteriorEntryWidth shape.size component) (packedBpCodeWordWidth shape.size)
  · exact hz
  have zero : GenericSelect.selectCeilDiv (packedReviewerInteriorEntryWidth shape.size component)
      (packedBpCodeWordWidth shape.size) = 0 := by omega
  rw [zero, Nat.zero_mul] at hg
  omega

theorem LocateFrame.metadata (base : Nat) (hb : 256 ≤ base) (shape : CartesianShape)
    (before after : Registers) (frame : LocateFrame base before after)
    (hm : MetadataMatches shape before) : MetadataMatches shape after := by
  intro i hi
  rw [frame (16 + i) (Or.inl (by omega))]
  exact hm i hi

theorem copyInputsFrom_safe (destination width : Nat) (sources : List Nat)
    (memory : Memory) (s : Data) (fit : s.Fits width) :
    (copyInputsFrom destination sources).Safe memory width s := by
  apply SimpleScalar.safe memory width _ _ s fit
  induction sources generalizing destination with
  | nil => trivial
  | cons source rest ih => exact ⟨True.intro, ih (destination + 1)⟩

theorem exportSpanBlock_safe (base offset width : Nat) (memory : Memory)
    (s : Data) (fit : s.Fits width) :
    (exportSpanBlock base offset).Safe memory width s := by
  apply SimpleScalar.safe memory width _ _ s fit
  simp [exportSpanBlock, Block.sequence, SimpleScalar]

theorem regularLocateBlock_envelope_safe (base width e : Nat) (memory : Memory)
    (s : Data) (fit : s.Fits width) (one : 1 < 2 ^ width)
    (cap : e + 2 * (e * e) < 2 ^ width)
    (bitbase : s.regs (base + 1) ≤ e) (stride : s.regs (base + 3) ≤ e)
    (count : s.regs (base + 4) ≤ e) :
    (regularLocateBlock base).Safe memory width s := by
  apply regularLocateBlock_safe base width memory s fit one
  · intro active
    have hp := Nat.mul_le_mul (show s.regs base ≤ e by omega) stride
    omega
  · intro active
    have hp := Nat.mul_le_mul (show s.regs base ≤ e by omega) stride
    omega

theorem interiorLocateBlock_envelope_safe (base width e : Nat) (memory : Memory)
    (s : Data) (fit : s.Fits width) (one : 1 < 2 ^ width)
    (cap : e + 2 * (e * e) < 2 ^ width)
    (count : s.regs (base + 2) ≤ e) (bitbase : s.regs (base + 3) ≤ e)
    (entry : s.regs (base + 4) ≤ e) (bp : s.regs (base + 6) ≤ e)
    (chunks : 0 < s.regs (base + 5)) :
    (interiorLocateBlock base).Safe memory width s := by
  apply interiorLocateBlock_safe base width memory s fit one chunks
  intro _ active
  have hd := Nat.div_le_self (s.regs base - s.regs (base + 1)) (s.regs (base + 5))
  have hm := Nat.mod_le (s.regs base - s.regs (base + 1)) (s.regs (base + 5))
  have hp := Nat.mul_le_mul (show (s.regs base - s.regs (base + 1)) /
      s.regs (base + 5) ≤ e by omega) entry
  have hq := Nat.mul_le_mul (show (s.regs base - s.regs (base + 1)) %
      s.regs (base + 5) ≤ e by omega) bp
  exact ⟨by omega, by omega, by omega⟩

theorem regularCaseBlock_safe (base : Nat) (hb : 256 ≤ base) (shape : CartesianShape)
    (segment : Nat) (hsegment : segment < 23) (memory : Memory) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (regularCaseBlock base segment).Safe memory (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs
      subst status
      have copies := copyInputsFrom_safe (base + 32) (wordWidth shape.size)
        (regularCaseInputs base segment) memory ⟨regs, .running⟩ fit
      have hp := copyInputsFrom_source (base + 32) (regularCaseInputs base segment) memory regs
        (by intro r hr; simp only [regularCaseInputs, List.mem_cons, List.not_mem_nil, or_false] at hr; omega)
      let prepared := (copyInputsFrom (base + 32) (regularCaseInputs base segment)).eval memory ⟨regs, .running⟩
      have fp : prepared.final.Fits (wordWidth shape.size) := Block.eval_fits _ _ _ _ copies
      have b1 := hm.envelope shape regs (58 + 4 * segment) (by omega)
      have b3 := hm.envelope shape regs (58 + 4 * segment + 2) (by omega)
      have b4 := hm.envelope shape regs (58 + 4 * segment + 3) (by omega)
      have v1 := hp.2.1 1 (by simp [regularCaseInputs])
      have v3 := hp.2.1 3 (by simp [regularCaseInputs])
      have v4 := hp.2.1 4 (by simp [regularCaseInputs])
      simp only [regularCaseInputs, List.getElem_cons_succ, List.getElem_cons_zero] at v1 v3 v4
      have child := regularLocateBlock_envelope_safe (base + 32) (wordWidth shape.size)
        (metadataEnvelope shape.size) memory prepared.final fp
        (by have := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ wordWidth shape.size by unfold wordWidth; omega); omega)
        (by have := reader_polynomial_fit shape.size; omega)
        (Nat.le_trans (Nat.le_of_eq v1) b1)
        (Nat.le_trans (Nat.le_of_eq v3) b3)
        (Nat.le_trans (Nat.le_of_eq v4) b4)
      exact Block.safe_seq copies (Block.safe_seq child
        (exportSpanBlock_safe base 37 (wordWidth shape.size) memory _
          (Block.eval_fits _ _ _ _ child)))
  · exact Block.safe_stopped memory _ _ s fit hs

theorem interiorCaseBlock_safe (base : Nat) (hb : 256 ≤ base) (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) (memory : Memory) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (interiorCaseBlock base component).Safe memory (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs
      subst status
      have hc := interiorComponentIndex_lt component
      have copies := copyInputsFrom_safe (base + 32) (wordWidth shape.size)
        (interiorCaseInputs base component) memory ⟨regs, .running⟩ fit
      have hp := copyInputsFrom_source (base + 32) (interiorCaseInputs base component) memory regs
        (by intro r hr; simp only [interiorCaseInputs, List.mem_cons, List.not_mem_nil, or_false] at hr; omega)
      let prepared := (copyInputsFrom (base + 32) (interiorCaseInputs base component)).eval memory ⟨regs, .running⟩
      have fp : prepared.final.Fits (wordWidth shape.size) := Block.eval_fits _ _ _ _ copies
      have b2 := hm.envelope shape regs (150 + 5 * interiorComponentIndex component + 1) (by omega)
      have b3 := hm.envelope shape regs (150 + 5 * interiorComponentIndex component + 2) (by omega)
      have b4 := hm.envelope shape regs (150 + 5 * interiorComponentIndex component + 3) (by omega)
      have b6 := hm.envelope shape regs 32 (by omega)
      have b5 := hm.interior_chunks_pos shape regs component
      have v2 := hp.2.1 2 (by simp [interiorCaseInputs])
      have v3 := hp.2.1 3 (by simp [interiorCaseInputs])
      have v4 := hp.2.1 4 (by simp [interiorCaseInputs])
      have v5 := hp.2.1 5 (by simp [interiorCaseInputs])
      have v6 := hp.2.1 6 (by simp [interiorCaseInputs])
      simp only [interiorCaseInputs, List.getElem_cons_succ, List.getElem_cons_zero] at v2 v3 v4 v5 v6
      have child := interiorLocateBlock_envelope_safe (base + 32) (wordWidth shape.size)
        (metadataEnvelope shape.size) memory prepared.final fp
        (by have := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ wordWidth shape.size by unfold wordWidth; omega); omega)
        (by have := reader_polynomial_fit shape.size; omega)
        (Nat.le_trans (Nat.le_of_eq v2) b2)
        (Nat.le_trans (Nat.le_of_eq v3) b3)
        (Nat.le_trans (Nat.le_of_eq v4) b4)
        (Nat.le_trans (Nat.le_of_eq v6) b6)
        (Nat.lt_of_lt_of_eq b5 v5.symm)
      exact Block.safe_seq copies (Block.safe_seq child
        (exportSpanBlock_safe base 39 (wordWidth shape.size) memory _
          (Block.eval_fits _ _ _ _ child)))
  · exact Block.safe_stopped memory _ _ s fit hs

theorem absentLocationBlock_safe (base width : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits width) : (absentLocationBlock base).Safe memory width s := by
  apply SimpleScalar.safe memory width _ _ s fit
  simp [absentLocationBlock, Block.sequence, SimpleScalar, Nat.two_pow_pos]

theorem segmentTestBlock_safe (base segment width : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits width) (one : 1 < 2 ^ width) (value : segment < 2 ^ width) :
    (segmentTestBlock base segment).Safe memory width s := by
  apply SimpleScalar.safe memory width _ _ s fit
  exact ⟨value, one⟩

theorem interiorDispatch_safe (base : Nat) (hb : 256 ≤ base) (shape : CartesianShape)
    (components : List PackedReviewerInteriorComponentTag) (memory : Memory) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (interiorDispatch base components).Safe memory (wordWidth shape.size) s := by
  induction components generalizing s with
  | nil => exact absentLocationBlock_safe base _ memory s fit
  | cons component rest ih =>
      by_cases hs : s.status = .running
      · cases s with
        | mk regs status =>
          dsimp only at hs
          subst status
          have head := interiorCaseBlock_safe base hb shape component memory ⟨regs, .running⟩ fit hm
          have fp := Block.eval_fits memory _ _ _ head
          have source := interiorCaseBlock_source base hb component memory regs
          have mp := source.2.2.metadata base hb shape regs _ hm
          apply Block.safe_seq head
          apply Block.safe_ifZero fp
          split
          · exact ih _ fp mp
          · exact Block.safe_skip memory _ _ fp
      · exact Block.safe_stopped memory _ _ s fit hs

theorem regularDispatch_safe (base : Nat) (hb : 256 ≤ base) (shape : CartesianShape)
    (segments : List Nat) (hsegments : ∀ segment ∈ segments, segment < 23)
    (memory : Memory) (s : Data) (fit : s.Fits (wordWidth shape.size))
    (hm : MetadataMatches shape s.regs) :
    (regularDispatch base segments).Safe memory (wordWidth shape.size) s := by
  induction segments generalizing s with
  | nil => exact absentLocationBlock_safe base _ memory s fit
  | cons segment rest ih =>
      by_cases hs : s.status = .running
      · cases s with
        | mk regs status =>
          dsimp only at hs
          subst status
          have hs := hsegments segment (by simp)
          have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
            (show 32 ≤ wordWidth shape.size by unfold wordWidth; omega)
          have head := segmentTestBlock_safe base segment (wordWidth shape.size) memory
            ⟨regs, .running⟩ fit (by omega) (by omega)
          have fp := Block.eval_fits memory _ _ _ head
          have mp := (segmentTestBlock_frame base segment memory regs).metadata base hb shape regs _ hm
          apply Block.safe_seq head
          apply Block.safe_ifZero fp
          split
          · exact ih (by intro x hx; exact hsegments x (by simp [hx])) _ fp mp
          · exact regularCaseBlock_safe base hb shape segment hs memory _ fp mp
      · exact Block.safe_stopped memory _ _ s fit hs

theorem locateBlock_safe (base : Nat) (hb : 256 ≤ base) (shape : CartesianShape)
    (memory : Memory) (s : Data) (fit : s.Fits (wordWidth shape.size))
    (hm : MetadataMatches shape s.regs) :
    (locateBlock base).Safe memory (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs
      subst status
      have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
        (show 32 ≤ wordWidth shape.size by unfold wordWidth; omega)
      have head := segmentTestBlock_safe base 20 (wordWidth shape.size) memory
        ⟨regs, .running⟩ fit (by omega) (by omega)
      have fp := Block.eval_fits memory _ _ _ head
      have mp := (segmentTestBlock_frame base 20 memory regs).metadata base hb shape regs _ hm
      apply Block.safe_seq head
      apply Block.safe_ifZero fp
      split
      · exact regularDispatch_safe base hb shape (List.range 23)
          (by intro x hx; exact List.mem_range.mp hx) memory _ fp mp
      · exact interiorDispatch_safe base hb shape interiorComponents memory _ fp mp
  · exact Block.safe_stopped memory _ _ s fit hs

theorem storedRegularSpan_position_bound (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (segment index : Nat) (hs : segment < 23)
    (span : NumericSpan) (found : storedRegularSpan regs segment index = some span) :
    span.position ≤ metadataEnvelope shape.size +
      2 * (metadataEnvelope shape.size * metadataEnvelope shape.size) := by
  have hb := hm.envelope shape regs (58 + 4 * segment) (by omega)
  have ht := hm.envelope shape regs (58 + 4 * segment + 2) (by omega)
  have hc := hm.envelope shape regs (58 + 4 * segment + 3) (by omega)
  simp only [storedRegularSpan, regularSpan] at found
  split at found
  · rename_i active
    cases found
    have hp := Nat.mul_le_mul (show index ≤ metadataEnvelope shape.size by omega) ht
    dsimp only
    omega
  · cases found

theorem storedInteriorSpan_position_bound (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (index : Nat)
    (component : PackedReviewerInteriorComponentTag) (span : NumericSpan)
    (found : storedInteriorSpan regs index component = some span) :
    span.position ≤ metadataEnvelope shape.size +
      2 * (metadataEnvelope shape.size * metadataEnvelope shape.size) := by
  have hc := interiorComponentIndex_lt component
  have hb := hm.envelope shape regs (150 + 5 * interiorComponentIndex component + 2) (by omega)
  have he := hm.envelope shape regs (150 + 5 * interiorComponentIndex component + 3) (by omega)
  have hn := hm.envelope shape regs (150 + 5 * interiorComponentIndex component + 1) (by omega)
  have hw := hm.envelope shape regs 32 (by omega)
  simp only [storedInteriorSpan, interiorSpan] at found
  split at found
  · rename_i active
    cases found
    have hd := Nat.div_le_self (index - regs (150 + 5 * interiorComponentIndex component))
      (regs (150 + 5 * interiorComponentIndex component + 4))
    have hr := Nat.mod_le (index - regs (150 + 5 * interiorComponentIndex component))
      (regs (150 + 5 * interiorComponentIndex component + 4))
    have hp := Nat.mul_le_mul (show (index - regs (150 + 5 * interiorComponentIndex component)) /
      regs (150 + 5 * interiorComponentIndex component + 4) ≤ metadataEnvelope shape.size by omega) he
    have hq := Nat.mul_le_mul (show (index - regs (150 + 5 * interiorComponentIndex component)) %
      regs (150 + 5 * interiorComponentIndex component + 4) ≤ metadataEnvelope shape.size by omega) hw
    dsimp only
    omega
  · cases found

theorem storedInteriorFind_position_bound (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (index : Nat)
    (components : List PackedReviewerInteriorComponentTag) (span : NumericSpan)
    (found : components.findSome? (storedInteriorSpan regs index) = some span) :
    span.position ≤ metadataEnvelope shape.size +
      2 * (metadataEnvelope shape.size * metadataEnvelope shape.size) := by
  induction components with
  | nil => simp at found
  | cons component rest ih =>
      simp only [List.findSome?_cons] at found
      cases hh : storedInteriorSpan regs index component with
      | none => simp only [hh] at found; exact ih found
      | some value =>
          simp only [hh, Option.some.injEq] at found
          subst value
          exact storedInteriorSpan_position_bound shape regs hm index component span hh

theorem reviewerLogicalSpan_position_bound (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (segment index : Nat) (span : NumericSpan)
    (found : reviewerLogicalSpan shape.size (longCount shape)
      (packedReviewerSparseCount shape) segment index = some span) :
    span.position ≤ metadataEnvelope shape.size +
      2 * (metadataEnvelope shape.size * metadataEnvelope shape.size) := by
  rw [← storedLogicalSpan_canonical shape regs hm segment index] at found
  unfold storedLogicalSpan at found
  split at found
  · exact storedInteriorFind_position_bound shape regs hm index interiorComponents span found
  · split at found
    · exact storedRegularSpan_position_bound shape regs hm segment index ‹_› span found
    · cases found

theorem decodeSpanNat_value_lt (width position len : Nat) (memory : Memory)
    (hw : 0 < width) (hl : len < width) (memoryFit : MemoryWordsFit memory width)
    (value : Nat) (found : decodeSpanNat width position len memory = some value) :
    value < 2 ^ len := by
  by_cases hz : len = 0
  · simp only [decodeSpanNat, hz, if_true, Option.some.injEq] at found
    subst value
    exact Nat.two_pow_pos _
  · simp only [decodeSpanNat, hz, if_false] at found
    cases hf : memory[position / width]? with
    | none => simp [hf] at found
    | some first =>
        simp only [hf, bind, Option.bind] at found
        by_cases same : position % width + len ≤ width
        · simp only [same, if_true, Option.some.injEq] at found
          subst value
          exact Nat.mod_lt _ (Nat.two_pow_pos _)
        · simp only [same, if_false] at found
          cases hs : memory[position / width + 1]? with
          | none => simp [hs] at found
          | some second =>
              simp only [hs, Option.some.injEq] at found
              subst value
              exact (span_crossing_bounds width (position % width) len first second
                (Nat.mod_lt position hw) hl (by omega) (memoryFit.reply hf)).2.2.2.2.2.2.2

theorem readSpanPrefix_safe (memory : Memory) (width : Nat) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (hw : 8 ≤ width)
    (position : 174 * regs 22 + regs 8195 < 2 ^ width) :
    readSpanPrefix.Safe memory width ⟨regs, .running⟩ := by
  apply ScalarChecks_safe memory width _ _ fit
  have f22 := fit.1 22
  have f8196 := fit.1 8196
  dsimp only at f22 f8196
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  simp [ScalarChecks, readSpanPrefix, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval]
  omega

theorem readSpanSuffix_safe (memory : Memory) (width : Nat) (s : Data)
    (fit : s.Fits width) (one : 1 < 2 ^ width) (packet : s.regs 8259 + 1 < 2 ^ width) :
    readSpanSuffix.Safe memory width s := by
  have hwne : width ≠ 0 := by intro h; simp [h] at one
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs packet fit
      subst status
      apply ScalarChecks_safe memory width _ _ fit
      have f := fit.1 8258
      dsimp only at f
      simp [hwne, ScalarChecks, readSpanSuffix, Block.sequence, Block.eval,
        Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
        Data.ofState, Registers.write, Arithmetic.eval]
      omega
  · exact Block.safe_stopped memory width _ s fit hs

theorem readSpanBody_safe (memory : Memory) (width : Nat) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (hw : 8 ≤ width)
    (memoryFit : MemoryWordsFit memory width) (hwidth : regs 22 = width)
    (position : 174 * width + regs 8195 < 2 ^ width) (length : regs 8196 < width) :
    readSpanBody.Safe memory width ⟨regs, .running⟩ := by
  have hp := readSpanPrefix_safe memory width regs fit hw (by simpa [hwidth] using position)
  have fp := Block.eval_fits memory width _ _ hp
  rw [readSpanPrefix_source] at fp
  have w : physicalSpanInputs regs 8256 = width := by simp [physicalSpanInputs, Registers.write, hwidth]
  have p : physicalSpanInputs regs 8257 = 174 * width + regs 8195 := by simp [physicalSpanInputs, Registers.write, hwidth]
  have l : physicalSpanInputs regs 8258 = regs 8196 := by simp [physicalSpanInputs, Registers.write]
  have spanSafe := spanBlock_safe 8256 width (174 * width + regs 8195) (regs 8196) memory
    ⟨physicalSpanInputs regs, .running⟩ (by omega) memoryFit fp w p l position length
  have fs := Block.eval_fits memory width _ _ spanSafe
  have source := spanBlock_source 8256 width (174 * width + regs 8195) (regs 8196)
    memory (physicalSpanInputs regs) w p l
  have suffix : readSpanSuffix.Safe memory width
      ((spanBlock 8256).eval memory ⟨physicalSpanInputs regs, .running⟩).final := by
    cases hd : decodeSpanNat width (174 * width + regs 8195) (regs 8196) memory with
    | none =>
        have stopped := source.1
        simp only [hd, SpanOutcome] at stopped
        apply Block.safe_stopped memory width _ _ fs
        rw [stopped]
        decide
    | some value =>
        have output := source.1
        simp only [hd, SpanOutcome] at output
        have hv := decodeSpanNat_value_lt width (174 * width + regs 8195) (regs 8196)
          memory (by omega) length memoryFit value hd
        have hpow := Nat.pow_lt_pow_right (by decide : 1 < 2) length
        apply readSpanSuffix_safe memory width _ fs
        · have := Nat.pow_le_pow_right (by decide : 0 < 2) hw; omega
        · rw [output.2]
          omega
  apply Block.safe_seq hp
  rw [readSpanPrefix_source]
  exact Block.safe_seq spanSafe suffix

theorem logicalReadBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    logicalReadBlock.Safe (shapeMemory shape) (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs
      subst status
      have locsafe := locateBlock_safe 8192 (by decide) shape (shapeMemory shape)
        ⟨regs, .running⟩ fit hm
      have fp := Block.eval_fits _ _ _ _ locsafe
      have source := locateBlock_canonical 8192 (by decide) shape (shapeMemory shape) regs hm
      let located := (locateBlock 8192).eval (shapeMemory shape) ⟨regs, .running⟩
      have mp := source.2.2.metadata 8192 (by decide) shape regs located.final.regs hm
      have running : located.final = ⟨located.final.regs, .running⟩ := by
        have hs : located.final.status = .running := source.1.1
        generalize located.final = data at hs ⊢
        cases data
        simp_all
      apply Block.safe_seq locsafe
      apply Block.safe_ifZero fp
      split
      · exact SimpleScalar.safe _ _ _ (Nat.two_pow_pos _) _ fp
      · rename_i present
        change readSpanBody.Safe _ _ located.final
        rw [running]
        have hwidth : located.final.regs 22 = wordWidth shape.size := by
          have h := mp 6 (by decide)
          rw [metadata_wordWidth_field] at h
          exact h
        cases hspan : reviewerLogicalSpan shape.size (longCount shape)
            (packedReviewerSparseCount shape) (regs 8192) (regs 8193) with
        | none =>
            have flag := source.1.2.1
            simp only [hspan, spanPresence] at flag
            exact (present flag).elim
        | some span =>
            have hp := source.1.2.2.1
            have hl := source.1.2.2.2
            simp only [hspan, spanPosition, spanLength, Option.map_some, Option.getD_some] at hp hl
            have position := reviewerLogicalSpan_position_bound shape regs hm
              (regs 8192) (regs 8193) span hspan
            have widthBound := mp.envelope shape located.final.regs 22 (by decide)
            rw [hwidth] at widthBound
            have prefixBound := Nat.mul_le_mul_left 174 widthBound
            have cap := reader_polynomial_fit shape.size
            have lengthBound := reviewerLogicalSpan_length_le shape.size (longCount shape)
              (packedReviewerSparseCount shape) ⟨⟨.leftSelect, 0, 0⟩, .entryBaseOccurrence, regs 8192, regs 8193⟩ span hspan
            have strict := oldWidth_lt_wordWidth shape.size
            apply readSpanBody_safe (shapeMemory shape) (wordWidth shape.size) located.final.regs
              (by rw [← running]; exact fp) (by unfold wordWidth; omega)
              (shapeMemory_words_fit shape) hwidth
            · rw [hp]
              omega
            · rw [hl]
              omega
  · exact Block.safe_stopped _ _ _ s fit hs

/-- Source-only safety interface for callers of a supplied reader block. -/
def ReaderSafe (shape : CartesianShape) (memory : Memory) (reader : Block) : Prop :=
  ∀ s, s.Fits (wordWidth shape.size) → MetadataMatches shape s.regs →
    reader.Safe memory (wordWidth shape.size) s

theorem logicalReadBlock_readerSafe (shape : CartesianShape) :
    ReaderSafe shape (shapeMemory shape) logicalReadBlock := logicalReadBlock_safe shape

theorem logicalReadBlock_output_bounds (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    let actual := logicalReadBlock.eval (shapeMemory shape) ⟨regs, .running⟩
    actual.final.regs 8194 ≤ 2 ^ packedReviewerCellWidth shape.size ∧
    actual.final.regs 8195 ≤ packedReviewerCellWidth shape.size := by
  have h := logicalReadBlock_correct shape regs hm
  dsimp only
  rw [h.2.1, h.2.2.1]
  cases hr : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
      (regs 8192) (regs 8193) with
  | none => simp [logicalPacket, logicalLength]
  | some bits =>
      have fits := packedReviewerGlobalReadStore_word_fits shape
        ⟨⟨.leftSelect, 0, 0⟩, .entryBaseOccurrence, regs 8192, regs 8193⟩ bits hr
      have value := fits.value_lt_two_pow
      exact ⟨by dsimp only [logicalPacket]; omega, fits⟩

theorem logicalReadBlock_fieldsFit (width : Nat) (bound : 8280 < 2 ^ width) :
    logicalReadBlock.FieldsFit width := by
  have hwne : width ≠ 0 := by intro h; simp [h] at bound
  have locate := locateBlock_fieldsFit 8192 width (by decide) (by omega)
  have span := spanBlock_fieldsFit 8256 width (by omega)
  have prefixFields : readSpanPrefix.FieldsFit width := by
    simp [hwne, readSpanPrefix, Block.sequence, Block.FieldsFit, Action.instruction,
      Instruction.Fits, Instruction.encoding, Instruction.operands, Arithmetic.code]
    omega
  have suffixFields : readSpanSuffix.FieldsFit width := by
    simp [hwne, readSpanSuffix, Block.sequence, Block.FieldsFit, Action.instruction,
      Instruction.Fits, Instruction.encoding, Instruction.operands, Arithmetic.code]
    omega
  refine ⟨locate, ?_, ?_, ?_, prefixFields, span, suffixFields⟩
  all_goals simp [hwne, Instruction.Fits, Instruction.encoding, Instruction.operands,
    Block.FieldsFit, Action.instruction] <;> omega

theorem logicalReaderProgram_fieldsFit (n : Nat) :
    ∀ instruction ∈ logicalReaderProgram, instruction.Fits (wordWidth n) := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth n by unfold wordWidth; omega)
  have fields := logicalReadBlock.compile_fits (wordWidth n) 0
    (logicalReadBlock_fieldsFit _ (by omega)) (by simp; omega)
  intro instruction hi
  rcases List.mem_append.mp hi with hi | hi
  · exact fields instruction hi
  · simp only [List.mem_singleton] at hi
    subst instruction
    simp [Instruction.Fits, Instruction.encoding, Instruction.operands]
    omega

theorem logicalReaderRun_safe (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size) :
    let expected := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
      (regs 8192) (regs 8193)
    let actual := logicalReaderRun (shapeMemory shape) regs
    actual.result = some (logicalPacket expected) ∧
    actual.final.regs 8195 = logicalLength expected ∧
    actual.reads = readerReceipts shape (shapeMemory shape) (regs 8192) (regs 8193) ∧
    actual.steps ≤ 1069 ∧ ReaderFrame regs actual.final.regs ∧
    actual.final.Fits (wordWidth shape.size) ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe (wordWidth shape.size) t.before t.instruction ∧
        t.after.Fits (wordWidth shape.size)) ∧
    (∀ index, index ≤ 1069 →
      (run (shapeMemory shape) logicalReaderProgram index ⟨regs, 0, .running⟩).final.Fits
        (wordWidth shape.size)) := by
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth shape.size by unfold wordWidth; omega)
  have sourceFit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) :=
    ⟨fit, fun _ h => Status.noConfusion h⟩
  have sourceSafe := logicalReadBlock_safe shape _ sourceFit hm
  have actual := logicalReadBlock.compile_with_halt_safe (shapeMemory shape)
    (wordWidth shape.size) 8194 ⟨regs, 0, .running⟩ rfl
    (logicalReadBlock_fieldsFit _ (by omega))
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega)
    (by simp; omega) ⟨Nat.two_pow_pos _, sourceFit⟩ sourceSafe
  have value := logicalReaderRun_correct shape regs hm
  refine ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2, ?_⟩
  simpa only [logicalReaderRun, logicalReaderProgram, logicalReadBlock_size,
    show 1068 + 1 = 1069 by decide] using actual.2.2.2.2

/-- Two charged moves install the request after the charged metadata setup. -/
def readerInputMoves : Block := copyInputsFrom 8192 [0, 1]

def readerSetupRun (xs : List Int) (segment index : Nat) : Run :=
  run (buildMemory xs) (metadataSetupBlock.compileAt 0) 348
    (initialState xs.length segment index)

def readerInputRun (xs : List Int) (segment index : Nat) : Run :=
  run (buildMemory xs) (readerInputMoves.compileAt 0) 2
    ⟨(readerSetupRun xs segment index).final.regs, 0, .running⟩

theorem readerInputMoves_run (shape : CartesianShape) (memory : Memory) (n : Nat) (regs : Registers)
    (segment index : Nat) (mf : MetadataMatches shape regs)
    (rf : ∀ r, regs r < 2 ^ wordWidth n)
    (i0 : regs 0 = segment) (i1 : regs 1 = index) :
    let actual := run memory (readerInputMoves.compileAt 0) 2 ⟨regs, 0, .running⟩
    MetadataMatches shape actual.final.regs ∧
    (∀ r, actual.final.regs r < 2 ^ wordWidth n) ∧
    actual.final.regs 8192 = segment ∧ actual.final.regs 8193 = index ∧
    actual.reads = [] ∧ actual.steps ≤ 2 ∧
    (∀ k, k ≤ 2 → (run memory (readerInputMoves.compileAt 0) k
      ⟨regs, 0, .running⟩).final.Fits (wordWidth n)) := by
  have ds : (⟨regs, .running⟩ : Data).Fits (wordWidth n) :=
    ⟨rf, fun _ h => Status.noConfusion h⟩
  have source := copyInputsFrom_source 8192 [0, 1] memory regs
    (by intro r hr; simp at hr; omega)
  have safe := copyInputsFrom_safe 8192 (wordWidth n) [0, 1] memory _ ds
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 32 ≤ wordWidth n by unfold wordWidth; omega)
  have fields : readerInputMoves.FieldsFit (wordWidth n) := by
    have hw : wordWidth n ≠ 0 := Nat.ne_of_gt (wordWidth_pos n)
    simp [readerInputMoves, copyInputsFrom, Block.FieldsFit, Action.instruction,
      Instruction.Fits, Instruction.encoding, Instruction.operands, hw]
    omega
  have actual := readerInputMoves.compile_run_safe memory (wordWidth n)
    ⟨regs, 0, .running⟩ rfl fields (by simp [readerInputMoves, copyInputsFrom_size]; omega)
    ⟨Nat.two_pow_pos _, ds⟩ safe
  have rr := congrArg Data.regs actual.1
  change (run memory (readerInputMoves.compileAt 0) 2 ⟨regs, 0, .running⟩).final.regs =
    ((copyInputsFrom 8192 [0, 1]).eval memory ⟨regs, .running⟩).final.regs at rr
  have sourceMeta : MetadataMatches shape
      ((copyInputsFrom 8192 [0, 1]).eval memory ⟨regs, .running⟩).final.regs := by
    intro i hi
    rw [source.2.2.1 (16 + i) (Or.inl (by omega))]
    exact mf i hi
  have v0 := source.2.1 0 (by decide)
  have v1 := source.2.1 1 (by decide)
  have mx : readerInputMoves.size = 2 := by simp [readerInputMoves, copyInputsFrom_size]
  refine ⟨by rw [rr]; exact sourceMeta, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact actual.2.2.2.2.1.2.1
  · rw [rr]
    exact v0.trans i0
  · rw [rr]
    exact v1.trans i1
  · exact actual.2.1.trans source.2.2.2
  · simpa only [mx] using actual.2.2.1
  · simpa only [mx] using actual.2.2.2.2.2.2

theorem readerInputRun_prepared (xs : List Int) (segment index : Nat)
    (fit : (initialState xs.length segment index).Fits (wordWidth xs.length)) :
    let actual := readerInputRun xs segment index
    MetadataMatches (SuccinctClassic.cartesianShape xs) actual.final.regs ∧
    (∀ r, actual.final.regs r < 2 ^ wordWidth xs.length) ∧
    actual.final.regs 8192 = segment ∧ actual.final.regs 8193 = index ∧
    actual.reads = [] ∧ actual.steps ≤ 2 ∧
    (∀ k, k ≤ 2 →
      (run (buildMemory xs) (readerInputMoves.compileAt 0) k
        ⟨(run (buildMemory xs) (metadataSetupBlock.compileAt 0) 348 (initialState xs.length segment index)).final.regs, 0, .running⟩).final.Fits
          (wordWidth xs.length)) := by
  unfold readerInputRun readerSetupRun
  obtain ⟨_, setupMeta, _, setupFrame, _, _, _, setupFit, _, _⟩ :=
    buildMemory_setup_run_safe xs (initialState xs.length segment index) rfl rfl fit.2.1
  have i0 : (run (buildMemory xs) (metadataSetupBlock.compileAt 0) 348 (initialState xs.length segment index)).final.regs 0 = segment := by
    exact (setupFrame 0 (by decide) (Or.inl (by decide))).trans
      (inputRegisters_left xs.length segment index)
  have i1 : (run (buildMemory xs) (metadataSetupBlock.compileAt 0) 348 (initialState xs.length segment index)).final.regs 1 = index := by
    exact (setupFrame 1 (by decide) (Or.inl (by decide))).trans
      (inputRegisters_right xs.length segment index)
  have h := readerInputMoves_run (SuccinctClassic.cartesianShape xs) (buildMemory xs) xs.length
    (run (buildMemory xs) (metadataSetupBlock.compileAt 0) 348 (initialState xs.length segment index)).final.regs segment index setupMeta
    setupFit.2.1 i0 i1
  exact h
/-- The reader input bank is produced by actual setup and actual copy runs.
The conclusion is the same standalone 1069-budget reader execution. -/
theorem logicalReaderRun_safe_list (xs : List Int) (regs : Registers) (segment index : Nat)
    (hm : MetadataMatches (SuccinctClassic.cartesianShape xs) regs)
    (fit : ∀ r, regs r < 2 ^ wordWidth xs.length)
    (hs : regs 8192 = segment) (hi : regs 8193 = index) :
    let shape := SuccinctClassic.cartesianShape xs
    let expected := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index
    let actual := logicalReaderRun (buildMemory xs) regs
    actual.result = some (logicalPacket expected) ∧
    actual.final.regs 8195 = logicalLength expected ∧
    actual.reads = readerReceipts shape (buildMemory xs) segment index ∧
    actual.steps ≤ 1069 ∧ ReaderFrame regs actual.final.regs ∧
    actual.final.Fits (wordWidth xs.length) ∧
    (∀ (k : Nat) (t : Transition), actual.transitions[k]? = some t →
      Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧
        t.after.Fits (wordWidth xs.length)) ∧
    (∀ k, k ≤ 1069 →
      (run (buildMemory xs) logicalReaderProgram k ⟨regs, 0, .running⟩).final.Fits
        (wordWidth xs.length)) := by
  have h := logicalReaderRun_safe (SuccinctClassic.cartesianShape xs) regs hm
    (by simpa only [packedReviewerCartesianShape_size] using fit)
  simpa only [hs, hi, packedReviewerCartesianShape_size, buildMemory] using h
theorem logicalReaderRun_from_initialState (xs : List Int) (segment index : Nat)
    (fit : (initialState xs.length segment index).Fits (wordWidth xs.length)) :
    let shape := SuccinctClassic.cartesianShape xs
    let regs := (readerInputRun xs segment index).final.regs
    let expected := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index
    let actual := logicalReaderRun (buildMemory xs) regs
    actual.result = some (logicalPacket expected) ∧
    actual.final.regs 8195 = logicalLength expected ∧
    actual.reads = readerReceipts shape (buildMemory xs) segment index ∧
    actual.steps ≤ 1069 ∧ ReaderFrame regs actual.final.regs ∧
    actual.final.Fits (wordWidth xs.length) ∧
    (∀ (k : Nat) (t : Transition), actual.transitions[k]? = some t →
      Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧
        t.after.Fits (wordWidth xs.length)) ∧
    (∀ k, k ≤ 1069 →
      (run (buildMemory xs) logicalReaderProgram k ⟨regs, 0, .running⟩).final.Fits
        (wordWidth xs.length)) := by
  have prepared := readerInputRun_prepared xs segment index fit
  exact logicalReaderRun_safe_list xs (readerInputRun xs segment index).final.regs
    segment index prepared.1 prepared.2.1 prepared.2.2.1 prepared.2.2.2.1
theorem logicalReaderRun_allocation (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size) :
    (shapeMemory shape).length * wordWidth shape.size ≤
      2 * shape.size + allocationRho shape.size ∧
    wordWidth shape.size ≤ 192 * (Nat.log2 (shape.size + 2) + 1) ∧
    (∀ value ∈ shapeMemory shape, value < 2 ^ wordWidth shape.size) ∧
    (logicalReaderRun (shapeMemory shape) regs).result =
      some (logicalPacket ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        (regs 8192) (regs 8193))) ∧
    (∀ k, k ≤ 1069 →
      (run (shapeMemory shape) logicalReaderProgram k ⟨regs, 0, .running⟩).final.Fits
        (wordWidth shape.size)) := by
  have h := logicalReaderRun_safe shape regs hm fit
  exact ⟨shapeMemory_capacity_le shape, wordWidth_le_log shape.size,
    shapeMemory_words_fit shape, h.1, h.2.2.2.2.2.2.2⟩

theorem logicalReaderRun_read_fits (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size)
    (index : Nat) (t : Transition) (receipt : Receipt)
    (occurrence : (logicalReaderRun (shapeMemory shape) regs).transitions[index]? = some t)
    (read : t.receipt = some receipt) :
    receipt.address < 2 ^ wordWidth shape.size ∧
    receipt.reply = (shapeMemory shape)[receipt.address]? ∧
    (∀ value, receipt.reply = some value → value < 2 ^ wordWidth shape.size) := by
  have safe := (logicalReaderRun_safe shape regs hm fit).2.2.2.2.2.2.1 index t occurrence
  exact run_read_fits occurrence read safe.1 safe.2

namespace ReaderSafetyConsumers

theorem source_expectedType : ∀ (shape : CartesianShape) (regs : Registers) (status : Status),
    (∀ r, regs r < 2 ^ wordWidth shape.size) →
    (∀ value, status = .halted value → value < 2 ^ wordWidth shape.size) →
    (∀ i < 174, regs (16 + i) = ((metadata shape)[i]?).getD 0) →
    (locateBlock 8192).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, status⟩ ∧
    logicalReadBlock.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, status⟩ := by
  intro shape regs status fit haltFit metadata
  exact ⟨locateBlock_safe 8192 (by decide) shape _ _ ⟨fit, haltFit⟩ metadata,
    logicalReadBlock_safe shape _ ⟨fit, haltFit⟩ metadata⟩

theorem run_expectedType (shape : CartesianShape) (regs : Registers)
    (metadata : ∀ i < 174, regs (16 + i) = ((metadata shape)[i]?).getD 0)
    (fit : ∀ r, regs r < 2 ^ wordWidth shape.size) :
    (run (shapeMemory shape) (logicalReadBlock.compileAt 0 ++ [.halt 8194])
      1069 ⟨regs, 0, .running⟩).result =
      some (logicalPacket ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        (regs 8192) (regs 8193))) ∧
    (run (shapeMemory shape) (logicalReadBlock.compileAt 0 ++ [.halt 8194])
      1069 ⟨regs, 0, .running⟩).reads =
      readerReceipts shape (shapeMemory shape) (regs 8192) (regs 8193) ∧
    (∀ (k : Nat) (t : Transition),
      (run (shapeMemory shape) (logicalReadBlock.compileAt 0 ++ [.halt 8194])
        1069 ⟨regs, 0, .running⟩).transitions[k]? = some t →
      Instruction.Safe (wordWidth shape.size) t.before t.instruction ∧
        t.after.Fits (wordWidth shape.size)) ∧
    (∀ k, k ≤ 1069 →
      (run (shapeMemory shape) (logicalReadBlock.compileAt 0 ++ [.halt 8194])
        k ⟨regs, 0, .running⟩).final.Fits (wordWidth shape.size)) := by
  obtain ⟨result, _, reads, _, _, _, trace, prefixes⟩ := logicalReaderRun_safe shape regs metadata fit
  exact ⟨result, reads, trace, prefixes⟩

theorem absent_request (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size)
    (absent : reviewerLogicalSpan shape.size (longCount shape)
      (packedReviewerSparseCount shape) (regs 8192) (regs 8193) = none) :
    (logicalReaderRun (shapeMemory shape) regs).result = some 0 ∧
    (logicalReaderRun (shapeMemory shape) regs).reads = [] ∧
    (∀ k, k ≤ 1069 →
      (run (shapeMemory shape) logicalReaderProgram k ⟨regs, 0, .running⟩).final.Fits
        (wordWidth shape.size)) := by
  have reference := directLogicalReadNat_eq_globalReadStore shape (regs 8192) (regs 8193)
  simp [directLogicalReadNat, absent] at reference
  have missing : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
      (regs 8192) (regs 8193) = none := by
    cases h : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        (regs 8192) (regs 8193) with
    | none => rfl
    | some bits => simp [h] at reference
  obtain ⟨result, _, reads, _, _, _, _, prefixes⟩ := logicalReaderRun_safe shape regs hm fit
  exact ⟨by simpa [missing] using result, by simpa [readerReceipts, absent] using reads, prefixes⟩

theorem absent_segment (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size)
    (outside : 23 ≤ regs 8192) :
    (logicalReaderRun (shapeMemory shape) regs).reads = [] ∧
    (logicalReaderRun (shapeMemory shape) regs).final.Fits (wordWidth shape.size) := by
  have missing := absent_request shape regs hm fit
    (by simp [reviewerLogicalSpan, show ¬ regs 8192 < 23 by omega])
  exact ⟨missing.2.1, missing.2.2 1069 (by decide)⟩

theorem dead_interior (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size)
    (segment : regs 8192 = 20) (index : regs 8193 = packedInteriorComponentWords shape.size) :
    (logicalReaderRun (shapeMemory shape) regs).result = some 0 ∧
    (logicalReaderRun (shapeMemory shape) regs).reads = [] := by
  have h := absent_request shape regs hm fit
    (by simp [segment, index, reviewerLogicalSpan_interior,
      packedReviewerInteriorClassify_deadAddress])
  exact ⟨h.1, h.2.1⟩

theorem empty_sentinel :
    let regs := (readerInputRun [] 19 0).final.regs
    (logicalReaderRun (buildMemory []) regs).result = some 1 ∧
    (logicalReaderRun (buildMemory []) regs).final.regs 8195 = 0 ∧
    (logicalReaderRun (buildMemory []) regs).reads = [] ∧
    (∀ k, k ≤ 1069 →
      (run (buildMemory []) logicalReaderProgram k ⟨regs, 0, .running⟩).final.Fits
        (wordWidth 0)) := by
  have fit := initialState_fits 0 19 0 (by
    have := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 32 ≤ wordWidth 0 by unfold wordWidth; omega)
    omega) (Nat.two_pow_pos _)
  have h := logicalReaderRun_from_initialState [] 19 0 fit
  have pair := directLogicalReadNat_eq_globalReadStore (SuccinctClassic.cartesianShape []) 19 0
  simp only [packedReviewerCartesianShape_size, List.length_nil] at pair
  rw [directLogicalReadNat_empty_alias] at pair
  have empty : (concreteBPNativeSuccinctRMQGlobalReadStore (SuccinctClassic.cartesianShape [])).readWord?
      19 0 = some [] := by
    cases hr : (concreteBPNativeSuccinctRMQGlobalReadStore (SuccinctClassic.cartesianShape [])).readWord?
        19 0 with
    | none => simp [hr] at pair
    | some bits =>
        cases bits with
        | nil => rfl
        | cons bit rest => simp [hr] at pair
  refine ⟨by simpa [empty, logicalPacket, SuccinctSpace.bitsToNatLE] using h.1,
    by simpa [empty, logicalLength] using h.2.1, ?_, h.2.2.2.2.2.2.2⟩
  have reads := h.2.2.1
  simp only [readerReceipts, packedReviewerCartesianShape_size, List.length_nil] at reads
  rw [reviewerLogicalSpan_empty_alias] at reads
  simpa only [spanAttemptReceipts, if_pos rfl] using reads

theorem singleton_all_requests (value : Int) (segment index : Nat)
    (segmentFit : segment < 2 ^ wordWidth 1) (indexFit : index < 2 ^ wordWidth 1) :
    ∀ k, k ≤ 1069 →
      (run (buildMemory [value]) logicalReaderProgram k
        ⟨(readerInputRun [value] segment index).final.regs, 0, .running⟩).final.Fits
          (wordWidth 1) :=
  (logicalReaderRun_from_initialState [value] segment index
    (initialState_fits 1 segment index segmentFit indexFit)).2.2.2.2.2.2.2

theorem canonical_crossing (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size)
    (span : NumericSpan) (found : reviewerLogicalSpan shape.size (longCount shape)
      (packedReviewerSparseCount shape) (regs 8192) (regs 8193) = some span)
    (crossing : wordWidth shape.size <
      (174 * wordWidth shape.size + span.position) % wordWidth shape.size + span.length) :
    let address := (174 * wordWidth shape.size + span.position) / wordWidth shape.size
    ∃ first second,
      (shapeMemory shape)[address]? = some first ∧
      (shapeMemory shape)[address + 1]? = some second ∧
      (logicalReaderRun (shapeMemory shape) regs).reads =
        [⟨address, some first⟩, ⟨address + 1, some second⟩] ∧
      (∀ k, k ≤ 1069 →
        (run (shapeMemory shape) logicalReaderProgram k ⟨regs, 0, .running⟩).final.Fits
          (wordWidth shape.size)) := by
  obtain ⟨value, hd⟩ := canonical_span_decode shape (regs 8192) (regs 8193) span found
  have hmwidth := Nat.mod_lt (174 * wordWidth shape.size + span.position) (wordWidth_pos shape.size)
  have hn : span.length ≠ 0 := by omega
  have hc : ¬ (174 * wordWidth shape.size + span.position) % wordWidth shape.size +
      span.length ≤ wordWidth shape.size := by omega
  have hcn : ¬ span.position % wordWidth shape.size + span.length ≤ wordWidth shape.size := by
    simpa using hc
  cases hf : (shapeMemory shape)[(174 * wordWidth shape.size + span.position) / wordWidth shape.size]? with
  | none => simp [decodeSpanNat, hn, hf] at hd
  | some first =>
      cases hs : (shapeMemory shape)[(174 * wordWidth shape.size + span.position) / wordWidth shape.size + 1]? with
      | none => simp [decodeSpanNat, hn, hf, hcn, hs] at hd
      | some second =>
          obtain ⟨_, _, reads, _, _, _, _, prefixes⟩ := logicalReaderRun_safe shape regs hm fit
          exact ⟨first, second, hf, hs,
            by simpa [readerReceipts, found, spanAttemptReceipts, hn, hcn, hf, hs] using reads,
            prefixes⟩

end ReaderSafetyConsumers
end RMQ.SuccinctFinal.PackedWordRAM
