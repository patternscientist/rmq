import RMQ.Core.WordRAM.Packed.InteriorLocate
import RMQ.Core.WordRAM.Packed.Span
import RMQ.Core.WordRAM.Packed.Allocation
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerCrossing

/-!
# Direct repacked spans for every canonical logical word

Geometry is scalar and proof-free. The executable reader receives only size,
counts, numeric memory and logical segment/index. Shape and legacy bit stores
appear only in refinement theorems. A new physical span has its own physical
addresses; equality of logical replies does not identify old and new probes.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian PackedCellProbe SuccinctSpace

def regularDescriptorSpan (n lc sc segment index : Nat) : Option NumericSpan :=
  let fields := regularDescriptor n lc sc segment
  regularSpan index (fields[0]?.getD 0) (fields[1]?.getD 0)
    (fields[2]?.getD 0) (fields[3]?.getD 0)

def reviewerLogicalSpan (n lc sc segment index : Nat) : Option NumericSpan :=
  if segment < 23 then
    if segment = 20 then
      (packedReviewerInteriorClassify n index).map fun location =>
        ⟨packedReviewerClosedInteriorBitAddress n lc sc location, location.readWidth⟩
    else regularDescriptorSpan n lc sc segment index
  else none

def directLogicalReadNat (n lc sc : Nat) (memory : List Nat)
    (segment index : Nat) : Option (Nat × Nat) :=
  (reviewerLogicalSpan n lc sc segment index).bind fun span =>
    (decodeSpanNat (wordWidth n)
      (metadataWordCount * wordWidth n + span.position) span.length memory).map
        fun value => (value, span.length)

@[simp] theorem reviewerLogicalSpan_regular (n lc sc segment index : Nat)
    (hsegment : segment < 23) (h20 : segment ≠ 20) :
    reviewerLogicalSpan n lc sc segment index =
      regularDescriptorSpan n lc sc segment index := by
  simp [reviewerLogicalSpan, hsegment, h20]

@[simp] theorem reviewerLogicalSpan_interior (n lc sc index : Nat) :
    reviewerLogicalSpan n lc sc 20 index =
      (packedReviewerInteriorClassify n index).map fun location =>
        ⟨packedReviewerClosedInteriorBitAddress n lc sc location, location.readWidth⟩ := by
  simp [reviewerLogicalSpan]

@[simp] theorem reviewerLogicalSpan_outside (n lc sc segment index : Nat)
    (hsegment : 23 ≤ segment) : reviewerLogicalSpan n lc sc segment index = none := by
  simp [reviewerLogicalSpan, Nat.not_lt.mpr hsegment]

/-- Arbitrary original bit spans survive dense repacking. A zero-length
sentinel does not need its nominal position to lie inside the allocation. -/
theorem decodeSpanNat_repacked_span (headers : List Nat) (width : Nat)
    (old : List (List Bool)) (position len : Nat) (hw : 0 < width)
    (hlen : len ≤ width) (hbound : position + len ≤ old.flatten.length ∨ len = 0) :
    decodeSpanNat width (headers.length * width + position) len
      (repackWords headers width old) =
      some (bitsToNatLE ((old.flatten.drop position).take len)) := by
  by_cases hz : len = 0
  · simp [hz, bitsToNatLE]
  have hb : position + len ≤ old.flatten.length := hbound.resolve_right hz
  rw [repackWords, decodeSpanNat_append_shift headers _ width position len hw]
  have hcover : old.flatten.length ≤ (denseCells width old.flatten).length * width := by
    rw [denseCells_length]
    exact GenericSelect.selectCeilDiv_mul_ge_of_pos hw
  have hdecode := decodeSpanNat_uniform (denseCells width old.flatten)
    width position len hw (fun cell hc => denseCells_cell_length width old.flatten hw hc)
    hlen (Nat.le_trans hb hcover)
  change decodeSpanNat width position len
    ((denseCells width old.flatten).map bitsToNatLE) = _
  rw [hdecode, denseCells_flatten width old.flatten hw]
  unfold densePad
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by rw [List.length_drop]; omega)]

theorem selectCeilDiv_eq_packedChunkCount (len width : Nat) (hw : 0 < width) :
    GenericSelect.selectCeilDiv len width = packedChunkCount len width := by
  have hdiv : len / width * width + len % width = len := by
    have := Nat.mod_add_div len width
    rw [Nat.mul_comm width] at this
    omega
  have hmod := Nat.mod_lt len hw
  have hexp : len + width - 1 = (len % width + width - 1) + len / width * width := by
    omega
  unfold GenericSelect.selectCeilDiv packedChunkCount
  rw [hexp, Nat.add_mul_div_right _ _ hw]
  by_cases hz : len % width = 0
  · rw [if_pos hz, hz]
    simp only [Nat.zero_add, Nat.add_zero]
    rw [Nat.div_eq_of_lt (by omega), Nat.zero_add]
  · rw [if_neg hz]
    have he : len % width + width - 1 = (len % width - 1) + width := by omega
    rw [he, Nat.add_div_right _ hw, Nat.div_eq_of_lt (by omega)]
    omega

/-- The stored descriptor formula for one component, ready for scalar-source
selection. Its five entries are read independently of any semantic store. -/
def interiorDescriptorSpan (n lc sc index : Nat)
    (component : PackedReviewerInteriorComponentTag) : Option NumericSpan :=
  let fields := interiorDescriptor n lc sc component
  interiorSpan index (fields[0]?.getD 0) (fields[1]?.getD 0) (fields[2]?.getD 0)
    (fields[3]?.getD 0) (fields[4]?.getD 0) (packedBpCodeWordWidth n)

theorem interiorDescriptorSpan_eq (n lc sc index : Nat)
    (component : PackedReviewerInteriorComponentTag) :
    interiorDescriptorSpan n lc sc index component =
      if packedReviewerInteriorComponentWordPrefix n component ≤ index ∧
          index - packedReviewerInteriorComponentWordPrefix n component <
            packedReviewerInteriorComponentWordCount n component then
        let location := packedReviewerInteriorLocation n component
          (index - packedReviewerInteriorComponentWordPrefix n component)
        some ⟨packedReviewerClosedInteriorBitAddress n lc sc location, location.readWidth⟩
      else none := by
  have hw : 0 < packedBpCodeWordWidth n := SuccinctRank.machineWordBits_pos _
  simp [interiorDescriptorSpan, interiorDescriptor, interiorSpan,
    selectCeilDiv_eq_packedChunkCount _ _ hw, packedReviewerInteriorLocation,
    packedEntryChunkBitOffset, packedEntryChunkReadWidth,
    packedReviewerClosedInteriorBitAddress, Nat.add_assoc]

private theorem interiorClassify_of_component_range (n index : Nat)
    (component : PackedReviewerInteriorComponentTag)
    (hp : packedReviewerInteriorComponentWordPrefix n component ≤ index)
    (hi : index - packedReviewerInteriorComponentWordPrefix n component <
      packedReviewerInteriorComponentWordCount n component) :
    packedReviewerInteriorClassify n index =
      some (packedReviewerInteriorLocation n component
        (index - packedReviewerInteriorComponentWordPrefix n component)) := by
  cases component <;>
    simp only [packedReviewerInteriorComponentWordPrefix, packedReviewerInteriorComponentWordCount_eq,
      packedInteriorOffsets] at hp hi ⊢ <;>
    simp only [packedReviewerInteriorClassify, packedInteriorOffsets,
      packedInteriorComponentWords, Nat.sub_zero] <;>
    generalize packedBaselineWords n = a at hp hi ⊢ <;>
    generalize packedMinRelWords n = b at hp hi ⊢ <;>
    generalize packedMaxRelWords n = c at hp hi ⊢ <;>
    generalize packedArgOffsetWords n = d at hp hi ⊢ <;>
    generalize packedLocalTableWords n = e at hp hi ⊢ <;>
    generalize packedGlobalTableWords n = f at hp hi ⊢ <;>
    generalize packedLocalLevelWords n = g at hp hi ⊢ <;>
    generalize packedGlobalLevelWords n = h at hp hi ⊢ <;>
    simp (disch := omega) only [if_pos, if_neg]

private theorem interiorDescriptorSpan_of_classify (n lc sc index : Nat)
    (location : PackedReviewerInteriorLocation)
    (hc : packedReviewerInteriorClassify n index = some location) :
    interiorDescriptorSpan n lc sc index location.component =
      some ⟨packedReviewerClosedInteriorBitAddress n lc sc location, location.readWidth⟩ := by
  obtain ⟨hloc, hindex, hlocal⟩ := packedReviewerInteriorClassify_sound hc
  have hp : packedReviewerInteriorComponentWordPrefix n location.component ≤ index := by omega
  have he : index - packedReviewerInteriorComponentWordPrefix n location.component =
      location.localWordIndex := by omega
  rw [interiorDescriptorSpan_eq, if_pos (by simpa [he] using And.intro hp hlocal)]
  simp only [he, ← hloc]

private theorem interiorDescriptorSpan_some_classify (n lc sc index : Nat)
    (component : PackedReviewerInteriorComponentTag) (span : NumericSpan)
    (hs : interiorDescriptorSpan n lc sc index component = some span) :
    (packedReviewerInteriorClassify n index).map
      (fun location => (⟨packedReviewerClosedInteriorBitAddress n lc sc location,
        location.readWidth⟩ : NumericSpan)) = some span := by
  rw [interiorDescriptorSpan_eq] at hs
  split at hs
  next h =>
    rw [interiorClassify_of_component_range n index component h.1 h.2]
    exact hs
  next h => simp at hs

/-- The first successful stored interior descriptor agrees with the existing
closed classifier, for every index and every numeric pair of counts. -/
theorem reviewerLogicalSpan_interior_descriptors (n lc sc index : Nat) :
    reviewerLogicalSpan n lc sc 20 index =
      interiorComponents.findSome? (interiorDescriptorSpan n lc sc index) := by
  rw [reviewerLogicalSpan_interior]
  cases hc : packedReviewerInteriorClassify n index with
  | none =>
      symm
      apply List.findSome?_eq_none_iff.mpr
      intro component hcomponent
      cases hs : interiorDescriptorSpan n lc sc index component with
      | none => rfl
      | some span =>
          have bad := interiorDescriptorSpan_some_classify n lc sc index component span hs
          simp [hc] at bad
  | some location =>
      have hmem : location.component ∈ interiorComponents := by
        cases location.component <;> simp [interiorComponents]
      have hselected := interiorDescriptorSpan_of_classify n lc sc index location hc
      cases hf : interiorComponents.findSome? (interiorDescriptorSpan n lc sc index) with
      | none =>
          have hn := List.findSome?_eq_none_iff.mp hf location.component hmem
          rw [hselected] at hn
          cases hn
      | some span =>
          obtain ⟨component, hcomponent, hs⟩ := List.exists_of_findSome?_eq_some hf
          have hs' := interiorDescriptorSpan_some_classify n lc sc index component span hs
          simpa [hc] using hs'

private def legacySpan (n lc sc : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) : NumericSpan :=
  let base := match source with
    | .bpCode | .finalRankBPCodeAlias => packedReviewerCellWidth n
    | _ => packedReviewerClosedStridedBitAddress n lc source 0 (packedSourceStride n source)
  ⟨base + index * packedSourceStride n source,
    packedReviewerSourceReadWidth n lc sc source index⟩

private theorem legacySpan_plan (n lc sc : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    packedReviewerLegacyRawPlan n lc sc source index =
      packedReviewerProbePlan n (legacySpan n lc sc source index).position
        (legacySpan n lc sc source index).length := by
  cases source <;>
    simp [packedReviewerLegacyRawPlan, packedReviewerBPRawPlan, packedReviewerClosedSourceReadPlan,
      legacySpan, packedReviewerBPBitAddress, packedReviewerBPReadWidth,
      packedReviewerSourceReadWidth, packedSourceReadWidth, packedReviewerSourceBitLength,
      packedSourceBitLength, packedReviewerClosedStridedBitAddress]

private theorem legacySpan_decode (n lc sc : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat)
    (cells : List (List Bool)) :
    packedReviewerLegacyDecode n lc sc source index cells =
      packedReviewerDecodeSpan n (legacySpan n lc sc source index).position
        (legacySpan n lc sc source index).length cells := by
  cases source <;>
    simp [packedReviewerLegacyDecode, legacySpan, packedReviewerBPBitAddress,
      packedReviewerBPReadWidth, packedReviewerSourceReadWidth, packedSourceReadWidth,
      packedReviewerSourceBitLength, packedSourceBitLength,
      packedReviewerClosedStridedBitAddress]

private theorem regularDescriptorSpan_legacy (n lc sc segment index : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hsegment : segment < 20) (hsource : packedSegmentSource? segment = some source) :
    regularDescriptorSpan n lc sc segment index =
      if index < packedReviewerLegacyWordCount n lc sc source then
        some (legacySpan n lc sc source index) else none := by
  have h20 : segment ≠ 20 := by omega
  have h21 : segment ≠ 21 := by omega
  have h22 : segment ≠ 22 := by omega
  simp [regularDescriptorSpan, regularDescriptor, h20, h21, h22, hsource,
    regularSpan, legacySpan, packedReviewerSourceReadWidth]
  rfl

private theorem min_remaining_eq_width (index count width : Nat) (hi : index < count) :
    min width (count * width - index * width) = width := by
  have hm := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hm
  exact Nat.min_eq_left (by omega)

private theorem regularDescriptorSpan_fringe (n lc sc index : Nat) :
    regularDescriptorSpan n lc sc 21 index =
      if index < packedReviewerFringeCount n then
        some ⟨packedReviewerClosedFringeAddress n lc sc index, packedReviewerFringeWidth n⟩
      else none := by
  by_cases hi : index < packedReviewerFringeCount n
  · simp [regularDescriptorSpan, regularDescriptor, regularSpan, hi,
      min_remaining_eq_width _ _ _ hi, packedReviewerClosedFringeAddress]
  · simp [regularDescriptorSpan, regularDescriptor, regularSpan, hi]

private theorem regularDescriptorSpan_select (n lc sc index : Nat) :
    regularDescriptorSpan n lc sc 22 index =
      if index < packedReviewerSelectChunkCount n then
        some ⟨packedReviewerClosedSelectChunkAddress n lc sc index,
          packedReviewerSelectChunkWidth n⟩
      else none := by
  by_cases hi : index < packedReviewerSelectChunkCount n
  · simp [regularDescriptorSpan, regularDescriptor, regularSpan, hi,
      min_remaining_eq_width _ _ _ hi, packedReviewerClosedSelectChunkAddress]
  · simp [regularDescriptorSpan, regularDescriptor, regularSpan, hi]

/-- Scalar geometry gives exactly the old physical plan and old decoder
expression. This identifies the logical slice, not old/new probe occurrences. -/
theorem reviewerLogicalSpan_old_geometry (n lc sc : Nat)
    (request : PackedReviewerLogicalRequest) :
    packedReviewerLogicalPlan n lc sc request =
      ((reviewerLogicalSpan n lc sc request.segment request.index).map fun span =>
        spanPlan (packedReviewerCellWidth n) span.position span.length).getD [] ∧
    (∀ cells, packedReviewerLogicalDecode n lc sc request cells =
      (reviewerLogicalSpan n lc sc request.segment request.index).map fun span =>
        packedReviewerDecodeSpan n span.position span.length cells) := by
  rcases request with ⟨invocation, site, segment, index⟩
  dsimp only
  by_cases hlarge : 23 ≤ segment
  · obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hlarge
    rw [Nat.add_comm] at hoffset
    subst segment
    have hn : ¬offset + 23 < 20 := by omega
    have hn23 : ¬offset + 23 < 23 := by omega
    simp [packedReviewerLogicalPlan, packedReviewerLogicalDecode, reviewerLogicalSpan, hn, hn23]
  · have hs : segment = 0 ∨ segment = 1 ∨ segment = 2 ∨ segment = 3 ∨
        segment = 4 ∨ segment = 5 ∨ segment = 6 ∨ segment = 7 ∨ segment = 8 ∨
        segment = 9 ∨ segment = 10 ∨ segment = 11 ∨ segment = 12 ∨ segment = 13 ∨
        segment = 14 ∨ segment = 15 ∨ segment = 16 ∨ segment = 17 ∨ segment = 18 ∨
        segment = 19 ∨ segment = 20 ∨ segment = 21 ∨ segment = 22 := by omega
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals solve
    | (simp only [reviewerLogicalSpan_interior, packedReviewerLogicalPlan,
        packedReviewerLogicalDecode, packedReviewerClosedInteriorReadPlan]
       cases packedReviewerInteriorClassify n index <;>
         simp [packedReviewerClosedInteriorLocationPlan, packedReviewerProbePlan, spanPlan])
    | (rw [reviewerLogicalSpan_regular _ _ _ _ _ (by decide) (by decide),
        regularDescriptorSpan_fringe]
       split <;> simp [packedReviewerLogicalPlan, packedReviewerLogicalDecode,
         packedReviewerProbePlan, spanPlan, *])
    | (rw [reviewerLogicalSpan_regular _ _ _ _ _ (by decide) (by decide),
        regularDescriptorSpan_select]
       split <;> simp [packedReviewerLogicalPlan, packedReviewerLogicalDecode,
         packedReviewerProbePlan, spanPlan, *])
    | (rw [reviewerLogicalSpan_regular _ _ _ _ _ (by decide) (by decide),
        regularDescriptorSpan_legacy _ _ _ _ _ _ (by decide) rfl]
       split <;> simp [packedReviewerLogicalPlan, packedReviewerLogicalDecode,
         packedSegmentSource?, concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
         legacySpan_plan, legacySpan_decode,
         packedReviewerProbePlan, spanPlan, *])

/-- The existing all-segment decoder width theorem constrains the requested
span itself: a sufficiently long proof-side bit window realizes its length. -/
theorem reviewerLogicalSpan_length_le (n lc sc : Nat)
    (request : PackedReviewerLogicalRequest) (span : NumericSpan)
    (hspan : reviewerLogicalSpan n lc sc request.segment request.index = some span) :
    span.length ≤ packedReviewerCellWidth n := by
  let cells : List (List Bool) :=
    [List.replicate (span.position % packedReviewerCellWidth n + span.length) false]
  have hd := (reviewerLogicalSpan_old_geometry n lc sc request).2 cells
  rw [hspan, Option.map_some] at hd
  have hw := packedReviewerLogicalDecode_word_fits n lc sc request cells
    (packedReviewerDecodeSpan n span.position span.length cells) hd
  simpa [PackedReviewerWordFits, packedReviewerDecodeSpan, cells] using hw

/-- Nonempty one/two-cell plans inside a full-word allocation bound the
requested bit span. Empty plans intentionally imply no position bound. -/
private theorem spanPlan_fits_of_addresses (width position len count : Nat)
    (hw : 0 < width) (hlen : len ≤ width) (hpos : 0 < len)
    (hplan : ∀ address ∈ spanPlan width position len, address < count) :
    position + len ≤ count * width := by
  have hz : len ≠ 0 := by omega
  have hmod := Nat.mod_lt position hw
  have hdiv : position / width * width + position % width = position := by
    have := Nat.mod_add_div position width
    rw [Nat.mul_comm width] at this
    omega
  by_cases hc : position % width + len ≤ width
  · have ha := hplan (position / width) (by simp [spanPlan, hz, hc])
    have hm := Nat.mul_le_mul_right width (Nat.succ_le_of_lt ha)
    rw [Nat.succ_mul] at hm
    omega
  · have ha := hplan (position / width + 1) (by simp [spanPlan, hz, hc])
    have hm := Nat.mul_le_mul_right width (Nat.succ_le_of_lt ha)
    simp only [Nat.succ_mul] at hm
    omega

/-- Canonical plan-fetch correctness supplies the position bound for every
positive logical span; zero-length logical sentinels remain explicit. -/
theorem reviewerLogicalSpan_canonical_fits (shape : CartesianShape)
    (request : PackedReviewerLogicalRequest) (span : NumericSpan)
    (hspan : reviewerLogicalSpan shape.size (longCount shape) (packedReviewerSparseCount shape)
      request.segment request.index = some span) :
    span.position + span.length ≤ (packedReviewerMemory shape).flatten.length ∨ span.length = 0 := by
  by_cases hz : span.length = 0
  · exact Or.inr hz
  apply Or.inl
  have hw := reviewerLogicalSpan_length_le shape.size (longCount shape)
    (packedReviewerSparseCount shape) request span hspan
  have hgeom := (reviewerLogicalSpan_old_geometry shape.size (longCount shape)
    (packedReviewerSparseCount shape) request).1
  rw [hspan, Option.map_some, Option.getD_some] at hgeom
  have hb := spanPlan_fits_of_addresses (packedReviewerCellWidth shape.size)
    span.position span.length
    (packedReviewerCellCount shape.size (longCount shape) (packedReviewerSparseCount shape))
    (packedReviewerCellWidth_pos shape.size) hw (by omega) (by
      intro address ha
      exact packedReviewerLogicalPlan_address_lt_cellCount shape request (by rw [hgeom]; exact ha))
  rw [uniform_flatten_length (packedReviewerMemory shape) (packedReviewerCellWidth shape.size)
    (fun cell hc => packedReviewerMemory_cell_length shape hc), packedReviewerMemory_length]
  exact hb

private theorem reviewerLogicalRead_eq_spanFetch (n lc sc : Nat)
    (memory : List (List Bool)) (request : PackedReviewerLogicalRequest) :
    packedReviewerLogicalRead n lc sc memory request =
      (reviewerLogicalSpan n lc sc request.segment request.index).bind fun span =>
        (packedFetch memory (spanPlan (packedReviewerCellWidth n) span.position span.length)).map
          (packedReviewerDecodeSpan n span.position span.length) := by
  obtain ⟨hp, hd⟩ := reviewerLogicalSpan_old_geometry n lc sc request
  unfold packedReviewerLogicalRead
  rw [hp]
  cases hs : reviewerLogicalSpan n lc sc request.segment request.index with
  | none => simpa [hs, packedFetch] using hd []
  | some span =>
      simp only [Option.map_some, Option.getD_some, Option.bind_some]
      cases hf : packedFetch memory (spanPlan (packedReviewerCellWidth n) span.position span.length)
      · rfl
      · simpa [hs] using hd _

private theorem canonical_spanFetch (shape : CartesianShape) (span : NumericSpan)
    (hw : span.length ≤ packedReviewerCellWidth shape.size)
    (hfit : span.position + span.length ≤ (packedReviewerMemory shape).flatten.length ∨
      span.length = 0) :
    (packedFetch (packedReviewerMemory shape)
      (spanPlan (packedReviewerCellWidth shape.size) span.position span.length)).map
        (packedReviewerDecodeSpan shape.size span.position span.length) =
      some (((packedReviewerMemory shape).flatten.drop span.position).take span.length) := by
  rcases hfit with hfit | hz
  · have hb : span.position + span.length ≤ packedReviewerAllocatedBits shape.size
        (longCount shape) (packedReviewerSparseCount shape) := by
      rwa [packedReviewerMemory_flatten, packedReviewerPaddedBits_length] at hfit
    simpa only [spanPlan, packedReviewerProbePlan, packedReviewerMemory_flatten] using
      packedReviewerProbePlan_decode shape hw hb
  · simp [spanPlan, hz, packedFetch, packedReviewerDecodeSpan]

/-- Every canonical logical reply is preserved as its exact numeric value and
actual bit length on the same `shapeMemory` counted by the space theorem. -/
theorem directLogicalReadNat_eq_reviewer (shape : CartesianShape)
    (request : PackedReviewerLogicalRequest) :
    directLogicalReadNat shape.size (longCount shape) (packedReviewerSparseCount shape)
      (shapeMemory shape) request.segment request.index =
      (packedReviewerLogicalRead shape.size (longCount shape) (packedReviewerSparseCount shape)
        (packedReviewerMemory shape) request).map fun bits => (bitsToNatLE bits, bits.length) := by
  rw [reviewerLogicalRead_eq_spanFetch]
  unfold directLogicalReadNat
  cases hs : reviewerLogicalSpan shape.size (longCount shape) (packedReviewerSparseCount shape)
      request.segment request.index with
  | none => rfl
  | some span =>
      have hw := reviewerLogicalSpan_length_le shape.size (longCount shape)
        (packedReviewerSparseCount shape) request span hs
      have hfit := reviewerLogicalSpan_canonical_fits shape request span hs
      have hnew := decodeSpanNat_repacked_span (metadata shape) (wordWidth shape.size)
        (packedReviewerMemory shape) span.position span.length (wordWidth_pos shape.size)
        (Nat.le_trans hw (Nat.le_of_lt (oldWidth_lt_wordWidth shape.size))) hfit
      rw [metadata_length] at hnew
      have hold := canonical_spanFetch shape span hw hfit
      have hlength : (((packedReviewerMemory shape).flatten.drop span.position).take
          span.length).length = span.length := by
        rcases hfit with hb | hz
        · rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
        · simp [hz]
      simp only [Option.bind_some, shapeMemory, hnew, hold, Option.map_some, hlength]

theorem directLogicalReadNat_eq_globalReadStore (shape : CartesianShape) (segment index : Nat) :
    directLogicalReadNat shape.size (longCount shape) (packedReviewerSparseCount shape)
      (shapeMemory shape) segment index =
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index).map
        fun bits => (bitsToNatLE bits, bits.length) := by
  let request : PackedReviewerLogicalRequest :=
    ⟨⟨.leftSelect, 0, 0⟩, .entryBaseOccurrence, segment, index⟩
  have h := directLogicalReadNat_eq_reviewer shape request
  rwa [packedReviewerLogicalRead_eq_globalReadStore] at h

/-- A present empty word is a successful zero reply, even beyond the memory's
nominal endpoint. It is distinct from an absent logical word. -/
theorem directLogicalReadNat_zero (n lc sc segment index position : Nat) (memory : List Nat)
    (hspan : reviewerLogicalSpan n lc sc segment index = some ⟨position, 0⟩) :
    directLogicalReadNat n lc sc memory segment index = some (0, 0) := by
  simp [directLogicalReadNat, hspan]

theorem directLogicalReadNat_dead_interior (n lc sc : Nat) (memory : List Nat) :
    directLogicalReadNat n lc sc memory 20 (packedInteriorComponentWords n) = none := by
  simp [directLogicalReadNat, reviewerLogicalSpan_interior,
    packedReviewerInteriorClassify_deadAddress]

theorem reviewerLogicalSpan_empty_alias (lc sc : Nat) :
    reviewerLogicalSpan 0 lc sc 19 0 = some ⟨packedReviewerCellWidth 0, 0⟩ := by
  rw [reviewerLogicalSpan_regular _ _ _ _ _ (by decide) (by decide),
    regularDescriptorSpan_legacy _ _ _ _ _ _ (by decide) rfl]
  simp [packedReviewerLegacyWordCount, packedReviewerSourceWordCount,
    packedSourceWordCount, packedChunkCount, legacySpan,
    packedReviewerSourceReadWidth, packedReviewerSourceBitLength, packedSourceBitLength]

theorem directLogicalReadNat_empty_alias (lc sc : Nat) (memory : List Nat) :
    directLogicalReadNat 0 lc sc memory 19 0 = some (0, 0) :=
  directLogicalReadNat_zero _ _ _ _ _ _ _ (reviewerLogicalSpan_empty_alias lc sc)

/-- Independently spelled expected type pins the public all-segment theorem. -/
theorem logicalSpan_canonical_consumer : ∀ (shape : CartesianShape) (segment index : Nat),
    directLogicalReadNat shape.size (longCount shape) (packedReviewerSparseCount shape)
      (shapeMemory shape) segment index =
    Option.map (fun bits => (bitsToNatLE bits, List.length bits))
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index) := by
  intro shape segment index
  exact directLogicalReadNat_eq_globalReadStore shape segment index

theorem logicalSpan_empty_consumer (segment index : Nat) :
    directLogicalReadNat CartesianShape.empty.size (longCount .empty)
      (packedReviewerSparseCount .empty) (shapeMemory .empty) segment index =
    Option.map (fun bits => (bitsToNatLE bits, List.length bits))
      ((concreteBPNativeSuccinctRMQGlobalReadStore .empty).readWord? segment index) :=
  directLogicalReadNat_eq_globalReadStore .empty segment index

theorem logicalSpan_singleton_consumer (segment index : Nat) :
    directLogicalReadNat (CartesianShape.node .empty .empty).size
      (longCount (.node .empty .empty)) (packedReviewerSparseCount (.node .empty .empty))
      (shapeMemory (.node .empty .empty)) segment index =
    Option.map (fun bits => (bitsToNatLE bits, List.length bits))
      ((concreteBPNativeSuccinctRMQGlobalReadStore (.node .empty .empty)).readWord? segment index) :=
  directLogicalReadNat_eq_globalReadStore (.node .empty .empty) segment index

theorem logicalSpan_empty_sentinel_consumer :
    directLogicalReadNat CartesianShape.empty.size (longCount .empty)
      (packedReviewerSparseCount .empty) (shapeMemory .empty) 19 0 = some (0, 0) :=
  directLogicalReadNat_empty_alias _ _ _

theorem logicalSpan_dead_interior_consumer (shape : CartesianShape) :
    directLogicalReadNat shape.size (longCount shape) (packedReviewerSparseCount shape)
      (shapeMemory shape) 20 (packedInteriorComponentWords shape.size) = none :=
  directLogicalReadNat_dead_interior _ _ _ _

end RMQ.SuccinctFinal.PackedWordRAM
