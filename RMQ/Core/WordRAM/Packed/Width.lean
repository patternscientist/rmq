import RMQ.Core.WordRAM.Packed.Allocation

/-!+# Width of the actual counted metadata and repacked allocation

The polynomial envelope is a proof bound for the concrete fields. It adds no
machine state and makes no claim about registers or instruction operands.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian PackedCellProbe SuccinctSpace

def metadataEnvelope (n : Nat) : Nat :=
  64 * (2 ^ packedReviewerCellWidth n) ^ 2

theorem metadataEnvelope_lt_wordCapacity (n : Nat) :
    metadataEnvelope n < 2 ^ wordWidth n := by
  have h : 6 + packedReviewerCellWidth n * 2 < wordWidth n := by
    unfold wordWidth
    omega
  have heq : metadataEnvelope n = 2 ^ (6 + packedReviewerCellWidth n * 2) := by
    simp [metadataEnvelope, Nat.pow_add, Nat.pow_mul]
  rw [heq]
  exact Nat.pow_lt_pow_right (by omega) h

private theorem ceilDiv_le_self (a b : Nat) (hb : 0 < b) :
    GenericSelect.selectCeilDiv a b ≤ a := by
  by_cases ha : a = 0
  · subst a
    simp only [GenericSelect.selectCeilDiv, Nat.zero_add]
    have h : b - 1 < b := by omega
    rw [Nat.div_eq_of_lt h]
    omega
  · exact GenericSelect.selectCeilDiv_le_self_of_pos (by omega) hb

private theorem oldWidth_le_square (n : Nat) :
    packedReviewerCellWidth n ≤ (2 ^ packedReviewerCellWidth n) ^ 2 := by
  have hw := Nat.lt_two_pow_self (n := packedReviewerCellWidth n)
  have hp := Nat.two_pow_pos (packedReviewerCellWidth n)
  have hmul := Nat.le_mul_of_pos_right (2 ^ packedReviewerCellWidth n) hp
  simpa only [Nat.pow_two] using Nat.le_trans (Nat.le_of_lt hw) hmul

private theorem four_le_square (n : Nat) :
    4 ≤ (2 ^ packedReviewerCellWidth n) ^ 2 := by
  have hw := packedReviewerCellWidth_pos n
  have hp : 2 ≤ 2 ^ packedReviewerCellWidth n := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hw
    simpa using this
  have := Nat.mul_le_mul hp hp
  simpa [Nat.pow_two] using this

private theorem bpWidth_le_old (n : Nat) :
    packedBpCodeWordWidth n ≤ packedReviewerCellWidth n := by
  apply packedReviewerMachineWordBits_le_cellWidth
  have := packedTwoMul_le_reviewerBound n
  omega

private theorem payload_lt_oldCapacity (shape : CartesianShape) :
    packedReviewerPayloadLength shape.size (longCount shape)
      (packedReviewerSparseCount shape) < 2 ^ packedReviewerCellWidth shape.size := by
  have h := packedReviewerPayloadLength_le_bound shape
  have hc := packedReviewerCellBound_lt_two_pow_width shape.size
  unfold packedReviewerCellBound at hc
  omega

theorem interiorEntryWidth_le_seven (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) :
    packedReviewerInteriorEntryWidth shape.size component ≤
      7 * packedBpCodeWordWidth shape.size := by
  cases component with
  | baseline =>
      have hword := packedBpCodeWordWidth_pos shape.size
      simp only [packedReviewerInteriorEntryWidth]
      omega
  | minRel | maxRel | argOffset =>
      simpa [packedReviewerInteriorEntryWidth, packedBpCodeWordWidth,
        packedInteriorLayout_eq, CartesianShape.bpCode_length] using
        SuccinctClose.canonicalRelativeRmmRelativeWidth_le_seven_machine shape
  | localOffset =>
      simpa [packedReviewerInteriorEntryWidth, packedBpCodeWordWidth,
        packedInteriorLayout_eq, CartesianShape.bpCode_length] using
        SuccinctClose.canonicalRelativeRmmOffsetWidth_le_seven_machine shape
  | globalBlock =>
      simpa [packedReviewerInteriorEntryWidth, packedBpCodeWordWidth,
        packedInteriorLayout_eq, CartesianShape.bpCode_length] using
        SuccinctClose.canonicalRelativeRmmBlockWidth_le_seven_machine shape
  | localLevel =>
      simpa [packedReviewerInteriorEntryWidth, packedBpCodeWordWidth,
        packedInteriorLayout_eq, CartesianShape.bpCode_length] using
        SuccinctClose.bpSparseLevelLocalWidth_le_seven_machine shape
  | globalLevel =>
      simpa [packedReviewerInteriorEntryWidth, packedBpCodeWordWidth,
        packedInteriorLayout_eq, CartesianShape.bpCode_length] using
        SuccinctClose.bpSparseLevelGlobalWidth_le_seven_machine shape

theorem interiorComponentWordSpan_le_dead (n : Nat)
    (component : PackedReviewerInteriorComponentTag) :
    packedReviewerInteriorComponentWordPrefix n component +
      packedReviewerInteriorComponentWordCount n component ≤
        (packedInteriorOffsets n).deadAddress := by
  cases component <;>
    simp [packedReviewerInteriorComponentWordPrefix,
      packedReviewerInteriorComponentWordCount_eq, packedInteriorOffsets,
      packedInteriorComponentWords] <;> omega

private theorem interiorBitPrefix_le_payload (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) :
    packedReviewerClosedInteriorOffset shape.size (longCount shape)
        (packedReviewerSparseCount shape) +
      packedReviewerInteriorComponentBitPrefix shape.size component ≤
      packedReviewerPayloadLength shape.size (longCount shape)
        (packedReviewerSparseCount shape) := by
  obtain ⟨suffix, hs⟩ := packedReviewerInteriorDirectory_decompose shape component
  have hlen := congrArg List.length hs
  rw [SuccinctClose.canonicalRelativeRmmInteriorDirectory_payload_length_eq_raw,
    List.length_append, List.length_append,
    ← packedReviewerInteriorComponentBitPrefix_eq] at hlen
  unfold packedReviewerClosedInteriorOffset packedReviewerPayloadLength
  rw [packedReviewerClosedAccessLength_eq]
  omega

theorem interiorDescriptor_le_envelope (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) {word : Nat}
    (hword : word ∈ interiorDescriptor shape.size (longCount shape)
      (packedReviewerSparseCount shape) component) :
    word ≤ metadataEnvelope shape.size := by
  have hspan := interiorComponentWordSpan_le_dead shape.size component
  have hdead := packedReviewerInteriorDeadAddress_lt_two_pow_of_shape shape
  have hprefix := interiorBitPrefix_le_payload shape component
  have hpay := payload_lt_oldCapacity shape
  have hentry := interiorEntryWidth_le_seven shape component
  have hbp := bpWidth_le_old shape.size
  have hw := oldWidth_le_square shape.size
  have hpow := Nat.le_mul_of_pos_right (2 ^ packedReviewerCellWidth shape.size)
    (Nat.two_pow_pos (packedReviewerCellWidth shape.size))
  have hceil := ceilDiv_le_self (packedReviewerInteriorEntryWidth shape.size component)
    (packedBpCodeWordWidth shape.size) (packedBpCodeWordWidth_pos shape.size)
  simp only [interiorDescriptor, List.mem_cons, List.not_mem_nil, or_false] at hword
  unfold metadataEnvelope
  simp only [Nat.pow_two] at *
  rcases hword with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem scalarGeometry_le_envelope (shape : CartesianShape) :
    ∀ word ∈ scalarMetadata shape, word ≤ metadataEnvelope shape.size := by
  let n := shape.size
  let w := packedReviewerCellWidth n
  let q := 2 ^ w
  have hq : 2 ≤ q := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) (packedReviewerCellWidth_pos n)
    simpa [q, w] using this
  have hq2 : q ≤ q ^ 2 := by
    simpa [Nat.pow_two] using Nat.le_mul_of_pos_right q (by omega)
  have hsq : 4 ≤ q ^ 2 := four_le_square n
  have hw : w < q := Nat.lt_two_pow_self
  have hn : n + 1 ≤ q := packedReviewerInputSize_lt_two_pow_cellWidth n
  have hbp : packedBpCodeWordWidth n ≤ w := bpWidth_le_old n
  have hcount : packedReviewerCellCount n (longCount shape)
      (packedReviewerSparseCount shape) < q :=
    packedReviewerSparsePreludeCellCount_lt_two_pow_reviewerWidth shape
  have hbits : packedReviewerCellCount n (longCount shape)
      (packedReviewerSparseCount shape) * w ≤ q ^ 2 := by
    simpa [Nat.pow_two] using Nat.mul_le_mul (Nat.le_of_lt hcount) (Nat.le_of_lt hw)
  have hceil := ceilDiv_le_self
    (packedReviewerCellCount n (longCount shape) (packedReviewerSparseCount shape) * w)
    (wordWidth n) (wordWidth_pos n)
  have hlong : longCount shape < q := longCount_lt_two_pow_reviewerWidth shape
  have hsparse : packedReviewerSparseCount shape < q :=
    packedReviewerSparseCount_lt_two_pow_reviewerWidth shape
  have hsuper := packedSuperSlots_le_input n
  have hslots := packedSparseSlots_le_input n
  have hbound := packedTwoMul_le_reviewerBound n
  have hlongW : packedLongFlagWordSize n ≤ w := by
    apply packedReviewerMachineWordBits_le_cellWidth
    omega
  have hsparseW : packedSparseWordSize n ≤ w := by
    apply packedReviewerMachineWordBits_le_cellWidth
    omega
  have hselect : packedSelectWordSize n = packedBpCodeWordWidth n := rfl
  have hss : packedSelectSuperStride n ≤ q ^ 2 := by
    change packedBpCodeWordWidth n * packedBpCodeWordWidth n ≤ q ^ 2
    simpa [Nat.pow_two] using Nat.mul_le_mul (by omega : packedBpCodeWordWidth n ≤ q)
      (by omega : packedBpCodeWordWidth n ≤ q)
  have hls : packedSelectLocalStride n ≤ packedBpCodeWordWidth n := by
    unfold packedSelectLocalStride GenericSelect.localStride
    apply Nat.max_le.mpr
    exact ⟨packedBpCodeWordWidth_pos n, Nat.div_le_self _ _⟩
  have hlps : packedSelectLocalSlotsPerSuper n ≤ packedSelectSuperStride n :=
    ceilDiv_le_self _ _ (GenericSelect.localStride_pos _)
  have hbase : packedSummaryBase n ≤ w := by
    apply packedReviewerMachineWordBits_le_cellWidth
    omega
  have hblocks : (packedInteriorLayout n).blockCount ≤ n := Nat.div_le_self _ _
  have hsuperSample : (packedInteriorLayout n).superSampleCount ≤ n + 1 := by
    have := Nat.div_le_self (packedInteriorLayout n).blockCount
      (packedInteriorLayout n).blocksPerSuper
    unfold SuccinctClose.RelativeRmm.Layout.superSampleCount
    omega
  have hmacro : (packedInteriorLayout n).macroSize ≤ q ^ 2 := by
    change packedSummaryBase n * packedSummaryBase n ≤ q ^ 2
    simpa [Nat.pow_two] using Nat.mul_le_mul (by omega : packedSummaryBase n ≤ q)
      (by omega : packedSummaryBase n ≤ q)
  have hmacroSample : (packedInteriorLayout n).macroSampleCount ≤ n + 1 := by
    have := Nat.div_le_self (packedInteriorLayout n).blockCount
      (packedInteriorLayout n).macroSize
    unfold SuccinctClose.RelativeRmm.Layout.macroSampleCount
    omega
  have hglobalLevel : (packedInteriorLayout n).globalLevelCount ≤ w := by
    apply packedReviewerMachineWordBits_le_cellWidth
    omega
  have hblockWidth : (packedInteriorLayout n).blockAddressWidth ≤ w := by
    apply packedReviewerMachineWordBits_le_cellWidth
    omega
  have hrelative := interiorEntryWidth_le_seven shape .minRel
  have hoffset := interiorEntryWidth_le_seven shape .localOffset
  have hlocalLevel := interiorEntryWidth_le_seven shape .localLevel
  have hglobalLevelWidth := interiorEntryWidth_le_seven shape .globalLevel
  simp only [packedReviewerInteriorEntryWidth] at hrelative hoffset hlocalLevel hglobalLevelWidth
  have hfringe : packedFringeChunkBits n ≤ packedBpCodeWordWidth n := by
    have := Nat.div_le_self (Nat.log2 (2 * n)) 8
    change Nat.log2 (2 * n) / 8 + 1 ≤ Nat.log2 (2 * n) + 1
    omega
  have hdead : (packedInteriorOffsets n).deadAddress < q :=
    packedReviewerInteriorDeadAddress_lt_two_pow_of_shape shape
  simp only [packedInteriorOffsets, packedInteriorComponentWords] at hdead
  intro word hword
  simp only [scalarMetadata, List.mem_cons, List.not_mem_nil, or_false] at hword
  change word ≤ 64 * q ^ 2
  simp only [packedInteriorOffsets, packedInteriorComponentWords, wordWidth,
    metadataWordCount, SuccinctClose.RelativeRmm.Layout.levelCount,
    SuccinctClose.bpSparseLevelDomain] at hword
  rcases hword with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [packedInteriorLayout, packedSummaryBlockSizeRaw,
    wordWidth, SuccinctClose.bpSparseLevelDomain] at *
  all_goals dsimp only [n, w, q] at *
  all_goals omega

private theorem chunkCount_le_succ (len stride : Nat) :
    packedChunkCount len stride ≤ len + 1 := by
  have hd := Nat.div_le_self len stride
  unfold packedChunkCount
  split <;> omega

private theorem legacyCount_le_twice_bits_add_two
    (n lc sc : Nat) (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hstride : 0 < packedSourceStride n source) :
    packedReviewerLegacyWordCount n lc sc source ≤
      2 * packedReviewerSourceBitLength n lc sc source + 2 := by
  have scaled (count stride : Nat) (hpos : 0 < stride) :
      count ≤ 2 * (count * stride) + 2 := by
    have h := Nat.le_mul_of_pos_right count hpos
    omega
  have hbp := chunkCount_le_succ (2*n) (packedBpCodeWordWidth n)
  have hlong := chunkCount_le_succ (packedSuperSlots n) (packedLongFlagWordSize n)
  have hsparse := chunkCount_le_succ (packedSparseSlots n) (packedSparseWordSize n)
  have halias := chunkCount_le_succ (2*n) (packedRankWordSize n)
  cases source <;>
    simp only [packedReviewerLegacyWordCount, packedReviewerSourceWordCount,
      packedReviewerSourceBitLength, packedSourceBitLength,
      reduceCtorEq, if_false, if_true]
  all_goals first
    | exact scaled _ _ hstride
    | (try simp only [packedSourceWordCount]; omega)

private theorem legacySource_info (segment : Nat) (hsegment : segment < 20)
    {source : ConcreteBPNativeSuccinctRMQFlatPayloadSource}
    (hsource : packedSegmentSource? segment = some source) :
    source = .bpCode ∨ source = .finalRankBPCodeAlias ∨
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
      10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 =>
      simp only [packedSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?, Option.some.injEq] at hsource
      subst source
      simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources]
  | _ + 20 => omega

private theorem legacyStride_pos (n : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hsource : source = .bpCode ∨ source = .finalRankBPCodeAlias ∨
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources) :
    0 < packedSourceStride n source := by
  cases source <;>
    simp_all [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources,
      packedSourceStride, packedBpCodeWordWidth, packedSuperWidth, packedLocalWidth,
      packedLongFlagWordSize, packedSparseWordSize, packedRankWordSize,
      packedRankBlockWidth, GenericSelect.wordBits, SuccinctRank.machineWordBits]

private theorem legacyBits_le_payload (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hsource : source = .bpCode ∨ source = .finalRankBPCodeAlias ∨
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources) :
    packedReviewerSourceBitLength shape.size (longCount shape)
        (packedReviewerSparseCount shape) source ≤
      packedReviewerPayloadLength shape.size (longCount shape)
        (packedReviewerSparseCount shape) := by
  rcases hsource with rfl | rfl | hmem
  · simp only [packedReviewerSourceBitLength, reduceCtorEq, if_false,
      packedSourceBitLength, packedReviewerPayloadLength]
    omega
  · simp only [packedReviewerSourceBitLength, reduceCtorEq, if_false,
      packedSourceBitLength, packedReviewerPayloadLength]
    omega
  · have h := packedReviewerSourceOffset_fits shape source hmem
    rw [packedReviewerSourceBitLength_eq] at h
    omega

theorem regularDescriptor_le_envelope (shape : CartesianShape)
    (segment : Nat) (hsegment : segment < 23) {word : Nat}
    (hword : word ∈ regularDescriptor shape.size (longCount shape)
      (packedReviewerSparseCount shape) segment) :
    word ≤ metadataEnvelope shape.size := by
  have hpay := payload_lt_oldCapacity shape
  have hw := oldWidth_le_square shape.size
  have hpow : 2 ^ packedReviewerCellWidth shape.size ≤
      (2 ^ packedReviewerCellWidth shape.size) ^ 2 := by
    simpa [Nat.pow_two] using Nat.le_mul_of_pos_right (2 ^ packedReviewerCellWidth shape.size)
      (Nat.two_pow_pos (packedReviewerCellWidth shape.size))
  have hsq := four_le_square shape.size
  unfold regularDescriptor at hword
  split at hword
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hword
    subst word
    omega
  · rename_i h20
    split at hword
    · have hf := packedReviewerFringeOffset_fits shape.size (longCount shape)
        (packedReviewerSparseCount shape)
      have hfw := packedFringeEntryWidth_le_reviewerCellWidth shape.size
      have hfc := packedReviewerFringeCount_lt_two_pow shape.size
      simp only [packedReviewerClosedFringeAddress,
        packedReviewerClosedFringeOffset_eq, Nat.zero_mul, Nat.add_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hword
      change packedReviewerFringeOffset shape.size (longCount shape)
        (packedReviewerSparseCount shape) +
        packedReviewerFringeCount shape.size * packedReviewerFringeWidth shape.size ≤ _ at hf
      change packedReviewerFringeWidth shape.size ≤ _ at hfw
      unfold metadataEnvelope
      rcases hword with rfl | rfl | rfl | rfl <;> omega
    · rename_i h21
      split at hword
      · have hf := packedReviewerSelectChunkOffset_fits shape.size (longCount shape)
          (packedReviewerSparseCount shape)
        have hfw := packedSelectChunkEntryWidth_le_reviewerCellWidth shape.size
        have hfc := packedReviewerSelectChunkCount_lt_two_pow shape.size
        simp only [packedReviewerClosedSelectChunkAddress,
          packedReviewerClosedSelectChunkOffset_eq, Nat.zero_mul, Nat.add_zero,
          List.mem_cons, List.not_mem_nil, or_false] at hword
        change packedReviewerSelectChunkOffset shape.size (longCount shape)
          (packedReviewerSparseCount shape) +
          packedReviewerSelectChunkCount shape.size * packedReviewerSelectChunkWidth shape.size ≤ _ at hf
        change packedReviewerSelectChunkWidth shape.size ≤ _ at hfw
        unfold metadataEnvelope
        rcases hword with rfl | rfl | rfl | rfl <;> omega
      · rename_i h22
        have hlegacy : segment < 20 := by omega
        cases hsource : packedSegmentSource? segment with
        | none =>
            simp only [hsource, List.mem_cons, List.not_mem_nil, or_false, or_self] at hword
            subst word
            omega
        | some source =>
            have hinfo := legacySource_info segment hlegacy hsource
            have hstride := legacyStride_pos shape.size source hinfo
            have hstrideLe := packedSourceStride_le_reviewerCellWidth shape.size source
              (packedReviewerSegmentSource_counted shape.size segment hlegacy hsource)
            have hbits := legacyBits_le_payload shape source hinfo
            have hcount := legacyCount_le_twice_bits_add_two shape.size (longCount shape)
              (packedReviewerSparseCount shape) source hstride
            have hbase :
                (match source with
                  | .bpCode | .finalRankBPCodeAlias => packedReviewerCellWidth shape.size
                  | _ => packedReviewerClosedStridedBitAddress shape.size (longCount shape)
                      source 0 (packedSourceStride shape.size source)) ≤
                packedReviewerCellWidth shape.size +
                  packedReviewerPayloadLength shape.size (longCount shape)
                    (packedReviewerSparseCount shape) := by
              rcases hinfo with rfl | rfl | hmem
              · simp
              · simp
              · have hoff := packedReviewerSourceOffset_fits shape source hmem
                have haddr := packedReviewerClosedStridedBitAddress_eq shape.size
                  (longCount shape) source 0 (packedSourceStride shape.size source) hmem
                simp only [packedReviewerStridedBitAddress, Nat.zero_mul, Nat.add_zero] at haddr
                split <;> omega
            simp only [hsource, List.mem_cons, List.not_mem_nil, or_false] at hword
            unfold metadataEnvelope
            rcases hword with rfl | rfl | rfl | rfl
            all_goals first
              | omega
              | (cases source <;> dsimp only at hbase ⊢ <;> omega)

theorem metadata_words_le_envelope (shape : CartesianShape) :
    ∀ word ∈ metadata shape, word ≤ metadataEnvelope shape.size := by
  intro word hword
  simp only [metadata, List.mem_append] at hword
  rcases hword with (hscalar | hregular) | hinterior
  · exact scalarGeometry_le_envelope shape word hscalar
  · obtain ⟨words, hwords, hword⟩ := List.mem_flatten.mp hregular
    obtain ⟨segment, hsegment, rfl⟩ := List.mem_map.mp hwords
    exact regularDescriptor_le_envelope shape segment (List.mem_range.mp hsegment) hword
  · obtain ⟨words, hwords, hword⟩ := List.mem_flatten.mp hinterior
    obtain ⟨component, _, rfl⟩ := List.mem_map.mp hwords
    exact interiorDescriptor_le_envelope shape component hword

theorem metadata_words_fit (shape : CartesianShape) :
    ∀ word ∈ metadata shape, word < 2 ^ wordWidth shape.size := by
  intro word hword
  exact Nat.lt_of_le_of_lt (metadata_words_le_envelope shape word hword)
    (metadataEnvelope_lt_wordCapacity shape.size)

theorem shapeMemory_words_fit (shape : CartesianShape) :
    ∀ word ∈ shapeMemory shape, word < 2 ^ wordWidth shape.size := by
  intro word hword
  exact repackWords_word_lt (metadata shape) (wordWidth shape.size)
    (packedReviewerMemory shape) (wordWidth_pos shape.size) (metadata_words_fit shape) hword

theorem buildMemory_words_fit (xs : List Int) :
    ∀ word ∈ buildMemory xs, word < 2 ^ wordWidth xs.length := by
  have h := shapeMemory_words_fit (SuccinctClassic.cartesianShape xs)
  simpa only [buildMemory, packedReviewerCartesianShape_size] using h

theorem shapeMemory_length_eq (shape : CartesianShape) :
    (shapeMemory shape).length = metadataWordCount +
      GenericSelect.selectCeilDiv
        (packedReviewerCellCount shape.size (longCount shape)
          (packedReviewerSparseCount shape) * packedReviewerCellWidth shape.size)
        (wordWidth shape.size) := by
  simp only [shapeMemory, repackWords, List.length_append, metadata_length,
    denseWords_length, denseCount]
  rw [uniform_flatten_length (packedReviewerMemory shape) (packedReviewerCellWidth shape.size)
    (by intro cell hc; exact packedReviewerMemory_cell_length shape hc), packedReviewerMemory_length]

theorem shapeMemory_length_fit (shape : CartesianShape) :
    (shapeMemory shape).length < 2 ^ wordWidth shape.size := by
  rw [shapeMemory_length_eq]
  apply metadata_words_fit shape
  apply List.mem_append_left
  apply List.mem_append_left
  simp [scalarMetadata]

theorem buildMemory_length_fit (xs : List Int) :
    (buildMemory xs).length < 2 ^ wordWidth xs.length := by
  have h := shapeMemory_length_fit (SuccinctClassic.cartesianShape xs)
  simpa only [buildMemory, packedReviewerCartesianShape_size] using h

/-- Covers every allocated address and the first failed address in this allocation. -/
theorem buildMemory_address_fit (xs : List Int) (address : Nat)
    (haddress : address ≤ (buildMemory xs).length) :
    address < 2 ^ wordWidth xs.length :=
  Nat.lt_of_le_of_lt haddress (buildMemory_length_fit xs)

/-- Invalid representable endpoints are a separate program-guard obligation. -/
theorem validEndpoints_fit (xs : List Int) (left right : Nat)
    (hvalid : left < right ∧ right ≤ xs.length) :
    left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length := by
  have h := size_lt_wordCapacity xs.length
  omega

/-- An independently written expected-type consumer fixes the same allocation,
width, residual, and endpoint domain used by the lead execution join. -/
theorem allocation_width_requiredFacts (xs : List Int) :
    (∀ word ∈ buildMemory xs, word < 2 ^ wordWidth xs.length) ∧
    (∀ address ≤ (buildMemory xs).length, address < 2 ^ wordWidth xs.length) ∧
    ((buildMemory xs).length * wordWidth xs.length ≤
      2 * xs.length + allocationRho xs.length) ∧
    (wordWidth xs.length ≤ 192 * (Nat.log2 (xs.length + 2) + 1)) ∧
    (∀ left right, left < right ∧ right ≤ xs.length →
      left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length) :=
  ⟨buildMemory_words_fit xs, buildMemory_address_fit xs,
    buildMemory_capacity_le xs, wordWidth_le_log xs.length, validEndpoints_fit xs⟩

example : ∀ word ∈ buildMemory [], word < 2 ^ wordWidth 0 :=
  buildMemory_words_fit []

example (value : Int) : (buildMemory [value]).length < 2 ^ wordWidth 1 :=
  buildMemory_length_fit [value]

example (value : Int) : 0 < 2 ^ wordWidth 1 ∧ 1 < 2 ^ wordWidth 1 :=
  validEndpoints_fit [value] 0 1 (by simp)

example (shape : CartesianShape) (_long : 0 < longCount shape)
    (_sparse : 0 < packedReviewerSparseCount shape) :
    ∀ word ∈ metadata shape, word < 2 ^ wordWidth shape.size :=
  metadata_words_fit shape

end RMQ.SuccinctFinal.PackedWordRAM
