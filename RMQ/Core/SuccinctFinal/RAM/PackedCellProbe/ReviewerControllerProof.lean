import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerController
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerLogicalSimulation
import RMQ.Core.SuccinctRMQClassic

/-!
# Correctness of the all-size reviewer-memory controller

This file is the proof-only bridge from the executable physical controller to
the accepted logical whole-query run.  The executable definitions imported
from `ReviewerController` never receive a `CartesianShape`, `List Int`, logical
store, semantic callback, or expected answer.  Shape and the canonical logical
store occur here only as refinement witnesses for the one physical run against
`packedReviewerMemory shape`.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-! ## Exact physical answer to every logical word request -/

private theorem packedReviewerTake_eq_take_min_length
    {alpha : Type} (xs : List alpha) (count : Nat) :
    xs.take count = xs.take (min count xs.length) := by
  by_cases hle : count <= xs.length
  · rw [Nat.min_eq_left hle]
  · have hlen : xs.length <= count := by omega
    rw [Nat.min_eq_right hlen, List.take_length,
      List.take_of_length_le hlen]

/-- The balanced-parenthesis code is literally the first payload component. -/
theorem packedReviewerPayload_bpSlice
    (shape : CartesianShape) (offset width : Nat)
    (hfit : offset + width <= shape.bpCode.length) :
    ((packedReviewerPayloadBits shape).drop offset).take width =
      (shape.bpCode.drop offset).take width := by
  unfold packedReviewerPayloadBits
    concreteBPNativeSuccinctRMQCanonicalReviewerPayload
    concreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout
  dsimp only
  rw [show
      shape.bpCode ++
              concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload
                shape ++
            (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload ++
          (SuccinctClose.bpFringeChunkTable
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload ++
        (SuccinctClose.bpChunkSelectTable
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).payload =
        shape.bpCode ++
          (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape ++
            (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload ++
              (SuccinctClose.bpFringeChunkTable
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload ++
                (SuccinctClose.bpChunkSelectTable
                  (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
                  false).payload) by
        simp [List.append_assoc]]
  exact packedPrefixSlice shape.bpCode _ hfit

/--
Both logical BP aliases are answered option-for-option by the physical reviewer
memory.  The final-rank alias includes its canonical empty sentinel words; they
have a zero-cell plan and decode to `[]`, not to a decorative read.
-/
theorem packedReviewerBPRead_eq_words
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hsource : source = .bpCode ∨ source = .finalRankBPCodeAlias)
    (index : Nat) :
    packedReviewerBPRead shape.size (packedReviewerMemory shape) source index =
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? := by
  have hne :
      source !=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative := by
    rcases hsource with rfl | rfl <;> decide
  cases hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? with
  | none =>
      have hle := packedSourceWords_of_none shape source hne hget
      have hnot :
          ¬ index < packedSourceWordCount shape.size 0 source := by
        rcases hsource with rfl | rfl <;>
          simpa [packedSourceWordCount] using hle
      simp [packedReviewerBPRead, hnot, hget]
  | some word =>
      have hslice := packedSourceWords_of_some shape source hget
      have hltReviewer :=
        packedReviewerSourceWordCount_of_some shape source hget
      have hlt : index < packedSourceWordCount shape.size 0 source := by
        rcases hsource with rfl | rfl <;>
          simpa [packedReviewerSourceWordCount, packedSourceWordCount] using
            hltReviewer
      rw [packedWordSlice_of_lt (by
        rcases hsource with rfl | rfl <;>
          simpa [packedSourceWordCount] using hlt)] at hslice
      have hpayloadLength :
          (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
            shape source).length = 2 * shape.size := by
        rcases hsource with rfl | rfl <;>
          simpa [concreteBPNativeSuccinctRMQFlatPayloadSourcePayload] using
            CartesianShape.bpCode_length shape
      have hwidth :
          packedReviewerBPReadWidth shape.size source index =
            min (packedSourceStride shape.size source)
              ((concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
                  shape source).length -
                index * packedSourceStride shape.size source) := by
        unfold packedReviewerBPReadWidth packedSourceReadWidth
        rcases hsource with rfl | rfl <;>
          simp [packedSourceBitLength, hpayloadLength]
      have hword :
          word =
            ((shape.bpCode.drop
                (index * packedSourceStride shape.size source)).take
              (packedReviewerBPReadWidth shape.size source index)) := by
        have hsliceword := Option.some.inj hslice
        have hsourcePayload :
            concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source =
              shape.bpCode := by
          rcases hsource with rfl | rfl <;>
            rfl
        rw [hsourcePayload] at hsliceword
        calc
          word =
              (shape.bpCode.drop
                  (index * packedSourceStride shape.size source)).take
                (packedSourceStride shape.size source) := hsliceword.symm
          _ =
              (shape.bpCode.drop
                  (index * packedSourceStride shape.size source)).take
                (min (packedSourceStride shape.size source)
                  (shape.bpCode.drop
                    (index * packedSourceStride shape.size source)).length) :=
            packedReviewerTake_eq_take_min_length _ _
          _ =
              (shape.bpCode.drop
                  (index * packedSourceStride shape.size source)).take
                (packedReviewerBPReadWidth shape.size source index) := by
            rw [hwidth, hpayloadLength]
            simp [List.length_drop, CartesianShape.bpCode_length shape]
      by_cases hzero :
          packedReviewerBPReadWidth shape.size source index = 0
      · have hempty : word = [] := by
          rw [hword, hzero]
          simp
        simp [packedReviewerBPRead, hlt, packedReviewerBPRawPlan,
          hzero, packedReviewerProbePlan, hempty,
          packedReviewerDecodeSpan, packedFetch]
      · have hpos :
            0 < packedReviewerBPReadWidth shape.size source index := by
          omega
        have hinside :
            index * packedSourceStride shape.size source < 2 * shape.size := by
          rw [hwidth, hpayloadLength] at hpos
          omega
        have hfitBP :
            index * packedSourceStride shape.size source +
                packedReviewerBPReadWidth shape.size source index <=
              shape.bpCode.length := by
          rw [CartesianShape.bpCode_length shape, hwidth, hpayloadLength]
          omega
        have hpayLength := packedReviewerPayloadBits_length_eq shape
        have hfitPayload :
            index * packedSourceStride shape.size source +
                packedReviewerBPReadWidth shape.size source index <=
              packedReviewerPayloadLength shape.size (longCount shape)
                (packedReviewerSparseCount shape) := by
          rw [← hpayLength]
          have hprefix : shape.bpCode.length <=
              (packedReviewerPayloadBits shape).length := by
            unfold packedReviewerPayloadBits
              concreteBPNativeSuccinctRMQCanonicalReviewerPayload
              concreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout
            dsimp only
            simp
          omega
        have hserial :=
          packedReviewerSerialized_le_allocated shape.size (longCount shape)
            (packedReviewerSparseCount shape)
        have hfitAllocation :
            packedReviewerBPBitAddress shape.size source index +
                packedReviewerBPReadWidth shape.size source index <=
              packedReviewerAllocatedBits shape.size (longCount shape)
                (packedReviewerSparseCount shape) := by
          unfold packedReviewerBPBitAddress
          omega
        have hstride : PackedSourceCounted shape.size source := by
          rcases hsource with rfl | rfl <;> trivial
        have hreadWidth :
            packedReviewerBPReadWidth shape.size source index <=
              packedReviewerCellWidth shape.size :=
          Nat.le_trans
            (packedSourceReadWidth_le_stride shape.size 0 source index)
            (packedSourceStride_le_reviewerCellWidth shape.size source hstride)
        have hdecode :=
          packedReviewerProbePlan_decode shape hreadWidth hfitAllocation
        have hpayloadSlice :=
          packedReviewerPayloadSlice shape
            (index * packedSourceStride shape.size source)
            (packedReviewerBPReadWidth shape.size source index) hfitPayload
        have hbpSlice :=
          packedReviewerPayload_bpSlice shape
            (index * packedSourceStride shape.size source)
            (packedReviewerBPReadWidth shape.size source index) hfitBP
        unfold packedReviewerBPRead
        rw [if_pos hlt]
        calc
          (packedFetch (packedReviewerMemory shape)
                (packedReviewerBPRawPlan shape.size source index)).map
              (packedReviewerDecodeSpan shape.size
                (packedReviewerBPBitAddress shape.size source index)
                (packedReviewerBPReadWidth shape.size source index)) =
              some (((packedReviewerPaddedBits shape).drop
                (packedReviewerBPBitAddress shape.size source index)).take
                  (packedReviewerBPReadWidth shape.size source index)) := by
            simpa [packedReviewerBPRawPlan] using hdecode
          _ = some (((packedReviewerPayloadBits shape).drop
                (index * packedSourceStride shape.size source)).take
              (packedReviewerBPReadWidth shape.size source index)) := by
            simpa [packedReviewerBPBitAddress] using congrArg some hpayloadSlice
          _ = some ((shape.bpCode.drop
                (index * packedSourceStride shape.size source)).take
              (packedReviewerBPReadWidth shape.size source index)) := by
            exact congrArg some hbpSlice
          _ = some word := by rw [← hword]

/-- Below segment 20 the global store is exactly the source selected by the
closed segment map. -/
theorem packedReviewerGlobalReadStore_legacy
    (shape : CartesianShape) {segment : Nat}
    (hsegment : segment < 20)
    {source : ConcreteBPNativeSuccinctRMQFlatPayloadSource}
    (hsource : packedSegmentSource? segment = some source)
    (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index =
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? := by
  rw [← packedExecutedStore_is_reviewerStore shape segment index]
  change
    (if segment < 20 then
        (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
          segment index
      else if segment = 20 then
        (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
          shape).store.words[index]?
      else if segment = concreteBPNativeFringeChunkTraceSegment then
        (SuccinctClose.bpFringeChunkTable
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).store.words[index]?
      else if segment = concreteBPNativeSelectChunkTraceSegment then
        (SuccinctClose.bpChunkSelectTable
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).store.words[index]?
      else none) = _
  rw [if_pos hsegment]
  unfold concreteBPNativeSuccinctRMQFlatPayloadReadStore
  change
    concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment =
      some source at hsource
  change
    (match concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment with
      | some selectedSource =>
          (concreteBPNativeSuccinctRMQFlatPayloadSourceWords
            shape selectedSource)[index]?
      | none => none) = _
  rw [hsource]

private theorem packedReviewerLogicalPlan_legacy_eq
    (n longCount sparseCount : Nat) (request : PackedReviewerLogicalRequest)
    (hsegment : request.segment < 20)
    {source : ConcreteBPNativeSuccinctRMQFlatPayloadSource}
    (hsource : packedSegmentSource? request.segment = some source) :
    packedReviewerLogicalPlan n longCount sparseCount request =
      if request.index <
          packedReviewerLegacyWordCount n longCount sparseCount source then
        packedReviewerLegacyRawPlan n longCount sparseCount source request.index
      else [] := by
  have h20 : request.segment ≠ 20 := by omega
  have h21 : request.segment ≠ 21 := by omega
  have h22 : request.segment ≠ 22 := by omega
  simp [packedReviewerLogicalPlan, h20, h21, h22, hsegment, hsource]

private theorem packedReviewerLogicalDecode_legacy_eq
    (n longCount sparseCount : Nat) (request : PackedReviewerLogicalRequest)
    (cells : List (List Bool))
    (hsegment : request.segment < 20)
    {source : ConcreteBPNativeSuccinctRMQFlatPayloadSource}
    (hsource : packedSegmentSource? request.segment = some source) :
    packedReviewerLogicalDecode n longCount sparseCount request cells =
      if request.index <
          packedReviewerLegacyWordCount n longCount sparseCount source then
        some (packedReviewerLegacyDecode n longCount sparseCount source
          request.index cells)
      else none := by
  have h20 : request.segment ≠ 20 := by omega
  have h21 : request.segment ≠ 21 := by omega
  have h22 : request.segment ≠ 22 := by omega
  simp [packedReviewerLogicalDecode, h20, h21, h22, hsegment, hsource]

/-- A successful legacy global-store read lies inside its exact reviewer count. -/
theorem packedReviewerGlobalReadStore_legacy_index_lt_count
    (shape : CartesianShape) {segment index : Nat}
    (hsegment : segment < 20)
    {source : ConcreteBPNativeSuccinctRMQFlatPayloadSource}
    (hsource : packedSegmentSource? segment = some source)
    {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          segment index = some word) :
    index < packedReviewerSourceWordCount shape.size (longCount shape)
      (packedReviewerSparseCount shape) source := by
  have hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? =
        some word := by
    rw [← packedReviewerGlobalReadStore_legacy shape hsegment hsource index]
    exact hread
  exact packedReviewerSourceWordCount_of_some shape source hget

theorem packedReviewerLogicalRead_eq_sourceRead
    (n longCount sparseCount : Nat) (memory : List (List Bool))
    (request : PackedReviewerLogicalRequest)
    (hsegment : request.segment < 20)
    {source : ConcreteBPNativeSuccinctRMQFlatPayloadSource}
    (hsource : packedSegmentSource? request.segment = some source)
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources)
    (hbp : source != .bpCode)
    (halias : source != .finalRankBPCodeAlias) :
    packedReviewerLogicalRead n longCount sparseCount memory request =
      packedReviewerSourceRead n longCount sparseCount memory source
      request.index := by
  by_cases hindex :
      request.index <
        packedReviewerLegacyWordCount n longCount sparseCount source
  · unfold packedReviewerLogicalRead packedReviewerSourceRead
    rw [packedReviewerLogicalPlan_legacy_eq n longCount sparseCount request
          hsegment hsource,
      if_pos hindex,
      packedReviewerLegacyRawPlan_eq_sourceGeometry n longCount sparseCount
        source request.index hmem,
      if_pos (by simpa [packedReviewerLegacyWordCount] using hindex)]
    cases hfetch : packedFetch memory
        (packedReviewerSourceReadPlan n longCount sparseCount source
          request.index) with
    | none => simp [hfetch]
    | some cells =>
        simp only [hfetch]
        rw [packedReviewerLogicalDecode_legacy_eq n longCount sparseCount
              request cells hsegment hsource,
          if_pos hindex,
          packedReviewerLegacyDecode_eq_sourceGeometry n longCount sparseCount
            source request.index cells hmem]
        rfl
  · unfold packedReviewerLogicalRead packedReviewerSourceRead
    rw [packedReviewerLogicalPlan_legacy_eq n longCount sparseCount request
          hsegment hsource,
      if_neg hindex]
    simp only [packedFetch]
    rw [
      packedReviewerLogicalDecode_legacy_eq n longCount sparseCount request []
        hsegment hsource,
      if_neg hindex,
      if_neg (by simpa [packedReviewerLegacyWordCount] using hindex)]

theorem packedReviewerLogicalRead_eq_bpRead
    (n longCount sparseCount : Nat) (memory : List (List Bool))
    (request : PackedReviewerLogicalRequest)
    (hsegment : request.segment < 20)
    {source : ConcreteBPNativeSuccinctRMQFlatPayloadSource}
    (hsource : packedSegmentSource? request.segment = some source)
    (hbp : source = .bpCode ∨ source = .finalRankBPCodeAlias) :
    packedReviewerLogicalRead n longCount sparseCount memory request =
      packedReviewerBPRead n memory source request.index := by
  have hcount :
      packedReviewerLegacyWordCount n longCount sparseCount source =
        packedSourceWordCount n 0 source := by
    rcases hbp with rfl | rfl <;>
      rfl
  by_cases hindex :
      request.index <
        packedReviewerLegacyWordCount n longCount sparseCount source
  · unfold packedReviewerLogicalRead packedReviewerBPRead
    rw [packedReviewerLogicalPlan_legacy_eq n longCount sparseCount request
          hsegment hsource,
      if_pos hindex,
      if_pos (by simpa [hcount] using hindex)]
    rcases hbp with rfl | rfl
    · simp only [packedReviewerLegacyRawPlan]
      cases hfetch : packedFetch memory
          (packedReviewerBPRawPlan n .bpCode request.index) with
      | none => simp [hfetch]
      | some cells =>
          simp only [hfetch]
          rw [packedReviewerLogicalDecode_legacy_eq n longCount sparseCount
            request cells hsegment hsource, if_pos hindex]
          rfl
    · simp only [packedReviewerLegacyRawPlan]
      cases hfetch : packedFetch memory
          (packedReviewerBPRawPlan n .finalRankBPCodeAlias request.index) with
      | none => simp [hfetch]
      | some cells =>
          simp only [hfetch]
          rw [packedReviewerLogicalDecode_legacy_eq n longCount sparseCount
            request cells hsegment hsource, if_pos hindex]
          rfl
  · unfold packedReviewerLogicalRead packedReviewerBPRead
    rw [packedReviewerLogicalPlan_legacy_eq n longCount sparseCount request
          hsegment hsource,
      if_neg hindex]
    simp only [packedFetch]
    rw [
      packedReviewerLogicalDecode_legacy_eq n longCount sparseCount request []
        hsegment hsource,
      if_neg hindex,
      if_neg (by simpa [hcount] using hindex)]

/-- A non-BP legacy request lowers through the exact consumed access source. -/
theorem packedReviewerLogicalRead_eq_legacySource
    (shape : CartesianShape) (request : PackedReviewerLogicalRequest)
    (hsegment : request.segment < 20)
    {source : ConcreteBPNativeSuccinctRMQFlatPayloadSource}
    (hsource : packedSegmentSource? request.segment = some source)
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources)
    (hcounted : PackedSourceCounted shape.size source)
    (hbp : source != .bpCode)
    (halias : source != .finalRankBPCodeAlias) :
    packedReviewerLogicalRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape) request =
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index := by
  calc
    packedReviewerLogicalRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape) request =
        packedReviewerSourceRead shape.size (longCount shape)
          (packedReviewerSparseCount shape) (packedReviewerMemory shape)
          source request.index :=
      packedReviewerLogicalRead_eq_sourceRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape) request
        hsegment hsource hmem hbp halias
    _ =
        (concreteBPNativeSuccinctRMQFlatPayloadSourceWords
          shape source)[request.index]? :=
      packedReviewerSourceRead_eq_words shape source hmem hcounted request.index
    _ =
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index :=
      (packedReviewerGlobalReadStore_legacy shape hsegment hsource
        request.index).symm

/-- A BP-backed legacy request preserves its segment-specific word geometry. -/
theorem packedReviewerLogicalRead_eq_legacyBP
    (shape : CartesianShape) (request : PackedReviewerLogicalRequest)
    (hsegment : request.segment < 20)
    {source : ConcreteBPNativeSuccinctRMQFlatPayloadSource}
    (hsource : packedSegmentSource? request.segment = some source)
    (hbp : source = .bpCode ∨ source = .finalRankBPCodeAlias) :
    packedReviewerLogicalRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape) request =
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index := by
  calc
    packedReviewerLogicalRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape) request =
        packedReviewerBPRead shape.size (packedReviewerMemory shape)
          source request.index :=
      packedReviewerLogicalRead_eq_bpRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape) request
        hsegment hsource hbp
    _ =
        (concreteBPNativeSuccinctRMQFlatPayloadSourceWords
          shape source)[request.index]? :=
      packedReviewerBPRead_eq_words shape source hbp request.index
    _ =
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index :=
      (packedReviewerGlobalReadStore_legacy shape hsegment hsource
        request.index).symm

theorem packedReviewerLogicalRead_eq_interiorRead
    (n longCount sparseCount : Nat) (memory : List (List Bool))
    (invocation : PackedReviewerInvocation) (site : PackedReviewerReadSite)
    (index : Nat) :
    packedReviewerLogicalRead n longCount sparseCount memory
        { invocation := invocation, site := site, segment := 20, index := index } =
      packedReviewerInteriorRead n longCount sparseCount memory index := by
  cases hclassify : packedReviewerInteriorClassify n index with
  | none =>
      simp [packedReviewerLogicalRead, packedReviewerLogicalPlan,
        packedReviewerLogicalDecode, packedReviewerInteriorRead,
        packedReviewerInteriorReadPlan, packedReviewerClosedInteriorReadPlan_eq,
        packedReviewerClosedInteriorBitAddress_eq, hclassify, packedFetch]
  | some location =>
      cases hfetch : packedFetch memory
          (packedReviewerInteriorLocationPlan n longCount sparseCount location) <;>
        simp [packedReviewerLogicalRead, packedReviewerLogicalPlan,
          packedReviewerLogicalDecode, packedReviewerInteriorRead,
          packedReviewerInteriorReadPlan, packedReviewerClosedInteriorReadPlan_eq,
          packedReviewerClosedInteriorBitAddress_eq, hclassify, hfetch]

theorem packedReviewerLogicalRead_eq_fringeRead
    (n longCount sparseCount : Nat) (memory : List (List Bool))
    (invocation : PackedReviewerInvocation) (site : PackedReviewerReadSite)
    (index : Nat) :
    packedReviewerLogicalRead n longCount sparseCount memory
        { invocation := invocation, site := site, segment := 21, index := index } =
      packedReviewerFringeRead n longCount sparseCount memory index := by
  by_cases hindex : index < packedReviewerFringeCount n
  · cases hfetch : packedFetch memory
        (packedReviewerProbePlan n
          (packedReviewerFringeAddress n longCount sparseCount index)
          (packedReviewerFringeWidth n)) <;>
      simp [packedReviewerLogicalRead, packedReviewerLogicalPlan,
        packedReviewerLogicalDecode, packedReviewerFringeRead,
        packedReviewerClosedFringeAddress_eq, hindex, hfetch]
  · simp [packedReviewerLogicalRead, packedReviewerLogicalPlan,
      packedReviewerLogicalDecode, packedReviewerFringeRead,
      packedReviewerClosedFringeAddress_eq, hindex, packedFetch]

theorem packedReviewerLogicalRead_eq_selectChunkRead
    (n longCount sparseCount : Nat) (memory : List (List Bool))
    (invocation : PackedReviewerInvocation) (site : PackedReviewerReadSite)
    (index : Nat) :
    packedReviewerLogicalRead n longCount sparseCount memory
        { invocation := invocation, site := site, segment := 22, index := index } =
      packedReviewerSelectChunkRead n longCount sparseCount memory index := by
  by_cases hindex : index < packedReviewerSelectChunkCount n
  · cases hfetch : packedFetch memory
        (packedReviewerProbePlan n
          (packedReviewerSelectChunkAddress n longCount sparseCount index)
          (packedReviewerSelectChunkWidth n)) <;>
      simp [packedReviewerLogicalRead, packedReviewerLogicalPlan,
        packedReviewerLogicalDecode, packedReviewerSelectChunkRead,
        packedReviewerClosedSelectChunkAddress_eq, hindex, hfetch]
  · simp [packedReviewerLogicalRead, packedReviewerLogicalPlan,
      packedReviewerLogicalDecode, packedReviewerSelectChunkRead,
      packedReviewerClosedSelectChunkAddress_eq, hindex, packedFetch]

/-- Segment 21 is backed option-for-option, including absent rows. -/
theorem packedReviewerFringeRead_eq_segment21
    (shape : CartesianShape) (index : Nat) :
    packedReviewerFringeRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape) index =
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21 index := by
  cases hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21 index with
  | some word => exact packedReviewerFringeRead_of_some shape hread
  | none =>
      by_cases hindex : index < packedReviewerFringeCount shape.size
      · have hbp : shape.bpCode.length = 2 * shape.size :=
          CartesianShape.bpCode_length shape
        have hcount :
            packedReviewerFringeCount shape.size =
              (SuccinctClose.bpFringeChunkEntries
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).length := by
          unfold packedReviewerFringeCount
          rw [hbp, SuccinctClose.bpFringeChunkEntries_length]
        have hwords := packedReviewerFringeChunkWords shape index
        rw [hread, packedWordSlice_of_lt (by omega)] at hwords
        simp at hwords
      · simp [packedReviewerFringeRead, hindex, hread]

/-- Segment 22 is backed option-for-option, including absent rows. -/
theorem packedReviewerSelectChunkRead_eq_segment22
    (shape : CartesianShape) (index : Nat) :
    packedReviewerSelectChunkRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape) index =
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 22 index := by
  cases hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 22 index with
  | some word => exact packedReviewerSelectChunkRead_of_some shape hread
  | none =>
      by_cases hindex : index < packedReviewerSelectChunkCount shape.size
      · have hbp : shape.bpCode.length = 2 * shape.size :=
          CartesianShape.bpCode_length shape
        have hcount :
            packedReviewerSelectChunkCount shape.size =
              (SuccinctClose.bpChunkSelectEntries
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
                false).length := by
          unfold packedReviewerSelectChunkCount
          rw [hbp, SuccinctClose.bpChunkSelectEntries_length]
        have hwords := packedReviewerSelectChunkWords shape index
        rw [hread, packedWordSlice_of_lt (by omega)] at hwords
        simp at hwords
      · simp [packedReviewerSelectChunkRead, hindex, hread]

/--
Every logical request of the whole-query protocol is answered by exactly the
same word as the canonical global store, using only the reviewer cell array.
This is the closed all-segment lowering theorem consumed by the controller
simulation.
-/
theorem packedReviewerLogicalRead_eq_globalReadStore
    (shape : CartesianShape) (request : PackedReviewerLogicalRequest) :
    packedReviewerLogicalRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape) request =
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index := by
  rcases request with ⟨invocation, site, segment, index⟩
  by_cases hlarge : 23 <= segment
  · obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hlarge
    rw [packedExecutedStore_silent_from_twentyThree]
    have h20 : 23 + offset ≠ 20 := by omega
    have h21 : 23 + offset ≠ 21 := by omega
    have h22 : 23 + offset ≠ 22 := by omega
    have hnot : ¬ 23 + offset < 20 := by omega
    simp [packedReviewerLogicalRead, packedReviewerLogicalPlan,
      packedReviewerLogicalDecode, h20, h21, h22, hnot, packedFetch]
  · have hsegment : segment <= 22 := by omega
    have hcases :
        segment = 0 ∨ segment = 1 ∨ segment = 2 ∨ segment = 3 ∨
        segment = 4 ∨ segment = 5 ∨ segment = 6 ∨ segment = 7 ∨
        segment = 8 ∨ segment = 9 ∨ segment = 10 ∨ segment = 11 ∨
        segment = 12 ∨ segment = 13 ∨ segment = 14 ∨ segment = 15 ∨
        segment = 16 ∨ segment = 17 ∨ segment = 18 ∨ segment = 19 ∨
        segment = 20 ∨ segment = 21 ∨ segment = 22 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact packedReviewerLogicalRead_eq_legacyBP shape _ (by simp) rfl
        (Or.inl rfl)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacySource shape _ (by simp) rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalRead_eq_legacyBP shape _ (by simp) rfl
        (Or.inr rfl)
    · rw [packedReviewerLogicalRead_eq_interiorRead,
        packedReviewerInteriorRead_eq_segment20]
    · rw [packedReviewerLogicalRead_eq_fringeRead,
        packedReviewerFringeRead_eq_segment21]
    · rw [packedReviewerLogicalRead_eq_selectChunkRead,
        packedReviewerSelectChunkRead_eq_segment22]

/-! ## Every canonical logical plan is allocated and fetches -/

private theorem packedReviewerSourceWords_some_of_lt
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index : Nat)
    (hlt : index < packedReviewerSourceWordCount shape.size (longCount shape)
      (packedReviewerSparseCount shape) source) :
    exists word,
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords
        shape source)[index]? = some word := by
  cases hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords
        shape source)[index]? with
  | some word => exact ⟨word, rfl⟩
  | none =>
      by_cases hsparse :
          source =
            ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative
      · subst source
        have hget' :
            (GenericSelect.sparseExceptionRelativeTable shape.bpCode
              false).store.words[index]? = none := hget
        rw [packedFixedWidthTable_getElem?] at hget'
        have hltEntries :
            index <
              (GenericSelect.sparseExceptionRelativeEntries shape.bpCode
                false).length := by
          simpa [packedReviewerSourceWordCount,
            packedReviewerSparseCount] using hlt
        rw [packedWordSlice_of_lt hltEntries] at hget'
        simp at hget'
      · have hsparse' :
            source !=
              ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative := by
          simp [hsparse]
        have hle := packedSourceWords_of_none shape source hsparse' hget
        have hlt' :
            index < packedSourceWordCount shape.size (longCount shape)
              source := by
          simpa [packedReviewerSourceWordCount, hsparse] using hlt
        omega

private theorem packedReviewerLegacySource_fetch
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources)
    (hcounted : PackedSourceCounted shape.size source)
    (hbp : source != .bpCode)
    (halias : source != .finalRankBPCodeAlias)
    (index : Nat)
    (hlt : index < packedReviewerLegacyWordCount shape.size (longCount shape)
      (packedReviewerSparseCount shape) source) :
    exists cells,
      packedFetch (packedReviewerMemory shape)
        (packedReviewerLegacyRawPlan shape.size (longCount shape)
          (packedReviewerSparseCount shape) source index) = some cells := by
  have hlt' :
      index < packedReviewerSourceWordCount shape.size (longCount shape)
        (packedReviewerSparseCount shape) source := by
    exact hlt
  rcases packedReviewerSourceWords_some_of_lt shape source index hlt' with
    ⟨word, hword⟩
  have hread := packedReviewerSourceRead_eq_words shape source hmem hcounted index
  rw [hword] at hread
  unfold packedReviewerSourceRead at hread
  rw [if_pos hlt'] at hread
  cases hfetch :
      packedFetch (packedReviewerMemory shape)
        (packedReviewerSourceReadPlan shape.size (longCount shape)
          (packedReviewerSparseCount shape) source index) with
  | none => simp [hfetch] at hread
  | some cells =>
      refine ⟨cells, ?_⟩
      rw [packedReviewerLegacyRawPlan_eq_sourceGeometry shape.size
        (longCount shape) (packedReviewerSparseCount shape) source index hmem]
      exact hfetch

private theorem packedReviewerLegacyBP_fetch
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hbp : source = .bpCode ∨ source = .finalRankBPCodeAlias)
    (index : Nat)
    (hlt : index < packedReviewerLegacyWordCount shape.size (longCount shape)
      (packedReviewerSparseCount shape) source) :
    exists cells,
      packedFetch (packedReviewerMemory shape)
        (packedReviewerLegacyRawPlan shape.size (longCount shape)
          (packedReviewerSparseCount shape) source index) = some cells := by
  have hcount :
      packedReviewerLegacyWordCount shape.size (longCount shape)
          (packedReviewerSparseCount shape) source =
        packedSourceWordCount shape.size 0 source := by
    rcases hbp with rfl | rfl <;> rfl
  have hlt' : index < packedSourceWordCount shape.size 0 source := by
    simpa [hcount] using hlt
  have hltReviewer :
      index < packedReviewerSourceWordCount shape.size (longCount shape)
        (packedReviewerSparseCount shape) source := by
    rcases hbp with rfl | rfl <;>
      simpa [packedReviewerSourceWordCount, packedSourceWordCount] using hlt'
  rcases packedReviewerSourceWords_some_of_lt shape source index hltReviewer with
    ⟨word, hword⟩
  have hread := packedReviewerBPRead_eq_words shape source hbp index
  rw [hword] at hread
  unfold packedReviewerBPRead at hread
  rw [if_pos hlt'] at hread
  cases hfetch :
      packedFetch (packedReviewerMemory shape)
        (packedReviewerBPRawPlan shape.size source index) with
  | none => simp [hfetch] at hread
  | some cells =>
      refine ⟨cells, ?_⟩
      rcases hbp with rfl | rfl <;>
        simpa [packedReviewerLegacyRawPlan] using hfetch

private theorem packedReviewerLogicalPlan_fetch_legacySource
    (shape : CartesianShape)
    (invocation : PackedReviewerInvocation) (site : PackedReviewerReadSite)
    (segment index : Nat)
    (hsegment : segment < 20)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hsource : packedSegmentSource? segment = some source)
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources)
    (hcounted : PackedSourceCounted shape.size source)
    (hbp : source != .bpCode)
    (halias : source != .finalRankBPCodeAlias) :
    exists cells,
      packedFetch (packedReviewerMemory shape)
        (packedReviewerLogicalPlan shape.size (longCount shape)
          (packedReviewerSparseCount shape)
          { invocation := invocation, site := site, segment := segment,
            index := index }) = some cells := by
  by_cases hindex :
      index < packedReviewerLegacyWordCount shape.size (longCount shape)
        (packedReviewerSparseCount shape) source
  · rw [packedReviewerLogicalPlan_legacy_eq shape.size (longCount shape)
      (packedReviewerSparseCount shape) _ hsegment hsource, if_pos hindex]
    exact packedReviewerLegacySource_fetch shape source hmem hcounted hbp halias
      index hindex
  · rw [packedReviewerLogicalPlan_legacy_eq shape.size (longCount shape)
      (packedReviewerSparseCount shape) _ hsegment hsource, if_neg hindex]
    exact ⟨[], by simp [packedFetch]⟩

private theorem packedReviewerLogicalPlan_fetch_legacyBP
    (shape : CartesianShape)
    (invocation : PackedReviewerInvocation) (site : PackedReviewerReadSite)
    (segment index : Nat)
    (hsegment : segment < 20)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hsource : packedSegmentSource? segment = some source)
    (hbp : source = .bpCode ∨ source = .finalRankBPCodeAlias) :
    exists cells,
      packedFetch (packedReviewerMemory shape)
        (packedReviewerLogicalPlan shape.size (longCount shape)
          (packedReviewerSparseCount shape)
          { invocation := invocation, site := site, segment := segment,
            index := index }) = some cells := by
  by_cases hindex :
      index < packedReviewerLegacyWordCount shape.size (longCount shape)
        (packedReviewerSparseCount shape) source
  · rw [packedReviewerLogicalPlan_legacy_eq shape.size (longCount shape)
      (packedReviewerSparseCount shape) _ hsegment hsource, if_pos hindex]
    exact packedReviewerLegacyBP_fetch shape source hbp index hindex
  · rw [packedReviewerLogicalPlan_legacy_eq shape.size (longCount shape)
      (packedReviewerSparseCount shape) _ hsegment hsource, if_neg hindex]
    exact ⟨[], by simp [packedFetch]⟩

private theorem packedReviewerInteriorPlan_fetch
    (shape : CartesianShape) (index : Nat) :
    exists cells,
      packedFetch (packedReviewerMemory shape)
        (packedReviewerInteriorReadPlan shape.size (longCount shape)
          (packedReviewerSparseCount shape) index) = some cells := by
  cases hclassify : packedReviewerInteriorClassify shape.size index with
  | none => exact ⟨[], by simp [packedReviewerInteriorReadPlan, hclassify,
      packedFetch]⟩
  | some location =>
      have hread := packedReviewerInteriorRead_of_classify shape hclassify
      unfold packedReviewerInteriorRead at hread
      rw [hclassify] at hread
      cases hfetch :
          packedFetch (packedReviewerMemory shape)
            (packedReviewerInteriorLocationPlan shape.size (longCount shape)
              (packedReviewerSparseCount shape) location) with
      | none => simp [hfetch] at hread
      | some cells =>
          exact ⟨cells, by simpa [packedReviewerInteriorReadPlan, hclassify]
            using hfetch⟩

private theorem packedReviewerFringePlan_fetch
    (shape : CartesianShape) (index : Nat) :
    exists cells,
      packedFetch (packedReviewerMemory shape)
        (if index < packedReviewerFringeCount shape.size then
          packedReviewerProbePlan shape.size
            (packedReviewerFringeAddress shape.size (longCount shape)
              (packedReviewerSparseCount shape) index)
            (packedReviewerFringeWidth shape.size)
        else []) = some cells := by
  by_cases hindex : index < packedReviewerFringeCount shape.size
  · have hbp : shape.bpCode.length = 2 * shape.size :=
      CartesianShape.bpCode_length shape
    have hcount :
        packedReviewerFringeCount shape.size =
          (SuccinctClose.bpFringeChunkEntries
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).length := by
      unfold packedReviewerFringeCount
      rw [hbp, SuccinctClose.bpFringeChunkEntries_length]
    have hword := packedReviewerFringeChunkWords shape index
    rw [packedWordSlice_of_lt (by omega)] at hword
    have hread := packedReviewerFringeRead_of_some shape hword
    unfold packedReviewerFringeRead at hread
    rw [if_pos hindex] at hread
    cases hfetch :
        packedFetch (packedReviewerMemory shape)
          (packedReviewerProbePlan shape.size
            (packedReviewerFringeAddress shape.size (longCount shape)
              (packedReviewerSparseCount shape) index)
            (packedReviewerFringeWidth shape.size)) with
    | none => simp [hfetch] at hread
    | some cells => exact ⟨cells, by simpa [hindex] using hfetch⟩
  · exact ⟨[], by simp [hindex, packedFetch]⟩

private theorem packedReviewerSelectChunkPlan_fetch
    (shape : CartesianShape) (index : Nat) :
    exists cells,
      packedFetch (packedReviewerMemory shape)
        (if index < packedReviewerSelectChunkCount shape.size then
          packedReviewerProbePlan shape.size
            (packedReviewerSelectChunkAddress shape.size (longCount shape)
              (packedReviewerSparseCount shape) index)
            (packedReviewerSelectChunkWidth shape.size)
        else []) = some cells := by
  by_cases hindex : index < packedReviewerSelectChunkCount shape.size
  · have hbp : shape.bpCode.length = 2 * shape.size :=
      CartesianShape.bpCode_length shape
    have hcount :
        packedReviewerSelectChunkCount shape.size =
          (SuccinctClose.bpChunkSelectEntries
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
            false).length := by
      unfold packedReviewerSelectChunkCount
      rw [hbp, SuccinctClose.bpChunkSelectEntries_length]
    have hword := packedReviewerSelectChunkWords shape index
    rw [packedWordSlice_of_lt (by omega)] at hword
    have hread := packedReviewerSelectChunkRead_of_some shape hword
    unfold packedReviewerSelectChunkRead at hread
    rw [if_pos hindex] at hread
    cases hfetch :
        packedFetch (packedReviewerMemory shape)
          (packedReviewerProbePlan shape.size
            (packedReviewerSelectChunkAddress shape.size (longCount shape)
              (packedReviewerSparseCount shape) index)
            (packedReviewerSelectChunkWidth shape.size)) with
    | none => simp [hfetch] at hread
    | some cells => exact ⟨cells, by simpa [hindex] using hfetch⟩
  · exact ⟨[], by simp [hindex, packedFetch]⟩

/-- Every all-size logical plan succeeds against the one reviewer allocation. -/
theorem packedReviewerLogicalPlan_fetch
    (shape : CartesianShape) (request : PackedReviewerLogicalRequest) :
    exists cells,
      packedFetch (packedReviewerMemory shape)
        (packedReviewerLogicalPlan shape.size (longCount shape)
          (packedReviewerSparseCount shape) request) = some cells := by
  rcases request with ⟨invocation, site, segment, index⟩
  by_cases hlarge : 23 <= segment
  · obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hlarge
    have h20 : 23 + offset ≠ 20 := by omega
    have h21 : 23 + offset ≠ 21 := by omega
    have h22 : 23 + offset ≠ 22 := by omega
    have hnot : ¬ 23 + offset < 20 := by omega
    exact ⟨[], by simp [packedReviewerLogicalPlan, h20, h21, h22, hnot,
      packedFetch]⟩
  · have hsegment : segment <= 22 := by omega
    have hcases :
        segment = 0 ∨ segment = 1 ∨ segment = 2 ∨ segment = 3 ∨
        segment = 4 ∨ segment = 5 ∨ segment = 6 ∨ segment = 7 ∨
        segment = 8 ∨ segment = 9 ∨ segment = 10 ∨ segment = 11 ∨
        segment = 12 ∨ segment = 13 ∨ segment = 14 ∨ segment = 15 ∨
        segment = 16 ∨ segment = 17 ∨ segment = 18 ∨ segment = 19 ∨
        segment = 20 ∨ segment = 21 ∨ segment = 22 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact packedReviewerLogicalPlan_fetch_legacyBP shape invocation site 0
        index (by omega) .bpCode rfl (Or.inl rfl)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        1 index (by omega) .selectSuperBaseOccurrence rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        2 index (by omega) .selectSuperBaseWordIndex rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        3 index (by omega) .selectSuperRankBefore rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        4 index (by omega) .selectSuperFirstOffset rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        5 index (by omega) .selectLocalBaseOccurrence rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        6 index (by omega) .selectLocalBaseWordIndex rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        7 index (by omega) .selectLocalRankBefore rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        8 index (by omega) .selectLocalFirstOffset rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        9 index (by omega) .selectLongFlagRankSuperTrue rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        10 index (by omega) .selectLongFlagRankBlockTrue rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        11 index (by omega) .selectLongFlagBits rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        12 index (by omega) .selectLongRelative rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        13 index (by omega) .selectSparseRankSuperTrue rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        14 index (by omega) .selectSparseRankBlockTrue rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        15 index (by omega) .selectSparseFlagBits rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        16 index (by omega) .selectSparseRelative rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        17 index (by omega) .finalRankSuperFalse rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacySource shape invocation site
        18 index (by omega) .finalRankBlockFalse rfl
        (by simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
        trivial (by decide) (by decide)
    · exact packedReviewerLogicalPlan_fetch_legacyBP shape invocation site 19
        index (by omega) .finalRankBPCodeAlias rfl (Or.inr rfl)
    · rw [packedReviewerLogicalPlan_segment20_eq shape.size
        (longCount shape) (packedReviewerSparseCount shape) _ rfl]
      exact packedReviewerInteriorPlan_fetch shape index
    · rw [packedReviewerLogicalPlan_segment21_eq shape.size
        (longCount shape) (packedReviewerSparseCount shape) _ rfl]
      exact packedReviewerFringePlan_fetch shape index
    · rw [packedReviewerLogicalPlan_segment22_eq shape.size
        (longCount shape) (packedReviewerSparseCount shape) _ rfl]
      exact packedReviewerSelectChunkPlan_fetch shape index

theorem packedReviewerLogicalPlan_address_lt_cellCount
    (shape : CartesianShape) (request : PackedReviewerLogicalRequest)
    {address : Nat}
    (haddress :
      address ∈ packedReviewerLogicalPlan shape.size (longCount shape)
        (packedReviewerSparseCount shape) request) :
    address < packedReviewerCellCount shape.size (longCount shape)
      (packedReviewerSparseCount shape) := by
  rcases packedReviewerLogicalPlan_fetch shape request with ⟨cells, hfetch⟩
  rw [← packedReviewerMemory_length shape]
  exact packedReviewerSparsePrelude_fetch_some_address_lt hfetch haddress

theorem packedReviewerLogicalPlan_address_lt_two_pow
    (shape : CartesianShape) (request : PackedReviewerLogicalRequest)
    {address : Nat}
    (haddress :
      address ∈ packedReviewerLogicalPlan shape.size (longCount shape)
        (packedReviewerSparseCount shape) request) :
    address < 2 ^ packedReviewerCellWidth shape.size :=
  Nat.lt_trans
    (packedReviewerLogicalPlan_address_lt_cellCount shape request haddress)
    (packedReviewerSparsePreludeCellCount_lt_two_pow_reviewerWidth shape)

theorem packedReviewerInputSize_lt_two_pow_cellWidth (n : Nat) :
    n < 2 ^ packedReviewerCellWidth n := by
  have htwo := packedTwoMul_le_reviewerBound n
  have hpow := packedReviewerCellBound_lt_two_pow_width n
  omega

/-- Valid half-open endpoints fit the same query-independent modeled word. -/
theorem packedReviewerValidEndpoints_lt_two_pow_cellWidth
    (n left right : Nat) (hvalid : left < right ∧ right <= n) :
    left < 2 ^ packedReviewerCellWidth n ∧
      right < 2 ^ packedReviewerCellWidth n := by
  have hn := packedReviewerInputSize_lt_two_pow_cellWidth n
  omega

/-! ## Constructor-exhaustive machine operands -/

/-- One scalar fits the single query-independent reviewer word. -/
abbrev PackedReviewerNatFits (n value : Nat) : Prop :=
  value < 2 ^ packedReviewerCellWidth n

/-- One logical or physical reply is at most one reviewer word. -/
def PackedReviewerWordFits (n : Nat) (word : List Bool) : Prop :=
  word.length <= packedReviewerCellWidth n

/--
A bounded collection of words is a multiword buffer, not one wider word.
`count` accounts for the number of separately represented words.
-/
def PackedReviewerBufferFits
    (n count : Nat) (words : List (List Bool)) : Prop :=
  words.length <= count ∧
    forall word, word ∈ words -> PackedReviewerWordFits n word

/-- Dynamic operands carried by a read-site constructor. -/
def packedReviewerReadSiteOperands : PackedReviewerReadSite -> List Nat
  | .entryBaseOccurrence
  | .entryBaseWordIndex
  | .entryRankBefore
  | .entryFirstOffset
  | .rankSuper
  | .rankBlock
  | .rankWord
  | .rankChunk
  | .selectChunkRank
  | .selectChunkValue
  | .relativeOffset => []
  | .denseBPWord slot
  | .bpWindowWord slot
  | .fringeChunk slot
  | .interiorChunk slot => [slot]

/-- Dynamic operands carried by one instruction invocation. -/
def packedReviewerInvocationOperands
    (invocation : PackedReviewerInvocation) : List Nat :=
  [invocation.argument, invocation.argument2]

/--
Every dynamically encoded scalar retained by one logical request.  The
instruction and nullary site constructors are typed finite control; the four
site constructors with a `Nat` payload contribute that payload explicitly.
-/
def packedReviewerLogicalRequestOperands
    (request : PackedReviewerLogicalRequest) : List Nat :=
  packedReviewerInvocationOperands request.invocation ++
    packedReviewerReadSiteOperands request.site ++
      [request.segment, request.index]

/-- Dynamic operands retained by physical provenance. -/
def packedReviewerPhysicalOriginOperands :
    PackedReviewerPhysicalOrigin -> List Nat
  | .header => []
  | .sparsePrelude _ => []
  | .wholeQuery request => packedReviewerLogicalRequestOperands request

/-- Every dynamically encoded scalar in one attempted physical request. -/
def packedReviewerPhysicalRequestOperands
    (request : PackedReviewerPhysicalRequest) : List Nat :=
  packedReviewerPhysicalOriginOperands request.origin ++
    [request.address, request.ordinal, request.cellCount]

/-! ### Explicit finite-control encodings -/

/-- Literal two-bit encoding of the four fixed instruction occurrences. -/
def packedReviewerInstructionSiteCode : PackedReviewerInstructionSite -> Nat
  | .leftSelect => 0
  | .rightSelect => 1
  | .lcaClose => 2
  | .finalRank => 3

/-- Literal four-bit encoding of every logical read-site constructor. -/
def packedReviewerReadSiteCode : PackedReviewerReadSite -> Nat
  | .entryBaseOccurrence => 0
  | .entryBaseWordIndex => 1
  | .entryRankBefore => 2
  | .entryFirstOffset => 3
  | .rankSuper => 4
  | .rankBlock => 5
  | .rankWord => 6
  | .rankChunk => 7
  | .selectChunkRank => 8
  | .selectChunkValue => 9
  | .relativeOffset => 10
  | .denseBPWord _ => 11
  | .bpWindowWord _ => 12
  | .fringeChunk _ => 13
  | .interiorChunk _ => 14

/-- Literal two-bit encoding of the three sparse-header probe kinds. -/
def packedReviewerSparsePreludeRequestCode :
    PackedReviewerSparsePreludeRequest -> Nat
  | .rankSuper => 0
  | .rankBlock => 1
  | .flagWord => 2

/-- Literal two-bit encoding of physical provenance constructors. -/
def packedReviewerPhysicalOriginCode : PackedReviewerPhysicalOrigin -> Nat
  | .header => 0
  | .sparsePrelude _ => 1
  | .wholeQuery _ => 2

/-- Literal three-bit encoding of the public controller's seven phases. -/
def packedReviewerControllerStatePhaseCode :
    PackedReviewerControllerState -> Nat
  | .header _ _ _ => 0
  | .preludeReady _ _ _ _ _ => 1
  | .preludeProbe _ _ _ _ _ _ _ => 2
  | .wholeReady _ _ _ _ _ _ _ => 3
  | .wholeProbe _ _ _ _ _ _ _ _ _ => 4
  | .done _ => 5
  | .failed => 6

/-- The instruction and site tags of every logical request are explicit. -/
structure PackedReviewerLogicalControlCodesFit
    (n : Nat) (request : PackedReviewerLogicalRequest) : Prop where
  instruction :
    PackedReviewerNatFits n
      (packedReviewerInstructionSiteCode request.invocation.instruction)
  site : PackedReviewerNatFits n (packedReviewerReadSiteCode request.site)

/--
Every physical-origin tag is explicit; nested logical or sparse-prelude tags
are retained when that origin constructor carries one.
-/
structure PackedReviewerPhysicalControlCodesFit
    (n : Nat) (origin : PackedReviewerPhysicalOrigin) : Prop where
  origin_tag : PackedReviewerNatFits n (packedReviewerPhysicalOriginCode origin)
  nested_tag :
    match origin with
    | .header => True
    | .sparsePrelude request =>
        PackedReviewerNatFits n (packedReviewerSparsePreludeRequestCode request)
    | .wholeQuery request => PackedReviewerLogicalControlCodesFit n request

/-- Constructor-exhaustive modeled-word condition for a logical request. -/
structure PackedReviewerLogicalRequestOperandsFit
    (n : Nat) (request : PackedReviewerLogicalRequest) : Prop where
  operands_fit :
    forall operand,
      operand ∈ packedReviewerLogicalRequestOperands request ->
        PackedReviewerNatFits n operand

/--
Constructor-exhaustive modeled-word condition for a physical request.  The
order fields also retain the stronger plan fact used by the trace grouping.
-/
structure PackedReviewerPhysicalRequestOperandsFit
    (n : Nat) (request : PackedReviewerPhysicalRequest) : Prop where
  operands_fit :
    forall operand,
      operand ∈ packedReviewerPhysicalRequestOperands request ->
        PackedReviewerNatFits n operand
  ordinal_lt : request.ordinal < request.cellCount
  cellCount_le_two : request.cellCount <= 2

/--
Fuel-indexed request-width invariant mirroring a first-order request/reply
driver.  It checks the request produced now and then the state obtained from
the exact supplied-store reply.  Because it follows logical transitions rather
than physical plans, zero-cell segment-20 dead attempts are included.
-/
def PackedReviewerRequestsFitFrom {State : Type}
    (n : Nat) (store : WordRAM.ReadStore)
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State) :
    Nat -> State -> Prop
  | 0, _ => True
  | fuel + 1, state =>
      match nextRequest state with
      | none => True
      | some request =>
          PackedReviewerLogicalRequestOperandsFit n request ∧
            PackedReviewerRequestsFitFrom n store nextRequest consumeReply fuel
              (consumeReply state
                (store.readWord? request.segment request.index))

/-- A proved request-width prefix remains proved after shortening its fuel. -/
theorem PackedReviewerRequestsFitFrom.mono
    {State : Type} (n : Nat) (store : WordRAM.ReadStore)
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State)
    {small large : Nat} {state : State}
    (hfit : PackedReviewerRequestsFitFrom n store nextRequest consumeReply
      large state)
    (hle : small <= large) :
    PackedReviewerRequestsFitFrom n store nextRequest consumeReply small state := by
  induction small generalizing large state with
  | zero => trivial
  | succ small ih =>
      cases large with
      | zero => omega
      | succ large =>
          cases hrequest : nextRequest state with
          | none => simp [PackedReviewerRequestsFitFrom, hrequest]
          | some request =>
              have hstep :
                  PackedReviewerLogicalRequestOperandsFit n request ∧
                    PackedReviewerRequestsFitFrom n store nextRequest
                      consumeReply large
                      (consumeReply state
                        (store.readWord? request.segment request.index)) := by
                simpa [PackedReviewerRequestsFitFrom, hrequest] using hfit
              simp only [PackedReviewerRequestsFitFrom, hrequest]
              exact ⟨hstep.1, ih hstep.2 (by omega)⟩

/-- Exact one-step inversion of the request-width prefix invariant. -/
theorem PackedReviewerRequestsFitFrom.step
    {State : Type} (n : Nat) (store : WordRAM.ReadStore)
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State)
    (fuel : Nat) (state : State) (request : PackedReviewerLogicalRequest)
    (hfit : PackedReviewerRequestsFitFrom n store nextRequest consumeReply
      (fuel + 1) state)
    (hrequest : nextRequest state = some request) :
    PackedReviewerLogicalRequestOperandsFit n request ∧
      PackedReviewerRequestsFitFrom n store nextRequest consumeReply fuel
        (consumeReply state
          (store.readWord? request.segment request.index)) := by
  simpa [PackedReviewerRequestsFitFrom, hrequest] using hfit

/-- A driver whose fuel-indexed invariant holds emits only fitting requests. -/
theorem packedReviewerDriveLogical_trace_request_operands_fit_of_fitFrom
    (n : Nat) (store : WordRAM.ReadStore) (fuel : Nat)
    (state : PackedReviewerWholeState)
    (hfit :
      PackedReviewerRequestsFitFrom n store
        packedReviewerWholeNextRequest packedReviewerWholeConsumeReply
        fuel state)
    {event : PackedReviewerLogicalEvent}
    (hmem : event ∈ (packedReviewerDriveLogical store fuel state).trace) :
    PackedReviewerLogicalRequestOperandsFit n event.request := by
  induction fuel generalizing state event with
  | zero =>
      simp [packedReviewerDriveLogical] at hmem
  | succ fuel ih =>
      cases hresult : packedReviewerWholeResult state with
      | some value =>
          simp [packedReviewerDriveLogical, hresult] at hmem
      | none =>
          cases hrequest : packedReviewerWholeNextRequest state with
          | none =>
              simp [packedReviewerDriveLogical, hresult, hrequest] at hmem
          | some request =>
              have hstep :
                  PackedReviewerLogicalRequestOperandsFit n request ∧
                    PackedReviewerRequestsFitFrom n store
                      packedReviewerWholeNextRequest
                      packedReviewerWholeConsumeReply fuel
                      (packedReviewerWholeConsumeReply state
                        (store.readWord? request.segment request.index)) := by
                simpa [PackedReviewerRequestsFitFrom, hrequest] using hfit
              simp only [packedReviewerDriveLogical, hresult, hrequest,
                List.mem_cons] at hmem
              rcases hmem with rfl | htail
              · exact hstep.1
              · exact ih _ hstep.2 htail

/-- The full controller request is at most a two-cell request. -/
theorem packedReviewerPhysicalRequest_small_fields_fit
    (n : Nat) (request : PackedReviewerPhysicalRequest)
    (hordinal : request.ordinal < request.cellCount)
    (hcount : request.cellCount <= 2) :
    PackedReviewerNatFits n request.ordinal ∧
      PackedReviewerNatFits n request.cellCount := by
  have hcapacity := packedReviewerCellBound_lt_two_pow_width n
  constructor <;> omega

/-- The always-present charged fringe table supplies forty bits of slack. -/
theorem packedReviewerFringeTableOverhead_ge_forty (n : Nat) :
    40 <= SuccinctClose.bpFringeTableOverhead n := by
  let c := SuccinctClose.bpFringeChunkBits (2 * n)
  have hc : 0 < c := SuccinctClose.bpFringeChunkBits_pos _
  have hpow : 2 <= 2 ^ c := by
    have hone := GenericSelect.one_lt_two_pow_of_pos hc
    omega
  have hcTwo : 2 <= c + 1 := by omega
  have hsquare : 2 * 2 <= (c + 1) * (c + 1) :=
    Nat.mul_le_mul hcTwo hcTwo
  have hrows : 8 <= SuccinctClose.bpFringeChunkRowCount c := by
    unfold SuccinctClose.bpFringeChunkRowCount
    have hmul := Nat.mul_le_mul hpow hsquare
    simpa using hmul
  have hfirst : 3 <= 2 * c + 1 := by omega
  have hsecond : 4 <= 2 * c + 2 := by omega
  have hthird : 2 <= c + 1 := by omega
  have hinner : 4 * 2 <= (2 * c + 2) * (c + 1) :=
    Nat.mul_le_mul hsecond hthird
  have hentryBound :
      24 <= SuccinctClose.bpFringeChunkEntryBound c := by
    unfold SuccinctClose.bpFringeChunkEntryBound
    have hmul := Nat.mul_le_mul hfirst hinner
    simpa using hmul
  have hlog : 4 <=
      Nat.log2 (SuccinctClose.bpFringeChunkEntryBound c) := by
    apply (Nat.le_log2 (by omega)).2
    exact Nat.le_trans (by decide : (2 : Nat) ^ 4 <= 24) hentryBound
  have hwidth : 5 <= SuccinctClose.bpFringeChunkEntryWidth c := by
    unfold SuccinctClose.bpFringeChunkEntryWidth
    omega
  unfold SuccinctClose.bpFringeTableOverhead
  change 40 <=
    SuccinctClose.bpFringeChunkRowCount c *
      SuccinctClose.bpFringeChunkEntryWidth c
  have hmul := Nat.mul_le_mul hrows hwidth
  simpa using hmul

/-- The fixed segment tags `0..22` fit even at input size zero. -/
theorem packedReviewerCellBound_ge_forty (n : Nat) :
    40 <= packedReviewerCellBound n := by
  have hoverhead := packedReviewerFringeTableOverhead_ge_forty n
  unfold packedReviewerCellBound
    concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
  omega

/--
The canonical select budget contains the sparse-relative table's literal
512-bit additive allowance.  This is a real term of the all-size reviewer
bound, not a sampled-size estimate.
-/
theorem packedReviewerCellBound_ge_five_twelve (n : Nat) :
    512 <= packedReviewerCellBound n := by
  unfold packedReviewerCellBound
    concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
    genericSparseExceptionBPCloseAccessOverhead
    GenericSelect.canonicalSparseExceptionSelectOverhead
    GenericSelect.canonicalSparseExceptionDirectoryOverhead
    GenericSelect.sparseExceptionRelativeTableOverhead
  omega

/-- Every fixed controller scalar (`<= 512`) fits even at the smallest size. -/
theorem packedReviewerFixedScalar_fits
    (n value : Nat) (hvalue : value <= 512) :
    PackedReviewerNatFits n value := by
  have hbound := packedReviewerCellBound_ge_five_twelve n
  have hcapacity := packedReviewerCellBound_lt_two_pow_width n
  omega

/-- Sixteen dormant/control tags fit every reviewer word, including size zero. -/
theorem packedReviewerFiniteControlCode_fits
    (n code : Nat) (hcode : code < 16) : PackedReviewerNatFits n code := by
  have hbound := packedReviewerCellBound_ge_forty n
  have hcapacity := packedReviewerCellBound_lt_two_pow_width n
  omega

theorem packedReviewerLogicalControlCodes_fit
    (n : Nat) (request : PackedReviewerLogicalRequest) :
    PackedReviewerLogicalControlCodesFit n request := by
  constructor
  · apply packedReviewerFiniteControlCode_fits
    cases request.invocation.instruction <;>
      simp [packedReviewerInstructionSiteCode]
  · apply packedReviewerFiniteControlCode_fits
    cases request.site <;> simp [packedReviewerReadSiteCode]

theorem packedReviewerPhysicalControlCodes_fit
    (n : Nat) (origin : PackedReviewerPhysicalOrigin) :
    PackedReviewerPhysicalControlCodesFit n origin := by
  cases origin with
  | header =>
      exact
        { origin_tag := by
            simpa [packedReviewerPhysicalOriginCode] using
              packedReviewerFiniteControlCode_fits n 0 (by omega)
          nested_tag := by trivial }
  | sparsePrelude request =>
      exact
        { origin_tag := by
            simpa [packedReviewerPhysicalOriginCode] using
              packedReviewerFiniteControlCode_fits n 1 (by omega)
          nested_tag := by
            apply packedReviewerFiniteControlCode_fits
            cases request <;> simp [packedReviewerSparsePreludeRequestCode] }
  | wholeQuery request =>
      exact
        { origin_tag := by
            simpa [packedReviewerPhysicalOriginCode] using
              packedReviewerFiniteControlCode_fits n 2 (by omega)
          nested_tag := packedReviewerLogicalControlCodes_fit n request }

theorem packedReviewerControllerStatePhaseCode_fits
    (n : Nat) (state : PackedReviewerControllerState) :
    PackedReviewerNatFits n (packedReviewerControllerStatePhaseCode state) := by
  apply packedReviewerFiniteControlCode_fits
  cases state <;> simp [packedReviewerControllerStatePhaseCode]

theorem packedReviewerTwoMul_add_three_le_cellBound (n : Nat) :
    2 * n + 3 <= packedReviewerCellBound n := by
  have hoverhead := packedReviewerFringeTableOverhead_ge_forty n
  unfold packedReviewerCellBound
    concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
  omega

theorem packedReviewerSegment_le_twentyTwo_fits
    (n segment : Nat) (hsegment : segment <= 22) :
    PackedReviewerNatFits n segment := by
  have hbound := packedReviewerCellBound_ge_forty n
  have hcapacity := packedReviewerCellBound_lt_two_pow_width n
  omega

/-- Constructor helper separating provenance, site, segment, and index bounds. -/
theorem packedReviewerLogicalRequestOperandsFit_mk
    (n : Nat) (request : PackedReviewerLogicalRequest)
    (hinvocation :
      forall operand,
        operand ∈ packedReviewerInvocationOperands request.invocation ->
          PackedReviewerNatFits n operand)
    (hsite :
      forall operand, operand ∈ packedReviewerReadSiteOperands request.site ->
        PackedReviewerNatFits n operand)
    (hsegment : PackedReviewerNatFits n request.segment)
    (hindex : PackedReviewerNatFits n request.index) :
    PackedReviewerLogicalRequestOperandsFit n request := by
  constructor
  intro operand hopen
  simp [packedReviewerLogicalRequestOperands] at hopen
  rcases hopen with hinv | hsiteOperand | rfl | rfl
  · exact hinvocation operand hinv
  · exact hsite operand hsiteOperand
  · exact hsegment
  · exact hindex

/-- The two scalar fields of an invocation are pinned independently. -/
theorem packedReviewerInvocationOperands_fit
    (n : Nat) (invocation : PackedReviewerInvocation)
    (hargument : PackedReviewerNatFits n invocation.argument)
    (hargument2 : PackedReviewerNatFits n invocation.argument2) :
    forall operand,
      operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits n operand := by
  intro operand hmem
  simp [packedReviewerInvocationOperands] at hmem
  rcases hmem with rfl | rfl
  · exact hargument
  · exact hargument2

/-- An input-select invocation has one bounded endpoint and a zero spare field. -/
theorem packedReviewerSelectInvocation_operands_fit
    (shape : CartesianShape) (instruction : PackedReviewerInstructionSite)
    (index : Nat) (hindex : index < shape.size) :
    forall operand,
      operand ∈ packedReviewerInvocationOperands
        { instruction := instruction, argument := index } ->
      PackedReviewerNatFits shape.size operand := by
  apply packedReviewerInvocationOperands_fit
  · exact Nat.lt_trans hindex
      (packedReviewerInputSize_lt_two_pow_cellWidth shape.size)
  · exact Nat.two_pow_pos _

/-- Two canonical close positions fit as one LCA invocation. -/
theorem packedReviewerLcaInvocation_operands_fit
    (shape : CartesianShape) (leftClose rightClose : Nat)
    (hleft : leftClose < 2 * shape.size)
    (hright : rightClose < 2 * shape.size) :
    forall operand,
      operand ∈ packedReviewerInvocationOperands
        { instruction := .lcaClose
          argument := leftClose
          argument2 := rightClose } ->
      PackedReviewerNatFits shape.size operand := by
  apply packedReviewerInvocationOperands_fit
  · change leftClose < 2 ^ packedReviewerCellWidth shape.size
    have hbound := packedTwoMul_le_reviewerBound shape.size
    have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
    omega
  · change rightClose < 2 ^ packedReviewerCellWidth shape.size
    have hbound := packedTwoMul_le_reviewerBound shape.size
    have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
    omega

/-- A valid close-plus-one operand fits the final-rank invocation. -/
theorem packedReviewerFinalRankInvocation_operands_fit
    (shape : CartesianShape) (answerClose : Nat)
    (hanswer : answerClose < 2 * shape.size) :
    forall operand,
      operand ∈ packedReviewerInvocationOperands
        { instruction := .finalRank, argument := answerClose + 1 } ->
      PackedReviewerNatFits shape.size operand := by
  apply packedReviewerInvocationOperands_fit
  · change answerClose + 1 < 2 ^ packedReviewerCellWidth shape.size
    have hbound := packedReviewerTwoMul_add_three_le_cellBound shape.size
    have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
    omega
  · change 0 < 2 ^ packedReviewerCellWidth shape.size
    exact Nat.two_pow_pos _

/-- The size-only select leaf returns the independent canonical close value. -/
theorem packedSelectCloseLeaf_global_value_eq_reference
    (shape : CartesianShape) (index : Nat) :
    (packedSelectCloseLeaf
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size index).value =
        SuccinctSpace.bpCloseOfInorder? shape index := by
  rw [← packedSelectCloseLeaf_eq shape
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) index]
  rw [concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_globalReadStore]
  have href :=
    concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted
      shape index
  have hvalue := congrArg Costed.value href
  have hexact := concreteBPNativeSelectCloseInterpretedCosted_exact shape index
  exact hvalue.trans (by simpa [Costed.erase] using hexact)

/-- A valid canonical select returns one close position below `2n`. -/
theorem packedSelectCloseLeaf_global_value_some_and_bound
    (shape : CartesianShape) (index : Nat) (hindex : index < shape.size) :
    exists close,
      (packedSelectCloseLeaf
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size index).value =
          some close ∧
        close < 2 * shape.size := by
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt shape hindex with
    ⟨close, hclose⟩
  refine ⟨close, ?_, ?_⟩
  · rw [packedSelectCloseLeaf_global_value_eq_reference, hclose]
  · simpa [CartesianShape.bpCode_length shape] using
      SuccinctSpace.bpCloseOfInorder?_bounds shape hclose

/-- Every charged fringe-table row index fits the reviewer word. -/
theorem packedReviewerFringeCount_lt_two_pow (n : Nat) :
    packedReviewerFringeCount n < 2 ^ packedReviewerCellWidth n := by
  let c := SuccinctClose.bpFringeChunkBits (2 * n)
  have hwidth : 0 < SuccinctClose.bpFringeChunkEntryWidth c := by
    unfold SuccinctClose.bpFringeChunkEntryWidth
    omega
  have hcountOverhead :
      packedReviewerFringeCount n <=
        SuccinctClose.bpFringeTableOverhead n := by
    simpa [packedReviewerFringeCount, SuccinctClose.bpFringeTableOverhead, c]
      using
        (Nat.le_mul_of_pos_right
          (SuccinctClose.bpFringeChunkRowCount c) hwidth)
  have hoverheadBound :
      SuccinctClose.bpFringeTableOverhead n <= packedReviewerCellBound n := by
    unfold packedReviewerCellBound
      concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
    omega
  have hcapacity := packedReviewerCellBound_lt_two_pow_width n
  omega

/-- Every charged select-chunk-table row index fits the reviewer word. -/
theorem packedReviewerSelectChunkCount_lt_two_pow (n : Nat) :
    packedReviewerSelectChunkCount n < 2 ^ packedReviewerCellWidth n := by
  let c := SuccinctClose.bpFringeChunkBits (2 * n)
  have hwidth : 0 < SuccinctClose.bpChunkSelectEntryWidth c := by
    unfold SuccinctClose.bpChunkSelectEntryWidth
    omega
  have hcountOverhead :
      packedReviewerSelectChunkCount n <=
        SuccinctClose.bpChunkSelectTableOverhead n := by
    simpa [packedReviewerSelectChunkCount,
      SuccinctClose.bpChunkSelectTableOverhead, c] using
        (Nat.le_mul_of_pos_right
          (SuccinctClose.bpChunkSelectRowCount c) hwidth)
  have hoverheadBound :
      SuccinctClose.bpChunkSelectTableOverhead n <=
        packedReviewerCellBound n := by
    unfold packedReviewerCellBound
      concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
    omega
  have hcapacity := packedReviewerCellBound_lt_two_pow_width n
  omega

private theorem packedReviewerContainedSourceCount_lt_two_pow
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources)
    (count : Nat)
    (hcount :
      count <=
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
          shape source).length) :
    count < 2 ^ packedReviewerCellWidth shape.size := by
  have hsource := packedReviewerSourceOffset_fits shape source hmem
  have hpayload := packedReviewerPayloadBits_length_eq shape
  have hbound := packedReviewerPayloadLength_le_bound shape
  have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
  unfold packedReviewerCellBound at hcapacity
  omega

/-- Every canonical local-entry row index fits the reviewer word. -/
theorem packedReviewerLocalSlots_lt_two_pow (shape : CartesianShape) :
    packedLocalSlots shape.size <
      2 ^ packedReviewerCellWidth shape.size := by
  have hlength := packedReviewerSourceBitLength_eq shape
    ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence
  have hwidth : 0 < packedLocalWidth shape.size := by
    unfold packedLocalWidth
    exact SuccinctRank.machineWordBits_pos _
  have hcount :
      packedLocalSlots shape.size <=
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectLocalBaseOccurrence).length := by
    have hmul := Nat.le_mul_of_pos_right (packedLocalSlots shape.size) hwidth
    have heq :
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectLocalBaseOccurrence).length =
          packedLocalSlots shape.size * packedLocalWidth shape.size := by
      simpa [packedReviewerSourceBitLength, packedSourceBitLength,
        packedSourceWordCount, packedSourceStride] using hlength
    rw [heq]
    exact hmul
  exact packedReviewerContainedSourceCount_lt_two_pow shape
    .selectLocalBaseOccurrence (by
      simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
    (packedLocalSlots shape.size) hcount

/-- Every canonical long-relative row index fits the reviewer word. -/
theorem packedReviewerLongRelativeSlots_lt_two_pow
    (shape : CartesianShape) :
    packedLongRelativeSlots shape.size (longCount shape) <
      2 ^ packedReviewerCellWidth shape.size := by
  have hlength := packedReviewerSourceBitLength_eq shape
    ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLongRelative
  have hwidth : 0 < packedSuperWidth shape.size := by
    unfold packedSuperWidth
    exact SuccinctRank.machineWordBits_pos _
  have hcount :
      packedLongRelativeSlots shape.size (longCount shape) <=
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectLongRelative).length := by
    have hmul := Nat.le_mul_of_pos_right
      (packedLongRelativeSlots shape.size (longCount shape)) hwidth
    have heq :
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectLongRelative).length =
          packedLongRelativeSlots shape.size (longCount shape) *
            packedSuperWidth shape.size := by
      simpa [packedReviewerSourceBitLength, packedSourceBitLength,
        packedSourceWordCount, packedSourceStride] using hlength
    rw [heq]
    exact hmul
  exact packedReviewerContainedSourceCount_lt_two_pow shape
    .selectLongRelative (by
      simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
    (packedLongRelativeSlots shape.size (longCount shape)) hcount

/-- Every actual canonical sparse-relative row index fits the reviewer word. -/
theorem packedReviewerSparseCount_lt_two_pow (shape : CartesianShape) :
    packedReviewerSparseCount shape <
      2 ^ packedReviewerCellWidth shape.size := by
  have hlength := packedReviewerSourceBitLength_eq shape
    ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative
  have hwidth : 0 < packedLocalWidth shape.size := by
    unfold packedLocalWidth
    exact SuccinctRank.machineWordBits_pos _
  have hcount :
      packedReviewerSparseCount shape <=
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectSparseRelative).length := by
    have hmul := Nat.le_mul_of_pos_right
      (packedReviewerSparseCount shape) hwidth
    have heq :
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectSparseRelative).length =
          packedReviewerSparseCount shape * packedLocalWidth shape.size := by
      simpa [packedReviewerSourceBitLength] using hlength
    rw [heq]
    exact hmul
  exact packedReviewerContainedSourceCount_lt_two_pow shape
    .selectSparseRelative (by
      simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources])
    (packedReviewerSparseCount shape) hcount

/-- A successful canonical BP-word read carries a fitting logical index. -/
theorem packedReviewerSuccessfulBPIndex_fits
    (shape : CartesianShape) {index : Nat} {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 index =
        some word) :
    PackedReviewerNatFits shape.size index := by
  have hlt := packedReviewerGlobalReadStore_legacy_index_lt_count shape
    (segment := 0) (index := index) (by omega) (source := .bpCode) rfl hread
  have hdiv :
      2 * shape.size / packedBpCodeWordWidth shape.size <= 2 * shape.size :=
    Nat.div_le_self _ _
  have hcount :
      packedChunkCount (2 * shape.size) (packedBpCodeWordWidth shape.size) <=
        2 * shape.size + 1 := by
    unfold packedChunkCount
    split <;> omega
  have hbound := packedReviewerTwoMul_add_three_le_cellBound shape.size
  have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
  simp [packedReviewerSourceWordCount, packedSourceWordCount] at hlt
  omega

/-- A successful read of any of the four canonical local-entry fields fits. -/
theorem packedReviewerSuccessfulLocalEntryIndex_fits
    (shape : CartesianShape) {segment index : Nat} {word : List Bool}
    (hlow : 5 <= segment) (hhigh : segment <= 8)
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          segment index = some word) :
    PackedReviewerNatFits shape.size index := by
  have hbound := packedReviewerLocalSlots_lt_two_pow shape
  have hcases : segment = 5 ∨ segment = 6 ∨ segment = 7 ∨ segment = 8 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals
    first
    | exact Nat.lt_trans
        (packedReviewerGlobalReadStore_legacy_index_lt_count shape
          (segment := 5) (index := index) (by omega)
          (source := .selectLocalBaseOccurrence) rfl hread)
        (by simpa [packedReviewerSourceWordCount, packedSourceWordCount] using hbound)
    | exact Nat.lt_trans
        (packedReviewerGlobalReadStore_legacy_index_lt_count shape
          (segment := 6) (index := index) (by omega)
          (source := .selectLocalBaseWordIndex) rfl hread)
        (by simpa [packedReviewerSourceWordCount, packedSourceWordCount] using hbound)
    | exact Nat.lt_trans
        (packedReviewerGlobalReadStore_legacy_index_lt_count shape
          (segment := 7) (index := index) (by omega)
          (source := .selectLocalRankBefore) rfl hread)
        (by simpa [packedReviewerSourceWordCount, packedSourceWordCount] using hbound)
    | exact Nat.lt_trans
        (packedReviewerGlobalReadStore_legacy_index_lt_count shape
          (segment := 8) (index := index) (by omega)
          (source := .selectLocalFirstOffset) rfl hread)
        (by simpa [packedReviewerSourceWordCount, packedSourceWordCount] using hbound)

/-- A successful canonical long-relative read carries a fitting slot. -/
theorem packedReviewerSuccessfulLongRelativeIndex_fits
    (shape : CartesianShape) {index : Nat} {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 12 index =
        some word) :
    PackedReviewerNatFits shape.size index := by
  exact Nat.lt_trans
    (packedReviewerGlobalReadStore_legacy_index_lt_count shape
      (segment := 12) (index := index) (by omega)
      (source := .selectLongRelative) rfl hread)
    (by simpa [packedReviewerSourceWordCount, packedSourceWordCount] using
      packedReviewerLongRelativeSlots_lt_two_pow shape)

/-- A successful canonical sparse-relative read carries a fitting slot. -/
theorem packedReviewerSuccessfulSparseRelativeIndex_fits
    (shape : CartesianShape) {index : Nat} {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 16 index =
        some word) :
    PackedReviewerNatFits shape.size index := by
  exact Nat.lt_trans
    (packedReviewerGlobalReadStore_legacy_index_lt_count shape
      (segment := 16) (index := index) (by omega)
      (source := .selectSparseRelative) rfl hread)
    (by simpa [packedReviewerSourceWordCount] using
      packedReviewerSparseCount_lt_two_pow shape)

/-- One successful long-relative phase has one fitting request. -/
theorem packedReviewerLongRelative_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (base slot : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 12 slot =
        some word) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerSelectNextRequest packedReviewerSelectConsumeReply 1
      (.longRelative invocation base slot) := by
  have hrequest :
      PackedReviewerLogicalRequestOperandsFit shape.size
        { invocation := invocation
          site := .relativeOffset
          segment := 12
          index := slot } := by
    apply packedReviewerLogicalRequestOperandsFit_mk
    · exact hinvocation
    · simp [packedReviewerReadSiteOperands]
    · exact packedReviewerSegment_le_twentyTwo_fits shape.size 12 (by omega)
    · exact packedReviewerSuccessfulLongRelativeIndex_fits shape hread
  simp [PackedReviewerRequestsFitFrom, packedReviewerSelectNextRequest,
    packedReviewerSelectConsumeReply, hrequest]

/-- One successful sparse-relative phase has one fitting request. -/
theorem packedReviewerSparseRelative_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (base slot : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 16 slot =
        some word) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerSelectNextRequest packedReviewerSelectConsumeReply 1
      (.sparseRelative invocation base slot) := by
  have hrequest :
      PackedReviewerLogicalRequestOperandsFit shape.size
        { invocation := invocation
          site := .relativeOffset
          segment := 16
          index := slot } := by
    apply packedReviewerLogicalRequestOperandsFit_mk
    · exact hinvocation
    · simp [packedReviewerReadSiteOperands]
    · exact packedReviewerSegment_le_twentyTwo_fits shape.size 16 (by omega)
    · exact packedReviewerSuccessfulSparseRelativeIndex_fits shape hread
  simp [PackedReviewerRequestsFitFrom, packedReviewerSelectNextRequest,
    packedReviewerSelectConsumeReply, hrequest]

/-- The first dense BP-word phase has one fitting request when it succeeds. -/
theorem packedReviewerDenseFirstWord_request_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index basePosition baseOccurrence : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0
          (basePosition / packedSelectWordSize shape.size) = some word) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerSelectNextRequest packedReviewerSelectConsumeReply 1
      (.denseFirstWord invocation shape.size index basePosition
        baseOccurrence) := by
  let slot := basePosition / packedSelectWordSize shape.size
  have hslot := packedReviewerSuccessfulBPIndex_fits shape hread
  have hrequest :
      PackedReviewerLogicalRequestOperandsFit shape.size
        { invocation := invocation
          site := .denseBPWord slot
          segment := 0
          index := slot } := by
    apply packedReviewerLogicalRequestOperandsFit_mk
    · exact hinvocation
    · intro operand hmem
      simp [packedReviewerReadSiteOperands] at hmem
      subst operand
      exact hslot
    · exact packedReviewerSegment_le_twentyTwo_fits shape.size 0 (by omega)
    · exact hslot
  simpa [slot, PackedReviewerRequestsFitFrom,
    packedReviewerSelectNextRequest] using And.intro hrequest trivial

/-- The second dense BP-word phase has one fitting request when it succeeds. -/
theorem packedReviewerDenseSecondWord_request_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index basePosition baseOccurrence beforeFirst uptoFirst : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0
          (basePosition / packedSelectWordSize shape.size + 1) = some word) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerSelectNextRequest packedReviewerSelectConsumeReply 1
      (.denseSecondWord invocation shape.size index basePosition
        baseOccurrence beforeFirst uptoFirst) := by
  let slot := basePosition / packedSelectWordSize shape.size + 1
  have hslot := packedReviewerSuccessfulBPIndex_fits shape hread
  have hrequest :
      PackedReviewerLogicalRequestOperandsFit shape.size
        { invocation := invocation
          site := .denseBPWord slot
          segment := 0
          index := slot } := by
    apply packedReviewerLogicalRequestOperandsFit_mk
    · exact hinvocation
    · intro operand hmem
      simp [packedReviewerReadSiteOperands] at hmem
      subst operand
      exact hslot
    · exact packedReviewerSegment_le_twentyTwo_fits shape.size 0 (by omega)
    · exact hslot
  simpa [slot, PackedReviewerRequestsFitFrom,
    packedReviewerSelectNextRequest] using And.intro hrequest trivial

private theorem packedReviewerEntryRequest_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (site : PackedReviewerReadSite) (segment index : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    (hsite : packedReviewerReadSiteOperands site = [])
    (hsegment : segment <= 22)
    (hindex : PackedReviewerNatFits shape.size index) :
    PackedReviewerLogicalRequestOperandsFit shape.size
      { invocation := invocation, site := site, segment := segment,
        index := index } := by
  apply packedReviewerLogicalRequestOperandsFit_mk
  · exact hinvocation
  · intro operand hopen
    rw [hsite] at hopen
    simp at hopen
  · exact packedReviewerSegment_le_twentyTwo_fits shape.size segment hsegment
  · exact hindex

/-- The four fixed select-entry field reads preserve the same bounded index. -/
theorem packedReviewerEntryStart_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerEntryKind) (index : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    (hindex : PackedReviewerNatFits shape.size index) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerEntryNextRequest packedReviewerEntryConsumeReply 4
      (.baseOccurrence invocation kind index) := by
  have hbase : kind.segmentBase <= 5 := by
    cases kind <;> simp [PackedReviewerEntryKind.segmentBase]
  have h0 := packedReviewerEntryRequest_fit shape invocation
    .entryBaseOccurrence kind.segmentBase index hinvocation rfl (by omega) hindex
  have h1 := packedReviewerEntryRequest_fit shape invocation
    .entryBaseWordIndex (kind.segmentBase + 1) index hinvocation rfl
      (by omega) hindex
  have h2 := packedReviewerEntryRequest_fit shape invocation
    .entryRankBefore (kind.segmentBase + 2) index hinvocation rfl
      (by omega) hindex
  have h3 := packedReviewerEntryRequest_fit shape invocation
    .entryFirstOffset (kind.segmentBase + 3) index hinvocation rfl
      (by omega) hindex
  simp only [PackedReviewerRequestsFitFrom,
    packedReviewerEntryNextRequest, packedReviewerEntryConsumeReply]
  exact ⟨h0, h1, h2, h3, trivial⟩

/-- The initial super-entry phase of every valid select has fitting requests. -/
theorem packedReviewerSelectSuperEntryStart_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size) :
    let slot := GenericSelect.selectSuperSlot index
      (packedSelectSuperStride shape.size)
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerEntryNextRequest packedReviewerEntryConsumeReply 4
      (.baseOccurrence invocation .super slot) := by
  dsimp only
  have hslotLe :
      GenericSelect.selectSuperSlot index
          (packedSelectSuperStride shape.size) <= index := by
    unfold GenericSelect.selectSuperSlot
    exact Nat.div_le_self _ _
  have hslot :
      PackedReviewerNatFits shape.size
        (GenericSelect.selectSuperSlot index
          (packedSelectSuperStride shape.size)) :=
    Nat.lt_of_le_of_lt hslotLe
      (Nat.lt_trans hindex
        (packedReviewerInputSize_lt_two_pow_cellWidth shape.size))
  exact packedReviewerEntryStart_requests_fit shape invocation .super
    (GenericSelect.selectSuperSlot index
      (packedSelectSuperStride shape.size)) hinvocation hslot

/-- A successful canonical local entry has four fitting field requests. -/
theorem packedReviewerSelectLocalEntryStart_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (localSlot : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 5 localSlot =
        some word) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerEntryNextRequest packedReviewerEntryConsumeReply 4
      (.baseOccurrence invocation .local localSlot) := by
  exact packedReviewerEntryStart_requests_fit shape invocation .local localSlot
    hinvocation
    (packedReviewerSuccessfulLocalEntryIndex_fits shape (segment := 5)
      (by omega) (by omega) hread)

private theorem packedReviewerRankQueryPos_fits
    (n pos : Nat) (kind : PackedReviewerRankKind) :
    PackedReviewerNatFits n (packedReviewerRankQueryPos kind n pos) := by
  have hq := Nat.min_le_right pos (kind.bitLength n)
  cases kind with
  | selectLong =>
      have hslots := packedSuperSlots_le_input n
      have hn := packedReviewerInputSize_lt_two_pow_cellWidth n
      simpa [PackedReviewerRankKind.bitLength] using
        Nat.lt_of_le_of_lt (Nat.le_trans hq hslots) hn
  | selectSparse =>
      have hslots := packedSparseSlots_le_input n
      have hn := packedReviewerInputSize_lt_two_pow_cellWidth n
      simpa [PackedReviewerRankKind.bitLength] using
        Nat.lt_of_le_of_lt (Nat.le_trans hq hslots) hn
  | close =>
      have htwo := packedTwoMul_le_reviewerBound n
      have hcapacity := packedReviewerCellBound_lt_two_pow_width n
      change Nat.min pos (2 * n) < 2 ^ packedReviewerCellWidth n
      have hqBound : Nat.min pos (2 * n) <= packedReviewerCellBound n :=
        Nat.le_trans (by simpa [PackedReviewerRankKind.bitLength] using hq) htwo
      exact Nat.lt_of_le_of_lt
        (Nat.le_trans hqBound (Nat.le_add_right _ _)) hcapacity

private theorem packedReviewerRankFixedRequest_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (site : PackedReviewerReadSite) (segment index : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    (hsite : packedReviewerReadSiteOperands site = [])
    (hsegment : segment <= 22)
    (hindex : PackedReviewerNatFits shape.size index) :
    PackedReviewerLogicalRequestOperandsFit shape.size
      { invocation := invocation, site := site, segment := segment,
        index := index } :=
  packedReviewerEntryRequest_fit shape invocation site segment index
    hinvocation hsite hsegment hindex

private theorem packedReviewerRankFold_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerRankKind) (word : List Bool)
    (effectiveLimit base fuel j remaining acc : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    (hremaining : remaining <= fuel) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerRankNextRequest packedReviewerRankConsumeReply fuel
      (.fold invocation kind shape.size word effectiveLimit j remaining acc
        base) := by
  induction fuel generalizing j remaining acc with
  | zero =>
      have : remaining = 0 := by omega
      subst remaining
      trivial
  | succ fuel ih =>
      cases remaining with
      | zero =>
          simp [PackedReviewerRequestsFitFrom,
            packedReviewerRankNextRequest]
      | succ remaining =>
          let c := packedFringeChunkBits shape.size
          let sliceLen :=
            SuccinctClose.bpWordChunkSliceLen c effectiveLimit j
          let slot :=
            SuccinctClose.bpFringeChunkSlot c
              (SuccinctClose.bpFringeWindowChunkValue c word j)
              sliceLen sliceLen
          have hslotCount : slot < packedReviewerFringeCount shape.size := by
            have hslot := SuccinctClose.bpFringeChunkSlot_lt_rowCount
              (SuccinctClose.bpFringeWindowChunkValue_lt c word j)
              (SuccinctClose.bpWordChunkSliceLen_le c effectiveLimit j)
              (SuccinctClose.bpWordChunkSliceLen_le c effectiveLimit j)
            simpa [slot, sliceLen, c, packedReviewerFringeCount,
              packedFringeChunkBits] using hslot
          have hslot : PackedReviewerNatFits shape.size slot :=
            Nat.lt_trans hslotCount
              (packedReviewerFringeCount_lt_two_pow shape.size)
          have hrequest :
              PackedReviewerLogicalRequestOperandsFit shape.size
                { invocation := invocation
                  site := .rankChunk
                  segment := 21
                  index := slot } :=
            packedReviewerRankFixedRequest_fit shape invocation .rankChunk 21
              slot hinvocation rfl (by omega) hslot
          simp only [PackedReviewerRequestsFitFrom,
            packedReviewerRankNextRequest]
          change
            PackedReviewerLogicalRequestOperandsFit shape.size
                { invocation := invocation
                  site := .rankChunk
                  segment := 21
                  index := slot } ∧ _
          refine ⟨hrequest, ?_⟩
          by_cases hlast : remaining = 0
          · subst remaining
            cases fuel <;>
              simp [packedReviewerRankConsumeReply,
                PackedReviewerRequestsFitFrom, packedReviewerRankNextRequest]
          · have hremaining' : remaining <= fuel := by omega
            simpa [packedReviewerRankConsumeReply, hlast, c, sliceLen, slot]
              using ih (j + 1) remaining
                (SuccinctClose.bpWordRankStepDecoded c kind.target sliceLen acc
                  (packedReviewerDecodeNat
                    ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                      21 slot)))
                hremaining'

private theorem packedReviewerRankStartFold_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerRankKind) (word : List Bool) (limit base : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerRankNextRequest packedReviewerRankConsumeReply 8
      (packedReviewerRankStartFold invocation kind shape.size word limit base) := by
  let effectiveLimit := SuccinctClose.bpWordRankEffLimit word limit
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits shape.size)
      effectiveLimit
  by_cases hcount : count = 0
  · simp [packedReviewerRankStartFold, effectiveLimit, count, hcount,
      PackedReviewerRequestsFitFrom, packedReviewerRankNextRequest]
  · have hcountLe : count <= 8 :=
      SuccinctClose.bpWordChunkCount_le_eight _ _
    simpa [packedReviewerRankStartFold, effectiveLimit, count, hcount] using
      packedReviewerRankFold_requests_fit shape invocation kind word
        effectiveLimit base 8 0 count 0 hinvocation hcountLe

/-- Rank performs three fixed reads and at most eight charged chunk reads. -/
theorem packedReviewerRankStart_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerRankKind) (pos : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerRankNextRequest packedReviewerRankConsumeReply 11
      (.superSample invocation kind shape.size pos) := by
  let q := packedReviewerRankQueryPos kind shape.size pos
  have hq : PackedReviewerNatFits shape.size q :=
    packedReviewerRankQueryPos_fits shape.size pos kind
  have hsuperIndex :
      PackedReviewerNatFits shape.size
        (q / kind.wordSize shape.size / kind.blocksPerSuper shape.size) := by
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)) hq
  have hblockIndex :
      PackedReviewerNatFits shape.size (q / kind.wordSize shape.size) :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hq
  have hsuperSegment : kind.superSegment <= 17 := by
    cases kind <;> simp [PackedReviewerRankKind.superSegment]
  have hsuper := packedReviewerRankFixedRequest_fit shape invocation .rankSuper
    kind.superSegment
    (q / kind.wordSize shape.size / kind.blocksPerSuper shape.size)
    hinvocation rfl (by omega) hsuperIndex
  have hblock := packedReviewerRankFixedRequest_fit shape invocation .rankBlock
    kind.blockSegment (q / kind.wordSize shape.size)
    hinvocation rfl (by
      unfold PackedReviewerRankKind.blockSegment
      omega) hblockIndex
  have hword := packedReviewerRankFixedRequest_fit shape invocation .rankWord
    kind.wordSegment (q / kind.wordSize shape.size)
    hinvocation rfl (by
      unfold PackedReviewerRankKind.wordSegment
      omega) hblockIndex
  simp only [PackedReviewerRequestsFitFrom, packedReviewerRankNextRequest,
    packedReviewerRankConsumeReply]
  refine ⟨hsuper, hblock, hword, ?_⟩
  generalize packedReviewerDecodeNat
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        kind.superSegment
        (q / kind.wordSize shape.size / kind.blocksPerSuper shape.size)) =
    superValue
  generalize packedReviewerDecodeNat
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        kind.blockSegment (q / kind.wordSize shape.size)) = blockValue
  generalize
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        kind.wordSegment (q / kind.wordSize shape.size) = wordValue
  cases superValue with
  | none => simp [PackedReviewerRequestsFitFrom, packedReviewerRankNextRequest]
  | some superValue =>
      cases blockValue with
      | none => simp [PackedReviewerRequestsFitFrom, packedReviewerRankNextRequest]
      | some blockValue =>
          cases wordValue with
          | none =>
              simp [PackedReviewerRequestsFitFrom, packedReviewerRankNextRequest]
          | some wordValue =>
              change PackedReviewerRequestsFitFrom shape.size
                (concreteBPNativeSuccinctRMQGlobalReadStore shape)
                packedReviewerRankNextRequest packedReviewerRankConsumeReply 8
                (packedReviewerRankStartFold invocation kind shape.size
                  wordValue
                  (q - q / kind.wordSize shape.size * kind.wordSize shape.size)
                  (superValue + blockValue))
              exact packedReviewerRankStartFold_requests_fit shape invocation kind
                wordValue
                (q - q / kind.wordSize shape.size * kind.wordSize shape.size)
                (superValue + blockValue) hinvocation

private theorem packedReviewerWordSelectRankReply_exact
    (shape : CartesianShape) (word : List Bool) (j : Nat) :
    let c := packedFringeChunkBits shape.size
    let value := SuccinctClose.bpFringeWindowChunkValue c word j
    let sliceLen := SuccinctClose.bpWordChunkSliceLen c word.length j
    let slot := SuccinctClose.bpFringeChunkSlot c value sliceLen sliceLen
    packedReviewerDecodeNat
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21 slot) =
      some (SuccinctClose.bpFringeChunkPacked c value sliceLen sliceLen) := by
  dsimp only
  unfold packedReviewerDecodeNat
  rw [show (21 : Nat) = concreteBPNativeFringeChunkTraceSegment by rfl]
  rw [concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable]
  rw [packedFringeChunkBits_eq]
  rw [(SuccinctClose.bpFringeChunkTable
    (packedFringeChunkBits shape.size)).read_exact]
  exact SuccinctClose.bpFringeChunkEntries_getElem
    (SuccinctClose.bpFringeWindowChunkValue_lt
      (packedFringeChunkBits shape.size) word j)
    (SuccinctClose.bpWordChunkSliceLen_le
      (packedFringeChunkBits shape.size) word.length j)
    (SuccinctClose.bpWordChunkSliceLen_le
      (packedFringeChunkBits shape.size) word.length j)

private theorem packedReviewerWordSelectSelectChunk_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (target : Bool) (word : List Bool) (j remaining occurrence fuel : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    (hoccurrence : occurrence <= packedFringeChunkBits shape.size)
    (hfuel : 0 < fuel) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerWordSelectNextRequest
      packedReviewerWordSelectConsumeReply fuel
      (.selectChunk invocation shape.size target word j remaining occurrence) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      let c := packedFringeChunkBits shape.size
      let value := SuccinctClose.bpFringeWindowChunkValue c word j
      let slot := SuccinctClose.bpChunkSelectSlot c value occurrence
      have hslotCount : slot < packedReviewerSelectChunkCount shape.size := by
        have hslot := SuccinctClose.bpChunkSelectSlot_lt_rowCount
          (SuccinctClose.bpFringeWindowChunkValue_lt c word j) hoccurrence
        simpa [slot, value, c, packedReviewerSelectChunkCount,
          packedFringeChunkBits] using hslot
      have hslot : PackedReviewerNatFits shape.size slot :=
        Nat.lt_trans hslotCount
          (packedReviewerSelectChunkCount_lt_two_pow shape.size)
      have hrequest :
          PackedReviewerLogicalRequestOperandsFit shape.size
            { invocation := invocation
              site := .selectChunkValue
              segment := 22
              index := slot } :=
        packedReviewerRankFixedRequest_fit shape invocation .selectChunkValue 22
          slot hinvocation rfl (by omega) hslot
      simp only [PackedReviewerRequestsFitFrom,
        packedReviewerWordSelectNextRequest]
      change
        PackedReviewerLogicalRequestOperandsFit shape.size
            { invocation := invocation
              site := .selectChunkValue
              segment := 22
              index := slot } ∧ _
      refine ⟨hrequest, ?_⟩
      cases fuel <;>
        simp [packedReviewerWordSelectConsumeReply,
          PackedReviewerRequestsFitFrom, packedReviewerWordSelectNextRequest]

private theorem packedReviewerWordSelectRankChunk_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (target : Bool) (word : List Bool) (j remaining occurrence : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerWordSelectNextRequest
      packedReviewerWordSelectConsumeReply (remaining + 1)
      (.rankChunk invocation shape.size target word j remaining occurrence) := by
  induction remaining generalizing j occurrence with
  | zero =>
      simp [PackedReviewerRequestsFitFrom,
        packedReviewerWordSelectNextRequest]
  | succ remaining ih =>
      let c := packedFringeChunkBits shape.size
      let value := SuccinctClose.bpFringeWindowChunkValue c word j
      let sliceLen := SuccinctClose.bpWordChunkSliceLen c word.length j
      let slot := SuccinctClose.bpFringeChunkSlot c value sliceLen sliceLen
      let packed := SuccinctClose.bpFringeChunkPacked c value sliceLen sliceLen
      have hvalue : value < 2 ^ c :=
        SuccinctClose.bpFringeWindowChunkValue_lt c word j
      have hsliceLen : sliceLen <= c :=
        SuccinctClose.bpWordChunkSliceLen_le c word.length j
      have hslotCount : slot < packedReviewerFringeCount shape.size := by
        have hslot := SuccinctClose.bpFringeChunkSlot_lt_rowCount
          hvalue hsliceLen hsliceLen
        simpa [slot, value, sliceLen, c, packedReviewerFringeCount,
          packedFringeChunkBits] using hslot
      have hslot : PackedReviewerNatFits shape.size slot :=
        Nat.lt_trans hslotCount
          (packedReviewerFringeCount_lt_two_pow shape.size)
      have hrequest :
          PackedReviewerLogicalRequestOperandsFit shape.size
            { invocation := invocation
              site := .selectChunkRank
              segment := 21
              index := slot } :=
        packedReviewerRankFixedRequest_fit shape invocation .selectChunkRank 21
          slot hinvocation rfl (by omega) hslot
      have hreply :
          packedReviewerDecodeNat
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                21 slot) = some packed := by
        simpa [c, value, sliceLen, slot, packed] using
          packedReviewerWordSelectRankReply_exact shape word j
      let rank := Succinct.rankPrefix target
        (SuccinctClose.bpFringeChunkPattern c value) sliceLen
      have hrank :
          SuccinctClose.bpChunkRankOfEntry c target sliceLen packed = rank := by
        simpa [rank, packed] using
          (SuccinctClose.bpChunkRankOfEntry_packed c target hvalue hsliceLen)
      have hrankLe : rank <= c := by
        have hle := Succinct.rankPrefix_le_length target
          (SuccinctClose.bpFringeChunkPattern c value) sliceLen
        simpa [rank] using hle
      simp only [PackedReviewerRequestsFitFrom,
        packedReviewerWordSelectNextRequest]
      change
        PackedReviewerLogicalRequestOperandsFit shape.size
            { invocation := invocation
              site := .selectChunkRank
              segment := 21
              index := slot } ∧ _
      refine ⟨hrequest, ?_⟩
      change PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerWordSelectNextRequest
        packedReviewerWordSelectConsumeReply (remaining + 1)
        (packedReviewerWordSelectConsumeReply
          (.rankChunk invocation shape.size target word j (remaining + 1)
            occurrence)
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21 slot))
      by_cases hselect : occurrence < rank
      · have hstate :
            packedReviewerWordSelectConsumeReply
                (.rankChunk invocation shape.size target word j (remaining + 1)
                  occurrence)
                ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                  21 slot) =
              .selectChunk invocation shape.size target word j (remaining + 1)
                occurrence := by
          simp only [packedReviewerWordSelectConsumeReply]
          rw [hreply]
          simp only [Option.getD_some]
          rw [hrank, if_pos hselect]
        rw [hstate]
        exact
          packedReviewerWordSelectSelectChunk_requests_fit shape invocation
            target word j (remaining + 1) occurrence (remaining + 1)
            hinvocation (by omega) (by omega)
      · by_cases hlast : remaining = 0
        · subst remaining
          have hstate :
              packedReviewerWordSelectConsumeReply
                  (.rankChunk invocation shape.size target word j 1 occurrence)
                  ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                    21 slot) = .done none := by
            simp only [packedReviewerWordSelectConsumeReply]
            rw [hreply]
            simp only [Option.getD_some]
            rw [hrank, if_neg hselect]
            rfl
          rw [hstate]
          trivial
        · have hstate :
              packedReviewerWordSelectConsumeReply
                  (.rankChunk invocation shape.size target word j (remaining + 1)
                    occurrence)
                  ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                    21 slot) =
                .rankChunk invocation shape.size target word (j + 1) remaining
                  (occurrence - rank) := by
            simp only [packedReviewerWordSelectConsumeReply]
            rw [hreply]
            simp only [Option.getD_some]
            rw [hrank, if_neg hselect, if_neg hlast]
          rw [hstate]
          exact ih (j + 1) (occurrence - rank)

/--
The canonical word-select fold performs one honest rank-table read per chunk
and at most one select-table read; every dynamic operand fits at every size.
-/
theorem packedReviewerWordSelectStart_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (target : Bool) (word : List Bool) (occurrence : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand) :
    let state := packedReviewerWordSelectStart invocation shape.size target word
      occurrence
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerWordSelectNextRequest
      packedReviewerWordSelectConsumeReply
      (packedReviewerWordSelectRemaining state) state := by
  dsimp only
  let count := SuccinctClose.bpWordChunkCount
    (packedFringeChunkBits shape.size) word.length
  by_cases hcount : count = 0
  · simp [packedReviewerWordSelectStart, count, hcount,
      packedReviewerWordSelectRemaining, PackedReviewerRequestsFitFrom,
      packedReviewerWordSelectNextRequest]
  · simpa [packedReviewerWordSelectStart, count, hcount,
      packedReviewerWordSelectRemaining] using
        packedReviewerWordSelectRankChunk_requests_fit shape invocation target
          word 0 count occurrence hinvocation

private theorem packedReviewerFringe_read_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (window : List Bool) (relLo relHi j remaining : Nat)
    (foldState : Nat × Option (Nat × Nat))
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerFringeNextRequest packedReviewerFringeConsumeReply remaining
      (.chunk invocation shape.size window relLo relHi j remaining foldState) := by
  induction remaining generalizing j foldState with
  | zero => trivial
  | succ remaining ih =>
      let c := packedFringeChunkBits shape.size
      let slot :=
        SuccinctClose.bpFringeChunkSlot c
          (SuccinctClose.bpFringeWindowChunkValue c window j)
          (SuccinctClose.bpFringeChunkStartOff c relLo j)
          (SuccinctClose.bpFringeChunkEndOff c relHi j)
      have hslotCount : slot < packedReviewerFringeCount shape.size := by
        have hslot := SuccinctClose.bpFringeChunkSlot_lt_rowCount
          (SuccinctClose.bpFringeWindowChunkValue_lt c window j)
          (SuccinctClose.bpFringeChunkStartOff_le c relLo j)
          (SuccinctClose.bpFringeChunkEndOff_le c relHi j)
        simpa [slot, c, packedReviewerFringeCount, packedFringeChunkBits] using
          hslot
      have hslot : PackedReviewerNatFits shape.size slot :=
        Nat.lt_trans hslotCount (packedReviewerFringeCount_lt_two_pow shape.size)
      have hrequest :
          PackedReviewerLogicalRequestOperandsFit shape.size
            { invocation := invocation
              site := .fringeChunk slot
              segment := 21
              index := slot } := by
        apply packedReviewerLogicalRequestOperandsFit_mk
        · exact hinvocation
        · intro operand hopen
          simp [packedReviewerReadSiteOperands] at hopen
          subst operand
          exact hslot
        · exact packedReviewerSegment_le_twentyTwo_fits shape.size 21 (by omega)
        · exact hslot
      simp only [PackedReviewerRequestsFitFrom,
        packedReviewerFringeNextRequest]
      change
        PackedReviewerLogicalRequestOperandsFit shape.size
            { invocation := invocation
              site := .fringeChunk slot
              segment := 21
              index := slot } ∧ _
      refine ⟨hrequest, ?_⟩
      let nextState :=
        SuccinctClose.bpFringeChunkStepDecoded c relLo relHi j foldState
          (packedReviewerDecodeNat
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              21 slot))
      by_cases hlast : remaining = 0
      · subst remaining
        simp [packedReviewerFringeConsumeReply, PackedReviewerRequestsFitFrom,
          nextState, c, slot]
      · simpa [packedReviewerFringeConsumeReply, hlast, nextState, c, slot]
          using ih (j + 1) nextState

/-- Every fringe request is an intrinsic row of the charged table. -/
theorem packedReviewerFringeStart_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (window : List Bool) (seed relLo relHi count : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand) :
    let state := packedReviewerFringeStart invocation shape.size window seed
      relLo relHi count
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerFringeNextRequest packedReviewerFringeConsumeReply
      (packedReviewerFringeRemaining state) state := by
  dsimp only
  by_cases hcount : count = 0
  · simp [packedReviewerFringeStart, hcount,
      packedReviewerFringeRemaining, PackedReviewerRequestsFitFrom,
      packedReviewerFringeNextRequest]
  · simpa [packedReviewerFringeStart, hcount,
      packedReviewerFringeRemaining] using
        packedReviewerFringe_read_requests_fit shape invocation window
          relLo relHi 0 count (seed, none) hinvocation

private theorem packedReviewerBPWindow_read_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (blockSize close next fuel : Nat) (wordsRev : List (List Bool))
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    (hclose : close < 2 * shape.size)
    (hfour : next + fuel = 4) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerBPWindowNextRequest packedReviewerBPWindowConsumeReply fuel
      (.read invocation shape.size blockSize close next wordsRev) := by
  induction fuel generalizing next wordsRev with
  | zero => trivial
  | succ fuel ih =>
      have hnext : next < 4 := by omega
      let firstWord :=
        SuccinctClose.blockStartOf blockSize
            (SuccinctClose.blockOfClose blockSize close) /
          packedBpCodeWordWidth shape.size
      have hbase :
          SuccinctClose.blockStartOf blockSize
              (SuccinctClose.blockOfClose blockSize close) <= close :=
        SuccinctClose.blockStartOf_blockOfClose_le
      have hfirst : firstWord <= close :=
        Nat.le_trans (Nat.div_le_self _ _) hbase
      have hindexLe : firstWord + next <= 2 * shape.size + 3 := by omega
      have hindex : PackedReviewerNatFits shape.size (firstWord + next) := by
        have hbound := packedReviewerTwoMul_add_three_le_cellBound shape.size
        have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
        omega
      have hnextFits : PackedReviewerNatFits shape.size next :=
        packedReviewerSegment_le_twentyTwo_fits shape.size next (by omega)
      have hrequest :
          PackedReviewerLogicalRequestOperandsFit shape.size
            { invocation := invocation
              site := .bpWindowWord next
              segment := 0
              index := firstWord + next } := by
        apply packedReviewerLogicalRequestOperandsFit_mk
        · exact hinvocation
        · intro operand hopen
          simp [packedReviewerReadSiteOperands] at hopen
          subst operand
          exact hnextFits
        · exact packedReviewerSegment_le_twentyTwo_fits shape.size 0 (by omega)
        · exact hindex
      simp only [PackedReviewerRequestsFitFrom,
        packedReviewerBPWindowNextRequest, hnext, if_pos]
      change
        PackedReviewerLogicalRequestOperandsFit shape.size
            { invocation := invocation
              site := .bpWindowWord next
              segment := 0
              index := firstWord + next } ∧ _
      refine ⟨hrequest, ?_⟩
      by_cases hlast : next + 1 = 4
      · have hfuel0 : fuel = 0 := by omega
        subst fuel
        trivial
      · have hfour' : next + 1 + fuel = 4 := by omega
        simpa [packedReviewerBPWindowConsumeReply, hlast, firstWord] using
          ih (next + 1)
            (((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                0 (firstWord + next)).getD [] :: wordsRev)
            hfour'

/-- The four-word BP window keeps both slot and physical word index bounded. -/
theorem packedReviewerBPWindowStart_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (blockSize close : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    (hclose : close < 2 * shape.size) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerBPWindowNextRequest packedReviewerBPWindowConsumeReply 4
      (packedReviewerBPWindowStart invocation shape.size blockSize close) := by
  simpa [packedReviewerBPWindowStart] using
    packedReviewerBPWindow_read_requests_fit shape invocation blockSize close
      0 4 [] hinvocation hclose rfl

/-- All-size linear envelope for the counted fringe-table bits. -/
theorem packedReviewerFringeTableOverhead_le_linear (n : Nat) :
    SuccinctClose.bpFringeTableOverhead n <= 32768 * (n + 1) := by
  let c := SuccinctClose.bpFringeChunkBits (2 * n)
  have hwidth := SuccinctClose.bpFringeChunkEntryWidth_le c
  have hwidthPow : 3 * c + 6 <= 2 ^ (3 * c + 6) :=
    SuccinctSpace.nat_le_two_pow _
  have hrows := SuccinctClose.bpFringeChunkRowCount_le_two_pow c
  have htable :
      SuccinctClose.bpFringeTableOverhead n <= 2 ^ (6 * c + 8) := by
    unfold SuccinctClose.bpFringeTableOverhead
    change
      SuccinctClose.bpFringeChunkRowCount c *
          SuccinctClose.bpFringeChunkEntryWidth c <= 2 ^ (6 * c + 8)
    calc
      SuccinctClose.bpFringeChunkRowCount c *
          SuccinctClose.bpFringeChunkEntryWidth c <=
        2 ^ (3 * c + 2) * 2 ^ (3 * c + 6) :=
          Nat.mul_le_mul hrows (by omega)
      _ = 2 ^ (6 * c + 8) := by
        rw [← Nat.pow_add]
        congr 1
        omega
  have hc : c = Nat.log2 (2 * n) / 8 + 1 := rfl
  have hexponent : 6 * c + 8 <= Nat.log2 (2 * n) + 14 := by
    rw [hc]
    omega
  have hmono :
      2 ^ (6 * c + 8) <= 2 ^ (Nat.log2 (2 * n) + 14) :=
    Nat.pow_le_pow_right (by omega) hexponent
  have hpow14 : (2 : Nat) ^ 14 = 16384 := by decide
  cases n with
  | zero =>
      simp [SuccinctClose.bpFringeTableOverhead,
        SuccinctClose.bpFringeChunkBits,
        SuccinctClose.bpFringeChunkRowCount,
        SuccinctClose.bpFringeChunkEntryWidth,
        SuccinctClose.bpFringeChunkEntryBound, Nat.log2]
  | succ m =>
      have hself : 2 ^ Nat.log2 (2 * (m + 1)) <= 2 * (m + 1) :=
        Nat.log2_self_le (by omega)
      have hfactor :
          2 ^ (Nat.log2 (2 * (m + 1)) + 14) =
            16384 * 2 ^ Nat.log2 (2 * (m + 1)) := by
        rw [Nat.pow_add, hpow14, Nat.mul_comm]
      rw [hfactor] at hmono
      have hscaled := Nat.mul_le_mul_left 16384 hself
      omega

/-- All-size linear envelope for the counted select-chunk-table bits. -/
theorem packedReviewerSelectChunkTableOverhead_le_linear (n : Nat) :
    SuccinctClose.bpChunkSelectTableOverhead n <= 128 * (n + 1) := by
  let c := SuccinctClose.bpFringeChunkBits (2 * n)
  have hwidth := SuccinctClose.bpChunkSelectEntryWidth_le c
  have hwidthPow : c + 2 <= 2 ^ (c + 2) :=
    SuccinctSpace.nat_le_two_pow _
  have hrows := SuccinctClose.bpChunkSelectRowCount_le_two_pow c
  have htable :
      SuccinctClose.bpChunkSelectTableOverhead n <= 2 ^ (3 * c + 3) := by
    unfold SuccinctClose.bpChunkSelectTableOverhead
    change
      SuccinctClose.bpChunkSelectRowCount c *
          SuccinctClose.bpChunkSelectEntryWidth c <= 2 ^ (3 * c + 3)
    calc
      SuccinctClose.bpChunkSelectRowCount c *
          SuccinctClose.bpChunkSelectEntryWidth c <=
        2 ^ (2 * c + 1) * 2 ^ (c + 2) :=
          Nat.mul_le_mul hrows (by omega)
      _ = 2 ^ (3 * c + 3) := by
        rw [← Nat.pow_add]
        congr 1
        omega
  have hc : c = Nat.log2 (2 * n) / 8 + 1 := rfl
  have hexponent : 3 * c + 3 <= Nat.log2 (2 * n) + 6 := by
    rw [hc]
    omega
  have hmono :
      2 ^ (3 * c + 3) <= 2 ^ (Nat.log2 (2 * n) + 6) :=
    Nat.pow_le_pow_right (by omega) hexponent
  have hpow6 : (2 : Nat) ^ 6 = 64 := by decide
  cases n with
  | zero =>
      simp [SuccinctClose.bpChunkSelectTableOverhead,
        SuccinctClose.bpFringeChunkBits,
        SuccinctClose.bpChunkSelectRowCount,
        SuccinctClose.bpChunkSelectEntryWidth, Nat.log2]
  | succ m =>
      have hself : 2 ^ Nat.log2 (2 * (m + 1)) <= 2 * (m + 1) :=
        Nat.log2_self_le (by omega)
      have hfactor :
          2 ^ (Nat.log2 (2 * (m + 1)) + 6) =
            64 * 2 ^ Nat.log2 (2 * (m + 1)) := by
        rw [Nat.pow_add, hpow6, Nat.mul_comm]
      rw [hfactor] at hmono
      have hscaled := Nat.mul_le_mul_left 64 hself
      omega

/-- The reviewer cell-bound argument fits the established linear capacity. -/
theorem packedReviewerCellBound_add_two_le_linearCapacity (n : Nat) :
    packedReviewerCellBound n + 2 <= 400000 * (n + 1) := by
  have haccess := genericSparseExceptionBPCloseAccessOverhead_le_linear n
  have hinterior :=
    SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead_le_linear n
  have hfringe := packedReviewerFringeTableOverhead_le_linear n
  have hselect := packedReviewerSelectChunkTableOverhead_le_linear n
  unfold packedReviewerCellBound
    concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
    SuccinctClose.canonicalRelativeRmmInteriorOverhead
  omega

/-- The one reviewer cell width is explicitly logarithmic at every size. -/
theorem packedReviewerCellWidth_le_log (n : Nat) :
    packedReviewerCellWidth n <=
      20 * (Nat.log2 (n + 2) + 1) := by
  have hmono :
      packedReviewerCellWidth n <=
        concreteBPNativeSuccinctRMQReviewerWordBits n := by
    unfold packedReviewerCellWidth
      concreteBPNativeSuccinctRMQReviewerWordBits
      concreteBPNativeSuccinctRMQReviewerCapacity
    exact SuccinctRank.machineWordBits_mono_le
      (packedReviewerCellBound_add_two_le_linearCapacity n)
  exact Nat.le_trans hmono
    (concreteBPNativeSuccinctRMQReviewerWordBits_le_log n)

/-- The all-size sparse-count header value fits the same reviewer word. -/
theorem packedReviewerSparseCount_lt_two_pow_reviewerWidth
    (shape : CartesianShape) :
    packedReviewerSparseCount shape <
      2 ^ packedReviewerCellWidth shape.size := by
  let count :=
    RMQ.Succinct.rankPrefix true
      (GenericSelect.sparseExceptionFlagBits shape.bpCode false)
      (GenericSelect.localSlotCount shape.bpCode false)
  have hword :=
    GenericSelect.sparseExceptionCount_wordBits_le_length shape.bpCode false
  have hwordPos : 0 < GenericSelect.wordBits shape.bpCode.length := by
    unfold GenericSelect.wordBits
    exact SuccinctRank.machineWordBits_pos _
  have hstride :
      GenericSelect.localStride shape.bpCode.length <=
        GenericSelect.wordBits shape.bpCode.length := by
    unfold GenericSelect.localStride
    exact Nat.max_le.2 ⟨by omega, Nat.div_le_self _ _⟩
  have hcountStride :
      count * GenericSelect.localStride shape.bpCode.length <=
        count * GenericSelect.wordBits shape.bpCode.length :=
    Nat.mul_le_mul_left count hstride
  have hlength : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have hsparse : packedReviewerSparseCount shape <= 2 * shape.size := by
    unfold packedReviewerSparseCount
    rw [GenericSelect.sparseExceptionRelativeEntries_length]
    change count * GenericSelect.localStride shape.bpCode.length <=
      2 * shape.size
    rw [← hlength]
    exact Nat.le_trans hcountStride hword
  have hbound := packedTwoMul_le_reviewerBound shape.size
  have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
  omega

/-- A decoder span never contains more bits than the requested width. -/
theorem packedReviewerDecodeSpan_length_le
    (n bit width : Nat) (cells : List (List Bool)) :
    (packedReviewerDecodeSpan n bit width cells).length <= width := by
  unfold packedReviewerDecodeSpan
  exact List.length_take_le _ _

/-- The numeric value of any one-word decoder span is machine-representable. -/
theorem packedReviewerDecodeSpan_value_lt_two_pow
    (n bit width : Nat) (cells : List (List Bool))
    (hwidth : width <= packedReviewerCellWidth n) :
    SuccinctSpace.bitsToNatLE (packedReviewerDecodeSpan n bit width cells) <
      2 ^ packedReviewerCellWidth n := by
  have hlength := packedReviewerDecodeSpan_length_le n bit width cells
  have hvalue := GenericSelect.bitsToNatLE_lt_two_pow_length
    (packedReviewerDecodeSpan n bit width cells)
  have hpower :
      2 ^ (packedReviewerDecodeSpan n bit width cells).length <=
        2 ^ packedReviewerCellWidth n :=
    Nat.pow_le_pow_right (by omega) (Nat.le_trans hlength hwidth)
  omega

/-- Every closed legacy decoder returns at most one reviewer word. -/
theorem packedReviewerLegacyDecode_word_fits
    (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat)
    (cells : List (List Bool)) (hcounted : PackedSourceCounted n source) :
    PackedReviewerWordFits n
      (packedReviewerLegacyDecode n longCount sparseCount source index cells) := by
  unfold PackedReviewerWordFits
  cases source <;>
    simp only [packedReviewerLegacyDecode, packedReviewerBPReadWidth] <;>
    apply Nat.le_trans (packedReviewerDecodeSpan_length_le _ _ _ _)
  all_goals
    first
    | exact Nat.le_trans
        (packedSourceReadWidth_le_stride n 0 _ index)
        (packedSourceStride_le_reviewerCellWidth n _ hcounted)
    | exact Nat.le_trans
        (packedReviewerSourceReadWidth_le_stride n longCount sparseCount _ index)
        (packedSourceStride_le_reviewerCellWidth n _ hcounted)

/-- Every source named by a legacy segment is part of the counted layout. -/
theorem packedReviewerSegmentSource_counted
    (n segment : Nat) (hsegment : segment < 20)
    {source : ConcreteBPNativeSuccinctRMQFlatPayloadSource}
    (hsource : packedSegmentSource? segment = some source) :
    PackedSourceCounted n source := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
      10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 =>
      cases source <;>
        simp [packedSegmentSource?,
          concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
          PackedSourceCounted] at hsource ⊢
  | _ + 20 => omega

/-- Closed form of the logical decoder on its legacy segment range. -/
private theorem packedReviewerLogicalDecode_of_segment_lt_twenty
    (n longCount sparseCount : Nat) (request : PackedReviewerLogicalRequest)
    (cells : List (List Bool)) (hsegment : request.segment < 20) :
    packedReviewerLogicalDecode n longCount sparseCount request cells =
      match packedSegmentSource? request.segment with
      | none => none
      | some source =>
          if request.index <
              packedReviewerLegacyWordCount n longCount sparseCount source then
            some (packedReviewerLegacyDecode n longCount sparseCount source
              request.index cells)
          else none := by
  rcases request with ⟨invocation, site, segment, index⟩
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
      10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 => rfl
  | offset + 20 =>
      have : False := by
        change offset + 20 < 20 at hsegment
        omega
      exact this.elim

/--
Every successful logical decoder reply is one modeled word, across all legacy
sources and all three close segments.  This statement concerns the exact
reviewer decoder, not the older flat sibling decoder.
-/
theorem packedReviewerLogicalDecode_word_fits
    (n longCount sparseCount : Nat) (request : PackedReviewerLogicalRequest)
    (cells : List (List Bool)) (word : List Bool)
    (hword :
      packedReviewerLogicalDecode n longCount sparseCount request cells =
        some word) :
    PackedReviewerWordFits n word := by
  rcases request with ⟨invocation, site, segment, index⟩
  by_cases hlegacy : segment < 20
  · cases hsource : packedSegmentSource? segment with
    | none =>
        rw [packedReviewerLogicalDecode_of_segment_lt_twenty _ _ _ _ _
          hlegacy, hsource] at hword
        simp at hword
    | some source =>
        rw [packedReviewerLogicalDecode_of_segment_lt_twenty _ _ _ _ _
          hlegacy, hsource] at hword
        by_cases hindex :
            index < packedReviewerLegacyWordCount n longCount sparseCount source
        · have hcounted :=
            packedReviewerSegmentSource_counted n segment hlegacy hsource
          have heq :
              packedReviewerLegacyDecode n longCount sparseCount source index
                  cells = word := by
            simpa [hindex] using hword
          rw [← heq]
          exact packedReviewerLegacyDecode_word_fits n longCount sparseCount
            source index cells hcounted
        · simp [hindex] at hword
  · by_cases h20 : segment = 20
    · subst segment
      cases hlocation : packedReviewerInteriorClassify n index with
      | none =>
          simp [packedReviewerLogicalDecode, hlocation] at hword
      | some location =>
          rw [packedReviewerLogicalDecode_segment20_eq n longCount sparseCount
            { invocation := invocation, site := site, segment := 20,
              index := index } cells rfl, hlocation] at hword
          have heq :
              packedReviewerDecodeSpan n
                  (packedReviewerClosedInteriorBitAddress n longCount sparseCount
                    location)
                  location.readWidth cells = word := by
            simpa [packedReviewerClosedInteriorBitAddress_eq] using
              Option.some.inj hword
          rw [← heq]
          exact Nat.le_trans
            (packedReviewerDecodeSpan_length_le n _ location.readWidth cells)
            (by
              have hlocationEq :=
                (packedReviewerInteriorClassify_sound hlocation).1
              rw [hlocationEq]
              exact packedReviewerInteriorReadWidth_le_cellWidth n
                location.component location.localWordIndex)
    · by_cases h21 : segment = 21
      · subst segment
        by_cases hindex : index < packedReviewerFringeCount n
        · have heq :
              packedReviewerDecodeSpan n
                  (packedReviewerClosedFringeAddress n longCount sparseCount index)
                  (packedReviewerFringeWidth n) cells = word := by
              rw [packedReviewerLogicalDecode_segment21_eq n longCount sparseCount
                { invocation := invocation, site := site, segment := 21,
                  index := index } cells rfl, if_pos hindex] at hword
              simpa [packedReviewerClosedFringeAddress_eq] using
                Option.some.inj hword
          rw [← heq]
          exact Nat.le_trans
            (packedReviewerDecodeSpan_length_le n _ (packedReviewerFringeWidth n)
              cells)
            (packedFringeEntryWidth_le_reviewerCellWidth n)
        · simp [packedReviewerLogicalDecode, hindex] at hword
      · by_cases h22 : segment = 22
        · subst segment
          by_cases hindex : index < packedReviewerSelectChunkCount n
          · have heq :
                packedReviewerDecodeSpan n
                    (packedReviewerClosedSelectChunkAddress n longCount
                      sparseCount index)
                    (packedReviewerSelectChunkWidth n) cells = word := by
                rw [packedReviewerLogicalDecode_segment22_eq n longCount sparseCount
                  { invocation := invocation, site := site, segment := 22,
                    index := index } cells rfl, if_pos hindex] at hword
                simpa [packedReviewerClosedSelectChunkAddress_eq] using
                  Option.some.inj hword
            rw [← heq]
            exact Nat.le_trans
              (packedReviewerDecodeSpan_length_le n _
                (packedReviewerSelectChunkWidth n) cells)
              (packedSelectChunkEntryWidth_le_reviewerCellWidth n)
          · simp [packedReviewerLogicalDecode, hindex] at hword
        · have hlarge : 23 <= segment := by omega
          obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hlarge
          have hnot : ¬ 23 + offset < 20 := by omega
          simp only [packedReviewerLogicalDecode] at hword
          rw [if_neg hnot] at hword
          contradiction

/-- Every successful canonical global-store reply is one reviewer word. -/
theorem packedReviewerGlobalReadStore_word_fits
    (shape : CartesianShape) (request : PackedReviewerLogicalRequest)
    (word : List Bool)
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index = some word) :
    PackedReviewerWordFits shape.size word := by
  have hlowered := packedReviewerLogicalRead_eq_globalReadStore shape request
  rw [hread] at hlowered
  unfold packedReviewerLogicalRead at hlowered
  cases hfetch :
      packedFetch (packedReviewerMemory shape)
        (packedReviewerLogicalPlan shape.size (longCount shape)
          (packedReviewerSparseCount shape) request) with
  | none => simp [hfetch] at hlowered
  | some cells =>
      apply packedReviewerLogicalDecode_word_fits shape.size (longCount shape)
        (packedReviewerSparseCount shape) request cells word
      simpa [hfetch] using hlowered

/-- Every successful K1 prelude decode is one reviewer word. -/
theorem packedReviewerDecodePreludeReplies_word_fits
    (n longCount : Nat) (state : PackedReviewerSparsePreludeState)
    (request : PackedReviewerSparsePreludeRequest)
    (cells : List (List Bool)) (word : List Bool)
    (hrequest : packedReviewerSparsePreludeNextRequest state = some request)
    (hword :
      packedReviewerDecodePreludeReplies n longCount state cells = some word) :
    PackedReviewerWordFits n word := by
  have hcounted : PackedSourceCounted n request.source := by
    cases request <;>
      simp [PackedReviewerSparsePreludeRequest.source, PackedSourceCounted]
  by_cases hindex :
      request.index n < packedSourceWordCount n longCount request.source
  · have heq :
        packedReviewerDecodeSpan n
            (packedReviewerSparsePreludeRequestBitAddress n longCount request)
            (packedSourceReadWidth n longCount request.source (request.index n))
            cells = word := by
      simpa [packedReviewerDecodePreludeReplies, hrequest, hindex] using hword
    rw [← heq]
    exact Nat.le_trans
      (packedReviewerDecodeSpan_length_le n _
        (packedSourceReadWidth n longCount request.source (request.index n))
        cells)
      (Nat.le_trans
        (packedSourceReadWidth_le_stride n longCount request.source
          (request.index n))
        (packedSourceStride_le_reviewerCellWidth n request.source hcounted))
  · simp [packedReviewerDecodePreludeReplies, hrequest, hindex] at hword

/-- A one-word bit string also has a one-word numeric value. -/
theorem PackedReviewerWordFits.value_lt_two_pow
    {n : Nat} {word : List Bool} (hword : PackedReviewerWordFits n word) :
    SuccinctSpace.bitsToNatLE word < 2 ^ packedReviewerCellWidth n := by
  have hvalue := GenericSelect.bitsToNatLE_lt_two_pow_length word
  have hpower : 2 ^ word.length <= 2 ^ packedReviewerCellWidth n :=
    Nat.pow_le_pow_right (by omega) hword
  omega

/-- Every stored physical reviewer cell and its decoded value fit `W(n)`. -/
theorem packedReviewerMemory_word_and_value_fit
    (shape : CartesianShape) {cell : List Bool}
    (hmem : cell ∈ packedReviewerMemory shape) :
    PackedReviewerWordFits shape.size cell ∧
      SuccinctSpace.bitsToNatLE cell <
        2 ^ packedReviewerCellWidth shape.size := by
  have hlength := packedReviewerMemory_cell_length shape hmem
  constructor
  · exact Nat.le_of_eq hlength
  · simpa [hlength] using GenericSelect.bitsToNatLE_lt_two_pow_length cell

private theorem packedReviewerList_length_le_flatten_length_of_pos
    (words : List (List Bool))
    (hpos : forall word, word ∈ words -> 0 < word.length) :
    words.length <= (SuccinctSpace.flattenPayloadWords words).length := by
  induction words with
  | nil => exact Nat.le_refl 0
  | cons head tail ih =>
      have hhead : 0 < head.length := hpos head List.mem_cons_self
      have htail : forall word, word ∈ tail -> 0 < word.length := by
        intro word hmem
        exact hpos word (List.mem_cons_of_mem head hmem)
      simp only [List.length_cons, SuccinctSpace.flattenPayloadWords,
        List.length_append]
      have hrec := ih htail
      omega

private theorem packedReviewerChunk_mem_length_pos
    {wordSize : Nat} (hwordSize : 0 < wordSize) (payload word : List Bool)
    (hmem : word ∈ SuccinctSpace.chunkPayloadWords wordSize payload) :
    0 < word.length := by
  unfold SuccinctSpace.chunkPayloadWords at hmem
  generalize payload.length + 1 = fuel at hmem
  induction fuel generalizing payload with
  | zero =>
      change word ∈ [] at hmem
      exact False.elim (List.not_mem_nil hmem)
  | succ fuel ih =>
      cases payload with
      | nil =>
          change word ∈ [] at hmem
          exact False.elim (List.not_mem_nil hmem)
      | cons bit rest =>
          change word ∈
            ((bit :: rest).take wordSize ::
              SuccinctSpace.chunkPayloadWordsFuel wordSize fuel
                ((bit :: rest).drop wordSize)) at hmem
          cases hmem with
          | head =>
              rw [List.length_take]
              cases wordSize with
              | zero => contradiction
              | succ wordSize => simp
          | tail _ htail => exact ih _ htail

private theorem packedReviewerFixedWidthMachineWords_length_le_payload
    {entries : List Nat} {width wordSize : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (hwordSize : 0 < wordSize) :
    (SuccinctSpace.fixedWidthNatTableMachineWords table wordSize).length <=
      table.payload.length := by
  calc
    (SuccinctSpace.fixedWidthNatTableMachineWords table wordSize).length <=
        (SuccinctSpace.flattenPayloadWords
          (SuccinctSpace.fixedWidthNatTableMachineWords table wordSize)).length := by
      apply packedReviewerList_length_le_flatten_length_of_pos
      intro word hmem
      rcases List.mem_flatMap.mp hmem with ⟨logical, _hlogical, hchunk⟩
      exact packedReviewerChunk_mem_length_pos hwordSize logical word hchunk
    _ = table.payload.length := by
      unfold SuccinctSpace.fixedWidthNatTableMachineWords
      rw [SuccinctSpace.flattenPayloadWords_flatMap_chunkPayloadWords hwordSize]
      exact congrArg List.length table.store.erases

/-- The segment-20 dead/sentinel word index fits the reviewer address word. -/
theorem packedReviewerInteriorDeadAddress_lt_two_pow
    (shape : CartesianShape) :
    (packedInteriorOffsets shape.size).deadAddress <
      2 ^ packedReviewerCellWidth shape.size := by
  let summary := SuccinctClose.canonicalRelativeRmmSummaryTable shape
  let localTable := SuccinctClose.canonicalRelativeRmmInteriorLocalTable shape
  let global := SuccinctClose.canonicalRelativeRmmInteriorGlobalTable shape
  let localLevel :=
    SuccinctClose.canonicalRelativeRmmInteriorLocalLevelTable shape
  let globalLevel :=
    SuccinctClose.canonicalRelativeRmmInteriorGlobalLevelTable shape
  let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
  have hbase := packedReviewerFixedWidthMachineWords_length_le_payload
    summary.baselineTable hword
  have hmin := packedReviewerFixedWidthMachineWords_length_le_payload
    summary.minRelTable hword
  have hmax := packedReviewerFixedWidthMachineWords_length_le_payload
    summary.maxRelTable hword
  have harg := packedReviewerFixedWidthMachineWords_length_le_payload
    summary.argOffsetTable hword
  have hlocal := packedReviewerFixedWidthMachineWords_length_le_payload
    localTable.table hword
  have hglobal := packedReviewerFixedWidthMachineWords_length_le_payload
    global.table hword
  have hlocalLevel := packedReviewerFixedWidthMachineWords_length_le_payload
    localLevel.table hword
  have hglobalLevel := packedReviewerFixedWidthMachineWords_length_le_payload
    globalLevel.table hword
  have hinterior :
      (packedInteriorStoreWords shape).length <=
        (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload.length := by
    change
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words.toList.length <=
        (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload.length
    rw [show
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words.toList =
        (summary.baselineTable.machineStore hword).store.words.toList ++
          (summary.minRelTable.machineStore hword).store.words.toList ++
            (summary.maxRelTable.machineStore hword).store.words.toList ++
              (summary.argOffsetTable.machineStore hword).store.words.toList ++
                (localTable.table.machineStore hword).store.words.toList ++
                  (global.table.machineStore hword).store.words.toList ++
                    (localLevel.table.machineStore hword).store.words.toList ++
                      (globalLevel.table.machineStore hword).store.words.toList by
        simpa [summary, localTable, global, localLevel, globalLevel, hword] using
          SuccinctClose.canonicalRelativeRmmInteriorComponentStore_words_toList
            shape]
    simp only [List.length_append, Array.length_toList]
    simp [SuccinctClose.canonicalRelativeRmmInteriorDirectory,
      SuccinctSpace.FixedWidthNatTable.machineStore,
      SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.payload,
      SuccinctClose.PayloadLiveBPLocalSparseOffsetTable.payload,
      SuccinctClose.PayloadLiveBPGlobalSparseBlockTable.payload,
      SuccinctClose.PayloadLiveBPSparseLevelTable.payload,
      summary, localTable, global, localLevel, globalLevel] at *
    omega
  have hinside :
      (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload.length <=
        (packedReviewerPayloadBits shape).length := by
    unfold packedReviewerPayloadBits
      concreteBPNativeSuccinctRMQCanonicalReviewerPayload
      concreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout
    dsimp only
    simp only [List.length_append]
    omega
  have hpayload := packedReviewerPayloadBits_length_eq shape
  have hbound := packedReviewerPayloadLength_le_bound shape
  have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
  have hstore := packedReviewerInteriorStoreWords_length shape
  calc
    (packedInteriorOffsets shape.size).deadAddress =
        packedInteriorComponentWords shape.size := rfl
    _ = (packedInteriorStoreWords shape).length := hstore.symm
    _ <= (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload.length :=
      hinterior
    _ <= (packedReviewerPayloadBits shape).length := hinside
    _ = packedReviewerPayloadLength shape.size (longCount shape)
        (packedReviewerSparseCount shape) := hpayload
    _ <= packedReviewerCellBound shape.size := by
      simpa [packedReviewerCellBound] using hbound
    _ <= packedReviewerCellBound shape.size + 2 := Nat.le_add_right _ _
    _ < 2 ^ packedReviewerCellWidth shape.size := hcapacity

/-- Every reference interior-trace occurrence stays at or before the dead word. -/
theorem packedInteriorRangeMinRead_event_index_le_dead
    (shape : CartesianShape) (store : WordRAM.ReadStore)
    (startBlock count index : Nat) (reply : Option (List Bool))
    (hmem :
      WordRAM.TraceEvent.readWord
          concreteBPNativeInteriorTraceSegments.canonicalComponent index reply ∈
        (packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments store
          shape.size startBlock count).trace) :
    index <= (packedInteriorOffsets shape.size).deadAddress := by
  unfold packedInteriorRangeMinRead
    SuccinctClose.flatStoreExecutionTraceResultAtSegment at hmem
  rcases List.mem_map.mp hmem with ⟨read, hread, hevent⟩
  rcases read with ⟨address, stored⟩
  simp only [Prod.fst, Prod.snd] at hevent
  cases hevent
  have hfoot :
      index ∈
        SuccinctClose.canonicalRelativeRmmInteriorRangeFootprintWithRead shape
          (SuccinctClose.flatWordStoreOfReadStore store
            concreteBPNativeInteriorTraceSegments.canonicalComponent)
          startBlock count := by
    unfold
      SuccinctClose.canonicalRelativeRmmInteriorRangeFootprintWithRead
      SuccinctClose.canonicalRelativeRmmInteriorRangeMinExecutionWithRead
      SuccinctSpace.FlatStoreExecution.footprint
    rw [packedInteriorRangeMinComputation_eq]
    exact List.mem_map.mpr ⟨(index, reply), hread, rfl⟩
  have hle :=
    SuccinctClose.canonicalRelativeRmmInteriorRangeFootprint_address_le_dead
      shape
      (SuccinctClose.flatWordStoreOfReadStore store
        concreteBPNativeInteriorTraceSegments.canonicalComponent)
      startBlock count index hfoot
  simpa [packedInteriorOffsets_eq shape] using hle

/--
An in-flight segment-20 primitive stays within the inclusive live/dead word
interval.  The exclusive-end invariant is preserved one reply at a time.
-/
private theorem packedReviewerInteriorNat_read_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (start next remaining : Nat)
    (repliesRev : List (Option (List Bool)))
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    (hspan :
      start + next + remaining <=
        (packedInteriorOffsets shape.size).deadAddress + 1) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerInteriorNatNextRequest
      packedReviewerInteriorNatConsumeReply remaining
      (.read invocation shape.size start next remaining repliesRev) := by
  induction remaining generalizing next repliesRev with
  | zero => trivial
  | succ remaining ih =>
      have hslot :
          PackedReviewerNatFits shape.size (start + next) := by
        have hdead := packedReviewerInteriorDeadAddress_lt_two_pow shape
        omega
      have hrequest :
          PackedReviewerLogicalRequestOperandsFit shape.size
            { invocation := invocation
              site := .interiorChunk (start + next)
              segment := 20
              index := start + next } := by
        apply packedReviewerLogicalRequestOperandsFit_mk
        · exact hinvocation
        · intro operand hopen
          simp [packedReviewerReadSiteOperands] at hopen
          subst operand
          exact hslot
        · exact packedReviewerSegment_le_twentyTwo_fits shape.size 20 (by omega)
        · exact hslot
      simp only [PackedReviewerRequestsFitFrom,
        packedReviewerInteriorNatNextRequest]
      refine ⟨hrequest, ?_⟩
      by_cases hlast : remaining = 0
      · subst remaining
        simp [packedReviewerInteriorNatConsumeReply,
          PackedReviewerRequestsFitFrom]
      · have hspan' :
            start + (next + 1) + remaining <=
              (packedInteriorOffsets shape.size).deadAddress + 1 := by
          omega
        simpa [packedReviewerInteriorNatConsumeReply, hlast] using
          ih (next + 1)
            (((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                20 (start + next)) :: repliesRev)
            hspan'

/--
Every live table span stays below the exact segment-20 end, while an invalid
table index performs the one logical dead-sentinel attempt at that end.
-/
theorem packedReviewerInteriorNatStart_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (entryCount width base index : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    (hspan :
      base + entryCount *
          SuccinctSpace.fixedWidthNatTableMachineChunkCount width
            (packedBpCodeWordWidth shape.size) <=
        (packedInteriorOffsets shape.size).deadAddress) :
    let state := packedReviewerInteriorNatStart invocation shape.size
      entryCount width base index
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerInteriorNatNextRequest
      packedReviewerInteriorNatConsumeReply
      (packedReviewerInteriorNatRemaining state) state := by
  dsimp only
  let count :=
    SuccinctSpace.fixedWidthNatTableMachineChunkCount width
      (packedBpCodeWordWidth shape.size)
  by_cases hindex : index < entryCount
  · by_cases hcount : count = 0
    · simp [packedReviewerInteriorNatStart, count, hindex, hcount,
        packedReviewerInteriorNatRemaining, PackedReviewerRequestsFitFrom]
    · have hindexSucc : index + 1 <= entryCount := by omega
      have hmul := Nat.mul_le_mul_right count hindexSucc
      have hmul' : index * count + count <= entryCount * count := by
        simpa [Nat.add_mul, Nat.one_mul] using hmul
      have hstartSpan :
          base + index * count + 0 + count <=
            (packedInteriorOffsets shape.size).deadAddress + 1 := by
        calc
          base + index * count + 0 + count =
              base + (index * count + count) := by omega
          _ <= base + entryCount * count := Nat.add_le_add_left hmul' base
          _ <= (packedInteriorOffsets shape.size).deadAddress := hspan
          _ <= (packedInteriorOffsets shape.size).deadAddress + 1 :=
            Nat.le_add_right _ _
      simpa [packedReviewerInteriorNatStart, count, hindex, hcount,
        packedReviewerInteriorNatRemaining] using
          packedReviewerInteriorNat_read_requests_fit shape invocation
            (base + index * count) 0 count [] hinvocation hstartSpan
  · have hdeadSpan :
        (packedInteriorOffsets shape.size).deadAddress + 0 + 1 <=
          (packedInteriorOffsets shape.size).deadAddress + 1 := by omega
    simpa [packedReviewerInteriorNatStart, count, hindex,
      packedReviewerInteriorNatRemaining] using
        packedReviewerInteriorNat_read_requests_fit shape invocation
          (packedInteriorOffsets shape.size).deadAddress 0 1 []
          hinvocation hdeadSpan

/-! ### Proof-only exhaustive state inventory -/

def packedReviewerOptionNatFields : Option Nat -> List Nat
  | none => []
  | some value => [value]

def packedReviewerCandidateNatFields : PackedReviewerCandidate -> List Nat
  | none => []
  | some (value, index) => [value, index]

def packedReviewerEntryValueNatFields :
    Option GenericSelect.SparseDenseSelectDenseLocalEntry -> List Nat
  | none => []
  | some entry =>
      [entry.baseOccurrence, entry.baseWordIndex, entry.rankBefore,
        entry.firstOffset]

def packedReviewerInvocationNatFields
    (invocation : PackedReviewerInvocation) : List Nat :=
  [invocation.argument, invocation.argument2]

def packedReviewerEntryStateNatFields : PackedReviewerEntryState -> List Nat
  | .baseOccurrence invocation _ index =>
      packedReviewerInvocationNatFields invocation ++ [index]
  | .baseWordIndex invocation _ index baseOccurrence =>
      packedReviewerInvocationNatFields invocation ++ [index] ++
        packedReviewerOptionNatFields baseOccurrence
  | .rankBefore invocation _ index baseOccurrence baseWordIndex =>
      packedReviewerInvocationNatFields invocation ++ [index] ++
        packedReviewerOptionNatFields baseOccurrence ++
          packedReviewerOptionNatFields baseWordIndex
  | .firstOffset invocation _ index baseOccurrence baseWordIndex rankBefore =>
      packedReviewerInvocationNatFields invocation ++ [index] ++
        packedReviewerOptionNatFields baseOccurrence ++
          packedReviewerOptionNatFields baseWordIndex ++
            packedReviewerOptionNatFields rankBefore
  | .done value => packedReviewerEntryValueNatFields value

def packedReviewerRankStateNatFields : PackedReviewerRankState -> List Nat
  | .superSample invocation _ n pos =>
      packedReviewerInvocationNatFields invocation ++ [n, pos]
  | .blockSample invocation _ n pos superSample =>
      packedReviewerInvocationNatFields invocation ++ [n, pos] ++
        packedReviewerOptionNatFields superSample
  | .word invocation _ n pos superSample blockSample =>
      packedReviewerInvocationNatFields invocation ++ [n, pos] ++
        packedReviewerOptionNatFields superSample ++
          packedReviewerOptionNatFields blockSample
  | .fold invocation _ n _ effectiveLimit j remaining acc base =>
      packedReviewerInvocationNatFields invocation ++
        [n, effectiveLimit, j, remaining, acc, base]
  | .done value => [value]

def packedReviewerWordSelectStateNatFields :
    PackedReviewerWordSelectState -> List Nat
  | .rankChunk invocation n _ _ j remaining occurrence
  | .selectChunk invocation n _ _ j remaining occurrence =>
      packedReviewerInvocationNatFields invocation ++
        [n, j, remaining, occurrence]
  | .done value => packedReviewerOptionNatFields value

def packedReviewerFringeStateNatFields : PackedReviewerFringeState -> List Nat
  | .chunk invocation n _ relLo relHi j remaining (seed, candidate) =>
      packedReviewerInvocationNatFields invocation ++
        [n, relLo, relHi, j, remaining, seed] ++
          packedReviewerCandidateNatFields candidate
  | .done (seed, candidate) =>
      seed :: packedReviewerCandidateNatFields candidate

def packedReviewerBPWindowStateNatFields :
    PackedReviewerBPWindowState -> List Nat
  | .read invocation n blockSize close next _ =>
      packedReviewerInvocationNatFields invocation ++
        [n, blockSize, close, next]
  | .done _ => []

def packedReviewerInteriorNatStateNatFields :
    PackedReviewerInteriorNatState -> List Nat
  | .read invocation n start next remaining _ =>
      packedReviewerInvocationNatFields invocation ++
        [n, start, next, remaining]
  | .done value => packedReviewerOptionNatFields value

def packedReviewerCandidateContinuationNatFields :
    PackedReviewerCandidateContinuation -> List Nat
  | .finish => []
  | .localTwoLeft n macroIdx localStart count encoded outer =>
      [n, macroIdx, localStart, count, encoded] ++
        packedReviewerCandidateContinuationNatFields outer
  | .localTwoRight left outer =>
      packedReviewerCandidateNatFields left ++
        packedReviewerCandidateContinuationNatFields outer
  | .globalTwoLeft n macroStart macroSpanCount encoded outer =>
      [n, macroStart, macroSpanCount, encoded] ++
        packedReviewerCandidateContinuationNatFields outer
  | .globalTwoRight left outer =>
      packedReviewerCandidateNatFields left ++
        packedReviewerCandidateContinuationNatFields outer
  | .adjacentLeft n macroStart rightCount outer =>
      [n, macroStart, rightCount] ++
        packedReviewerCandidateContinuationNatFields outer
  | .adjacentRight left outer =>
      packedReviewerCandidateNatFields left ++
        packedReviewerCandidateContinuationNatFields outer
  | .leftMiddleLeft n macroStart middleCount outer =>
      [n, macroStart, middleCount] ++
        packedReviewerCandidateContinuationNatFields outer
  | .leftMiddleMiddle left outer =>
      packedReviewerCandidateNatFields left ++
        packedReviewerCandidateContinuationNatFields outer
  | .crossLeft n macroStart middleCount rightCount outer =>
      [n, macroStart, middleCount, rightCount] ++
        packedReviewerCandidateContinuationNatFields outer
  | .crossMiddle n macroStart middleCount rightCount left outer =>
      [n, macroStart, middleCount, rightCount] ++
        packedReviewerCandidateNatFields left ++
          packedReviewerCandidateContinuationNatFields outer
  | .crossRight left middle outer =>
      packedReviewerCandidateNatFields left ++
        packedReviewerCandidateNatFields middle ++
          packedReviewerCandidateContinuationNatFields outer

def packedReviewerInteriorNatContinuationNatFields :
    PackedReviewerInteriorNatContinuation -> List Nat
  | .summaryBaseline n block outer =>
      [n, block] ++ packedReviewerCandidateContinuationNatFields outer
  | .summaryMin n block baseline outer =>
      [n, block] ++ packedReviewerOptionNatFields baseline ++
        packedReviewerCandidateContinuationNatFields outer
  | .summaryMax n block baseline minRel outer =>
      [n, block] ++ packedReviewerOptionNatFields baseline ++
        packedReviewerOptionNatFields minRel ++
          packedReviewerCandidateContinuationNatFields outer
  | .summaryArg n block baseline minRel maxRel outer =>
      [n, block] ++ packedReviewerOptionNatFields baseline ++
        packedReviewerOptionNatFields minRel ++
          packedReviewerOptionNatFields maxRel ++
            packedReviewerCandidateContinuationNatFields outer
  | .localOffset n macroIdx localStart level outer =>
      [n, macroIdx, localStart, level] ++
        packedReviewerCandidateContinuationNatFields outer
  | .globalBlock n macroStart level outer =>
      [n, macroStart, level] ++
        packedReviewerCandidateContinuationNatFields outer
  | .localLevel n macroIdx localStart count outer =>
      [n, macroIdx, localStart, count] ++
        packedReviewerCandidateContinuationNatFields outer
  | .globalLevel n macroStart macroSpanCount outer =>
      [n, macroStart, macroSpanCount] ++
        packedReviewerCandidateContinuationNatFields outer

def packedReviewerInteriorStateNatFields :
    PackedReviewerInteriorState -> List Nat
  | .readNat invocation read continuation =>
      packedReviewerInvocationNatFields invocation ++
        packedReviewerInteriorNatStateNatFields read ++
          packedReviewerInteriorNatContinuationNatFields continuation
  | .done value => packedReviewerCandidateNatFields value

def packedReviewerSelectStateNatFields : PackedReviewerSelectState -> List Nat
  | .superEntry invocation n index entry =>
      packedReviewerInvocationNatFields invocation ++ [n, index] ++
        packedReviewerEntryStateNatFields entry
  | .localEntry invocation n index localSlot super entry =>
      packedReviewerInvocationNatFields invocation ++ [n, index, localSlot] ++
        packedReviewerEntryValueNatFields (some super) ++
          packedReviewerEntryStateNatFields entry
  | .longRank invocation n index super rank =>
      packedReviewerInvocationNatFields invocation ++ [n, index] ++
        packedReviewerEntryValueNatFields (some super) ++
          packedReviewerRankStateNatFields rank
  | .longRelative invocation base slot =>
      packedReviewerInvocationNatFields invocation ++ [base, slot]
  | .sparseRank invocation n index localSlot super loc rank =>
      packedReviewerInvocationNatFields invocation ++ [n, index, localSlot] ++
        packedReviewerEntryValueNatFields (some super) ++
          packedReviewerEntryValueNatFields (some loc) ++
            packedReviewerRankStateNatFields rank
  | .sparseRelative invocation base slot =>
      packedReviewerInvocationNatFields invocation ++ [base, slot]
  | .denseFirstWord invocation n index basePosition baseOccurrence =>
      packedReviewerInvocationNatFields invocation ++
        [n, index, basePosition, baseOccurrence]
  | .denseBeforeRank invocation n index basePosition baseOccurrence _ rank =>
      packedReviewerInvocationNatFields invocation ++
        [n, index, basePosition, baseOccurrence] ++
          packedReviewerRankStateNatFields rank
  | .denseUptoRank invocation n index basePosition baseOccurrence beforeFirst
      _ rank =>
      packedReviewerInvocationNatFields invocation ++
        [n, index, basePosition, baseOccurrence, beforeFirst] ++
          packedReviewerRankStateNatFields rank
  | .denseFirstSelect invocation n baseWord select =>
      packedReviewerInvocationNatFields invocation ++ [n, baseWord] ++
        packedReviewerWordSelectStateNatFields select
  | .denseSecondWord invocation n index basePosition baseOccurrence beforeFirst
      uptoFirst =>
      packedReviewerInvocationNatFields invocation ++
        [n, index, basePosition, baseOccurrence, beforeFirst, uptoFirst]
  | .denseSecondSelect invocation n baseWord select =>
      packedReviewerInvocationNatFields invocation ++ [n, baseWord] ++
        packedReviewerWordSelectStateNatFields select
  | .done value => packedReviewerOptionNatFields value

def packedReviewerLcaStateNatFields : PackedReviewerLcaState -> List Nat
  | .sameSeed invocation n leftClose rightClose rank
  | .leftSeed invocation n leftClose rightClose rank =>
      packedReviewerInvocationNatFields invocation ++
        [n, leftClose, rightClose] ++ packedReviewerRankStateNatFields rank
  | .sameWindow invocation n leftClose rightClose seed window
  | .leftWindow invocation n leftClose rightClose seed window =>
      packedReviewerInvocationNatFields invocation ++
        [n, leftClose, rightClose, seed] ++
          packedReviewerBPWindowStateNatFields window
  | .sameFringe invocation n leftClose rightClose seed base start fringe
  | .leftFringe invocation n leftClose rightClose seed base start fringe =>
      packedReviewerInvocationNatFields invocation ++
        [n, leftClose, rightClose, seed, base, start] ++
          packedReviewerFringeStateNatFields fringe
  | .middle invocation n leftClose rightClose left interior =>
      packedReviewerInvocationNatFields invocation ++
        [n, leftClose, rightClose] ++ packedReviewerCandidateNatFields left ++
          packedReviewerInteriorStateNatFields interior
  | .rightSeed invocation n leftClose rightClose left middle rank =>
      packedReviewerInvocationNatFields invocation ++
        [n, leftClose, rightClose] ++ packedReviewerCandidateNatFields left ++
          packedReviewerCandidateNatFields middle ++
            packedReviewerRankStateNatFields rank
  | .rightWindow invocation n leftClose rightClose seed left middle window =>
      packedReviewerInvocationNatFields invocation ++
        [n, leftClose, rightClose, seed] ++
          packedReviewerCandidateNatFields left ++
            packedReviewerCandidateNatFields middle ++
              packedReviewerBPWindowStateNatFields window
  | .rightFringe invocation n leftClose rightClose seed base start left middle
      fringe =>
      packedReviewerInvocationNatFields invocation ++
        [n, leftClose, rightClose, seed, base, start] ++
          packedReviewerCandidateNatFields left ++
            packedReviewerCandidateNatFields middle ++
              packedReviewerFringeStateNatFields fringe
  | .done value => packedReviewerOptionNatFields value

def packedReviewerWholeStateNatFields : PackedReviewerWholeState -> List Nat
  | .leftSelect n left right select =>
      [n, left, right] ++ packedReviewerSelectStateNatFields select
  | .rightSelect n left right leftClose select =>
      [n, left, right] ++ packedReviewerOptionNatFields leftClose ++
        packedReviewerSelectStateNatFields select
  | .lcaClose n left right leftClose rightClose lca =>
      [n, left, right, leftClose, rightClose] ++
        packedReviewerLcaStateNatFields lca
  | .finalRank n left right answerClose rank =>
      [n, left, right, answerClose] ++ packedReviewerRankStateNatFields rank
  | .done value => packedReviewerOptionNatFields value

def packedReviewerSparsePreludeStateNatFields :
    PackedReviewerSparsePreludeState -> List Nat
  | .awaitSuper n longCount => [n, longCount]
  | .awaitBlock n longCount _ => [n, longCount]
  | .awaitFlag n longCount _ _ => [n, longCount]
  | .done n longCount sparseCount => [n, longCount, sparseCount]

/-- Every scalar dynamically stored by the public controller, recursively. -/
def packedReviewerControllerStateNatFields :
    PackedReviewerControllerState -> List Nat
  | .header n left right => [n, left, right]
  | .preludeReady n left right longCount state =>
      [n, left, right, longCount] ++
        packedReviewerSparsePreludeStateNatFields state
  | .preludeProbe n left right longCount state nextOrdinal _ =>
      [n, left, right, longCount, nextOrdinal] ++
        packedReviewerSparsePreludeStateNatFields state
  | .wholeReady n left right longCount sparseCount logicalStepsLeft state =>
      [n, left, right, longCount, sparseCount, logicalStepsLeft] ++
        packedReviewerWholeStateNatFields state
  | .wholeProbe n left right longCount sparseCount logicalStepsAfterReply state
      nextOrdinal _ =>
      [n, left, right, longCount, sparseCount, logicalStepsAfterReply,
        nextOrdinal] ++ packedReviewerWholeStateNatFields state
  | .done value => packedReviewerOptionNatFields value
  | .failed => []

def packedReviewerRankStateWordFields :
    PackedReviewerRankState -> List (List Bool)
  | .word _ _ _ _ _ _ => []
  | .fold _ _ _ word _ _ _ _ _ => [word]
  | _ => []

def packedReviewerWordSelectStateWordFields :
    PackedReviewerWordSelectState -> List (List Bool)
  | .rankChunk _ _ _ word _ _ _
  | .selectChunk _ _ _ word _ _ _ => [word]
  | .done _ => []

def packedReviewerBPWindowStateWordFields :
    PackedReviewerBPWindowState -> List (List Bool)
  | .read _ _ _ _ _ wordsRev => wordsRev
  | .done _ => []

def packedReviewerInteriorNatStateWordFields :
    PackedReviewerInteriorNatState -> List (List Bool)
  | .read _ _ _ _ _ repliesRev => repliesRev.filterMap id
  | .done _ => []

def packedReviewerInteriorStateWordFields :
    PackedReviewerInteriorState -> List (List Bool)
  | .readNat _ read _ => packedReviewerInteriorNatStateWordFields read
  | .done _ => []

def packedReviewerSelectStateWordFields :
    PackedReviewerSelectState -> List (List Bool)
  | .superEntry _ _ _ _ => []
  | .localEntry _ _ _ _ _ _ => []
  | .longRank _ _ _ _ rank => packedReviewerRankStateWordFields rank
  | .longRelative _ _ _ => []
  | .sparseRank _ _ _ _ _ _ rank => packedReviewerRankStateWordFields rank
  | .sparseRelative _ _ _ => []
  | .denseFirstWord _ _ _ _ _ => []
  | .denseBeforeRank _ _ _ _ _ word rank
  | .denseUptoRank _ _ _ _ _ _ word rank =>
      word :: packedReviewerRankStateWordFields rank
  | .denseFirstSelect _ _ _ select
  | .denseSecondSelect _ _ _ select =>
      packedReviewerWordSelectStateWordFields select
  | .denseSecondWord _ _ _ _ _ _ _ => []
  | .done _ => []

def packedReviewerLcaStateWordFields :
    PackedReviewerLcaState -> List (List Bool)
  | .sameSeed _ _ _ _ rank
  | .leftSeed _ _ _ _ rank
  | .rightSeed _ _ _ _ _ _ rank => packedReviewerRankStateWordFields rank
  | .sameWindow _ _ _ _ _ window
  | .leftWindow _ _ _ _ _ window
  | .rightWindow _ _ _ _ _ _ _ window =>
      packedReviewerBPWindowStateWordFields window
  | .sameFringe _ _ _ _ _ _ _ _
  | .leftFringe _ _ _ _ _ _ _ _
  | .rightFringe _ _ _ _ _ _ _ _ _ _ => []
  | .middle _ _ _ _ _ interior => packedReviewerInteriorStateWordFields interior
  | .done _ => []

def packedReviewerWholeStateWordFields :
    PackedReviewerWholeState -> List (List Bool)
  | .leftSelect _ _ _ select
  | .rightSelect _ _ _ _ select => packedReviewerSelectStateWordFields select
  | .lcaClose _ _ _ _ _ lca => packedReviewerLcaStateWordFields lca
  | .finalRank _ _ _ _ rank => packedReviewerRankStateWordFields rank
  | .done _ => []

def packedReviewerSparsePreludeStateWordFields :
    PackedReviewerSparsePreludeState -> List (List Bool)
  | .awaitSuper _ _ => []
  | .awaitBlock _ _ superReply => [superReply]
  | .awaitFlag _ _ superReply blockReply => [superReply, blockReply]
  | .done _ _ _ => []

/-- Every separately represented one-word field recursively held by a state. -/
def packedReviewerControllerStateWordFields :
    PackedReviewerControllerState -> List (List Bool)
  | .header _ _ _ => []
  | .preludeReady _ _ _ _ state =>
      packedReviewerSparsePreludeStateWordFields state
  | .preludeProbe _ _ _ _ state _ repliesRev =>
      repliesRev ++ packedReviewerSparsePreludeStateWordFields state
  | .wholeReady _ _ _ _ _ _ state => packedReviewerWholeStateWordFields state
  | .wholeProbe _ _ _ _ _ _ state _ repliesRev =>
      repliesRev ++ packedReviewerWholeStateWordFields state
  | .done _ => []
  | .failed => []

def packedReviewerFringeStateWideFields :
    PackedReviewerFringeState -> List (List Bool)
  | .chunk _ _ window _ _ _ _ _ => [window]
  | .done _ => []

def packedReviewerBPWindowStateWideFields :
    PackedReviewerBPWindowState -> List (List Bool)
  | .read _ _ _ _ _ _ => []
  | .done bits => [bits]

def packedReviewerLcaStateWideFields :
    PackedReviewerLcaState -> List (List Bool)
  | .sameWindow _ _ _ _ _ window
  | .leftWindow _ _ _ _ _ window
  | .rightWindow _ _ _ _ _ _ _ window =>
      packedReviewerBPWindowStateWideFields window
  | .sameFringe _ _ _ _ _ _ _ fringe
  | .leftFringe _ _ _ _ _ _ _ fringe =>
      packedReviewerFringeStateWideFields fringe
  | .rightFringe _ _ _ _ _ _ _ _ _ fringe =>
      packedReviewerFringeStateWideFields fringe
  | _ => []

def packedReviewerWholeStateWideFields :
    PackedReviewerWholeState -> List (List Bool)
  | .lcaClose _ _ _ _ _ lca => packedReviewerLcaStateWideFields lca
  | _ => []

/-- Flattened BP windows are explicitly four-word buffers, never one word. -/
def packedReviewerControllerStateWideFields :
    PackedReviewerControllerState -> List (List Bool)
  | .wholeReady _ _ _ _ _ _ state
  | .wholeProbe _ _ _ _ _ _ state _ _ =>
      packedReviewerWholeStateWideFields state
  | _ => []

def packedReviewerRankStateControlBounds : PackedReviewerRankState -> Prop
  | .fold _ _ _ _ _ j remaining _ _ => j <= 33 ∧ remaining <= 33
  | _ => True

def packedReviewerWordSelectStateControlBounds :
    PackedReviewerWordSelectState -> Prop
  | .rankChunk _ _ _ _ j remaining _
  | .selectChunk _ _ _ _ j remaining _ => j <= 33 ∧ remaining <= 33
  | .done _ => True

def packedReviewerFringeStateControlBounds : PackedReviewerFringeState -> Prop
  | .chunk _ _ _ _ _ j remaining _ => j <= 33 ∧ remaining <= 33
  | .done _ => True

def packedReviewerBPWindowStateControlBounds :
    PackedReviewerBPWindowState -> Prop
  | .read _ _ _ _ next wordsRev =>
      next <= 4 ∧ wordsRev.length = next
  | .done _ => True

def packedReviewerInteriorNatStateControlBounds :
    PackedReviewerInteriorNatState -> Prop
  | .read _ _ _ next remaining repliesRev =>
      next <= 210 ∧ remaining <= 210 ∧ repliesRev.length = next
  | .done _ => True

def packedReviewerInteriorStateControlBounds :
    PackedReviewerInteriorState -> Prop
  | .readNat _ read _ => packedReviewerInteriorNatStateControlBounds read
  | .done _ => True

def packedReviewerSelectStateControlBounds : PackedReviewerSelectState -> Prop
  | .longRank _ _ _ _ rank
  | .sparseRank _ _ _ _ _ _ rank
  | .denseBeforeRank _ _ _ _ _ _ rank
  | .denseUptoRank _ _ _ _ _ _ _ rank =>
      packedReviewerRankStateControlBounds rank
  | .denseFirstSelect _ _ _ select
  | .denseSecondSelect _ _ _ select =>
      packedReviewerWordSelectStateControlBounds select
  | _ => True

def packedReviewerLcaStateControlBounds : PackedReviewerLcaState -> Prop
  | .sameSeed _ _ _ _ rank
  | .leftSeed _ _ _ _ rank
  | .rightSeed _ _ _ _ _ _ rank => packedReviewerRankStateControlBounds rank
  | .sameWindow _ _ _ _ _ window
  | .leftWindow _ _ _ _ _ window
  | .rightWindow _ _ _ _ _ _ _ window =>
      packedReviewerBPWindowStateControlBounds window
  | .sameFringe _ _ _ _ _ _ _ fringe
  | .leftFringe _ _ _ _ _ _ _ fringe =>
      packedReviewerFringeStateControlBounds fringe
  | .rightFringe _ _ _ _ _ _ _ _ _ fringe =>
      packedReviewerFringeStateControlBounds fringe
  | .middle _ _ _ _ _ interior => packedReviewerInteriorStateControlBounds interior
  | _ => True

def packedReviewerWholeStateControlBounds : PackedReviewerWholeState -> Prop
  | .leftSelect _ _ _ select
  | .rightSelect _ _ _ _ select => packedReviewerSelectStateControlBounds select
  | .lcaClose _ _ _ _ _ lca => packedReviewerLcaStateControlBounds lca
  | .finalRank _ _ _ _ rank => packedReviewerRankStateControlBounds rank
  | .done _ => True

/-- Literal bounds for fixed protocol counters and in-flight reply buffers. -/
def packedReviewerControllerStateControlBounds :
    PackedReviewerControllerState -> Prop
  | .header _ _ _ => True
  | .preludeReady _ _ _ _ state =>
      packedReviewerSparsePreludeRemaining state <= 3
  | .preludeProbe _ _ _ _ state nextOrdinal repliesRev =>
      packedReviewerSparsePreludeRemaining state <= 3 ∧
        nextOrdinal < 2 ∧ repliesRev.length = nextOrdinal
  | .wholeReady _ _ _ _ _ logicalStepsLeft state =>
      logicalStepsLeft <= 210 ∧ packedReviewerWholeRemaining state <= 210 ∧
        packedReviewerWholeStateControlBounds state
  | .wholeProbe _ _ _ _ _ logicalStepsAfterReply state nextOrdinal repliesRev =>
      logicalStepsAfterReply <= 210 ∧
        packedReviewerWholeRemaining state <= 210 ∧
          nextOrdinal < 2 ∧ repliesRev.length = nextOrdinal ∧
            packedReviewerWholeStateControlBounds state
  | .done _ => True
  | .failed => True

/-- Stack depth of the closed candidate-continuation language. -/
def packedReviewerCandidateContinuationDepth :
    PackedReviewerCandidateContinuation -> Nat
  | .finish => 0
  | .localTwoLeft _ _ _ _ _ outer
  | .localTwoRight _ outer
  | .globalTwoLeft _ _ _ _ outer
  | .globalTwoRight _ outer
  | .adjacentLeft _ _ _ outer
  | .adjacentRight _ outer
  | .leftMiddleLeft _ _ _ outer
  | .leftMiddleMiddle _ outer
  | .crossLeft _ _ _ _ outer
  | .crossMiddle _ _ _ _ _ outer
  | .crossRight _ _ outer =>
      packedReviewerCandidateContinuationDepth outer + 1

/-- One pending interior-Nat action above its candidate continuation. -/
def packedReviewerInteriorNatContinuationDepth :
    PackedReviewerInteriorNatContinuation -> Nat
  | .summaryBaseline _ _ outer
  | .summaryMin _ _ _ outer
  | .summaryMax _ _ _ _ outer
  | .summaryArg _ _ _ _ _ outer
  | .localOffset _ _ _ _ outer
  | .globalBlock _ _ _ outer
  | .localLevel _ _ _ _ outer
  | .globalLevel _ _ _ outer =>
      packedReviewerCandidateContinuationDepth outer + 1

def packedReviewerInteriorStateContinuationDepth :
    PackedReviewerInteriorState -> Nat
  | .readNat _ _ continuation =>
      packedReviewerInteriorNatContinuationDepth continuation
  | .done _ => 0

def packedReviewerLcaStateContinuationDepth : PackedReviewerLcaState -> Nat
  | .middle _ _ _ _ _ interior =>
      packedReviewerInteriorStateContinuationDepth interior
  | _ => 0

def packedReviewerWholeStateContinuationDepth : PackedReviewerWholeState -> Nat
  | .lcaClose _ _ _ _ _ lca => packedReviewerLcaStateContinuationDepth lca
  | _ => 0

/-- Defunctionalized continuation depth retained by the public state. -/
def packedReviewerControllerStateContinuationDepth :
    PackedReviewerControllerState -> Nat
  | .wholeReady _ _ _ _ _ _ state
  | .wholeProbe _ _ _ _ _ _ state _ _ =>
      packedReviewerWholeStateContinuationDepth state
  | _ => 0

/--
The proof-only state-width invariant.  It is exhaustive over every controller
and nested protocol constructor.  Scalar fields are individually encoded;
one-word fields are bounded individually; flattened BP windows are accounted
as at most four words; and fixed control counters have literal bounds.
-/
structure PackedReviewerControllerStateMachineFits
    (n : Nat) (state : PackedReviewerControllerState) : Prop where
  phase_tag :
    PackedReviewerNatFits n (packedReviewerControllerStatePhaseCode state)
  scalar_register_count :
    (packedReviewerControllerStateNatFields state).length <= 512
  scalar_fields :
    forall value, value ∈ packedReviewerControllerStateNatFields state ->
      PackedReviewerNatFits n value
  word_buffer :
    PackedReviewerBufferFits n 212
      (packedReviewerControllerStateWordFields state)
  wide_buffer_count :
    (packedReviewerControllerStateWideFields state).length <= 1
  wide_fields :
    forall bits, bits ∈ packedReviewerControllerStateWideFields state ->
      bits.length <= 4 * packedReviewerCellWidth n
  continuation_depth :
    packedReviewerControllerStateContinuationDepth state <= 3
  control_fields : packedReviewerControllerStateControlBounds state

/-- The canonical public entry state satisfies the exhaustive machine model. -/
theorem packedReviewerController_start_state_machine_fits
    (shape : CartesianShape) (left right : Nat) :
    PackedReviewerControllerStateMachineFits shape.size
      (packedReviewerController shape.size left right) := by
  by_cases hvalid : left < right ∧ right <= shape.size
  · have hendpoints :=
      packedReviewerValidEndpoints_lt_two_pow_cellWidth shape.size left right
        hvalid
    refine
      { phase_tag :=
          packedReviewerControllerStatePhaseCode_fits shape.size
            (packedReviewerController shape.size left right)
        scalar_register_count := ?_
        scalar_fields := ?_
        word_buffer := ?_
        wide_buffer_count := ?_
        wide_fields := ?_
        continuation_depth := ?_
        control_fields := ?_ }
    · simp [packedReviewerController, hvalid,
        packedReviewerControllerStateNatFields]
    · intro value hmem
      simp [packedReviewerController, hvalid,
        packedReviewerControllerStateNatFields] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
      · exact hendpoints.1
      · exact hendpoints.2
    · simp [PackedReviewerBufferFits, packedReviewerController, hvalid,
        packedReviewerControllerStateWordFields]
    · simp [packedReviewerController, hvalid,
        packedReviewerControllerStateWideFields]
    · intro bits hmem
      simp [packedReviewerController, hvalid,
        packedReviewerControllerStateWideFields] at hmem
    · simp [packedReviewerController, hvalid,
        packedReviewerControllerStateContinuationDepth]
    · simp [packedReviewerController, hvalid,
        packedReviewerControllerStateControlBounds]
  · have hstart : packedReviewerController shape.size left right = .done none := by
      simp [packedReviewerController, hvalid]
    rw [hstart]
    refine
      { phase_tag :=
          packedReviewerControllerStatePhaseCode_fits shape.size
            (.done none)
        scalar_register_count := ?_
        scalar_fields := ?_
        word_buffer := ?_
        wide_buffer_count := ?_
        wide_fields := ?_
        continuation_depth := ?_
        control_fields := ?_ }
    · simp [packedReviewerControllerStateNatFields,
        packedReviewerOptionNatFields]
    · intro value hmem
      simp [packedReviewerControllerStateNatFields,
        packedReviewerOptionNatFields] at hmem
    · simp [PackedReviewerBufferFits,
        packedReviewerControllerStateWordFields]
    · simp [packedReviewerControllerStateWideFields]
    · intro bits hmem
      simp [packedReviewerControllerStateWideFields] at hmem
    · simp [packedReviewerControllerStateContinuationDepth]
    · simp [packedReviewerControllerStateControlBounds]

/-- Canonical prefix reachability without adding proof fields to execution. -/
inductive PackedReviewerCanonicalReachable
    (shape : CartesianShape) (left right : Nat) :
    PackedReviewerControllerState -> Prop where
  | start :
      PackedReviewerCanonicalReachable shape left right
        (packedReviewerController shape.size left right)
  | step {state request} :
      PackedReviewerCanonicalReachable shape left right state ->
      packedReviewerNextRequest state = some request ->
      PackedReviewerCanonicalReachable shape left right
        (packedReviewerConsumeReply state
          ((packedReviewerMemory shape)[request.address]?))

/--
Canonical logical prefix reachability.  Unlike a theorem-only trace predicate,
each step is the actual request/reply transition against the canonical global
store; request provenance therefore remains attached to the state that
produced it.
-/
inductive PackedReviewerCanonicalLogicalReachable
    (shape : CartesianShape) (left right : Nat) :
    PackedReviewerWholeState -> Prop where
  | start :
      PackedReviewerCanonicalLogicalReachable shape left right
        (packedReviewerWholeStart shape.size left right)
  | step {state request} :
      PackedReviewerCanonicalLogicalReachable shape left right state ->
      packedReviewerWholeNextRequest state = some request ->
      PackedReviewerCanonicalLogicalReachable shape left right
        (packedReviewerWholeConsumeReply state
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index))

/--
Every trace event was produced by `nextRequest` at an operationally reachable
prefix state.  This is the bridge used by the constructor-by-constructor
operand invariant; it does not recover provenance from the erased trace.
-/
theorem packedReviewerDriveLogical_trace_reachable_request
    (shape : CartesianShape) (left right fuel : Nat)
    (state : PackedReviewerWholeState)
    (hstate :
      PackedReviewerCanonicalLogicalReachable shape left right state)
    {event : PackedReviewerLogicalEvent}
    (hmem : event ∈
      (packedReviewerDriveLogical
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) fuel state).trace) :
    exists requestState,
      PackedReviewerCanonicalLogicalReachable shape left right requestState ∧
        packedReviewerWholeNextRequest requestState = some event.request := by
  induction fuel generalizing state event with
  | zero =>
      simp [packedReviewerDriveLogical] at hmem
  | succ fuel ih =>
      cases hresult : packedReviewerWholeResult state with
      | some value =>
          simp [packedReviewerDriveLogical, hresult] at hmem
      | none =>
          cases hrequest : packedReviewerWholeNextRequest state with
          | none =>
              simp [packedReviewerDriveLogical, hresult, hrequest] at hmem
          | some request =>
              simp only [packedReviewerDriveLogical, hresult, hrequest,
                List.mem_cons] at hmem
              rcases hmem with rfl | htail
              · exact ⟨state, hstate, hrequest⟩
              · exact ih
                  (packedReviewerWholeConsumeReply state
                    ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                      request.segment request.index))
                  (PackedReviewerCanonicalLogicalReachable.step hstate hrequest)
                  htail

/-- The public 210-step logical trace is covered by canonical prefix states. -/
theorem packedReviewerDriveLogical_210_trace_reachable_request
    (shape : CartesianShape) (left right : Nat)
    {event : PackedReviewerLogicalEvent}
    (hmem : event ∈
      (packedReviewerDriveLogical
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) 210
        (packedReviewerWholeStart shape.size left right)).trace) :
    exists requestState,
      PackedReviewerCanonicalLogicalReachable shape left right requestState ∧
        packedReviewerWholeNextRequest requestState = some event.request :=
  packedReviewerDriveLogical_trace_reachable_request shape left right 210
    (packedReviewerWholeStart shape.size left right)
    .start hmem

/-! ## Proof-side occurrence-preserving physical expansion -/

def packedReviewerPhysicalEventsFrom
    (memory : List (List Bool)) (origin : PackedReviewerPhysicalOrigin)
    (cellCount : Nat) : Nat -> List Nat -> List PackedReviewerPhysicalEvent
  | _, [] => []
  | ordinal, address :: rest =>
      { request :=
          { origin := origin
            address := address
            ordinal := ordinal
            cellCount := cellCount }
        reply := memory[address]? } ::
        packedReviewerPhysicalEventsFrom memory origin cellCount
          (ordinal + 1) rest

def packedReviewerPhysicalEvents
    (memory : List (List Bool)) (origin : PackedReviewerPhysicalOrigin)
    (plan : List Nat) : List PackedReviewerPhysicalEvent :=
  packedReviewerPhysicalEventsFrom memory origin plan.length 0 plan

def packedReviewerHeaderPhysicalTrace
    (shape : CartesianShape) : List PackedReviewerPhysicalEvent :=
  packedReviewerPhysicalEvents (packedReviewerMemory shape) .header [0]

def packedReviewerSparsePreludePhysicalTrace
    (shape : CartesianShape) : List PackedReviewerPhysicalEvent :=
  (packedReviewerSparsePreludeRequests shape.size).flatMap fun request =>
    packedReviewerPhysicalEvents (packedReviewerMemory shape)
      (.sparsePrelude request)
      (packedReviewerSparsePreludeRequestPlan shape.size (longCount shape)
        request)

def packedReviewerLogicalEventPhysicalTrace
    (shape : CartesianShape) (event : PackedReviewerLogicalEvent) :
    List PackedReviewerPhysicalEvent :=
  packedReviewerPhysicalEvents (packedReviewerMemory shape)
    (.wholeQuery event.request)
    (packedReviewerLogicalPlan shape.size (longCount shape)
      (packedReviewerSparseCount shape) event.request)

def packedReviewerLogicalTracePhysicalTrace
    (shape : CartesianShape) (trace : List PackedReviewerLogicalEvent) :
    List PackedReviewerPhysicalEvent :=
  trace.flatMap (packedReviewerLogicalEventPhysicalTrace shape)

structure PackedReviewerLoweredWholeRun where
  terminal : Option (Option Nat)
  state : PackedReviewerWholeState
  logicalTrace : List PackedReviewerLogicalEvent
  physicalTrace : List PackedReviewerPhysicalEvent

def packedReviewerDriveLoweredWhole
    (shape : CartesianShape) : Nat -> PackedReviewerWholeState ->
      PackedReviewerLoweredWholeRun
  | 0, state =>
      { terminal := packedReviewerWholeResult state
        state := state
        logicalTrace := []
        physicalTrace := [] }
  | fuel + 1, state =>
      match packedReviewerWholeResult state with
      | some value =>
          { terminal := some value
            state := state
            logicalTrace := []
            physicalTrace := [] }
      | none =>
          match packedReviewerWholeNextRequest state with
          | none =>
              { terminal := none
                state := state
                logicalTrace := []
                physicalTrace := [] }
          | some request =>
              let reply :=
                packedReviewerLogicalRead shape.size (longCount shape)
                  (packedReviewerSparseCount shape)
                  (packedReviewerMemory shape) request
              let tail :=
                packedReviewerDriveLoweredWhole shape fuel
                  (packedReviewerWholeConsumeReply state reply)
              { terminal := tail.terminal
                state := tail.state
                logicalTrace := { request := request, reply := reply } ::
                  tail.logicalTrace
                physicalTrace :=
                  packedReviewerLogicalEventPhysicalTrace shape
                    { request := request, reply := reply } ++
                    tail.physicalTrace }

/-! ## Exact execution of a lowered whole-query state -/

def packedReviewerRunOfLowered
    (run : PackedReviewerLoweredWholeRun) : PackedReviewerRun where
  terminal := run.terminal
  failed := run.terminal.isNone
  state :=
    match run.terminal with
    | some value => .done value
    | none => .failed
  trace := run.physicalTrace

def packedReviewerPrependPhysicalEvents
    (events : List PackedReviewerPhysicalEvent) (tail : PackedReviewerRun) :
    PackedReviewerRun where
  terminal := tail.terminal
  failed := tail.failed
  state := tail.state
  trace := events ++ tail.trace

def packedReviewerPreludeAfterCells
    (n left right longCount : Nat)
    (state : PackedReviewerSparsePreludeState)
    (cells : List (List Bool)) : PackedReviewerControllerState :=
  match packedReviewerDecodePreludeReplies n longCount state cells with
  | none => .failed
  | some reply =>
      let state' := packedReviewerSparsePreludeConsumeReply state reply
      packedReviewerNormalizePrelude
        (packedReviewerSparsePreludeRemaining state')
        n left right longCount state'

@[simp] theorem packedReviewerDriveAgainstMemoryAux_done
    (memory : List (List Bool)) (fuel : Nat) (value : Option Nat) :
    packedReviewerDriveAgainstMemoryAux memory fuel (.done value) =
      { terminal := some value
        failed := false
        state := .done value
        trace := [] } := by
  cases fuel <;>
    simp [packedReviewerDriveAgainstMemoryAux,
      packedReviewerControllerResult, packedReviewerControllerFailed]

@[simp] theorem packedReviewerDriveAgainstMemoryAux_failed
    (memory : List (List Bool)) (fuel : Nat) :
    packedReviewerDriveAgainstMemoryAux memory fuel .failed =
      { terminal := none
        failed := true
        state := .failed
        trace := [] } := by
  cases fuel <;>
    simp [packedReviewerDriveAgainstMemoryAux,
      packedReviewerControllerResult, packedReviewerControllerFailed,
      packedReviewerNextRequest]

private theorem packedReviewerLogicalRead_of_fetch
    (shape : CartesianShape) (request : PackedReviewerLogicalRequest)
    {cells : List (List Bool)}
    (hfetch :
      packedFetch (packedReviewerMemory shape)
        (packedReviewerLogicalPlan shape.size (longCount shape)
          (packedReviewerSparseCount shape) request) = some cells) :
    packedReviewerLogicalRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape) request =
      packedReviewerLogicalDecode shape.size (longCount shape)
        (packedReviewerSparseCount shape) request cells := by
  unfold packedReviewerLogicalRead
  rw [hfetch]

/-- A dead/zero-cell logical word is consumed by normalization with no request. -/
theorem packedReviewerNormalizeWhole_zeroPlan
    (fuel n left right longCount sparseCount : Nat)
    (state : PackedReviewerWholeState)
    (request : PackedReviewerLogicalRequest)
    (hresult : packedReviewerWholeResult state = none)
    (hrequest : packedReviewerWholeNextRequest state = some request)
    (hplan : packedReviewerLogicalPlan n longCount sparseCount request = []) :
    packedReviewerNormalizeWhole (fuel + 1) n left right longCount sparseCount
        state =
      packedReviewerNormalizeWhole fuel n left right longCount sparseCount
        (packedReviewerWholeConsumeReply state
          (packedReviewerLogicalDecode n longCount sparseCount request [])) := by
  simp [packedReviewerNormalizeWhole, hresult, hrequest, hplan]

/--
With at least two physical slots per remaining logical step, driving the
residual-budget controller from its normalized whole state is exactly the
proof-side lowered run.  Surplus physical fuel is inert because the driver
stops at the resulting terminal controller state.
-/
theorem packedReviewerDriveNormalizedWhole_eq_lowered
    (shape : CartesianShape) (left right : Nat)
    (logicalFuel physicalFuel : Nat) (state : PackedReviewerWholeState)
    (hfuel : 2 * logicalFuel <= physicalFuel) :
    packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape)
        physicalFuel
        (packedReviewerNormalizeWhole logicalFuel shape.size left right
          (longCount shape) (packedReviewerSparseCount shape) state) =
      packedReviewerRunOfLowered
        (packedReviewerDriveLoweredWhole shape logicalFuel state) := by
  induction logicalFuel generalizing physicalFuel state with
  | zero =>
      cases hresult : packedReviewerWholeResult state with
      | some value =>
          simp [packedReviewerNormalizeWhole, packedReviewerDriveLoweredWhole,
            packedReviewerRunOfLowered, hresult]
      | none =>
          simp [packedReviewerNormalizeWhole, packedReviewerDriveLoweredWhole,
            packedReviewerRunOfLowered, hresult]
  | succ logicalFuel ih =>
      cases hresult : packedReviewerWholeResult state with
      | some value =>
          simp [packedReviewerNormalizeWhole, packedReviewerDriveLoweredWhole,
            packedReviewerRunOfLowered, hresult]
      | none =>
          cases hrequest : packedReviewerWholeNextRequest state with
          | none =>
              simp [packedReviewerNormalizeWhole,
                packedReviewerDriveLoweredWhole, packedReviewerRunOfLowered,
                hresult, hrequest]
          | some request =>
              let plan :=
                packedReviewerLogicalPlan shape.size (longCount shape)
                  (packedReviewerSparseCount shape) request
              have hplanLength : plan.length <= 2 := by
                exact packedReviewerLogicalPlan_length_le_two _ _ _ _
              rcases packedReviewerLogicalPlan_fetch shape request with
                ⟨cells, hfetch⟩
              have hlogicalRead :=
                packedReviewerLogicalRead_of_fetch shape request hfetch
              cases hplan : plan with
              | nil =>
                  have hfetchNil : cells = [] := by
                    simpa [plan, hplan, packedFetch] using hfetch.symm
                  subst cells
                  have htail := ih physicalFuel
                    (packedReviewerWholeConsumeReply state
                      (packedReviewerLogicalDecode shape.size (longCount shape)
                        (packedReviewerSparseCount shape) request [])) (by omega)
                  simp only [packedReviewerNormalizeWhole,
                    packedReviewerDriveLoweredWhole, hresult, hrequest]
                  simp only [plan, hplan] at hfetch hlogicalRead
                  simp [plan, hplan, packedReviewerLogicalEventPhysicalTrace,
                    packedReviewerPhysicalEvents,
                    packedReviewerPhysicalEventsFrom] at htail ⊢
                  simpa [hlogicalRead] using htail
              | cons first rest =>
                  cases rest with
                  | nil =>
                      cases hfirst : (packedReviewerMemory shape)[first]? with
                      | none =>
                          simp [plan, hplan, packedFetch, packedProbeCell,
                            hfirst] at hfetch
                      | some firstCell =>
                          have hcells : cells = [firstCell] := by
                            simpa [plan, hplan, packedFetch, packedProbeCell,
                              hfirst] using hfetch.symm
                          subst cells
                          cases physicalFuel with
                          | zero => omega
                          | succ physicalFuel =>
                              have htailFuel :
                                  2 * logicalFuel <= physicalFuel := by
                                omega
                              have htail := ih physicalFuel
                                (packedReviewerWholeConsumeReply state
                                  (packedReviewerLogicalDecode shape.size
                                    (longCount shape)
                                    (packedReviewerSparseCount shape) request
                                    [firstCell])) htailFuel
                              simp only [packedReviewerNormalizeWhole,
                                packedReviewerDriveLoweredWhole, hresult,
                                hrequest]
                              simp only [plan, hplan] at hfetch hlogicalRead
                              rw [hlogicalRead]
                              simp [packedReviewerDriveAgainstMemoryAux,
                                packedReviewerControllerResult,
                                packedReviewerNextRequest,
                                packedReviewerConsumeReply, hrequest, plan,
                                hplan, hfirst,
                                packedReviewerLogicalEventPhysicalTrace,
                                packedReviewerPhysicalEvents,
                                packedReviewerPhysicalEventsFrom,
                                packedReviewerRunOfLowered]
                              rw [htail]
                              simp [packedReviewerRunOfLowered]
                  | cons second tail =>
                      have htailNil : tail = [] := by
                        have := hplanLength
                        simp [plan, hplan] at this
                        cases tail with
                        | nil => rfl
                        | cons third tail => simp at this
                      subst tail
                      cases hfirst : (packedReviewerMemory shape)[first]? with
                      | none =>
                          simp [plan, hplan, packedFetch, packedProbeCell,
                            hfirst] at hfetch
                      | some firstCell =>
                          cases hsecond :
                              (packedReviewerMemory shape)[second]? with
                          | none =>
                              simp [plan, hplan, packedFetch, packedProbeCell,
                                hfirst, hsecond] at hfetch
                          | some secondCell =>
                              have hcells : cells = [firstCell, secondCell] := by
                                simpa [plan, hplan, packedFetch,
                                  packedProbeCell, hfirst, hsecond] using
                                    hfetch.symm
                              subst cells
                              cases physicalFuel with
                              | zero => omega
                              | succ physicalFuel =>
                                  cases physicalFuel with
                                  | zero => omega
                                  | succ physicalFuel =>
                                      have htailFuel :
                                          2 * logicalFuel <= physicalFuel := by
                                        omega
                                      have htail := ih physicalFuel
                                        (packedReviewerWholeConsumeReply state
                                          (packedReviewerLogicalDecode
                                            shape.size (longCount shape)
                                            (packedReviewerSparseCount shape)
                                            request
                                            [firstCell, secondCell])) htailFuel
                                      simp only [packedReviewerNormalizeWhole,
                                        packedReviewerDriveLoweredWhole,
                                        hresult, hrequest]
                                      simp only [plan, hplan] at hfetch hlogicalRead
                                      rw [hlogicalRead]
                                      simp [packedReviewerDriveAgainstMemoryAux,
                                        packedReviewerControllerResult,
                                        packedReviewerNextRequest,
                                        packedReviewerConsumeReply, hrequest,
                                        plan, hplan, hfirst, hsecond,
                                        packedReviewerLogicalEventPhysicalTrace,
                                        packedReviewerPhysicalEvents,
                                        packedReviewerPhysicalEventsFrom,
                                        packedReviewerRunOfLowered]
                                      rw [htail]
                                      simp [packedReviewerRunOfLowered]

/-- Execute one nonempty K1 prelude plan, preserving its exact per-cell block. -/
theorem packedReviewerDrivePreludeProbe_eq
    (memory : List (List Bool)) (n left right longCount : Nat)
    (state : PackedReviewerSparsePreludeState)
    (request : PackedReviewerSparsePreludeRequest)
    (hrequest : packedReviewerSparsePreludeNextRequest state = some request)
    (hnonempty : packedReviewerCurrentPreludePlan n longCount state ≠ [])
    (cells : List (List Bool))
    (hfetch : packedFetch memory
      (packedReviewerCurrentPreludePlan n longCount state) = some cells)
    (tailFuel : Nat) :
    packedReviewerDriveAgainstMemoryAux memory
        ((packedReviewerCurrentPreludePlan n longCount state).length + tailFuel)
        (.preludeProbe n left right longCount state 0 []) =
      packedReviewerPrependPhysicalEvents
        (packedReviewerPhysicalEvents memory (.sparsePrelude request)
          (packedReviewerCurrentPreludePlan n longCount state))
        (packedReviewerDriveAgainstMemoryAux memory tailFuel
          (packedReviewerPreludeAfterCells n left right longCount state cells)) := by
  let plan := packedReviewerCurrentPreludePlan n longCount state
  have hlength : plan.length <= 2 := by
    by_cases hindex :
        request.index n < packedSourceWordCount n longCount request.source
    · simpa [plan, packedReviewerCurrentPreludePlan, hrequest, hindex] using
        packedReviewerSparsePreludeRequestPlan_length_le_two n longCount request
    · simp [plan, packedReviewerCurrentPreludePlan, hrequest, hindex]
  have hfetchPlan : packedFetch memory plan = some cells := by
    simpa [plan] using hfetch
  cases hplan : plan with
  | nil =>
      apply False.elim
      apply hnonempty
      simpa [plan] using hplan
  | cons first rest =>
      cases rest with
      | nil =>
          cases hfirst : memory[first]? with
          | none =>
              simp [hplan, packedFetch, packedProbeCell, hfirst] at hfetchPlan
          | some firstCell =>
              have hcells : cells = [firstCell] := by
                simpa [hplan, packedFetch, packedProbeCell, hfirst] using
                  hfetchPlan.symm
              subst cells
              have hcurrent :
                  packedReviewerCurrentPreludePlan n longCount state =
                    [first] := by
                simpa [plan] using hplan
              simp [hcurrent, Nat.add_comm,
                packedReviewerDriveAgainstMemoryAux,
                packedReviewerControllerResult, packedReviewerNextRequest,
                packedReviewerConsumeReply, packedReviewerPreludeAfterCells,
                packedReviewerPrependPhysicalEvents,
                packedReviewerPhysicalEvents,
                packedReviewerPhysicalEventsFrom, hrequest, hfirst] <;>
                exact ⟨rfl, rfl, rfl, rfl⟩
      | cons second tail =>
          have htail : tail = [] := by
            have := hlength
            simp [plan, hplan] at this
            cases tail with
            | nil => rfl
            | cons third tail => simp at this
          subst tail
          cases hfirst : memory[first]? with
          | none =>
              simp [hplan, packedFetch, packedProbeCell, hfirst] at hfetchPlan
          | some firstCell =>
              cases hsecond : memory[second]? with
              | none =>
                  simp [hplan, packedFetch, packedProbeCell, hfirst,
                    hsecond] at hfetchPlan
              | some secondCell =>
                  have hcells : cells = [firstCell, secondCell] := by
                    simpa [hplan, packedFetch, packedProbeCell, hfirst,
                      hsecond] using hfetchPlan.symm
                  subst cells
                  have hcurrent :
                      packedReviewerCurrentPreludePlan n longCount state =
                        [first, second] := by
                    simpa [plan] using hplan
                  simp [hcurrent, Nat.add_comm,
                    packedReviewerDriveAgainstMemoryAux,
                    packedReviewerControllerResult, packedReviewerNextRequest,
                    packedReviewerConsumeReply,
                    packedReviewerPreludeAfterCells,
                    packedReviewerPrependPhysicalEvents,
                    packedReviewerPhysicalEvents,
                    packedReviewerPhysicalEventsFrom, hrequest, hfirst, hsecond] <;>
                    exact ⟨rfl, rfl, rfl, rfl⟩

private theorem packedReviewerPreludeRead_unpack
    (memory : List (List Bool)) (n longCount : Nat)
    (state : PackedReviewerSparsePreludeState)
    (request : PackedReviewerSparsePreludeRequest)
    (hrequest : packedReviewerSparsePreludeNextRequest state = some request)
    (word : List Bool)
    (hread : packedReviewerSparsePreludeRequestRead n longCount memory request =
      some word) :
    exists cells,
      packedReviewerCurrentPreludePlan n longCount state =
          packedReviewerSparsePreludeRequestPlan n longCount request /\
        packedFetch memory (packedReviewerCurrentPreludePlan n longCount state) =
          some cells /\
        packedReviewerDecodePreludeReplies n longCount state cells = some word := by
  unfold packedReviewerSparsePreludeRequestRead at hread
  by_cases hindex :
      request.index n < packedSourceWordCount n longCount request.source
  · rw [if_pos hindex] at hread
    cases hfetch : packedFetch memory
        (packedReviewerSparsePreludeRequestPlan n longCount request) with
    | none => simp [hfetch] at hread
    | some cells =>
        have hword :
            packedReviewerDecodeSpan n
                (packedReviewerSparsePreludeRequestBitAddress n longCount request)
                (packedSourceReadWidth n longCount request.source
                  (request.index n)) cells = word := by
          simpa [hfetch] using hread
        refine ⟨cells, ?_, ?_, ?_⟩
        · simp [packedReviewerCurrentPreludePlan, hrequest, hindex]
        · simpa [packedReviewerCurrentPreludePlan, hrequest, hindex] using
            hfetch
        · simp [packedReviewerDecodePreludeReplies, hrequest, hindex, hword]
  · rw [if_neg hindex] at hread
    simp at hread

/-- One canonical K1 logical reply is consumed with exactly its physical block. -/
theorem packedReviewerDriveNormalizePreludeStep_eq
    (memory : List (List Bool)) (n left right longCount remaining : Nat)
    (state : PackedReviewerSparsePreludeState)
    (request : PackedReviewerSparsePreludeRequest)
    (hresult : packedReviewerSparsePreludeResult state = none)
    (hrequest : packedReviewerSparsePreludeNextRequest state = some request)
    (word : List Bool)
    (hread : packedReviewerSparsePreludeRequestRead n longCount memory request =
      some word)
    (hremaining :
      packedReviewerSparsePreludeRemaining
          (packedReviewerSparsePreludeConsumeReply state word) = remaining)
    (tailFuel : Nat) :
    packedReviewerDriveAgainstMemoryAux memory
        ((packedReviewerCurrentPreludePlan n longCount state).length + tailFuel)
        (packedReviewerNormalizePrelude (remaining + 1)
          n left right longCount state) =
      packedReviewerPrependPhysicalEvents
        (packedReviewerPhysicalEvents memory (.sparsePrelude request)
          (packedReviewerCurrentPreludePlan n longCount state))
        (packedReviewerDriveAgainstMemoryAux memory tailFuel
          (packedReviewerNormalizePrelude remaining n left right longCount
            (packedReviewerSparsePreludeConsumeReply state word))) := by
  rcases packedReviewerPreludeRead_unpack memory n longCount state request
      hrequest word hread with ⟨cells, hplan, hfetch, hdecode⟩
  by_cases hnonempty : packedReviewerCurrentPreludePlan n longCount state = []
  · have hcells : cells = [] := by
      rw [hnonempty] at hfetch
      simpa [packedFetch] using hfetch.symm
    subst cells
    simp [packedReviewerNormalizePrelude, hresult, hnonempty, hdecode,
      packedReviewerPhysicalEvents, packedReviewerPhysicalEventsFrom,
      packedReviewerPrependPhysicalEvents]
  · have hprobe := packedReviewerDrivePreludeProbe_eq memory n left right
      longCount state request hrequest hnonempty cells hfetch tailFuel
    cases hplanCurrent : packedReviewerCurrentPreludePlan n longCount state with
    | nil => exact absurd hplanCurrent hnonempty
    | cons first rest =>
        simpa [packedReviewerNormalizePrelude, hresult, hplanCurrent,
          packedReviewerPreludeAfterCells, hdecode, hremaining] using hprobe

/-- The fixed three-site K1 prelude executes in source order and reaches K1. -/
theorem packedReviewerDriveCanonicalPrelude_eq
    (shape : CartesianShape) (left right wholeFuel : Nat) :
    let superState :=
      packedReviewerSparsePreludeInit shape.size (longCount shape)
    packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape)
        ((packedReviewerSparsePreludeRequestPlan shape.size
            (longCount shape) .rankSuper).length +
          ((packedReviewerSparsePreludeRequestPlan shape.size
              (longCount shape) .rankBlock).length +
            ((packedReviewerSparsePreludeRequestPlan shape.size
              (longCount shape) .flagWord).length + wholeFuel)))
        (packedReviewerNormalizePrelude 3 shape.size left right
          (longCount shape) superState) =
      packedReviewerPrependPhysicalEvents
        (packedReviewerSparsePreludePhysicalTrace shape)
        (packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape)
          wholeFuel
          (packedReviewerNormalizeWhole 210 shape.size left right
            (longCount shape) (packedReviewerSparseCount shape)
            (packedReviewerWholeStart shape.size left right))) := by
  rcases packedReviewerSparsePrelude_physicalReplies_exact shape with
    ⟨superReply, blockReply, flagReply, hsuper, hblock, hflag, hdecode⟩
  let superState :=
    packedReviewerSparsePreludeInit shape.size (longCount shape)
  let blockState :=
    packedReviewerSparsePreludeConsumeReply superState superReply
  let flagState :=
    packedReviewerSparsePreludeConsumeReply blockState blockReply
  let doneState :=
    packedReviewerSparsePreludeConsumeReply flagState flagReply
  have hsuperRequest :
      packedReviewerSparsePreludeNextRequest superState = some .rankSuper := by
    simp [superState, packedReviewerSparsePreludeInit,
      packedReviewerSparsePreludeNextRequest]
  have hblockRequest :
      packedReviewerSparsePreludeNextRequest blockState = some .rankBlock := by
    simp [blockState, superState, packedReviewerSparsePreludeInit,
      packedReviewerSparsePreludeConsumeReply,
      packedReviewerSparsePreludeNextRequest]
  have hflagRequest :
      packedReviewerSparsePreludeNextRequest flagState = some .flagWord := by
    simp [flagState, blockState, superState, packedReviewerSparsePreludeInit,
      packedReviewerSparsePreludeConsumeReply,
      packedReviewerSparsePreludeNextRequest]
  have hsuperRemaining :
      packedReviewerSparsePreludeRemaining blockState = 2 := by
    simp [blockState, superState, packedReviewerSparsePreludeInit,
      packedReviewerSparsePreludeConsumeReply,
      packedReviewerSparsePreludeRemaining]
  have hblockRemaining :
      packedReviewerSparsePreludeRemaining flagState = 1 := by
    simp [flagState, blockState, superState, packedReviewerSparsePreludeInit,
      packedReviewerSparsePreludeConsumeReply,
      packedReviewerSparsePreludeRemaining]
  have hflagRemaining :
      packedReviewerSparsePreludeRemaining doneState = 0 := by
    simp [doneState, flagState, blockState, superState,
      packedReviewerSparsePreludeInit,
      packedReviewerSparsePreludeConsumeReply,
      packedReviewerSparsePreludeRemaining]
  have hsuperResult : packedReviewerSparsePreludeResult superState = none := by
    simp [superState, packedReviewerSparsePreludeInit,
      packedReviewerSparsePreludeResult]
  have hblockResult : packedReviewerSparsePreludeResult blockState = none := by
    simp [blockState, superState, packedReviewerSparsePreludeInit,
      packedReviewerSparsePreludeConsumeReply,
      packedReviewerSparsePreludeResult]
  have hflagResult : packedReviewerSparsePreludeResult flagState = none := by
    simp [flagState, blockState, superState, packedReviewerSparsePreludeInit,
      packedReviewerSparsePreludeConsumeReply,
      packedReviewerSparsePreludeResult]
  have hsuperStep := packedReviewerDriveNormalizePreludeStep_eq
    (packedReviewerMemory shape) shape.size left right (longCount shape) 2
    superState .rankSuper hsuperResult hsuperRequest superReply hsuper
    hsuperRemaining
    ((packedReviewerCurrentPreludePlan shape.size (longCount shape)
        blockState).length +
      ((packedReviewerCurrentPreludePlan shape.size (longCount shape)
        flagState).length + wholeFuel))
  have hblockStep := packedReviewerDriveNormalizePreludeStep_eq
    (packedReviewerMemory shape) shape.size left right (longCount shape) 1
    blockState .rankBlock hblockResult hblockRequest blockReply hblock
    hblockRemaining
    ((packedReviewerCurrentPreludePlan shape.size (longCount shape)
      flagState).length + wholeFuel)
  have hflagStep := packedReviewerDriveNormalizePreludeStep_eq
    (packedReviewerMemory shape) shape.size left right (longCount shape) 0
    flagState .flagWord hflagResult hflagRequest flagReply hflag
    hflagRemaining wholeFuel
  have hdone :
      packedReviewerNormalizePrelude 0 shape.size left right (longCount shape)
          doneState =
        packedReviewerNormalizeWhole 210 shape.size left right
          (longCount shape) (packedReviewerSparseCount shape)
          (packedReviewerWholeStart shape.size left right) := by
    simp [packedReviewerNormalizePrelude, doneState, flagState, blockState,
      superState, packedReviewerSparsePreludeInit,
      packedReviewerSparsePreludeConsumeReply,
      packedReviewerSparsePreludeResult, hdecode]
  rcases packedReviewerPreludeRead_unpack (packedReviewerMemory shape)
      shape.size (longCount shape) superState .rankSuper hsuperRequest
      superReply hsuper with ⟨_, hsuperPlan, _, _⟩
  rcases packedReviewerPreludeRead_unpack (packedReviewerMemory shape)
      shape.size (longCount shape) blockState .rankBlock hblockRequest
      blockReply hblock with ⟨_, hblockPlan, _, _⟩
  rcases packedReviewerPreludeRead_unpack (packedReviewerMemory shape)
      shape.size (longCount shape) flagState .flagWord hflagRequest
      flagReply hflag with ⟨_, hflagPlan, _, _⟩
  dsimp only
  rw [← hsuperPlan, ← hblockPlan, ← hflagPlan]
  rw [hsuperStep]
  rw [hblockStep]
  rw [hflagStep, hdone]
  simp [packedReviewerPrependPhysicalEvents,
    packedReviewerSparsePreludePhysicalTrace,
    packedReviewerSparsePreludeRequests, hsuperPlan, hblockPlan, hflagPlan,
    List.append_assoc]

theorem packedReviewerControllerMeasure_valid_eq_427
    (n left right : Nat) (hvalid : left < right ∧ right <= n) :
    packedReviewerControllerMeasure (packedReviewerController n left right) =
      427 := by
  have hleft : left < n := by omega
  simp [packedReviewerController, hvalid, packedReviewerControllerMeasure,
    packedReviewerSparsePreludeRemaining, packedReviewerSparsePreludeInit,
    packedReviewerWholeRemaining, packedReviewerWholeStart,
    packedReviewerSelectStart, hleft, packedReviewerSelectRemaining,
    packedReviewerEntryRemaining]

/--
The actual public driver is header, K1 prelude, then the exact residual-budget
lowered whole run.  This is equality of the one executable run object.
-/
theorem packedReviewerRunAgainstMemory_eq_lowered
    (shape : CartesianShape) (left right : Nat)
    (hvalid : left < right ∧ right <= shape.size) :
    let lowered :=
      packedReviewerDriveLoweredWhole shape 210
        (packedReviewerWholeStart shape.size left right)
    packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right =
      packedReviewerPrependPhysicalEvents
        (packedReviewerHeaderPhysicalTrace shape)
        (packedReviewerPrependPhysicalEvents
          (packedReviewerSparsePreludePhysicalTrace shape)
          (packedReviewerRunOfLowered lowered)) := by
  let superPlan :=
    packedReviewerSparsePreludeRequestPlan shape.size (longCount shape)
      (.rankSuper)
  let blockPlan :=
    packedReviewerSparsePreludeRequestPlan shape.size (longCount shape)
      (.rankBlock)
  let flagPlan :=
    packedReviewerSparsePreludeRequestPlan shape.size (longCount shape)
      (.flagWord)
  let preludeCells := superPlan.length + blockPlan.length + flagPlan.length
  let wholeFuel := 426 - preludeCells
  have hprelude : preludeCells <= 6 := by
    have hbound := packedReviewerSparsePreludeProbePlan_length_le_six
      shape.size (longCount shape)
    simpa [preludeCells, superPlan, blockPlan, flagPlan,
      packedReviewerSparsePreludeProbePlan,
      packedReviewerSparsePreludeRequests, List.length_append,
      Nat.add_assoc] using hbound
  have hwholeFuel : 420 <= wholeFuel := by
    simp only [wholeFuel]
    omega
  have hfuelEq :
      superPlan.length + (blockPlan.length + (flagPlan.length + wholeFuel)) =
        426 := by
    simp only [wholeFuel, preludeCells]
    omega
  have hpreludeRun := packedReviewerDriveCanonicalPrelude_eq shape left right
    wholeFuel
  have hwholeRun := packedReviewerDriveNormalizedWhole_eq_lowered
    shape left right 210 wholeFuel
    (packedReviewerWholeStart shape.size left right) hwholeFuel
  have hheader := packedReviewerMemory_header_cell shape
  have hmeasure := packedReviewerControllerMeasure_valid_eq_427
    shape.size left right hvalid
  have hcontroller :
      packedReviewerController shape.size left right =
        .header shape.size left right := by
    simp [packedReviewerController, hvalid]
  have hconsume :
      packedReviewerConsumeReply (.header shape.size left right)
          (some (packedReviewerHeaderBits shape)) =
        packedReviewerNormalizePrelude 3 shape.size left right
          (longCount shape)
          (packedReviewerSparsePreludeInit shape.size (longCount shape)) := by
    simp only [packedReviewerConsumeReply, packedReviewerHeaderBits_decode,
      packedReviewerSparsePreludeRemaining,
      packedReviewerSparsePreludeInit]
  let headerEvent : PackedReviewerPhysicalEvent :=
    { request :=
        { origin := .header, address := 0, ordinal := 0, cellCount := 1 }
      reply := some (packedReviewerHeaderBits shape) }
  have hheaderTrace :
      packedReviewerHeaderPhysicalTrace shape = [headerEvent] := by
    simp [headerEvent, packedReviewerHeaderPhysicalTrace,
      packedReviewerPhysicalEvents, packedReviewerPhysicalEventsFrom, hheader]
  dsimp only
  simp only [packedReviewerRunAgainstMemory]
  rw [hmeasure]
  rw [hcontroller]
  rw [packedReviewerDriveAgainstMemoryAux]
  simp only [packedReviewerControllerResult, packedReviewerNextRequest]
  rw [hheader, hconsume]
  change packedReviewerPrependPhysicalEvents [headerEvent]
      (packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape) 426
        (packedReviewerNormalizePrelude 3 shape.size left right
          (longCount shape)
          (packedReviewerSparsePreludeInit shape.size (longCount shape)))) = _
  rw [hheaderTrace]
  apply congrArg (packedReviewerPrependPhysicalEvents [headerEvent])
  change packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape) 426
      (packedReviewerNormalizePrelude 3 shape.size left right
        (longCount shape)
        (packedReviewerSparsePreludeInit shape.size (longCount shape))) = _
  rw [← hfuelEq]
  simpa only [superPlan, blockPlan, flagPlan] using
    hpreludeRun.trans
      (congrArg
        (packedReviewerPrependPhysicalEvents
          (packedReviewerSparsePreludePhysicalTrace shape)) hwholeRun)


/-! ## Position- and multiplicity-preserving physical expansion -/

theorem packedReviewerPhysicalEventsFrom_length
    (memory : List (List Bool)) (origin : PackedReviewerPhysicalOrigin)
    (cellCount ordinal : Nat) (plan : List Nat) :
    (packedReviewerPhysicalEventsFrom memory origin cellCount ordinal
      plan).length = plan.length := by
  induction plan generalizing ordinal with
  | nil => rfl
  | cons address rest ih =>
      simp [packedReviewerPhysicalEventsFrom, ih]

theorem packedReviewerPhysicalEvents_length
    (memory : List (List Bool)) (origin : PackedReviewerPhysicalOrigin)
    (plan : List Nat) :
    (packedReviewerPhysicalEvents memory origin plan).length = plan.length := by
  exact packedReviewerPhysicalEventsFrom_length memory origin plan.length 0 plan

/-- Exact occurrence equation for one plan; no `List.Mem` collapse occurs. -/
theorem packedReviewerPhysicalEventsFrom_get?_eq
    (memory : List (List Bool)) (origin : PackedReviewerPhysicalOrigin)
    (cellCount ordinal : Nat) (plan : List Nat) (position : Nat) :
    (packedReviewerPhysicalEventsFrom memory origin cellCount ordinal
      plan)[position]? =
      plan[position]?.map fun address =>
        { request :=
            { origin := origin
              address := address
              ordinal := ordinal + position
              cellCount := cellCount }
          reply := memory[address]? } := by
  induction plan generalizing ordinal position with
  | nil => simp [packedReviewerPhysicalEventsFrom]
  | cons address rest ih =>
      cases position with
      | zero => simp [packedReviewerPhysicalEventsFrom]
      | succ position =>
          simp [packedReviewerPhysicalEventsFrom, ih, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm]

theorem packedReviewerPhysicalEvents_get?_eq
    (memory : List (List Bool)) (origin : PackedReviewerPhysicalOrigin)
    (plan : List Nat) (position : Nat) :
    (packedReviewerPhysicalEvents memory origin plan)[position]? =
      plan[position]?.map fun address =>
        { request :=
            { origin := origin
              address := address
              ordinal := position
              cellCount := plan.length }
          reply := memory[address]? } := by
  simpa [packedReviewerPhysicalEvents, Nat.zero_add] using
    packedReviewerPhysicalEventsFrom_get?_eq memory origin plan.length 0 plan
      position

/-- Membership in an expanded plan retains its exact ordinal and cell count. -/
theorem packedReviewerPhysicalEvents_request_eq
    (memory : List (List Bool)) (origin : PackedReviewerPhysicalOrigin)
    (plan : List Nat) {event : PackedReviewerPhysicalEvent}
    (hmem : event ∈ packedReviewerPhysicalEvents memory origin plan) :
    exists position address,
      plan[position]? = some address ∧
        event.request =
          { origin := origin
            address := address
            ordinal := position
            cellCount := plan.length } := by
  rcases List.mem_iff_getElem?.1 hmem with ⟨position, hposition⟩
  rw [packedReviewerPhysicalEvents_get?_eq] at hposition
  cases haddress : plan[position]? with
  | none => simp [haddress] at hposition
  | some address =>
      have hevent :
          { request :=
              { origin := origin
                address := address
                ordinal := position
                cellCount := plan.length }
            reply := memory[address]? } = event := by
        exact Option.some.inj (by simpa [haddress] using hposition)
      subst event
      exact ⟨position, address, haddress, rfl⟩

/--
One expanded plan preserves every origin operand, address, ordinal and count.
This is the reusable constructor-exhaustive leaf for header, K1, and whole-run
blocks.
-/
theorem packedReviewerPhysicalEvents_request_operands_fit
    (n : Nat) (memory : List (List Bool))
    (origin : PackedReviewerPhysicalOrigin) (plan : List Nat)
    (horigin :
      forall operand,
        operand ∈ packedReviewerPhysicalOriginOperands origin ->
          PackedReviewerNatFits n operand)
    (haddress :
      forall address, address ∈ plan -> PackedReviewerNatFits n address)
    (hcount : plan.length <= 2)
    {event : PackedReviewerPhysicalEvent}
    (hmem : event ∈ packedReviewerPhysicalEvents memory origin plan) :
    PackedReviewerPhysicalRequestOperandsFit n event.request := by
  rcases packedReviewerPhysicalEvents_request_eq memory origin plan hmem with
    ⟨position, address, hposition, hrequest⟩
  rw [hrequest]
  have hpositionLt : position < plan.length :=
    (List.getElem?_eq_some_iff.mp hposition).1
  have hsmall := packedReviewerPhysicalRequest_small_fields_fit n
    { origin := origin
      address := address
      ordinal := position
      cellCount := plan.length }
    hpositionLt hcount
  refine
    { operands_fit := ?_
      ordinal_lt := hpositionLt
      cellCount_le_two := hcount }
  intro operand hopen
  simp only [packedReviewerPhysicalRequestOperands,
    packedReviewerPhysicalOriginOperands, List.mem_append, List.mem_cons,
    List.mem_singleton] at hopen
  rcases hopen with horiginOperand | haddressOperand | hordinalOperand |
    hcountOperand | hnil
  · exact horigin operand horiginOperand
  · rw [haddressOperand]
    exact haddress address (List.mem_of_getElem? hposition)
  · rw [hordinalOperand]
    exact hsmall.1
  · rw [hcountOperand]
    exact hsmall.2
  · exact False.elim (List.not_mem_nil hnil)

theorem packedReviewerPhysicalEventsFrom_addresses
    (memory : List (List Bool)) (origin : PackedReviewerPhysicalOrigin)
    (cellCount ordinal : Nat) (plan : List Nat) :
    (packedReviewerPhysicalEventsFrom memory origin cellCount ordinal plan).map
        (fun event => event.request.address) = plan := by
  induction plan generalizing ordinal with
  | nil => rfl
  | cons address rest ih =>
      simp [packedReviewerPhysicalEventsFrom, ih]

theorem packedReviewerPhysicalEvents_addresses
    (memory : List (List Bool)) (origin : PackedReviewerPhysicalOrigin)
    (plan : List Nat) :
    (packedReviewerPhysicalEvents memory origin plan).map
        (fun event => event.request.address) = plan := by
  exact packedReviewerPhysicalEventsFrom_addresses memory origin plan.length 0
    plan

private theorem packedReviewerPhysicalEventsFrom_address_mem
    (memory : List (List Bool)) (origin : PackedReviewerPhysicalOrigin)
    (cellCount ordinal : Nat) (plan : List Nat)
    {event : PackedReviewerPhysicalEvent}
    (hmem : event ∈ packedReviewerPhysicalEventsFrom memory origin cellCount
      ordinal plan) :
    event.request.address ∈ plan := by
  induction plan generalizing event ordinal with
  | nil => simp [packedReviewerPhysicalEventsFrom] at hmem
  | cons address rest ih =>
      simp only [packedReviewerPhysicalEventsFrom, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · simp
      · exact List.mem_cons_of_mem _ (ih _ htail)

theorem packedReviewerPhysicalEvents_address_mem
    (memory : List (List Bool)) (origin : PackedReviewerPhysicalOrigin)
    (plan : List Nat) {event : PackedReviewerPhysicalEvent}
    (hmem : event ∈ packedReviewerPhysicalEvents memory origin plan) :
    event.request.address ∈ plan :=
  packedReviewerPhysicalEventsFrom_address_mem memory origin plan.length 0 plan
    hmem

/-- Every event in an expanded block is the literal lookup at its address. -/
private theorem packedReviewerPhysicalEventsFrom_memory_only
    (memory : List (List Bool)) (origin : PackedReviewerPhysicalOrigin)
    (cellCount ordinal : Nat) (plan : List Nat)
    {event : PackedReviewerPhysicalEvent}
    (hmem : event ∈ packedReviewerPhysicalEventsFrom memory origin cellCount
      ordinal plan) :
    event.reply = memory[event.request.address]? := by
  induction plan generalizing event ordinal with
  | nil => simp [packedReviewerPhysicalEventsFrom] at hmem
  | cons address rest ih =>
      simp only [packedReviewerPhysicalEventsFrom, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · rfl
      · exact ih _ htail

theorem packedReviewerPhysicalEvents_memory_only
    (memory : List (List Bool)) (origin : PackedReviewerPhysicalOrigin)
    (plan : List Nat) {event : PackedReviewerPhysicalEvent}
    (hmem : event ∈ packedReviewerPhysicalEvents memory origin plan) :
    event.reply = memory[event.request.address]? :=
  packedReviewerPhysicalEventsFrom_memory_only memory origin plan.length 0 plan
    hmem

/-- Ordered dynamic agreement on every request made by the first run. -/
def PackedReviewerMemoriesAgreeOnRun
    (memoryA memoryB : List (List Bool))
    (state : PackedReviewerControllerState) (fuel : Nat) : Prop :=
  forall event,
    event ∈ (packedReviewerDriveAgainstMemoryAux memoryA fuel state).trace ->
      memoryB[event.request.address]? = event.reply

/-- Dynamic agreement determines result, residual state, and full ordered trace. -/
theorem packedReviewerDriveAgainstMemoryAux_eq_of_agree
    (memoryA memoryB : List (List Bool)) (fuel : Nat)
    (state : PackedReviewerControllerState)
    (hagree : PackedReviewerMemoriesAgreeOnRun memoryA memoryB state fuel) :
    packedReviewerDriveAgainstMemoryAux memoryA fuel state =
      packedReviewerDriveAgainstMemoryAux memoryB fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases hresult : packedReviewerControllerResult state with
      | some value =>
          simp [packedReviewerDriveAgainstMemoryAux, hresult]
      | none =>
          cases hrequest : packedReviewerNextRequest state with
          | none =>
              simp [packedReviewerDriveAgainstMemoryAux, hresult, hrequest]
          | some request =>
              have hlookup :
                  memoryB[request.address]? = memoryA[request.address]? := by
                have hhead := hagree
                  ({ request := request
                     reply := memoryA[request.address]? } :
                    PackedReviewerPhysicalEvent)
                exact hhead (by
                  simp [packedReviewerDriveAgainstMemoryAux, hresult,
                    hrequest])
              have htailAgree : PackedReviewerMemoriesAgreeOnRun memoryA memoryB
                  (packedReviewerConsumeReply state
                    (memoryA[request.address]?)) fuel := by
                intro event hmem
                apply hagree event
                simp [packedReviewerDriveAgainstMemoryAux, hresult, hrequest,
                  hmem]
              have htail := ih
                (packedReviewerConsumeReply state
                  (memoryA[request.address]?)) htailAgree
              simp [packedReviewerDriveAgainstMemoryAux, hresult, hrequest,
                hlookup, htail]

theorem packedReviewerRunAgainstMemory_eq_of_agree
    (memoryA memoryB : List (List Bool)) (n left right : Nat)
    (hagree : PackedReviewerMemoriesAgreeOnRun memoryA memoryB
      (packedReviewerController n left right)
      (packedReviewerControllerMeasure
        (packedReviewerController n left right))) :
    packedReviewerRunAgainstMemory memoryA n left right =
      packedReviewerRunAgainstMemory memoryB n left right := by
  unfold packedReviewerRunAgainstMemory
  exact packedReviewerDriveAgainstMemoryAux_eq_of_agree memoryA memoryB _ _
    hagree

/--
The lowered proof run is the accepted logical driver, including occurrence
order, and its physical trace is the block expansion of that same logical
trace.  The only semantic bridge is the all-segment memory-lowering theorem.
-/
theorem packedReviewerDriveLoweredWhole_eq_logical
    (shape : CartesianShape) (fuel : Nat) (state : PackedReviewerWholeState) :
    let lowered := packedReviewerDriveLoweredWhole shape fuel state
    let logical :=
      packedReviewerDriveLogical
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) fuel state
    lowered.terminal = logical.terminal /\
      lowered.state = logical.state /\
      lowered.logicalTrace = logical.trace /\
      lowered.physicalTrace =
        packedReviewerLogicalTracePhysicalTrace shape logical.trace := by
  induction fuel generalizing state with
  | zero =>
      simp [packedReviewerDriveLoweredWhole, packedReviewerDriveLogical,
        packedReviewerLogicalTracePhysicalTrace]
  | succ fuel ih =>
      cases hresult : packedReviewerWholeResult state with
      | some value =>
          simp [packedReviewerDriveLoweredWhole, packedReviewerDriveLogical,
            hresult, packedReviewerLogicalTracePhysicalTrace]
      | none =>
          cases hrequest : packedReviewerWholeNextRequest state with
          | none =>
              simp [packedReviewerDriveLoweredWhole, packedReviewerDriveLogical,
                hresult, hrequest, packedReviewerLogicalTracePhysicalTrace]
          | some request =>
              have hread := packedReviewerLogicalRead_eq_globalReadStore
                shape request
              have htail := ih
                (packedReviewerWholeConsumeReply state
                  ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                    request.segment request.index))
              simp only [packedReviewerDriveLoweredWhole,
                packedReviewerDriveLogical, hresult, hrequest]
              rw [hread]
              simpa [packedReviewerLogicalTracePhysicalTrace,
                packedReviewerLogicalEventPhysicalTrace] using htail

/-- The fixed lowered run reaches the accepted packed whole-query result. -/
theorem packedReviewerDriveLoweredWhole_210_simulates_packedWholeQueryRun
    (shape : CartesianShape) (left right : Nat)
    (hleft : left < right) (hright : right <= shape.size) :
    let lowered :=
      packedReviewerDriveLoweredWhole shape 210
        (packedReviewerWholeStart shape.size left right)
    let reference :=
      packedWholeQueryRun
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        shape.size left right
    lowered.terminal = some reference.value /\
      lowered.state = .done reference.value /\
      lowered.logicalTrace.map PackedReviewerLogicalEvent.erase =
        reference.trace /\
      lowered.physicalTrace =
        packedReviewerLogicalTracePhysicalTrace shape lowered.logicalTrace := by
  have hlowered :=
    packedReviewerDriveLoweredWhole_eq_logical shape 210
      (packedReviewerWholeStart shape.size left right)
  have hlogical :=
    packedReviewerDriveLogical_210_simulates_packedWholeQueryRun
      shape left right hleft hright
  dsimp only at hlowered hlogical ⊢
  exact ⟨hlowered.1.trans hlogical.1,
    hlowered.2.1.trans hlogical.2.1,
    Eq.trans
      (congrArg (List.map PackedReviewerLogicalEvent.erase) hlowered.2.2.1)
      hlogical.2.2,
    hlowered.2.2.2.trans
      (congrArg (packedReviewerLogicalTracePhysicalTrace shape)
        hlowered.2.2.1).symm⟩

def packedReviewerExpectedPhysicalTrace
    (shape : CartesianShape) (left right : Nat) :
    List PackedReviewerPhysicalEvent :=
  if left < right ∧ right <= shape.size then
    packedReviewerHeaderPhysicalTrace shape ++
      packedReviewerSparsePreludePhysicalTrace shape ++
        packedReviewerLogicalTracePhysicalTrace shape
          (packedReviewerDriveLogical
            (concreteBPNativeSuccinctRMQGlobalReadStore shape) 210
            (packedReviewerWholeStart shape.size left right)).trace
  else
    []

structure PackedReviewerRunGrouping
    (shape : CartesianShape) (left right : Nat) : Prop where
  trace_eq :
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).trace =
        packedReviewerExpectedPhysicalTrace shape left right

/-- Global occurrence equality for the actual grouped physical transcript. -/
theorem PackedReviewerRunGrouping.get?_eq
    {shape : CartesianShape} {left right : Nat}
    (grouping : PackedReviewerRunGrouping shape left right)
    (position : Nat) :
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace[position]? =
      (packedReviewerExpectedPhysicalTrace shape left right)[position]? := by
  rw [grouping.trace_eq]

/-- Valid physical runs terminate correctly and carry their exact grouping. -/
theorem packedReviewerRunAgainstMemory_valid_certificate
    (shape : CartesianShape) (left right : Nat)
    (hleft : left < right) (hright : right <= shape.size) :
    let run :=
      packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right
    let reference :=
      packedWholeQueryRun
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        shape.size left right
    run.terminal = some reference.value /\
      run.failed = false /\
      run.state = .done reference.value /\
      PackedReviewerRunGrouping shape left right := by
  let lowered :=
    packedReviewerDriveLoweredWhole shape 210
      (packedReviewerWholeStart shape.size left right)
  have hrun := packedReviewerRunAgainstMemory_eq_lowered shape left right
    ⟨hleft, hright⟩
  have hcap :=
    packedReviewerDriveLoweredWhole_210_simulates_packedWholeQueryRun
      shape left right hleft hright
  have hlowered :=
    packedReviewerDriveLoweredWhole_eq_logical shape 210
      (packedReviewerWholeStart shape.size left right)
  dsimp only at hcap hlowered ⊢
  have hterminal : lowered.terminal =
      some (packedWholeQueryRun
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        shape.size left right).value := hcap.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrun]
    change lowered.terminal = _
    exact hterminal
  · rw [hrun]
    change lowered.terminal.isNone = false
    rw [hterminal]
    rfl
  · rw [hrun]
    change
      (match lowered.terminal with
      | some value => PackedReviewerControllerState.done value
      | none => PackedReviewerControllerState.failed) = _
    rw [hterminal]
  · constructor
    rw [hrun]
    simp only [packedReviewerPrependPhysicalEvents,
      packedReviewerRunOfLowered]
    rw [packedReviewerExpectedPhysicalTrace, if_pos ⟨hleft, hright⟩]
    exact congrArg
      (fun trace =>
        packedReviewerHeaderPhysicalTrace shape ++
          packedReviewerSparsePreludePhysicalTrace shape ++ trace)
      hlowered.2.2.2

/-- Invalid, empty, reversed, and out-of-range endpoints are pure physical none. -/
theorem packedReviewerRunAgainstMemory_invalid_certificate
    (shape : CartesianShape) (left right : Nat)
    (hbad : ¬ (left < right ∧ right <= shape.size)) :
    let run :=
      packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right
    run.terminal = some none /\
      run.failed = false /\
      run.state = .done none /\
      PackedReviewerRunGrouping shape left right := by
  dsimp only
  have hrun :
      packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right =
        { terminal := some none
          failed := false
          state := .done none
          trace := [] } := by
    simp [packedReviewerRunAgainstMemory, packedReviewerController, hbad,
      packedReviewerControllerMeasure, packedReviewerDriveAgainstMemoryAux,
      packedReviewerControllerResult, packedReviewerControllerFailed]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrun]
  · rw [hrun]
  · rw [hrun]
  · constructor
    rw [hrun]
    simp [packedReviewerExpectedPhysicalTrace, hbad]

/-- Invalid arbitrary endpoint pairs issue no physical request at all. -/
theorem packedReviewerRunAgainstMemory_invalid_trace_eq_nil
    (shape : CartesianShape) (left right : Nat)
    (hbad : ¬ (left < right ∧ right <= shape.size)) :
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).trace = [] := by
  have hcertificate :=
    packedReviewerRunAgainstMemory_invalid_certificate shape left right hbad
  dsimp only at hcertificate
  have hgrouping := hcertificate.2.2.2.trace_eq
  simpa [packedReviewerExpectedPhysicalTrace, hbad] using hgrouping

theorem packedReviewerExpectedPhysicalTrace_address_lt_cellCount
    (shape : CartesianShape) (left right : Nat)
    {event : PackedReviewerPhysicalEvent}
    (hmem : event ∈ packedReviewerExpectedPhysicalTrace shape left right) :
    event.request.address <
      packedReviewerCellCount shape.size (longCount shape)
        (packedReviewerSparseCount shape) := by
  by_cases hvalid : left < right ∧ right <= shape.size
  · rw [packedReviewerExpectedPhysicalTrace, if_pos hvalid] at hmem
    rcases List.mem_append.mp hmem with hprefix | hlogical
    · rcases List.mem_append.mp hprefix with hheader | hprelude
      · have haddress := packedReviewerPhysicalEvents_address_mem
          (packedReviewerMemory shape) .header [0] hheader
        simp only [List.mem_singleton] at haddress
        rw [haddress]
        unfold packedReviewerCellCount
        omega
      · unfold packedReviewerSparsePreludePhysicalTrace at hprelude
        rw [List.mem_flatMap] at hprelude
        rcases hprelude with ⟨request, hrequest, hevent⟩
        have haddress := packedReviewerPhysicalEvents_address_mem
          (packedReviewerMemory shape) (.sparsePrelude request)
          (packedReviewerSparsePreludeRequestPlan shape.size (longCount shape)
            request) hevent
        apply packedReviewerSparsePreludeProbePlan_address_lt_cellCount shape
        exact List.mem_flatMap.mpr ⟨request, hrequest, haddress⟩
    · unfold packedReviewerLogicalTracePhysicalTrace at hlogical
      rw [List.mem_flatMap] at hlogical
      rcases hlogical with ⟨logicalEvent, _htrace, hevent⟩
      exact packedReviewerLogicalPlan_address_lt_cellCount shape
        logicalEvent.request
        (packedReviewerPhysicalEvents_address_mem
          (packedReviewerMemory shape) (.wholeQuery logicalEvent.request)
          (packedReviewerLogicalPlan shape.size (longCount shape)
            (packedReviewerSparseCount shape) logicalEvent.request) hevent)
  · simp [packedReviewerExpectedPhysicalTrace, hvalid] at hmem

/-!
Request-operand closure is completed downstream in
`ReviewerControllerStateProof`, where the canonical prefix invariant can
justify dynamic logical indices without creating an import cycle.  This base
module retains the independent execution, grouping, allocation, backing,
reply, correctness, and cap theorems consumed by that closure.
-/

theorem PackedReviewerRunGrouping.address_lt_cellCount
    {shape : CartesianShape} {left right : Nat}
    (grouping : PackedReviewerRunGrouping shape left right)
    {event : PackedReviewerPhysicalEvent}
    (hmem : event ∈
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace) :
    event.request.address <
      packedReviewerCellCount shape.size (longCount shape)
        (packedReviewerSparseCount shape) := by
  rw [grouping.trace_eq] at hmem
  exact packedReviewerExpectedPhysicalTrace_address_lt_cellCount shape
    left right hmem

theorem PackedReviewerRunGrouping.address_lt_two_pow
    {shape : CartesianShape} {left right : Nat}
    (grouping : PackedReviewerRunGrouping shape left right)
    {event : PackedReviewerPhysicalEvent}
    (hmem : event ∈
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace) :
    event.request.address < 2 ^ packedReviewerCellWidth shape.size :=
  Nat.lt_trans (grouping.address_lt_cellCount hmem)
    (packedReviewerSparsePreludeCellCount_lt_two_pow_reviewerWidth shape)

/-- Every attempted request of a grouped canonical run receives a real cell. -/
theorem PackedReviewerRunGrouping.reply_some
    {shape : CartesianShape} {left right : Nat}
    (grouping : PackedReviewerRunGrouping shape left right)
    {event : PackedReviewerPhysicalEvent}
    (hmem : event ∈
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace) :
    exists cell, event.reply = some cell := by
  have hbacking := packedReviewerRunAgainstMemory_memory_only
    (packedReviewerMemory shape) shape.size left right event hmem
  have hltMemory :
      event.request.address < (packedReviewerMemory shape).length := by
    rw [packedReviewerMemory_length]
    exact grouping.address_lt_cellCount hmem
  refine
    ⟨(packedReviewerMemory shape)[event.request.address]'hltMemory, ?_⟩
  rw [hbacking]
  exact List.getElem?_eq_getElem hltMemory

theorem packedReviewerRunAgainstMemory_reply_width
    (shape : CartesianShape) (left right : Nat)
    {event : PackedReviewerPhysicalEvent} {cell : List Bool}
    (hmem : event ∈
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace)
    (hreply : event.reply = some cell) :
    cell.length = packedReviewerCellWidth shape.size := by
  have hbacking := packedReviewerRunAgainstMemory_memory_only
    (packedReviewerMemory shape) shape.size left right event hmem
  have hget : (packedReviewerMemory shape)[event.request.address]? =
      some cell := by
    rw [← hbacking, hreply]
  apply packedReviewerMemory_cell_length shape
  exact List.mem_iff_getElem?.2 ⟨event.request.address, hget⟩

/-- Every successful physical reply's decoded value fits the same word. -/
theorem packedReviewerRunAgainstMemory_reply_value_width
    (shape : CartesianShape) (left right : Nat)
    {event : PackedReviewerPhysicalEvent} {cell : List Bool}
    (hmem : event ∈
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace)
    (hreply : event.reply = some cell) :
    SuccinctSpace.bitsToNatLE cell <
      2 ^ packedReviewerCellWidth shape.size := by
  apply PackedReviewerWordFits.value_lt_two_pow
  exact Nat.le_of_eq
    (packedReviewerRunAgainstMemory_reply_width shape left right hmem hreply)

@[simp] theorem packedReviewerCartesianShape_size (xs : List Int) :
    (SuccinctClassic.cartesianShape xs).size = xs.length := by
  unfold SuccinctClassic.cartesianShape
  exact Cartesian.shape_size xs

theorem packedReviewerPackedReference_eq_public
    (xs : List Int) (left right : Nat)
    (hvalid : ValidRange xs left right) :
    let shape := SuccinctClassic.cartesianShape xs
    packedWholeQueryRun
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        shape.size left right =
      SuccinctClassic.queryTraceResult xs left right := by
  dsimp only
  let shape := SuccinctClassic.cartesianShape xs
  calc
    packedWholeQueryRun
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        shape.size left right =
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          left right :=
      (packedWholeQueryRun_eq shape
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) left right).symm
    _ = concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right :=
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore
        shape left right
    _ = SuccinctClassic.queryTraceResult xs left right :=
      (SuccinctClassic.queryTraceResult_valid xs left right hvalid).symm

theorem packedReviewerRunAgainstMemory_public_outcome
    (xs : List Int) (left right : Nat) :
    let shape := SuccinctClassic.cartesianShape xs
    let run := packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right
    run.terminal =
        some (SuccinctClassic.queryTraceResult xs left right).value /\
      run.failed = false /\
      run.state =
        .done (SuccinctClassic.queryTraceResult xs left right).value /\
      PackedReviewerRunGrouping shape left right := by
  let shape := SuccinctClassic.cartesianShape xs
  by_cases hvalid : ValidRange xs left right
  · have hshapeValid : left < right ∧ right <= shape.size := by
      simpa [shape, ValidRange, packedReviewerCartesianShape_size] using hvalid
    have hphysical := packedReviewerRunAgainstMemory_valid_certificate shape
      left right hshapeValid.1 hshapeValid.2
    have href := packedReviewerPackedReference_eq_public xs left right hvalid
    have hvalue := congrArg WordRAM.TraceResult.value href
    dsimp only at hphysical hvalue ⊢
    rw [hvalue] at hphysical
    simpa [shape, packedReviewerCartesianShape_size] using hphysical
  · have hshapeBad : ¬ (left < right ∧ right <= shape.size) := by
      simpa [shape, ValidRange, packedReviewerCartesianShape_size] using hvalid
    have hphysical := packedReviewerRunAgainstMemory_invalid_certificate shape
      left right hshapeBad
    have hpublic := SuccinctClassic.queryTraceResult_invalid xs left right hvalid
    dsimp only at hphysical ⊢
    simpa [shape, packedReviewerCartesianShape_size, hpublic,
      WordRAM.TraceResult.pure] using hphysical

theorem packedReviewerPublicResult_lt_two_pow
    (xs : List Int) (left right index : Nat)
    (hresult :
      (SuccinctClassic.queryTraceResult xs left right).value = some index) :
    index <
      2 ^ packedReviewerCellWidth
        (SuccinctClassic.cartesianShape xs).size := by
  by_cases hvalid : ValidRange xs left right
  · let len := right - left
    have hlen : 0 < len := by
      simp only [len]
      omega
    have hright : left + len = right := by
      simp only [len]
      omega
    have hbound : left + len <= xs.length := by
      rw [hright]
      exact hvalid.2
    have hexact := SuccinctClassic.queryCosted_exact xs hlen hbound
    have hvalue :
        (SuccinctClassic.queryTraceResult xs left right).value =
          some (scanWindow xs left len) := by
      rw [hright] at hexact
      simpa [SuccinctClassic.queryCosted, Costed.erase,
        WordRAM.TraceResult.toCosted] using hexact
    rw [hvalue] at hresult
    have hindex : index = scanWindow xs left len := Option.some.inj hresult.symm
    have hwindow := scanWindow_bounds xs left len hlen
    have hsize := packedReviewerInputSize_lt_two_pow_cellWidth xs.length
    rw [hindex, packedReviewerCartesianShape_size]
    omega
  · have hnone := SuccinctClassic.queryTraceResult_invalid xs left right
      hvalid
    rw [hnone] at hresult
    simp [WordRAM.TraceResult.pure] at hresult

theorem packedReviewerLogicalEventPhysicalTrace_length_le_two
    (shape : CartesianShape) (event : PackedReviewerLogicalEvent) :
    (packedReviewerLogicalEventPhysicalTrace shape event).length <= 2 := by
  rw [packedReviewerLogicalEventPhysicalTrace,
    packedReviewerPhysicalEvents_length]
  exact packedReviewerLogicalPlan_length_le_two _ _ _ _

theorem packedReviewerLogicalTracePhysicalTrace_length_le
    (shape : CartesianShape) (trace : List PackedReviewerLogicalEvent) :
    (packedReviewerLogicalTracePhysicalTrace shape trace).length <=
      2 * trace.length := by
  induction trace with
  | nil => simp [packedReviewerLogicalTracePhysicalTrace]
  | cons event rest ih =>
      have hevent :=
        packedReviewerLogicalEventPhysicalTrace_length_le_two shape event
      simp only [packedReviewerLogicalTracePhysicalTrace] at ih
      simp only [packedReviewerLogicalTracePhysicalTrace, List.flatMap_cons,
        List.length_append, List.length_cons]
      omega

/-- The independently expanded expected trace has the derived literal cap. -/
theorem packedReviewerExpectedPhysicalTrace_length_le_427
    (shape : CartesianShape) (left right : Nat) :
    (packedReviewerExpectedPhysicalTrace shape left right).length <= 427 := by
  by_cases hvalid : left < right ∧ right <= shape.size
  · have hlogical :=
      packedReviewerDriveLogical_trace_length_le
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) 210
        (packedReviewerWholeStart shape.size left right)
    have hwhole :=
      packedReviewerLogicalTracePhysicalTrace_length_le shape
        (packedReviewerDriveLogical
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) 210
          (packedReviewerWholeStart shape.size left right)).trace
    have hprelude :=
      packedReviewerSparsePreludeProbePlan_length_le_six shape.size
        (longCount shape)
    have hheader : (packedReviewerHeaderPhysicalTrace shape).length = 1 := by
      simp [packedReviewerHeaderPhysicalTrace,
        packedReviewerPhysicalEvents_length]
    have hpreludeTrace :
        (packedReviewerSparsePreludePhysicalTrace shape).length <= 6 := by
      simpa [packedReviewerSparsePreludePhysicalTrace,
        packedReviewerSparsePreludeProbePlan,
        packedReviewerPhysicalEvents_length] using hprelude
    rw [packedReviewerExpectedPhysicalTrace, if_pos hvalid,
      List.length_append, List.length_append, hheader]
    omega
  · simp [packedReviewerExpectedPhysicalTrace, hvalid]

/-- The 427 theorem is about the grouped actual run, not a stored cap field. -/
theorem PackedReviewerRunGrouping.trace_length_le_427
    {shape : CartesianShape} {left right : Nat}
    (grouping : PackedReviewerRunGrouping shape left right) :
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).trace.length <= 427 := by
  rw [grouping.trace_eq]
  exact packedReviewerExpectedPhysicalTrace_length_le_427 shape left right

/-!
The final request-operand theorems and `PackedReviewerPublicRunCertificate`
are assembled in `ReviewerControllerStateProof` from this module's
independent run facts and the downstream canonical state invariant.
-/

end PackedCellProbe
end SuccinctFinal
end RMQ
