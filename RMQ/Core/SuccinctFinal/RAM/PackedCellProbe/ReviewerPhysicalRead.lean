import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerSourceAddress

/-!
# The physical read over the consumed payload

`PhysicalRead.lean` answers a logical word read by probing `packedMemory`. This
module does the same over `packedReviewerMemory`, joining the three pieces the
re-target has now built: the address surface (`ReviewerSourceAddress`), the width
bound (`packedSourceStride_le_reviewerCellWidth`), and the conditional probe plan
(`ReviewerProbe`).

## What is reused rather than rebuilt

The per-source stride is reused. The reviewer word count and bit length are exact:
their sparse-relative arm uses the recovered `sparseCount` rather than the flat
layout's size-only capacity.

## The direction of the theorem

`packedReviewerSourceRead` rejects an index past the actual sparse-relative count,
so the former capacity gap is absent. Every successful logical read, including a
sparse-relative read, lowers exactly.

## Scope

All eighteen live access sources. The close half's segments are not
read here: they are not in the access list, so they have no
`packedReviewerAccessOffset`, and they are reached instead through
`packedReviewerPayload_interiorSlice`. Their read is a separate obligation.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open Cartesian
open SuccinctSpace

/-! ## The payload window inside the allocation -/

/--
**A payload range, read off the padded bit string.** Past the header cell, the
allocation is the consumed payload followed by counted padding, so any range inside
the payload is the same range of the padded string shifted by one cell.
-/
theorem packedReviewerPayloadSlice
    (shape : CartesianShape)
    (j width : Nat)
    (hfit : j + width <= packedReviewerPayloadLength shape.size (longCount shape)
      (packedReviewerSparseCount shape)) :
    ((packedReviewerPaddedBits shape).drop
        (packedReviewerCellWidth shape.size + j)).take width =
      ((packedReviewerPayloadBits shape).drop j).take width := by
  have hhdr := packedReviewerHeaderBits_length shape
  have hpay := packedReviewerPayloadBits_length_eq shape
  have hjle : j <= (packedReviewerPayloadBits shape).length := by omega
  have hwle : width <= ((packedReviewerPayloadBits shape).drop j).length := by
    rw [List.length_drop]
    omega
  unfold packedReviewerPaddedBits packedReviewerSerializedBits
  rw [List.append_assoc, ← List.drop_drop]
  rw [← hhdr]
  rw [List.drop_left]
  rw [List.drop_append_of_le_length hjle, List.take_append_of_le_length hwle]

/-- The whole window of a source sits inside the consumed payload. -/
theorem packedReviewerSourceOffset_fits
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources) :
    packedReviewerSourceOffset shape.size (longCount shape) source +
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length <=
      packedReviewerPayloadLength shape.size (longCount shape)
        (packedReviewerSparseCount shape) := by
  have hfits := packedReviewerAccessOffset_fits shape source hmem
  have hlen := packedReviewerAccessLength_eq shape
  unfold packedReviewerSourceOffset packedReviewerPayloadLength
  omega

/-! ## The read -/

/-- The exact number of logical words in a reviewer access source. -/
def packedReviewerSourceWordCount (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) : Nat :=
  if source =
      ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative then
    sparseCount
  else
    packedSourceWordCount n longCount source

/-- The exact bit width of one indexed reviewer-source read. -/
def packedReviewerSourceReadWidth (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) : Nat :=
  min (packedSourceStride n source)
    (packedReviewerSourceBitLength n longCount sparseCount source -
      index * packedSourceStride n source)

theorem packedReviewerSourceReadWidth_le_stride
    (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    packedReviewerSourceReadWidth n longCount sparseCount source index <=
      packedSourceStride n source := by
  unfold packedReviewerSourceReadWidth
  omega

/-- The bit address of one logical word inside the reviewer allocation. -/
def packedReviewerStridedBitAddress (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index stride : Nat) : Nat :=
  packedReviewerCellWidth n + packedReviewerSourceOffset n longCount source +
    index * stride

/-- The physical probe plan of one logical word read. -/
def packedReviewerSourceReadPlan (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    List Nat :=
  packedReviewerProbePlan n
    (packedReviewerStridedBitAddress n longCount source index
      (packedSourceStride n source))
    (packedReviewerSourceReadWidth n longCount sparseCount source index)

/-- One logical word read, answered by probing the reviewer memory. -/
def packedReviewerSourceRead (n longCount sparseCount : Nat)
    (memory : List (List Bool))
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    Option (List Bool) :=
  if index < packedReviewerSourceWordCount n longCount sparseCount source then
    (packedFetch memory
      (packedReviewerSourceReadPlan n longCount sparseCount source index)).map
      (packedReviewerDecodeSpan n
        (packedReviewerStridedBitAddress n longCount source index
          (packedSourceStride n source))
        (packedReviewerSourceReadWidth n longCount sparseCount source index))
  else
    none

/-- A logical word read never issues more than two physical probes. -/
theorem packedReviewerSourceReadPlan_length_le_two (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    (packedReviewerSourceReadPlan n longCount sparseCount source index).length <= 2 :=
  packedReviewerProbeCount_le_two _ _ _

/-- A successful logical source word lies inside the exact reviewer word count. -/
theorem packedReviewerSourceWordCount_of_some
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    {index : Nat} {word : List Bool}
    (hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? =
        some word) :
    index < packedReviewerSourceWordCount shape.size (longCount shape)
      (packedReviewerSparseCount shape) source := by
  by_cases hsparse :
      source =
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative
  · subst source
    have hget' :
        (GenericSelect.sparseExceptionRelativeTable shape.bpCode
          false).store.words[index]? = some word := hget
    rw [packedFixedWidthTable_getElem?] at hget'
    by_cases hi : index < packedReviewerSparseCount shape
    · simpa [packedReviewerSourceWordCount] using hi
    · have hle :
          (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false).length <=
            index := by
        simpa [packedReviewerSparseCount] using Nat.le_of_not_gt hi
      rw [packedWordSlice_of_le hle] at hget'
      exact absurd hget' (by simp)
  · have hslice := packedSourceWords_of_some shape source hget
    have hlt :
        index < packedSourceWordCount shape.size (longCount shape) source := by
      by_cases h :
          index < packedSourceWordCount shape.size (longCount shape) source
      · exact h
      · rw [packedWordSlice_of_le (by omega)] at hslice
        exact absurd hslice (by simp)
    simpa [packedReviewerSourceWordCount, hsparse] using hlt

/-! ## The lowering -/

set_option maxHeartbeats 1000000 in
/--
**Every successful logical word read of a live access source lowers to the physical
probe plan over the consumed payload.** The fetched cells decode to exactly the word
the source's word array returns.
-/
theorem packedReviewerSourceRead_of_some
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    {index : Nat} {word : List Bool}
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources)
    (hcounted : PackedSourceCounted shape.size source)
    (hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? =
        some word) :
    packedReviewerSourceRead shape.size (longCount shape)
        (packedReviewerSparseCount shape)
        (packedReviewerMemory shape) source index =
      some word := by
  have hslice := packedSourceWords_of_some shape source hget
  have hltCap :
      index < packedSourceWordCount shape.size (longCount shape) source := by
    by_cases h : index < packedSourceWordCount shape.size (longCount shape) source
    · exact h
    · rw [packedWordSlice_of_le (by omega)] at hslice
      exact absurd hslice (by simp)
  have hword :
      word =
        (((concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).drop
            (index * packedSourceStride shape.size source)).take
          (packedSourceStride shape.size source)) := by
    rw [packedWordSlice_of_lt hltCap] at hslice
    exact (Option.some.inj hslice).symm
  have hlt := packedReviewerSourceWordCount_of_some shape source hget
  have hsourceLen := packedReviewerSourceBitLength_eq shape source
  have hwindow :
      packedReviewerSourceReadWidth shape.size (longCount shape)
          (packedReviewerSparseCount shape) source index =
        min (packedSourceStride shape.size source)
          ((concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length -
            index * packedSourceStride shape.size source) := by
    unfold packedReviewerSourceReadWidth
    rw [← hsourceLen]
  have hsrc := packedReviewerPayload_accessSlice shape source hmem
  have hcontain := packedReviewerSourceOffset_fits shape source hmem
  have hwidth :=
    packedSourceStride_le_reviewerCellWidth shape.size source hcounted
  by_cases hzero :
      packedReviewerSourceReadWidth shape.size (longCount shape)
        (packedReviewerSparseCount shape) source index = 0
  · -- A zero-width read issues no probe at all, and the stored word is empty for
    -- exactly the reason the width is zero.
    have hempty : word = [] := by
      rw [hword]
      rw [hzero] at hwindow
      by_cases hstrideZero : packedSourceStride shape.size source = 0
      · rw [hstrideZero]
        simp
      · have hpast :
            (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length <=
              index * packedSourceStride shape.size source := by
          omega
        rw [List.drop_eq_nil_of_le hpast]
        simp
    have hplan :
        packedReviewerProbePlan shape.size
            (packedReviewerStridedBitAddress shape.size (longCount shape) source
              index (packedSourceStride shape.size source)) 0 = [] := by
      simp [packedReviewerProbePlan]
    unfold packedReviewerSourceRead packedReviewerSourceReadPlan
    rw [if_pos hlt, hzero, hplan, hempty]
    simp [packedFetch, packedReviewerDecodeSpan]
  · -- A positive-width read is contained in the source payload, hence in the
    -- consumed payload, hence in the allocated cells.
    have hpos :
        0 < packedReviewerSourceReadWidth shape.size (longCount shape)
          (packedReviewerSparseCount shape) source index := by
      omega
    have hminle :
        packedReviewerSourceReadWidth shape.size (longCount shape)
            (packedReviewerSparseCount shape) source index <=
          (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length -
            index * packedSourceStride shape.size source := by
      rw [hwindow]
      omega
    have hinside :
        index * packedSourceStride shape.size source <
          (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length := by
      omega
    have hfit2 :
        packedReviewerSourceOffset shape.size (longCount shape) source +
            index * packedSourceStride shape.size source +
            packedReviewerSourceReadWidth shape.size (longCount shape)
              (packedReviewerSparseCount shape) source index <=
          packedReviewerPayloadLength shape.size (longCount shape)
            (packedReviewerSparseCount shape) := by
      omega
    have hserial :=
      packedReviewerSerialized_le_allocated shape.size (longCount shape)
        (packedReviewerSparseCount shape)
    have haddr :
        packedReviewerStridedBitAddress shape.size (longCount shape) source index
            (packedSourceStride shape.size source) =
          packedReviewerCellWidth shape.size +
            (packedReviewerSourceOffset shape.size (longCount shape) source +
              index * packedSourceStride shape.size source) := by
      unfold packedReviewerStridedBitAddress
      omega
    have hfitalloc :
        packedReviewerStridedBitAddress shape.size (longCount shape) source index
            (packedSourceStride shape.size source) +
            packedReviewerSourceReadWidth shape.size (longCount shape)
              (packedReviewerSparseCount shape) source index <=
          packedReviewerAllocatedBits shape.size (longCount shape)
            (packedReviewerSparseCount shape) := by
      rw [haddr]
      omega
    have hwle :
        packedReviewerSourceReadWidth shape.size (longCount shape)
            (packedReviewerSparseCount shape) source index <=
          packedReviewerCellWidth shape.size :=
      Nat.le_trans
        (packedReviewerSourceReadWidth_le_stride shape.size (longCount shape)
          (packedReviewerSparseCount shape) source index)
        hwidth
    have hdecode := packedReviewerProbePlan_decode shape hwle hfitalloc
    have hpayslice :=
      packedReviewerPayloadSlice shape
        (packedReviewerSourceOffset shape.size (longCount shape) source +
          index * packedSourceStride shape.size source)
        (packedReviewerSourceReadWidth shape.size (longCount shape)
          (packedReviewerSparseCount shape) source index) hfit2
    -- the consumed-payload window is the stored word
    have hchain :
        ((packedReviewerPayloadBits shape).drop
              (packedReviewerSourceOffset shape.size (longCount shape) source +
                index * packedSourceStride shape.size source)).take
            (packedReviewerSourceReadWidth shape.size (longCount shape)
              (packedReviewerSparseCount shape) source index) =
          word := by
      obtain ⟨L, hL⟩ :
          exists L,
            (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length =
              L :=
        ⟨_, rfl⟩
      rw [hL] at hsrc hwindow
      rw [hword, hwindow, ← hsrc, List.drop_take, List.drop_drop,
        List.take_take, Nat.add_comm]
    unfold packedReviewerSourceRead packedReviewerSourceReadPlan
    rw [if_pos hlt, hdecode, haddr, hpayslice, hchain]

/--
**A live source is backed option-for-option.**  This strengthens the successful
read lowering to the absent-word case needed by a request/reply controller:
an out-of-range logical word issues no physical probe and returns `none`.
-/
theorem packedReviewerSourceRead_eq_words
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources)
    (hcounted : PackedSourceCounted shape.size source)
    (index : Nat) :
    packedReviewerSourceRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape)
        source index =
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? := by
  cases hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? with
  | some word =>
      exact packedReviewerSourceRead_of_some shape source hmem hcounted hget
  | none =>
      have hnot :
          ¬ index < packedReviewerSourceWordCount shape.size (longCount shape)
            (packedReviewerSparseCount shape) source := by
        by_cases hsparse :
            source =
              ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative
        · subst source
          intro hlt
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
              (source !=
                ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative) =
                true := by
            simp [hsparse]
          have hle := packedSourceWords_of_none shape source hsparse' hget
          simpa [packedReviewerSourceWordCount, hsparse] using
            (Nat.not_lt_of_ge hle)
      unfold packedReviewerSourceRead
      rw [if_neg hnot]

end PackedCellProbe

end SuccinctFinal

end RMQ
