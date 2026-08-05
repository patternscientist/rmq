import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerSourceAddress

/-!
# The physical read over the consumed payload

`PhysicalRead.lean` answers a logical word read by probing `packedMemory`. This
module does the same over `packedReviewerMemory`, joining the three pieces the
re-target has now built: the address surface (`ReviewerSourceAddress`), the width
bound (`packedSourceStride_le_reviewerCellWidth`), and the conditional probe plan
(`ReviewerProbe`).

## What is reused rather than rebuilt

The per-source *word geometry* -- `packedSourceStride`, `packedSourceWordCount`,
`packedSourceReadWidth` -- is not re-derived. Those are properties of a source's own
payload, not of the layout it is embedded in, so they are the same numbers over
either memory. Only the address is different, and only because the offset is.

## The direction of the theorem

`packedReviewerSourceRead_of_some` is an implication, not an equation, for the
reason recorded in `DD-20260804-022`: at an index between the sparse relative
table's actual entry count and its size-only capacity the packed read answers where
the store would have failed. Every **successful** logical read lowers exactly.

## Scope

Only the seventeen counted live access sources. The close half's segments are not
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
    (hstride : GenericSelect.localStride shape.bpCode.length = 1)
    (j width : Nat)
    (hfit : j + width <= packedReviewerPayloadLength shape.size (longCount shape)) :
    ((packedReviewerPaddedBits shape).drop
        (packedReviewerCellWidth shape.size + j)).take width =
      ((packedReviewerPayloadBits shape).drop j).take width := by
  have hhdr := packedReviewerHeaderBits_length shape
  have hpay := packedReviewerPayloadBits_length_eq shape hstride
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
    (hstride : GenericSelect.localStride shape.bpCode.length = 1)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources)
    (hne :
      source != ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative) :
    packedReviewerSourceOffset shape.size (longCount shape) source +
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length <=
      packedReviewerPayloadLength shape.size (longCount shape) := by
  have hfits := packedReviewerAccessOffset_fits shape source hmem hne
  have hlen := packedReviewerAccessLength_eq shape hstride
  unfold packedReviewerSourceOffset packedReviewerPayloadLength
  omega

/-! ## The read -/

/-- The bit address of one logical word inside the reviewer allocation. -/
def packedReviewerStridedBitAddress (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index stride : Nat) : Nat :=
  packedReviewerCellWidth n + packedReviewerSourceOffset n longCount source +
    index * stride

/-- The physical probe plan of one logical word read. -/
def packedReviewerSourceReadPlan (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    List Nat :=
  packedReviewerProbePlan n
    (packedReviewerStridedBitAddress n longCount source index
      (packedSourceStride n source))
    (packedSourceReadWidth n longCount source index)

/-- One logical word read, answered by probing the reviewer memory. -/
def packedReviewerSourceRead (n longCount : Nat) (memory : List (List Bool))
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    Option (List Bool) :=
  if index < packedSourceWordCount n longCount source then
    (packedFetch memory (packedReviewerSourceReadPlan n longCount source index)).map
      (packedReviewerDecodeSpan n
        (packedReviewerStridedBitAddress n longCount source index
          (packedSourceStride n source))
        (packedSourceReadWidth n longCount source index))
  else
    none

/-- A logical word read never issues more than two physical probes. -/
theorem packedReviewerSourceReadPlan_length_le_two (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    (packedReviewerSourceReadPlan n longCount source index).length <= 2 :=
  packedReviewerProbeCount_le_two _ _ _

/-! ## The lowering -/

set_option maxHeartbeats 1000000 in
/--
**Every successful logical word read of a live access source lowers to the physical
probe plan over the consumed payload.** The fetched cells decode to exactly the word
the source's word array returns.
-/
theorem packedReviewerSourceRead_of_some
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    {index : Nat} {word : List Bool}
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources)
    (hne :
      source != ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative)
    (hcounted : PackedSourceCounted shape.size source)
    (hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? =
        some word) :
    packedReviewerSourceRead shape.size (longCount shape)
        (packedReviewerMemory shape) source index =
      some word := by
  have hslice := packedSourceWords_of_some shape source hget
  have hlt :
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
    rw [packedWordSlice_of_lt hlt] at hslice
    exact (Option.some.inj hslice).symm
  have hwindow := packedSourceReadWidth_eq_window shape source hget
  have hsrc := packedReviewerPayload_accessSlice shape source hmem hne
  have hcontain := packedReviewerSourceOffset_fits shape hstride source hmem hne
  have hwidth :=
    packedSourceStride_le_reviewerCellWidth shape.size source hcounted
  by_cases hzero :
      packedSourceReadWidth shape.size (longCount shape) source index = 0
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
        0 < packedSourceReadWidth shape.size (longCount shape) source index := by
      omega
    have hminle :
        packedSourceReadWidth shape.size (longCount shape) source index <=
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
            packedSourceReadWidth shape.size (longCount shape) source index <=
          packedReviewerPayloadLength shape.size (longCount shape) := by
      omega
    have hserial :=
      packedReviewerSerialized_le_allocated shape.size (longCount shape)
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
            packedSourceReadWidth shape.size (longCount shape) source index <=
          packedReviewerAllocatedBits shape.size (longCount shape) := by
      rw [haddr]
      omega
    have hwle :
        packedSourceReadWidth shape.size (longCount shape) source index <=
          packedReviewerCellWidth shape.size :=
      Nat.le_trans
        (packedSourceReadWidth_le_stride shape.size (longCount shape) source index)
        hwidth
    have hdecode := packedReviewerProbePlan_decode shape hwle hfitalloc
    have hpayslice :=
      packedReviewerPayloadSlice shape hstride
        (packedReviewerSourceOffset shape.size (longCount shape) source +
          index * packedSourceStride shape.size source)
        (packedSourceReadWidth shape.size (longCount shape) source index) hfit2
    -- the consumed-payload window is the stored word
    have hchain :
        ((packedReviewerPayloadBits shape).drop
              (packedReviewerSourceOffset shape.size (longCount shape) source +
                index * packedSourceStride shape.size source)).take
            (packedSourceReadWidth shape.size (longCount shape) source index) =
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

end PackedCellProbe

end SuccinctFinal

end RMQ
