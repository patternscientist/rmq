import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerPhysicalRead
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerCloseRead
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerInteriorRead

/-!
# Closed arithmetic geometry for the reviewer controller

The proof-facing reviewer layout is deliberately described by the canonical
live-source list.  The physical controller cannot traverse that list: source
order is fixed program geometry, not query data.  This module gives the same
offsets as a closed match over source tags and gives the total access length as
the final prefix plus the decoded sparse-relative row count.

Only the drift theorems below mention the canonical source list.  Executable
plans use the closed definitions.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open Cartesian

/-! ## Closed access-prefix geometry -/

/-- Fixed prefix immediately before the sparse-rank superblock source. -/
def packedReviewerClosedSparseRankSuperPrefixLength
    (n longCount : Nat) : Nat :=
  packedSourceBitLength n longCount .finalRankSuperFalse +
    packedSourceBitLength n longCount .finalRankBlockFalse +
    packedSourceBitLength n longCount .selectSuperBaseOccurrence +
    packedSourceBitLength n longCount .selectSuperBaseWordIndex +
    packedSourceBitLength n longCount .selectSuperRankBefore +
    packedSourceBitLength n longCount .selectSuperFirstOffset +
    packedSourceBitLength n longCount .selectLocalBaseOccurrence +
    packedSourceBitLength n longCount .selectLocalBaseWordIndex +
    packedSourceBitLength n longCount .selectLocalRankBefore +
    packedSourceBitLength n longCount .selectLocalFirstOffset +
    packedSourceBitLength n longCount .selectLongFlagRankSuperTrue +
    packedSourceBitLength n longCount .selectLongFlagRankBlockTrue +
    packedSourceBitLength n longCount .selectLongFlagBits +
    packedSourceBitLength n longCount .selectLongRelative

/--
Bit offset of a live access source inside the access half.  Every arm is a
fixed arithmetic expression over `n` and the decoded `longCount`; no source
registry is constructed or traversed.
-/
def packedReviewerClosedAccessOffset (n longCount : Nat) :
    ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat
  | .finalRankSuperFalse => 0
  | .finalRankBlockFalse =>
      packedSourceBitLength n longCount .finalRankSuperFalse
  | .selectSuperBaseOccurrence =>
      packedSourceBitLength n longCount .finalRankSuperFalse +
        packedSourceBitLength n longCount .finalRankBlockFalse
  | .selectSuperBaseWordIndex =>
      packedSourceBitLength n longCount .finalRankSuperFalse +
        packedSourceBitLength n longCount .finalRankBlockFalse +
        packedSourceBitLength n longCount .selectSuperBaseOccurrence
  | .selectSuperRankBefore =>
      packedSourceBitLength n longCount .finalRankSuperFalse +
        packedSourceBitLength n longCount .finalRankBlockFalse +
        packedSourceBitLength n longCount .selectSuperBaseOccurrence +
        packedSourceBitLength n longCount .selectSuperBaseWordIndex
  | .selectSuperFirstOffset =>
      packedSourceBitLength n longCount .finalRankSuperFalse +
        packedSourceBitLength n longCount .finalRankBlockFalse +
        packedSourceBitLength n longCount .selectSuperBaseOccurrence +
        packedSourceBitLength n longCount .selectSuperBaseWordIndex +
        packedSourceBitLength n longCount .selectSuperRankBefore
  | .selectLocalBaseOccurrence =>
      packedSourceBitLength n longCount .finalRankSuperFalse +
        packedSourceBitLength n longCount .finalRankBlockFalse +
        packedSourceBitLength n longCount .selectSuperBaseOccurrence +
        packedSourceBitLength n longCount .selectSuperBaseWordIndex +
        packedSourceBitLength n longCount .selectSuperRankBefore +
        packedSourceBitLength n longCount .selectSuperFirstOffset
  | .selectLocalBaseWordIndex =>
      packedSourceBitLength n longCount .finalRankSuperFalse +
        packedSourceBitLength n longCount .finalRankBlockFalse +
        packedSourceBitLength n longCount .selectSuperBaseOccurrence +
        packedSourceBitLength n longCount .selectSuperBaseWordIndex +
        packedSourceBitLength n longCount .selectSuperRankBefore +
        packedSourceBitLength n longCount .selectSuperFirstOffset +
        packedSourceBitLength n longCount .selectLocalBaseOccurrence
  | .selectLocalRankBefore =>
      packedSourceBitLength n longCount .finalRankSuperFalse +
        packedSourceBitLength n longCount .finalRankBlockFalse +
        packedSourceBitLength n longCount .selectSuperBaseOccurrence +
        packedSourceBitLength n longCount .selectSuperBaseWordIndex +
        packedSourceBitLength n longCount .selectSuperRankBefore +
        packedSourceBitLength n longCount .selectSuperFirstOffset +
        packedSourceBitLength n longCount .selectLocalBaseOccurrence +
        packedSourceBitLength n longCount .selectLocalBaseWordIndex
  | .selectLocalFirstOffset =>
      packedSourceBitLength n longCount .finalRankSuperFalse +
        packedSourceBitLength n longCount .finalRankBlockFalse +
        packedSourceBitLength n longCount .selectSuperBaseOccurrence +
        packedSourceBitLength n longCount .selectSuperBaseWordIndex +
        packedSourceBitLength n longCount .selectSuperRankBefore +
        packedSourceBitLength n longCount .selectSuperFirstOffset +
        packedSourceBitLength n longCount .selectLocalBaseOccurrence +
        packedSourceBitLength n longCount .selectLocalBaseWordIndex +
        packedSourceBitLength n longCount .selectLocalRankBefore
  | .selectLongFlagRankSuperTrue =>
      packedSourceBitLength n longCount .finalRankSuperFalse +
        packedSourceBitLength n longCount .finalRankBlockFalse +
        packedSourceBitLength n longCount .selectSuperBaseOccurrence +
        packedSourceBitLength n longCount .selectSuperBaseWordIndex +
        packedSourceBitLength n longCount .selectSuperRankBefore +
        packedSourceBitLength n longCount .selectSuperFirstOffset +
        packedSourceBitLength n longCount .selectLocalBaseOccurrence +
        packedSourceBitLength n longCount .selectLocalBaseWordIndex +
        packedSourceBitLength n longCount .selectLocalRankBefore +
        packedSourceBitLength n longCount .selectLocalFirstOffset
  | .selectLongFlagRankBlockTrue =>
      packedSourceBitLength n longCount .finalRankSuperFalse +
        packedSourceBitLength n longCount .finalRankBlockFalse +
        packedSourceBitLength n longCount .selectSuperBaseOccurrence +
        packedSourceBitLength n longCount .selectSuperBaseWordIndex +
        packedSourceBitLength n longCount .selectSuperRankBefore +
        packedSourceBitLength n longCount .selectSuperFirstOffset +
        packedSourceBitLength n longCount .selectLocalBaseOccurrence +
        packedSourceBitLength n longCount .selectLocalBaseWordIndex +
        packedSourceBitLength n longCount .selectLocalRankBefore +
        packedSourceBitLength n longCount .selectLocalFirstOffset +
        packedSourceBitLength n longCount .selectLongFlagRankSuperTrue
  | .selectLongFlagBits =>
      packedSourceBitLength n longCount .finalRankSuperFalse +
        packedSourceBitLength n longCount .finalRankBlockFalse +
        packedSourceBitLength n longCount .selectSuperBaseOccurrence +
        packedSourceBitLength n longCount .selectSuperBaseWordIndex +
        packedSourceBitLength n longCount .selectSuperRankBefore +
        packedSourceBitLength n longCount .selectSuperFirstOffset +
        packedSourceBitLength n longCount .selectLocalBaseOccurrence +
        packedSourceBitLength n longCount .selectLocalBaseWordIndex +
        packedSourceBitLength n longCount .selectLocalRankBefore +
        packedSourceBitLength n longCount .selectLocalFirstOffset +
        packedSourceBitLength n longCount .selectLongFlagRankSuperTrue +
        packedSourceBitLength n longCount .selectLongFlagRankBlockTrue
  | .selectLongRelative =>
      packedSourceBitLength n longCount .finalRankSuperFalse +
        packedSourceBitLength n longCount .finalRankBlockFalse +
        packedSourceBitLength n longCount .selectSuperBaseOccurrence +
        packedSourceBitLength n longCount .selectSuperBaseWordIndex +
        packedSourceBitLength n longCount .selectSuperRankBefore +
        packedSourceBitLength n longCount .selectSuperFirstOffset +
        packedSourceBitLength n longCount .selectLocalBaseOccurrence +
        packedSourceBitLength n longCount .selectLocalBaseWordIndex +
        packedSourceBitLength n longCount .selectLocalRankBefore +
        packedSourceBitLength n longCount .selectLocalFirstOffset +
        packedSourceBitLength n longCount .selectLongFlagRankSuperTrue +
        packedSourceBitLength n longCount .selectLongFlagRankBlockTrue +
        packedSourceBitLength n longCount .selectLongFlagBits
  | .selectSparseRankSuperTrue =>
      packedReviewerClosedSparseRankSuperPrefixLength n longCount
  | .selectSparseRankBlockTrue =>
      packedReviewerClosedSparseRankSuperPrefixLength n longCount +
        packedSourceBitLength n longCount .selectSparseRankSuperTrue
  | .selectSparseFlagBits =>
      packedReviewerClosedSparseRankSuperPrefixLength n longCount +
        packedSourceBitLength n longCount .selectSparseRankSuperTrue +
        packedSourceBitLength n longCount .selectSparseRankBlockTrue
  | .selectSparseRelative =>
      packedReviewerClosedSparseRankSuperPrefixLength n longCount +
        packedSourceBitLength n longCount .selectSparseRankSuperTrue +
        packedSourceBitLength n longCount .selectSparseRankBlockTrue +
        packedSourceBitLength n longCount .selectSparseFlagBits
  | _ => 0

/-- Whole-payload offset of a live access source. -/
def packedReviewerClosedSourceOffset (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) : Nat :=
  2 * n + packedReviewerClosedAccessOffset n longCount source

/--
Exact closed length of all eighteen live access sources.  The first seventeen
sources form the final fixed prefix; the last source has exactly
`sparseCount * packedLocalWidth n` bits.
-/
def packedReviewerClosedAccessLength
    (n longCount sparseCount : Nat) : Nat :=
  packedReviewerClosedAccessOffset n longCount .selectSparseRelative +
    sparseCount * packedLocalWidth n

/-- Closed total length of the counted reviewer payload. -/
def packedReviewerClosedPayloadLength
    (n longCount sparseCount : Nat) : Nat :=
  2 * n + packedReviewerClosedAccessLength n longCount sparseCount +
    SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n +
    SuccinctClose.bpFringeTableOverhead n +
    SuccinctClose.bpChunkSelectTableOverhead n

set_option maxHeartbeats 1000000 in
/-- Proof-side drift guard for every one of the eighteen live sources. -/
theorem packedReviewerClosedAccessOffset_eq
    (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hsource :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources) :
    packedReviewerClosedAccessOffset n longCount source =
      packedReviewerAccessOffset n longCount source := by
  cases source <;>
    simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources] at hsource
  all_goals
    simp [packedReviewerClosedAccessOffset, packedReviewerAccessOffset,
      concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources,
      packedReviewerClosedSparseRankSuperPrefixLength, Nat.add_assoc]

/-- Whole-payload source offsets have the same proof-side meaning. -/
theorem packedReviewerClosedSourceOffset_eq
    (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hsource :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources) :
    packedReviewerClosedSourceOffset n longCount source =
      packedReviewerSourceOffset n longCount source := by
  unfold packedReviewerClosedSourceOffset packedReviewerSourceOffset
  rw [packedReviewerClosedAccessOffset_eq n longCount source hsource]

set_option maxHeartbeats 1000000 in
/-- The closed scalar total is exactly the former list-derived total. -/
theorem packedReviewerClosedAccessLength_eq
    (n longCount sparseCount : Nat) :
    packedReviewerClosedAccessLength n longCount sparseCount =
      packedReviewerAccessLength n longCount sparseCount := by
  simp [packedReviewerClosedAccessLength, packedReviewerClosedAccessOffset,
    packedReviewerClosedSparseRankSuperPrefixLength,
    packedReviewerAccessLength,
    concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources,
    packedReviewerSourceBitLength, Nat.add_assoc]

/-- The closed total payload length is unchanged. -/
theorem packedReviewerClosedPayloadLength_eq
    (n longCount sparseCount : Nat) :
    packedReviewerClosedPayloadLength n longCount sparseCount =
      packedReviewerPayloadLength n longCount sparseCount := by
  unfold packedReviewerClosedPayloadLength packedReviewerPayloadLength
  rw [packedReviewerClosedAccessLength_eq]

/-! ## Closed addresses for every executed logical segment -/

/-- Closed bit address for one live access-source word. -/
def packedReviewerClosedStridedBitAddress (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index stride : Nat) : Nat :=
  packedReviewerCellWidth n +
    packedReviewerClosedSourceOffset n longCount source + index * stride

/-- Closed one-or-two-cell plan for one live access-source word. -/
def packedReviewerClosedSourceReadPlan
    (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index : Nat) : List Nat :=
  packedReviewerProbePlan n
    (packedReviewerClosedStridedBitAddress n longCount source index
      (packedSourceStride n source))
    (packedReviewerSourceReadWidth n longCount sparseCount source index)

/-- Closed offset of the segment-20 interior directory. -/
def packedReviewerClosedInteriorOffset
    (n longCount sparseCount : Nat) : Nat :=
  2 * n + packedReviewerClosedAccessLength n longCount sparseCount

/-- Closed bit address for one classified ragged interior word. -/
def packedReviewerClosedInteriorBitAddress
    (n longCount sparseCount : Nat)
    (location : PackedReviewerInteriorLocation) : Nat :=
  packedReviewerCellWidth n +
    packedReviewerClosedInteriorOffset n longCount sparseCount +
    location.componentBitPrefix + location.bitOffset

/-- Closed plan for one classified ragged interior word. -/
def packedReviewerClosedInteriorLocationPlan
    (n longCount sparseCount : Nat)
    (location : PackedReviewerInteriorLocation) : List Nat :=
  packedReviewerProbePlan n
    (packedReviewerClosedInteriorBitAddress n longCount sparseCount location)
    location.readWidth

/-- Closed segment-20 plan; an absent classifier emits no read. -/
def packedReviewerClosedInteriorReadPlan
    (n longCount sparseCount index : Nat) : List Nat :=
  match packedReviewerInteriorClassify n index with
  | none => []
  | some location =>
      packedReviewerClosedInteriorLocationPlan n longCount sparseCount location

/-- Closed offset of the segment-21 fringe table. -/
def packedReviewerClosedFringeOffset
    (n longCount sparseCount : Nat) : Nat :=
  packedReviewerClosedInteriorOffset n longCount sparseCount +
    SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n

/-- Closed offset of the segment-22 select-chunk table. -/
def packedReviewerClosedSelectChunkOffset
    (n longCount sparseCount : Nat) : Nat :=
  packedReviewerClosedFringeOffset n longCount sparseCount +
    SuccinctClose.bpFringeTableOverhead n

/-- Closed segment-21 bit address. -/
def packedReviewerClosedFringeAddress
    (n longCount sparseCount index : Nat) : Nat :=
  packedReviewerCellWidth n +
    packedReviewerClosedFringeOffset n longCount sparseCount +
    index * packedReviewerFringeWidth n

/-- Closed segment-22 bit address. -/
def packedReviewerClosedSelectChunkAddress
    (n longCount sparseCount index : Nat) : Nat :=
  packedReviewerCellWidth n +
    packedReviewerClosedSelectChunkOffset n longCount sparseCount +
    index * packedReviewerSelectChunkWidth n

/-! ## Exact drift theorems for plans, widths, and decoders -/

theorem packedReviewerClosedStridedBitAddress_eq
    (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index stride : Nat)
    (hsource :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources) :
    packedReviewerClosedStridedBitAddress n longCount source index stride =
      packedReviewerStridedBitAddress n longCount source index stride := by
  unfold packedReviewerClosedStridedBitAddress
    packedReviewerStridedBitAddress
  rw [packedReviewerClosedSourceOffset_eq n longCount source hsource]

theorem packedReviewerClosedSourceReadPlan_eq
    (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index : Nat)
    (hsource :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources) :
    packedReviewerClosedSourceReadPlan n longCount sparseCount source index =
      packedReviewerSourceReadPlan n longCount sparseCount source index := by
  unfold packedReviewerClosedSourceReadPlan packedReviewerSourceReadPlan
  rw [packedReviewerClosedStridedBitAddress_eq n longCount source index
    (packedSourceStride n source) hsource]

theorem packedReviewerClosedInteriorOffset_eq
    (n longCount sparseCount : Nat) :
    packedReviewerClosedInteriorOffset n longCount sparseCount =
      packedReviewerInteriorPayloadOffset n longCount sparseCount := by
  unfold packedReviewerClosedInteriorOffset
    packedReviewerInteriorPayloadOffset
  rw [packedReviewerClosedAccessLength_eq]

theorem packedReviewerClosedInteriorBitAddress_eq
    (n longCount sparseCount : Nat)
    (location : PackedReviewerInteriorLocation) :
    packedReviewerClosedInteriorBitAddress n longCount sparseCount location =
      packedReviewerInteriorBitAddress n longCount sparseCount location := by
  unfold packedReviewerClosedInteriorBitAddress
    packedReviewerInteriorBitAddress
  rw [packedReviewerClosedInteriorOffset_eq]

theorem packedReviewerClosedInteriorLocationPlan_eq
    (n longCount sparseCount : Nat)
    (location : PackedReviewerInteriorLocation) :
    packedReviewerClosedInteriorLocationPlan n longCount sparseCount location =
      packedReviewerInteriorLocationPlan n longCount sparseCount location := by
  unfold packedReviewerClosedInteriorLocationPlan
    packedReviewerInteriorLocationPlan
  rw [packedReviewerClosedInteriorBitAddress_eq]

theorem packedReviewerClosedInteriorReadPlan_eq
    (n longCount sparseCount index : Nat) :
    packedReviewerClosedInteriorReadPlan n longCount sparseCount index =
      packedReviewerInteriorReadPlan n longCount sparseCount index := by
  cases hclassify : packedReviewerInteriorClassify n index with
  | none =>
      simp [packedReviewerClosedInteriorReadPlan,
        packedReviewerInteriorReadPlan, hclassify]
  | some location =>
      simp [packedReviewerClosedInteriorReadPlan,
        packedReviewerInteriorReadPlan, hclassify,
        packedReviewerClosedInteriorLocationPlan_eq]

theorem packedReviewerClosedFringeOffset_eq
    (n longCount sparseCount : Nat) :
    packedReviewerClosedFringeOffset n longCount sparseCount =
      packedReviewerFringeOffset n longCount sparseCount := by
  unfold packedReviewerClosedFringeOffset packedReviewerFringeOffset
    packedReviewerCloseOffset packedReviewerClosedInteriorOffset
  rw [packedReviewerClosedAccessLength_eq]

theorem packedReviewerClosedSelectChunkOffset_eq
    (n longCount sparseCount : Nat) :
    packedReviewerClosedSelectChunkOffset n longCount sparseCount =
      packedReviewerSelectChunkOffset n longCount sparseCount := by
  unfold packedReviewerClosedSelectChunkOffset
    packedReviewerSelectChunkOffset
  rw [packedReviewerClosedFringeOffset_eq]

theorem packedReviewerClosedFringeAddress_eq
    (n longCount sparseCount index : Nat) :
    packedReviewerClosedFringeAddress n longCount sparseCount index =
      packedReviewerFringeAddress n longCount sparseCount index := by
  unfold packedReviewerClosedFringeAddress packedReviewerFringeAddress
  rw [packedReviewerClosedFringeOffset_eq]

theorem packedReviewerClosedSelectChunkAddress_eq
    (n longCount sparseCount index : Nat) :
    packedReviewerClosedSelectChunkAddress n longCount sparseCount index =
      packedReviewerSelectChunkAddress n longCount sparseCount index := by
  unfold packedReviewerClosedSelectChunkAddress
    packedReviewerSelectChunkAddress
  rw [packedReviewerClosedSelectChunkOffset_eq]

end PackedCellProbe
end SuccinctFinal
end RMQ
