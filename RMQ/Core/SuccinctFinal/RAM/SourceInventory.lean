import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.SuccinctFinal.RAM.ReviewerReachability

/-!
# Store-parametric logical-read-source inventory

This module delivers the logical-read-source half of the Stage F row
`EG-CP-F03` inventory clause on the supplied-store route.

The canonical route already carries a typed source universe
(`ReviewerSource`), a total logical-segment map
(`concreteBPNativeSuccinctRMQReviewerSegmentSource?`) and a canonical-route
coverage theorem.  Two things are added here.

First, a per-source row.  `reviewerSourceLogicalSegments` names, for each of
the 22 sources, the exact set of logical segments that resolve to it, and one
checked theorem per source pins that set for every natural-number segment, not
merely for a sampled block.

Second, coverage on the supplied-store route.
`storeParametricRead_hasListedSource` states that every logical read event the
supplied-store controller emits -- successful or failed -- resolves to a listed
source and lands in that source's row.  It is quantified over every Cartesian
shape, every supplied read store, and every endpoint pair, with no validity
side condition on the endpoints.  `unlistedSegment_never_read` is its
complement.

Completeness of the enumeration is carried by the elaborator rather than by
prose: the source universe is a closed inductive, the per-source rows are
joined by case analysis on it, and the segment side is settled by a match that
covers `0 .. 22` together with the residual `_ + 23`.  Adding a source
constructor without extending `reviewerSourceLogicalSegments` makes this file
fail to elaborate.

Tightness runs the other way and is conditional.  Under the canonical global
read-store family every listed source is successfully read
(`every_source_read_under_canonicalStores`); under an everywhere-unreadable
store family none is (`no_source_read_under_blankStores`).  The store family is
therefore an explicit parameter of the tightness predicate, and the two results
together show the condition is load-bearing rather than decorative.

## What this module does not establish

Stated so the coverage theorem is not read as more than it is.

* **Segment-to-LABEL, not segment-to-WORDS.**  Every result here pins which
  `ReviewerSource` a logical segment resolves to.  None proves that the store
  row at that segment equals `ReviewerSourceWords shape <source>`.  Until that
  payload identity is discharged for all 23 rows, the source map is a naming
  convention over the segment space rather than a proved decomposition of the
  memory image, and the `{0, 19}` alias is an equality of labels rather than of
  returned words.
* **Geometry is out of scope.**  Row `EG-CP-F03` also covers offsets, lengths,
  branches, divisors and table selectors.  This module is the logical-read-source
  half only.  Note the geometry half has no closed inductive to case on, so its
  enumeration cannot borrow the completeness mechanism used here.
* **Tightness is store-family relative**, by construction: see
  `every_source_read_under_canonicalStores` against
  `no_source_read_under_blankStores`.
-/

namespace RMQ
namespace SuccinctFinal
namespace SourceInventory

/-! ## Per-source logical segment fibers -/

/-- The logical segments that resolve to each live source.  One row per
constructor of `ReviewerSource`; the shared BP-code source is the only row with
two segments, because logical segments `0` and `19` alias the same bit-word
region. -/
def reviewerSourceLogicalSegments : ReviewerSource -> List Nat
  | .sharedBPCode => [0, 19]
  | .finalRankSuperFalse => [17]
  | .finalRankBlockFalse => [18]
  | .selectSuperBaseOccurrence => [1]
  | .selectSuperBaseWordIndex => [2]
  | .selectSuperRankBefore => [3]
  | .selectSuperFirstOffset => [4]
  | .selectLocalBaseOccurrence => [5]
  | .selectLocalBaseWordIndex => [6]
  | .selectLocalRankBefore => [7]
  | .selectLocalFirstOffset => [8]
  | .selectLongFlagRankSuperTrue => [9]
  | .selectLongFlagRankBlockTrue => [10]
  | .selectLongFlagBits => [11]
  | .selectLongRelative => [12]
  | .selectSparseRankSuperTrue => [13]
  | .selectSparseRankBlockTrue => [14]
  | .selectSparseFlagBits => [15]
  | .selectSparseRelative => [16]
  | .canonicalClose => [20]
  | .fringeChunkTable => [21]
  | .selectChunkTable => [22]

theorem source_sharedBPCode_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.sharedBPCode ↔ (segment = 0 \/ segment = 19) := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_finalRankSuperFalse_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.finalRankSuperFalse ↔ segment = 17 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_finalRankBlockFalse_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.finalRankBlockFalse ↔ segment = 18 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectSuperBaseOccurrence_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectSuperBaseOccurrence ↔ segment = 1 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectSuperBaseWordIndex_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectSuperBaseWordIndex ↔ segment = 2 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectSuperRankBefore_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectSuperRankBefore ↔ segment = 3 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectSuperFirstOffset_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectSuperFirstOffset ↔ segment = 4 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectLocalBaseOccurrence_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectLocalBaseOccurrence ↔ segment = 5 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectLocalBaseWordIndex_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectLocalBaseWordIndex ↔ segment = 6 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectLocalRankBefore_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectLocalRankBefore ↔ segment = 7 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectLocalFirstOffset_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectLocalFirstOffset ↔ segment = 8 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectLongFlagRankSuperTrue_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectLongFlagRankSuperTrue ↔ segment = 9 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectLongFlagRankBlockTrue_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectLongFlagRankBlockTrue ↔ segment = 10 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectLongFlagBits_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectLongFlagBits ↔ segment = 11 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectLongRelative_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectLongRelative ↔ segment = 12 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectSparseRankSuperTrue_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectSparseRankSuperTrue ↔ segment = 13 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectSparseRankBlockTrue_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectSparseRankBlockTrue ↔ segment = 14 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectSparseFlagBits_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectSparseFlagBits ↔ segment = 15 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectSparseRelative_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectSparseRelative ↔ segment = 16 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_canonicalClose_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.canonicalClose ↔ segment = 20 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_fringeChunkTable_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.fringeChunkTable ↔ segment = 21 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

theorem source_selectChunkTable_segments (segment : Nat) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
        some ReviewerSource.selectChunkTable ↔ segment = 22 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      exact iff_of_false
        (by simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]) (by omega)

/-- The 22 per-source rows above, joined into one statement by case analysis on
the closed source inductive. -/
theorem segmentSource_iff_mem_logicalSegments
    (segment : Nat) (source : ReviewerSource) :
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source ↔
      segment ∈ reviewerSourceLogicalSegments source := by
  cases source
  · simpa [reviewerSourceLogicalSegments] using source_sharedBPCode_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_finalRankSuperFalse_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_finalRankBlockFalse_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectSuperBaseOccurrence_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectSuperBaseWordIndex_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectSuperRankBefore_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectSuperFirstOffset_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectLocalBaseOccurrence_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectLocalBaseWordIndex_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectLocalRankBefore_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectLocalFirstOffset_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectLongFlagRankSuperTrue_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectLongFlagRankBlockTrue_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectLongFlagBits_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectLongRelative_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectSparseRankSuperTrue_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectSparseRankBlockTrue_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectSparseFlagBits_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectSparseRelative_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_canonicalClose_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_fringeChunkTable_segments segment
  · simpa [reviewerSourceLogicalSegments] using
      source_selectChunkTable_segments segment

/-- The fibers partition the live logical segment block `0 .. 22`. -/
theorem logicalSegments_pairwise_disjoint
    {segment : Nat} {source other : ReviewerSource}
    (hsource : segment ∈ reviewerSourceLogicalSegments source)
    (hother : segment ∈ reviewerSourceLogicalSegments other) :
    source = other := by
  have h1 := (segmentSource_iff_mem_logicalSegments segment source).2 hsource
  have h2 := (segmentSource_iff_mem_logicalSegments segment other).2 hother
  exact Option.some.inj (h1.symm.trans h2)

theorem logicalSegments_lt_23
    {segment : Nat} {source : ReviewerSource}
    (hmem : segment ∈ reviewerSourceLogicalSegments source) : segment < 23 := by
  cases source <;>
    (revert hmem; simp [reviewerSourceLogicalSegments]; omega)

/-! ## Store-parametric coverage -/

/-- **Coverage.** Every logical read event emitted by the supplied-store
whole-query controller, successful or failed, at any shape, any supplied read
store, and any endpoint pair, carries a segment that resolves to a listed
source, and lies in that source's fiber. -/
theorem storeParametricRead_hasListedSource
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) {segment index : Nat} {word? : Option WordRAM.Word}
    (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape store left right).trace) :
    Exists fun source : ReviewerSource =>
      source ∈ concreteBPNativeSuccinctRMQReviewerPhysicalSources /\
      concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source /\
      segment ∈ reviewerSourceLogicalSegments source /\
      ReviewerSource.region source < 22 := by
  have hlt :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_read_segment_lt
      shape store left right hmem
  rcases (concreteBPNativeSuccinctRMQReviewerSegmentSource?_coverage segment).2 hlt
    with ⟨source, hsource⟩
  refine ⟨source, concreteBPNativeSuccinctRMQReviewerPhysicalSources_all source,
    hsource, (segmentSource_iff_mem_logicalSegments segment source).1 hsource, ?_⟩
  cases source <;> decide

/-- The listed source attributed to an emitted read is unique. -/
theorem storeParametricRead_source_unique
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) {segment index : Nat} {word? : Option WordRAM.Word}
    (_hmem : WordRAM.TraceEvent.readWord segment index word? ∈
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape store left right).trace)
    {source other : ReviewerSource}
    (hsource :
      concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source)
    (hother :
      concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some other) :
    source = other :=
  Option.some.inj (hsource.symm.trans hother)

/-- The union of the enumerated per-source fibers. -/
def reviewerInventorySegments : List Nat :=
  concreteBPNativeSuccinctRMQReviewerPhysicalSources.flatMap
    reviewerSourceLogicalSegments

/-- The union is exactly the 23 live logical segments, listed in source order:
the shared BP-code fiber `[0, 19]` first, then the remaining singletons. -/
theorem reviewerInventorySegments_literal :
    reviewerInventorySegments =
      [0, 19, 17, 18, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
        20, 21, 22] := rfl

theorem reviewerInventorySegments_length :
    reviewerInventorySegments.length = 23 := rfl

theorem reviewerInventorySegments_nodup : reviewerInventorySegments.Nodup := by
  decide

theorem mem_reviewerInventorySegments_iff (segment : Nat) :
    segment ∈ reviewerInventorySegments ↔ segment < 23 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => decide
  | _ + 23 =>
      refine iff_of_false ?_ (by omega)
      intro h
      rw [reviewerInventorySegments_literal] at h
      simp at h <;> omega

/-- Every emitted read of the supplied-store controller lands in the union of
the enumerated per-source fibers. -/
theorem storeParametricRead_segment_mem_inventory
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) {segment index : Nat} {word? : Option WordRAM.Word}
    (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape store left right).trace) :
    segment ∈ reviewerInventorySegments := by
  obtain ⟨source, hlisted, _hsource, hfiber, _hregion⟩ :=
    storeParametricRead_hasListedSource shape store left right hmem
  exact List.mem_flatMap.2 ⟨source, hlisted, hfiber⟩

/-- **Complement of coverage.** A segment outside the enumerated fibers is
never read by the supplied-store controller, at any shape, any supplied read
store, and any endpoint pair. -/
theorem unlistedSegment_never_read
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) {segment : Nat}
    (hout : segment ∉ reviewerInventorySegments) (index : Nat)
    (word? : Option WordRAM.Word) :
    WordRAM.TraceEvent.readWord segment index word? ∉
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape store left right).trace := by
  intro hmem
  exact hout
    (storeParametricRead_segment_mem_inventory shape store left right hmem)

/-! ## The canonical-store transfer, with its condition stated -/

/-- A source is successfully read by the supplied-store controller under a
given family of read stores. The family is an explicit parameter: every
transfer statement below names the family it holds for. -/
def SourceHasSuccessfulReadUnderStores (source : ReviewerSource)
    (stores : Cartesian.CartesianShape -> WordRAM.ReadStore) : Prop :=
  Exists fun xs : List Int =>
  Exists fun left : Nat =>
  Exists fun right : Nat =>
  Exists fun segment : Nat =>
  Exists fun index : Nat =>
  Exists fun word : WordRAM.Word =>
    RMQ.ValidRange xs left right /\
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source /\
    segment ∈ reviewerSourceLogicalSegments source /\
    WordRAM.TraceEvent.readWord segment index (some word) ∈
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (Cartesian.shape xs) (stores (Cartesian.shape xs)) left right).trace

/-- **Tightness, conditional on the canonical store family.** Every one of the
22 listed sources is successfully read by the supplied-store controller when
the supplied store is the canonical global read store of the queried shape. -/
theorem every_source_read_under_canonicalStores (source : ReviewerSource) :
    SourceHasSuccessfulReadUnderStores source
      concreteBPNativeSuccinctRMQGlobalReadStore := by
  obtain ⟨claim, hclaimSource, word, hocc⟩ :=
    concreteBPNativeSuccinctRMQReviewerSource_counted_successful_closed_valid_occurrence
      source (concreteBPNativeSuccinctRMQReviewerPhysicalSources_all source)
  obtain ⟨xs, left, right, globalPos, index, hvalid, hget, _rest⟩ := hocc
  refine ⟨xs, left, right, claim.segment, index, word, hvalid, hclaimSource,
    (segmentSource_iff_mem_logicalSegments claim.segment source).1 hclaimSource,
    ?_⟩
  rw [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore]
  exact List.mem_of_getElem? hget

/-- The everywhere-unreadable store family. -/
def blankReadStores : Cartesian.CartesianShape -> WordRAM.ReadStore :=
  fun _ => { readWord? := fun _ _ => none }

/-- **The condition is load-bearing.** Under the everywhere-unreadable store
family no listed source is successfully read, so the tightness statement above
cannot be restated for an arbitrary supplied store. -/
theorem no_source_read_under_blankStores (source : ReviewerSource) :
    ¬ SourceHasSuccessfulReadUnderStores source blankReadStores := by
  rintro ⟨xs, left, right, segment, index, word, _hvalid, _hsource, _hfiber, hmem⟩
  have hmatch :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_matchesReadStore
      (Cartesian.shape xs) (blankReadStores (Cartesian.shape xs)) left right _ hmem
  simp [WordRAM.TraceEvent.matchesReadStore, blankReadStores] at hmatch

/-! ## Capstone -/

/-- **The store-parametric logical-read-source inventory.**

Clause 1 (universe): the 22-constructor enumeration lists every value of the
source type, without repetition.
Clause 2 (per-source rows): each source's logical segment fiber is exactly the
listed one, for every natural-number segment.
Clause 3 (coverage): every logical read emitted by the supplied-store
controller -- successful or failed, at any shape, any supplied read store and
any endpoint pair -- resolves to a listed source and lies in that source's
fiber.
Clause 4 (complement): no read is emitted outside the enumerated fibers.
Clause 5 (tightness, conditioned): under the canonical global read store
family, every listed source is successfully read by the supplied-store
controller in some valid closed query. -/
theorem storeParametricSourceInventory :
    (forall source : ReviewerSource,
        source ∈ concreteBPNativeSuccinctRMQReviewerPhysicalSources) /\
    concreteBPNativeSuccinctRMQReviewerPhysicalSources.Nodup /\
    (forall (segment : Nat) (source : ReviewerSource),
        concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source ↔
          segment ∈ reviewerSourceLogicalSegments source) /\
    (forall (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
        (left right segment index : Nat) (word? : Option WordRAM.Word),
        WordRAM.TraceEvent.readWord segment index word? ∈
            (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
              shape store left right).trace ->
          Exists fun source : ReviewerSource =>
            source ∈ concreteBPNativeSuccinctRMQReviewerPhysicalSources /\
            concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
              some source /\
            segment ∈ reviewerSourceLogicalSegments source) /\
    (forall (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
        (left right segment index : Nat) (word? : Option WordRAM.Word),
        segment ∉ reviewerInventorySegments ->
          WordRAM.TraceEvent.readWord segment index word? ∉
            (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
              shape store left right).trace) /\
    (forall source : ReviewerSource,
        SourceHasSuccessfulReadUnderStores source
          concreteBPNativeSuccinctRMQGlobalReadStore) := by
  refine ⟨concreteBPNativeSuccinctRMQReviewerPhysicalSources_all,
    concreteBPNativeSuccinctRMQReviewerPhysicalSources_nodup,
    segmentSource_iff_mem_logicalSegments, ?_, ?_,
    every_source_read_under_canonicalStores⟩
  · intro shape store left right segment index word? hmem
    obtain ⟨source, hlisted, hsource, hfiber, _hregion⟩ :=
      storeParametricRead_hasListedSource shape store left right hmem
    exact ⟨source, hlisted, hsource, hfiber⟩
  · intro shape store left right segment index word? hout
    exact unlistedSegment_never_read shape store left right hout index word?

end SourceInventory
end SuccinctFinal
end RMQ
