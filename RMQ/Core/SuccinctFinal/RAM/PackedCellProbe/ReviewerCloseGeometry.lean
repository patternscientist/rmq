import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerSpace

/-!
# Word geometry for the consumed payload's close half

Step four of the `DD-20260804-038` re-target, begun. The executed store's three
close segments are `20` (interior component), `21` (fringe chunk table) and `22`
(select chunk table), by `packedReviewerPayload_backs_executedCloseSegments`.

## Segments 21 and 22 are immediate

Both chunk tables are `FixedWidthNatTable`s, so `packedFixedWidthTable_getElem?`
-- the generic lemma already carrying the eighteen live access sources -- applies
unchanged. Two one-line proofs.

## Segment 20 is not, and the reason is structural

The interior component store is **not** one uniform word grid over the interior
directory's payload, so no single `packedWordSlice` statement can describe it.

It is a `BoundedPayloadWordStore` assembled by nested `append` from eight
component machine stores: the summary's four columns, then the local, global,
local-level and global-level tables. Words are laid end to end at *word*
granularity while payloads concatenate at *bit* granularity, so a component whose
payload does not fill its last word leaves a ragged edge, and the next component's
first word does not begin at a multiple of the machine width.

There is a second, sharper reason, visible only in
`FixedWidthNatTable.machineStore`: its words are
`table.store.words.toList.flatMap (chunkPayloadWords wordSize)` -- each logical
entry is chunked **separately**. So even within one component the grid is uniform
only when the entry width divides, or fits inside, the machine word. Chunking the
component's payload as a whole would give different words.

What is established here is the pair of facts the piecewise geometry will be
stated against: the eight-way word split, and that the store flattens to exactly
the directory payload. The bits are all present and in order; only the word
boundaries are non-uniform.

## What this module does not establish

* No `packedWordSlice` statement for segment `20`. That needs eight per-component
  geometries plus the offset arithmetic of
  `canonicalRelativeRmmInteriorComponentOffsets`, and per the note above the
  per-component statements are not uniform-grid statements either.
* Nothing here lowers a close read to a cell probe.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-! ### Segment 21: the fringe chunk table -/

theorem packedReviewerFringeChunkWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21 i =
      packedWordSlice
        (SuccinctClose.bpFringeChunkTable
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload
        (SuccinctClose.bpFringeChunkEntries
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).length
        (SuccinctClose.bpFringeChunkEntryWidth
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)) i := by
  rw [packedExecutedStore_fringeChunkSegment shape i]
  exact packedFixedWidthTable_getElem? _ i

/-! ### Segment 22: the select chunk table -/

theorem packedReviewerSelectChunkWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 22 i =
      packedWordSlice
        (SuccinctClose.bpChunkSelectTable
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).payload
        (SuccinctClose.bpChunkSelectEntries
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).length
        (SuccinctClose.bpChunkSelectEntryWidth
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)) i := by
  rw [packedExecutedStore_selectChunkSegment shape i]
  exact packedFixedWidthTable_getElem? _ i

/-! ### The interior component store is not one uniform grid -/

/--
The interior component store's words are the eight component machine stores'
words laid end to end. Recorded as a definition-level fact so the piecewise
geometry has something to be stated against.
-/
theorem packedReviewerInteriorComponentWords_split (shape : CartesianShape) :
    (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words.toList =
      let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
      let summary := SuccinctClose.canonicalRelativeRmmSummaryTable shape
      (summary.baselineTable.machineStore hword).store.words.toList ++
        (summary.minRelTable.machineStore hword).store.words.toList ++
          (summary.maxRelTable.machineStore hword).store.words.toList ++
            (summary.argOffsetTable.machineStore hword).store.words.toList ++
              ((SuccinctClose.canonicalRelativeRmmInteriorLocalTable
                shape).table.machineStore hword).store.words.toList ++
                ((SuccinctClose.canonicalRelativeRmmInteriorGlobalTable
                  shape).table.machineStore hword).store.words.toList ++
                  ((SuccinctClose.canonicalRelativeRmmInteriorLocalLevelTable
                    shape).table.machineStore hword).store.words.toList ++
                    ((SuccinctClose.canonicalRelativeRmmInteriorGlobalLevelTable
                      shape).table.machineStore hword).store.words.toList :=
  SuccinctClose.canonicalRelativeRmmInteriorComponentStore_words_toList shape

/--
**The interior component store flattens to the interior directory's payload.**
The bits are all there and in order; what is not uniform is where the word
boundaries fall.
-/
theorem packedReviewerInteriorComponentStore_flattens (shape : CartesianShape) :
    SuccinctSpace.flattenPayloadWords
        (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
          shape).store.words.toList =
      (SuccinctClose.canonicalRelativeRmmSummaryTable shape).payload ++
        (SuccinctClose.canonicalRelativeRmmInteriorLocalTable shape).payload ++
          (SuccinctClose.canonicalRelativeRmmInteriorGlobalTable shape).payload ++
            (SuccinctClose.canonicalRelativeRmmInteriorLocalLevelTable
              shape).payload ++
              (SuccinctClose.canonicalRelativeRmmInteriorGlobalLevelTable
                shape).payload :=
  SuccinctClose.canonicalRelativeRmmInteriorComponentStore_flattens_payload shape

end PackedCellProbe
end SuccinctFinal
end RMQ
