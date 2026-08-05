import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerInteriorWidths

/-!
# How many machine words a component holds, and the index bound that follows

`DD-20260804-052` kept `FG-09`'s in-range obligation explicit rather than
absorbing it into an `Option`, and `DD-20260804-053` left it outstanding for all
eight interior components. This module discharges it from the hypothesis a
lowering actually has.

```
packedMachineStoreWords_size            : wordCount = entries.length * chunksPerEntry
packedEntryIndex_lt_of_lt               : i < count * c  ->  i / c < count
packedInteriorComponentWord_of_lt       : the address theorem, from i < wordCount
packedInteriorComponentWord_of_lt_size  : the same, against the stored word count
```

A component occupies exactly one machine word per entry per chunk. So an index
below the word count names an entry that exists, and the `i / c < entries.length`
side condition follows by division rather than by assumption.

`packedMachineStoreWords_size` needs **no** width positivity, and the first draft
carried one until the linter flagged it unused. The count is
`entries.length * chunksPerEntry` unconditionally: at width zero every entry
chunks to the empty list and `chunksPerEntry` is zero, so both sides are zero. The
hypothesis was removed rather than left in place, on the same principle that
removed the spurious `hstride` from `packedReviewerMemory_header_cell` -- a
hypothesis a theorem does not need misstates what it depends on.

## What this module does not establish

* Nothing places a component's payload inside the consumed payload. That still
  needs `canonicalRelativeRmmInteriorComponentOffsets`, and until it exists
  segment `20` does not reach a cell.
* No lowering issues any of these reads.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian
open RMQ.SuccinctSpace

/-- Length of a flatMap whose blocks all have the same length. -/
theorem packedFlatMapUniform_length
    {alpha beta : Type} (f : alpha -> List beta) {c : Nat}
    (l : List alpha)
    (huniform : forall {x : alpha}, List.Mem x l -> (f x).length = c) :
    (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : (f a).length = c := huniform List.mem_cons_self
      have ht : forall {x : alpha}, List.Mem x t -> (f x).length = c := by
        intro x hx
        exact huniform (List.mem_cons_of_mem a hx)
      rw [List.flatMap_cons, List.length_append, ha, ih ht, List.length_cons,
        Nat.succ_mul]
      omega

/--
**How many machine words a table occupies**: one per entry per chunk, exactly.
This is the count `FG-09`'s in-range obligation is measured against.
-/
theorem packedMachineStoreWords_size
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width)
    (hword : 0 < wordSize) :
    (table.machineStore hword).store.words.toList.length =
      entries.length * packedChunkCount width wordSize := by
  have huniform :
      forall {w : List Bool}, List.Mem w table.store.words.toList ->
        (chunkPayloadWords wordSize w).length =
          packedChunkCount width wordSize := by
    intro w hmem
    rcases List.getElem?_of_mem hmem with ⟨j, hj⟩
    have hw : w.length = width :=
      table.word_length_of_get? (by simpa [Array.getElem?_toList] using hj)
    rw [chunkPayloadWords_length_eq_div_add_indicator hword w, hw]
    rfl
  show (table.store.words.toList.flatMap (chunkPayloadWords wordSize)).length = _
  rw [packedFlatMapUniform_length (chunkPayloadWords wordSize) _ huniform,
    packedFixedWidthTable_words_length table]

/-- An index below the word count names an entry that exists. -/
theorem packedEntryIndex_lt_of_lt
    {count c i : Nat} (hc : 0 < c) (hi : i < count * c) : i / c < count :=
  (Nat.div_lt_iff_lt_mul hc).2 hi

/--
**The form an interior component actually uses.** The caller supplies
`i < wordCount`, which is what a lowering has, rather than the derived
`i / c < entries.length`.
-/
theorem packedInteriorComponentWord_of_lt
    {entries : List Nat} {width : Nat}
    (shape : CartesianShape)
    (table : FixedWidthNatTable entries width)
    (hpos : 0 < width) (i : Nat)
    (hi : i < entries.length *
      packedChunkCount width (packedInteriorWordSize shape)) :
    (table.machineStore (packedInteriorWordSize_pos shape)).store.words[i]? =
      some ((table.payload.drop
          (packedEntryChunkBitOffset width (packedInteriorWordSize shape) i)).take
        (packedEntryChunkReadWidth width (packedInteriorWordSize shape) i)) :=
  packedInteriorComponentWord shape table hpos i
    (packedEntryIndex_lt_of_lt
      (packedChunkCount_pos (packedInteriorWordSize_pos shape) hpos) hi)

/-- The same bound stated against the component's own stored word count. -/
theorem packedInteriorComponentWord_of_lt_size
    {entries : List Nat} {width : Nat}
    (shape : CartesianShape)
    (table : FixedWidthNatTable entries width)
    (hpos : 0 < width) (i : Nat)
    (hi : i < (table.machineStore
      (packedInteriorWordSize_pos shape)).store.words.toList.length) :
    (table.machineStore (packedInteriorWordSize_pos shape)).store.words[i]? =
      some ((table.payload.drop
          (packedEntryChunkBitOffset width (packedInteriorWordSize shape) i)).take
        (packedEntryChunkReadWidth width (packedInteriorWordSize shape) i)) := by
  rw [packedMachineStoreWords_size table (packedInteriorWordSize_pos shape)] at hi
  exact packedInteriorComponentWord_of_lt shape table hpos i hi

end PackedCellProbe
end SuccinctFinal
end RMQ
