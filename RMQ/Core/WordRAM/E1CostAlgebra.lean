/-
# The E1 cost algebra: block-level charge bounds, and the vocabulary bridge in use

This module does two things that were structurally absent from the tree
before it, both of them prerequisites for REQ-E1-06's conjunct (c).

**1. It EXERCISES the `catCount`/`filter` bridge.**  `catCount_eq_filter_length`
(`E1Machine.lean`) is the connecting fact; a fact stated and never used is
worth nothing, so this module carries it across the one gap it was written
for.  Machine-level accounting -- `run_steps_eq_category_sum`,
`run_readLog_length_eq_memoryRead_count` -- speaks `catCount`.  Every
BLOCK-level cap in this development speaks
`(log.filter (· == c)).length`.  `interiorChunkFold_readLog_le_eight` below
composes a block cap written in the second vocabulary into a statement about
the MACHINE'S OWN RECEIPT, which is written in the first.

**2. It states per-block `catLog.length <= <numeral>` bounds.**  These are the
ADDENDS of REQ-E1-06's derived literal.  The summation over a whole query
belongs to whoever composes the whole-query program; this module supplies the
terms and nothing more, and says so.

## Two warnings this module is written to respect

**`<=`, not `=`, wherever a bound is the point.**  REQ-E1-06 conjunct (c)
demands an inequality.  `machineWordBits` unfolds to `Nat.log2`, which is
well-founded recursion the kernel cannot evaluate, so an EQUATION whose value
passes through it is not `rfl`-checkable.  None of the bounds here passes
through `machineWordBits` at all -- they are counts of instructions, not of
bits -- but they are stated as `<=` regardless, because that is the shape the
requirement asks for and the shape that composes by `omega`.

**The two `33`s are NOT the same numeral, and neither is either `8`.**  This
module deliberately proves nothing against `33`.  For the record, since the
campaign shorthand "caps 33/8/8" conflates them:

* the FRINGE-WINDOW chunk-read cap, which lives INSIDE
  `endpointFringe = 4 + 33 = 37` (`ChargedFringeChunks.lean:1624-1687`);
* the WHOLE-INTERIOR-DIRECTORY read cap,
  `canonicalRelativeRmmPrincipledInteriorChargedTraceCost := 33`
  (`InteriorDirectory.lean:1934`);
* and `3 * rankClose = 33`, which is a coincidence of value.

The bound this module actually proves about the interior chunk fold is `8`,
and that `8` is the TABLE ADAPTER's per-read chunk cap
(`interiorChunkCount_le_eight`), which is a different `8` from the fringe's
per-word chunk cap (`machineWordBits_le_8_mul_bpFringeChunkBits`,
`ChargedWordChunks.lean:39`).  Two distinct literals that share a value.
-/
import RMQ.Core.WordRAM.E1InteriorChunkFold
import RMQ.Core.WordRAM.E1WholeQueryPublic

namespace RMQ
namespace WordRAM
namespace E1CostAlgebra

open E1Machine
open E1InteriorChunkFold
open E1Query

/-! ## 1. The bridge, carried across the gap it was written for

The chain, with the vocabulary each link is written in:

| link | vocabulary | source |
|---|---|---|
| the fold charges at most `8` reads | `filter` | `interiorChunkFoldCats_memoryRead_le_eight` |
| ... hence its `catCount` is at most `8` | **bridge** | `catCount_le_of_filter_length_le` |
| ... hence the machine's RECEIPT is at most `8` long | `catCount` | `RunsTo.readLog_length_eq_memoryRead_count` |

The first and last links could not be composed before the middle one existed.
-/

/-- The interior chunk fold's memory-read charge, in the MACHINE-LEVEL
`catCount` vocabulary rather than the block-level `filter` vocabulary it was
proved in.  This is `interiorChunkFoldCats_memoryRead_le_eight` transported
across `catCount_eq_filter_length`. -/
theorem interiorChunkFoldCats_catCount_memoryRead_le_eight
    (valid allPresent : Bool) (entriesLen chunkCount i : Nat) :
    catCount (interiorChunkFoldCats valid allPresent
        (chunkIters entriesLen chunkCount i)) Category.memoryRead ≤ 8 :=
  catCount_le_of_filter_length_le
    (interiorChunkFoldCats_memoryRead_le_eight valid allPresent
      entriesLen chunkCount i)

/--
THE BRIDGE DOING WORK.

Any run whose charge log is the interior chunk fold's emits a receipt of at
most `8` events -- a statement about the machine's ACTUAL read log, derived
from a cap that was only ever proved about a `filter` over a category list.

Without `catCount_eq_filter_length` the two halves of this proof cannot be
put next to each other: `interiorChunkFoldCats_memoryRead_le_eight` bounds a
`filter` length and `RunsTo.readLog_length_eq_memoryRead_count` produces a
`catCount`, and nothing in the tree said they were the same number.
-/
theorem interiorChunkFold_readLog_le_eight
    {store : ReadStore} {program : E1Machine.Program} {s s' : State}
    {reads : List TraceEvent} {valid allPresent : Bool}
    {entriesLen chunkCount i : Nat}
    (h : RunsTo store program s s' reads
      (interiorChunkFoldCats valid allPresent
        (chunkIters entriesLen chunkCount i))) :
    reads.length ≤ 8 := by
  rw [RunsTo.readLog_length_eq_memoryRead_count h]
  exact interiorChunkFoldCats_catCount_memoryRead_le_eight valid allPresent
    entriesLen chunkCount i

/-! ## 2. Per-block charge-length bounds: the addends

Each of these bounds ONE block's category log.  None of them is a whole-query
claim and none should be read as one.  The blocks whose logs are still
unbounded are listed at the end of this module.
-/

/-- The machine-computed iteration count is at most `8`, with NO size
hypothesis and no positivity side condition -- both arms of `chunkIters` are
bounded by `8` on the nose.  This is the parameter every interior fold bound
below is a function of. -/
theorem chunkIters_le_eight (entriesLen chunkCount i : Nat) :
    chunkIters entriesLen chunkCount i ≤ 8 := by
  unfold chunkIters
  split
  · exact Nat.min_le_right _ _
  · omega

/-- The fold's charge log, counted exactly: the validity-indexed init, then
`9` charges per read iteration and `8` per reversal iteration, then the
presence-indexed epilogue.  Stated as an equation because every quantity in
it is an instruction count -- nothing here passes through `machineWordBits`,
so the kernel boundary is not in play. -/
theorem interiorChunkFoldCats_length
    (valid allPresent : Bool) (iters : Nat) :
    (interiorChunkFoldCats valid allPresent iters).length =
      (interiorChunkInitCats valid).length + 17 * iters +
        (interiorChunkEpilogueCats allPresent).length := by
  unfold interiorChunkFoldCats
  rw [List.length_append, List.length_append, List.length_append,
    iterLog_const_length, iterLog_const_length,
    interiorChunkReadBodyCats_length, interiorChunkCombineCats_length]
  omega

/--
THE FOLD'S CHARGE CAP, DERIVED.

`156 = 17 + 8*9 + 8*8 + 3`: the dead path's longer init, eight read
iterations at `9` charges, eight reversal iterations at `8`, and the
all-present epilogue's extra step.  No size hypothesis.  The numeral is what
the algebra produces -- it is not asserted first and checked after.
-/
theorem interiorChunkFoldCats_length_le
    (valid allPresent : Bool) (entriesLen chunkCount i : Nat) :
    (interiorChunkFoldCats valid allPresent
        (chunkIters entriesLen chunkCount i)).length ≤ 156 := by
  rw [interiorChunkFoldCats_length]
  have hiters := chunkIters_le_eight entriesLen chunkCount i
  cases valid <;> cases allPresent <;>
    simp [interiorChunkInitCats_valid, interiorChunkInitCats_dead,
      interiorChunkEpilogueCats] <;> omega

end E1CostAlgebra
end WordRAM
end RMQ
