import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerInteriorCount

/-!
# Indexing the interior component store's concatenation

The three lemmas needed to locate one of the eight interior components inside
`canonicalRelativeRmmInteriorComponentStore`, whose word list is their
concatenation.

## The shape of the remaining work, measured rather than assumed

`packedReviewerInteriorComponentWords_split` presents the store as

```
A ++ B ++ C ++ D ++ E ++ F ++ G ++ H
```

and `++` is **left**-associative, so the term is
`(((((((A ++ B) ++ C) ++ D) ++ E) ++ F) ++ G) ++ H)`. A single
`packedConcatIndex_left` therefore does *not* reach `A`: the outermost operands are
the first seven components and `H`.

Reading component `k` needs `7 - k` peels with `packedConcatIndex_left`, each
justified by `packedConcatIndex_lt_append` widening the bound from `A.length` up
through the prefixes, then `k` applications of `packedConcatIndex_right` to skip
the components before it. The offsets in
`canonicalRelativeRmmInteriorComponentOffsets` are exactly those prefix lengths, so
the arithmetic matches by construction rather than by coincidence -- but the
peeling is per-component and is not yet written.

A first attempt stated two accessors directly and failed to unify twice: the `let`
binders in the split theorem's statement blocked reduction, and once `dsimp only`
removed those, the left-association did. Both facts are recorded so the next
attempt starts from the right shape rather than rediscovering them.

## What this module does not establish

* No component is located. These are the tools, not the result.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open RMQ.Cartesian
open RMQ.SuccinctSpace

/-! ### Indexing a concatenation -/

/-- An index inside the left operand reads the left operand. -/
theorem packedConcatIndex_left {alpha : Type} (xs ys : List alpha) {j : Nat}
    (hj : j < xs.length) : (xs ++ ys)[j]? = xs[j]? :=
  List.getElem?_append_left hj

/--
An index offset by the whole left operand reads the right one, at every `j`
including out of range -- both sides are `none` there.
-/
theorem packedConcatIndex_right {alpha : Type} (xs ys : List alpha) (j : Nat) :
    (xs ++ ys)[xs.length + j]? = ys[j]? := by
  rw [List.getElem?_append_right (by omega)]
  congr 1
  omega

/-- Widening a prefix preserves an in-range index. -/
theorem packedConcatIndex_lt_append {alpha : Type} (xs ys : List alpha) {j : Nat}
    (hj : j < xs.length) : j < (xs ++ ys).length := by
  rw [List.length_append]
  omega

end PackedCellProbe

end SuccinctFinal

end RMQ
