import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerConcatIndex

/-!
# Locating an interior component in the component store

`DD-20260804-055` recorded that the eight-way split is left-associated, so reading
component `k` needs `7 - k` peels with the bound widened through the prefixes.
This module carries that out for the leftmost component.

`packedConcatIndex_first_of_eight` is the peel chain written once, generically over
eight lists. `packedInteriorBaselineAccess` applies it: the baseline column's
machine words are the component store's first words, at the same indices.

Combined with `packedInteriorComponentWord_of_lt_size`, this is the first interior
component fully lowered -- store index to payload bit range -- and the first time
segment `20` reaches a computable address.

## What this module does not establish

* Seven components remain. Each needs its own offset skip
  (`packedConcatIndex_right`) before the peel chain, with the offset taken from
  `canonicalRelativeRmmInteriorComponentOffsets`.
* The baseline column's payload is located inside the *interior directory*, not
  yet inside the consumed payload; that composition is still outstanding.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian
open RMQ.SuccinctSpace

/--
**The leftmost of eight concatenated blocks.** Seven peels, each bound widened
from the one before, matching the left-associated shape recorded in
`DD-20260804-055`.
-/
theorem packedConcatIndex_first_of_eight {alpha : Type}
    (a b c d e f g h : List alpha) {j : Nat} (hj : j < a.length) :
    (a ++ b ++ c ++ d ++ e ++ f ++ g ++ h)[j]? = a[j]? := by
  have h1 : j < (a ++ b).length := packedConcatIndex_lt_append _ _ hj
  have h2 : j < (a ++ b ++ c).length := packedConcatIndex_lt_append _ _ h1
  have h3 : j < (a ++ b ++ c ++ d).length := packedConcatIndex_lt_append _ _ h2
  have h4 : j < (a ++ b ++ c ++ d ++ e).length := packedConcatIndex_lt_append _ _ h3
  have h5 : j < (a ++ b ++ c ++ d ++ e ++ f).length :=
    packedConcatIndex_lt_append _ _ h4
  have h6 : j < (a ++ b ++ c ++ d ++ e ++ f ++ g).length :=
    packedConcatIndex_lt_append _ _ h5
  rw [packedConcatIndex_left _ _ h6, packedConcatIndex_left _ _ h5,
    packedConcatIndex_left _ _ h4, packedConcatIndex_left _ _ h3,
    packedConcatIndex_left _ _ h2, packedConcatIndex_left _ _ h1,
    packedConcatIndex_left _ _ hj]

/--
**Component zero located.** The baseline column's machine words are the component
store's first words, at the same indices.
-/
theorem packedInteriorBaselineAccess (shape : CartesianShape) {j : Nat}
    (hj : j <
      ((SuccinctClose.canonicalRelativeRmmSummaryTable
        shape).baselineTable.machineStore
          (packedInteriorWordSize_pos shape)).store.words.toList.length) :
    (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words.toList[j]? =
      ((SuccinctClose.canonicalRelativeRmmSummaryTable
        shape).baselineTable.machineStore
          (packedInteriorWordSize_pos shape)).store.words.toList[j]? := by
  rw [packedReviewerInteriorComponentWords_split shape]
  dsimp only
  exact packedConcatIndex_first_of_eight _ _ _ _ _ _ _ _ hj

end PackedCellProbe
end SuccinctFinal
end RMQ
