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

* Four components remain (`interiorLocal`, `interiorGlobal`, `localLevel`,
  `globalLevel`). Each needs `7 - k` peels then its offset skip; the four done
  here cover the whole summary half and fix the pattern.
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

/--
**The second of eight concatenated blocks.** Six peels, then one offset skip --
the general shape `DD-20260804-055` predicted for component `k`: `7 - k` peels
followed by the skip.
-/
theorem packedConcatIndex_second_of_eight {alpha : Type}
    (a b c d e f g h : List alpha) {j : Nat} (hj : j < b.length) :
    (a ++ b ++ c ++ d ++ e ++ f ++ g ++ h)[a.length + j]? = b[j]? := by
  have h1 : a.length + j < (a ++ b).length := by
    rw [List.length_append]
    omega
  have h2 : a.length + j < (a ++ b ++ c).length :=
    packedConcatIndex_lt_append _ _ h1
  have h3 : a.length + j < (a ++ b ++ c ++ d).length :=
    packedConcatIndex_lt_append _ _ h2
  have h4 : a.length + j < (a ++ b ++ c ++ d ++ e).length :=
    packedConcatIndex_lt_append _ _ h3
  have h5 : a.length + j < (a ++ b ++ c ++ d ++ e ++ f).length :=
    packedConcatIndex_lt_append _ _ h4
  have h6 : a.length + j < (a ++ b ++ c ++ d ++ e ++ f ++ g).length :=
    packedConcatIndex_lt_append _ _ h5
  rw [packedConcatIndex_left _ _ h6, packedConcatIndex_left _ _ h5,
    packedConcatIndex_left _ _ h4, packedConcatIndex_left _ _ h3,
    packedConcatIndex_left _ _ h2, packedConcatIndex_left _ _ h1,
    packedConcatIndex_right]

/-- **Component one located**: the minRel column, after the baseline column. -/
theorem packedInteriorMinRelAccess (shape : CartesianShape) {j : Nat}
    (hj : j <
      ((SuccinctClose.canonicalRelativeRmmSummaryTable
        shape).minRelTable.machineStore
          (packedInteriorWordSize_pos shape)).store.words.toList.length) :
    (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words.toList[
          ((SuccinctClose.canonicalRelativeRmmSummaryTable
            shape).baselineTable.machineStore
              (packedInteriorWordSize_pos shape)).store.words.toList.length + j]? =
      ((SuccinctClose.canonicalRelativeRmmSummaryTable
        shape).minRelTable.machineStore
          (packedInteriorWordSize_pos shape)).store.words.toList[j]? := by
  rw [packedReviewerInteriorComponentWords_split shape]
  dsimp only
  exact packedConcatIndex_second_of_eight _ _ _ _ _ _ _ _ hj

/--
**The third of eight concatenated blocks.** Five peels, then a skip by the two
preceding blocks together -- the first case where the skipped offset is compound.
-/
theorem packedConcatIndex_third_of_eight {alpha : Type}
    (a b c d e f g h : List alpha) {j : Nat} (hj : j < c.length) :
    (a ++ b ++ c ++ d ++ e ++ f ++ g ++ h)[(a ++ b).length + j]? = c[j]? := by
  have h2 : (a ++ b).length + j < (a ++ b ++ c).length := by
    have hlen : (a ++ b ++ c).length = (a ++ b).length + c.length :=
      List.length_append
    omega
  have h3 : (a ++ b).length + j < (a ++ b ++ c ++ d).length :=
    packedConcatIndex_lt_append _ _ h2
  have h4 : (a ++ b).length + j < (a ++ b ++ c ++ d ++ e).length :=
    packedConcatIndex_lt_append _ _ h3
  have h5 : (a ++ b).length + j < (a ++ b ++ c ++ d ++ e ++ f).length :=
    packedConcatIndex_lt_append _ _ h4
  have h6 : (a ++ b).length + j < (a ++ b ++ c ++ d ++ e ++ f ++ g).length :=
    packedConcatIndex_lt_append _ _ h5
  rw [packedConcatIndex_left _ _ h6, packedConcatIndex_left _ _ h5,
    packedConcatIndex_left _ _ h4, packedConcatIndex_left _ _ h3,
    packedConcatIndex_left _ _ h2, packedConcatIndex_right]

/-- **Component two located**: the maxRel column. -/
theorem packedInteriorMaxRelAccess (shape : CartesianShape) {j : Nat}
    (hj : j <
      ((SuccinctClose.canonicalRelativeRmmSummaryTable
        shape).maxRelTable.machineStore
          (packedInteriorWordSize_pos shape)).store.words.toList.length) :
    (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words.toList[
          (((SuccinctClose.canonicalRelativeRmmSummaryTable
            shape).baselineTable.machineStore
              (packedInteriorWordSize_pos shape)).store.words.toList ++
            ((SuccinctClose.canonicalRelativeRmmSummaryTable
              shape).minRelTable.machineStore
                (packedInteriorWordSize_pos shape)).store.words.toList).length
            + j]? =
      ((SuccinctClose.canonicalRelativeRmmSummaryTable
        shape).maxRelTable.machineStore
          (packedInteriorWordSize_pos shape)).store.words.toList[j]? := by
  rw [packedReviewerInteriorComponentWords_split shape]
  dsimp only
  exact packedConcatIndex_third_of_eight _ _ _ _ _ _ _ _ hj

/-- **The fourth of eight concatenated blocks.** Four peels, then the skip. -/
theorem packedConcatIndex_fourth_of_eight {alpha : Type}
    (a b c d e f g h : List alpha) {j : Nat} (hj : j < d.length) :
    (a ++ b ++ c ++ d ++ e ++ f ++ g ++ h)[(a ++ b ++ c).length + j]? = d[j]? := by
  have h3 : (a ++ b ++ c).length + j < (a ++ b ++ c ++ d).length := by
    have hlen : (a ++ b ++ c ++ d).length = (a ++ b ++ c).length + d.length :=
      List.length_append
    omega
  have h4 : (a ++ b ++ c).length + j < (a ++ b ++ c ++ d ++ e).length :=
    packedConcatIndex_lt_append _ _ h3
  have h5 : (a ++ b ++ c).length + j < (a ++ b ++ c ++ d ++ e ++ f).length :=
    packedConcatIndex_lt_append _ _ h4
  have h6 : (a ++ b ++ c).length + j < (a ++ b ++ c ++ d ++ e ++ f ++ g).length :=
    packedConcatIndex_lt_append _ _ h5
  rw [packedConcatIndex_left _ _ h6, packedConcatIndex_left _ _ h5,
    packedConcatIndex_left _ _ h4, packedConcatIndex_left _ _ h3,
    packedConcatIndex_right]

/-- **Component three located**: the argOffset column, last of the summary four. -/
theorem packedInteriorArgOffsetAccess (shape : CartesianShape) {j : Nat}
    (hj : j <
      ((SuccinctClose.canonicalRelativeRmmSummaryTable
        shape).argOffsetTable.machineStore
          (packedInteriorWordSize_pos shape)).store.words.toList.length) :
    (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words.toList[
          ((((SuccinctClose.canonicalRelativeRmmSummaryTable
            shape).baselineTable.machineStore
              (packedInteriorWordSize_pos shape)).store.words.toList ++
            ((SuccinctClose.canonicalRelativeRmmSummaryTable
              shape).minRelTable.machineStore
                (packedInteriorWordSize_pos shape)).store.words.toList) ++
            ((SuccinctClose.canonicalRelativeRmmSummaryTable
              shape).maxRelTable.machineStore
                (packedInteriorWordSize_pos shape)).store.words.toList).length
            + j]? =
      ((SuccinctClose.canonicalRelativeRmmSummaryTable
        shape).argOffsetTable.machineStore
          (packedInteriorWordSize_pos shape)).store.words.toList[j]? := by
  rw [packedReviewerInteriorComponentWords_split shape]
  dsimp only
  exact packedConcatIndex_fourth_of_eight _ _ _ _ _ _ _ _ hj

end PackedCellProbe
end SuccinctFinal
end RMQ
