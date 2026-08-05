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

* All eight components are located, the bridge to
  `canonicalRelativeRmmInteriorComponentOffsets` is proved, and the interior
  directory's position inside the consumed payload is fixed. What remains is
  composing those three into one bit address, and the physical read over
  `packedReviewerMemory`.
* The baseline column's payload is located inside the *interior directory*, not
  yet inside the consumed payload; that composition is still outstanding.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian
open RMQ.SuccinctSpace
open SuccinctClose

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

/-- **The fifth of eight.** Three peels, then the skip. -/
theorem packedConcatIndex_fifth_of_eight {alpha : Type}
    (a b c d e f g h : List alpha) {j : Nat} (hj : j < e.length) :
    (a ++ b ++ c ++ d ++ e ++ f ++ g ++ h)[(a ++ b ++ c ++ d).length + j]? =
      e[j]? := by
  have h4 : (a ++ b ++ c ++ d).length + j < (a ++ b ++ c ++ d ++ e).length := by
    have hlen : (a ++ b ++ c ++ d ++ e).length =
        (a ++ b ++ c ++ d).length + e.length := List.length_append
    omega
  have h5 : (a ++ b ++ c ++ d).length + j <
      (a ++ b ++ c ++ d ++ e ++ f).length := packedConcatIndex_lt_append _ _ h4
  have h6 : (a ++ b ++ c ++ d).length + j <
      (a ++ b ++ c ++ d ++ e ++ f ++ g).length :=
    packedConcatIndex_lt_append _ _ h5
  rw [packedConcatIndex_left _ _ h6, packedConcatIndex_left _ _ h5,
    packedConcatIndex_left _ _ h4, packedConcatIndex_right]

/-- **The sixth of eight.** Two peels, then the skip. -/
theorem packedConcatIndex_sixth_of_eight {alpha : Type}
    (a b c d e f g h : List alpha) {j : Nat} (hj : j < f.length) :
    (a ++ b ++ c ++ d ++ e ++ f ++ g ++ h)[(a ++ b ++ c ++ d ++ e).length + j]? =
      f[j]? := by
  have h5 : (a ++ b ++ c ++ d ++ e).length + j <
      (a ++ b ++ c ++ d ++ e ++ f).length := by
    have hlen : (a ++ b ++ c ++ d ++ e ++ f).length =
        (a ++ b ++ c ++ d ++ e).length + f.length := List.length_append
    omega
  have h6 : (a ++ b ++ c ++ d ++ e).length + j <
      (a ++ b ++ c ++ d ++ e ++ f ++ g).length :=
    packedConcatIndex_lt_append _ _ h5
  rw [packedConcatIndex_left _ _ h6, packedConcatIndex_left _ _ h5,
    packedConcatIndex_right]

/-- **The seventh of eight.** One peel, then the skip. -/
theorem packedConcatIndex_seventh_of_eight {alpha : Type}
    (a b c d e f g h : List alpha) {j : Nat} (hj : j < g.length) :
    (a ++ b ++ c ++ d ++ e ++ f ++ g ++ h)[
        (a ++ b ++ c ++ d ++ e ++ f).length + j]? = g[j]? := by
  have h6 : (a ++ b ++ c ++ d ++ e ++ f).length + j <
      (a ++ b ++ c ++ d ++ e ++ f ++ g).length := by
    have hlen : (a ++ b ++ c ++ d ++ e ++ f ++ g).length =
        (a ++ b ++ c ++ d ++ e ++ f).length + g.length := List.length_append
    omega
  rw [packedConcatIndex_left _ _ h6, packedConcatIndex_right]

/--
**The eighth of eight.** No peels and no hypothesis: the last block is the outer
right operand, so `packedConcatIndex_right` applies directly, at every `j`.
-/
theorem packedConcatIndex_eighth_of_eight {alpha : Type}
    (a b c d e f g h : List alpha) (j : Nat) :
    (a ++ b ++ c ++ d ++ e ++ f ++ g ++ h)[
        (a ++ b ++ c ++ d ++ e ++ f ++ g).length + j]? = h[j]? :=
  packedConcatIndex_right _ _ j

/-- Word list of one interior component, at the interior machine word size. -/
abbrev packedInteriorBaselineWords (shape : CartesianShape) : List (List Bool) :=
  ((canonicalRelativeRmmSummaryTable shape).baselineTable.machineStore
    (packedInteriorWordSize_pos shape)).store.words.toList

abbrev packedInteriorMinRelWords (shape : CartesianShape) : List (List Bool) :=
  ((canonicalRelativeRmmSummaryTable shape).minRelTable.machineStore
    (packedInteriorWordSize_pos shape)).store.words.toList

abbrev packedInteriorMaxRelWords (shape : CartesianShape) : List (List Bool) :=
  ((canonicalRelativeRmmSummaryTable shape).maxRelTable.machineStore
    (packedInteriorWordSize_pos shape)).store.words.toList

abbrev packedInteriorArgOffsetWords (shape : CartesianShape) : List (List Bool) :=
  ((canonicalRelativeRmmSummaryTable shape).argOffsetTable.machineStore
    (packedInteriorWordSize_pos shape)).store.words.toList

abbrev packedInteriorLocalWords (shape : CartesianShape) : List (List Bool) :=
  ((canonicalRelativeRmmInteriorLocalTable shape).table.machineStore
    (packedInteriorWordSize_pos shape)).store.words.toList

abbrev packedInteriorGlobalWords (shape : CartesianShape) : List (List Bool) :=
  ((canonicalRelativeRmmInteriorGlobalTable shape).table.machineStore
    (packedInteriorWordSize_pos shape)).store.words.toList

abbrev packedInteriorLocalLevelWords (shape : CartesianShape) : List (List Bool) :=
  ((canonicalRelativeRmmInteriorLocalLevelTable shape).table.machineStore
    (packedInteriorWordSize_pos shape)).store.words.toList

abbrev packedInteriorGlobalLevelWords (shape : CartesianShape) : List (List Bool) :=
  ((canonicalRelativeRmmInteriorGlobalLevelTable shape).table.machineStore
    (packedInteriorWordSize_pos shape)).store.words.toList

abbrev packedInteriorStoreWords (shape : CartesianShape) : List (List Bool) :=
  (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList

/-- **Component four located**: the interior local offset table. -/
theorem packedInteriorLocalAccess (shape : CartesianShape) {j : Nat}
    (hj : j < (packedInteriorLocalWords shape).length) :
    (packedInteriorStoreWords shape)[
        (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
          packedInteriorMaxRelWords shape ++
            packedInteriorArgOffsetWords shape).length + j]? =
      (packedInteriorLocalWords shape)[j]? := by
  unfold packedInteriorStoreWords
  rw [packedReviewerInteriorComponentWords_split shape]
  dsimp only
  exact packedConcatIndex_fifth_of_eight _ _ _ _ _ _ _ _ hj

/-- **Component five located**: the interior global block table. -/
theorem packedInteriorGlobalAccess (shape : CartesianShape) {j : Nat}
    (hj : j < (packedInteriorGlobalWords shape).length) :
    (packedInteriorStoreWords shape)[
        (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
          packedInteriorMaxRelWords shape ++
            packedInteriorArgOffsetWords shape ++
              packedInteriorLocalWords shape).length + j]? =
      (packedInteriorGlobalWords shape)[j]? := by
  unfold packedInteriorStoreWords
  rw [packedReviewerInteriorComponentWords_split shape]
  dsimp only
  exact packedConcatIndex_sixth_of_eight _ _ _ _ _ _ _ _ hj

/-- **Component six located**: the local level table. -/
theorem packedInteriorLocalLevelAccess (shape : CartesianShape) {j : Nat}
    (hj : j < (packedInteriorLocalLevelWords shape).length) :
    (packedInteriorStoreWords shape)[
        (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
          packedInteriorMaxRelWords shape ++
            packedInteriorArgOffsetWords shape ++
              packedInteriorLocalWords shape ++
                packedInteriorGlobalWords shape).length + j]? =
      (packedInteriorLocalLevelWords shape)[j]? := by
  unfold packedInteriorStoreWords
  rw [packedReviewerInteriorComponentWords_split shape]
  dsimp only
  exact packedConcatIndex_seventh_of_eight _ _ _ _ _ _ _ _ hj

/-- **Component seven located**: the global level table, needing no bound. -/
theorem packedInteriorGlobalLevelAccess (shape : CartesianShape) (j : Nat) :
    (packedInteriorStoreWords shape)[
        (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
          packedInteriorMaxRelWords shape ++
            packedInteriorArgOffsetWords shape ++
              packedInteriorLocalWords shape ++
                packedInteriorGlobalWords shape ++
                  packedInteriorLocalLevelWords shape).length + j]? =
      (packedInteriorGlobalLevelWords shape)[j]? := by
  unfold packedInteriorStoreWords
  rw [packedReviewerInteriorComponentWords_split shape]
  dsimp only
  exact packedConcatIndex_eighth_of_eight _ _ _ _ _ _ _ _ j

/-! ### The offsets record is exactly these prefix lengths -/

theorem packedInteriorOffsets_baseline (shape : CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).baseline = 0 := rfl

theorem packedInteriorOffsets_minRel (shape : CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).minRel =
      (packedInteriorBaselineWords shape).length := by
  unfold canonicalRelativeRmmInteriorComponentOffsets packedInteriorBaselineWords
  simp

theorem packedInteriorOffsets_maxRel (shape : CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).maxRel =
      (packedInteriorBaselineWords shape ++
        packedInteriorMinRelWords shape).length := by
  unfold canonicalRelativeRmmInteriorComponentOffsets packedInteriorBaselineWords
    packedInteriorMinRelWords
  simp

theorem packedInteriorOffsets_argOffset (shape : CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).argOffset =
      (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
        packedInteriorMaxRelWords shape).length := by
  unfold canonicalRelativeRmmInteriorComponentOffsets packedInteriorBaselineWords
    packedInteriorMinRelWords packedInteriorMaxRelWords
  simp
  omega

theorem packedInteriorOffsets_localOffset (shape : CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).localOffset =
      (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
        packedInteriorMaxRelWords shape ++
          packedInteriorArgOffsetWords shape).length := by
  unfold canonicalRelativeRmmInteriorComponentOffsets packedInteriorBaselineWords
    packedInteriorMinRelWords packedInteriorMaxRelWords
    packedInteriorArgOffsetWords
  simp
  omega

theorem packedInteriorOffsets_globalBlock (shape : CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).globalBlock =
      (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
        packedInteriorMaxRelWords shape ++ packedInteriorArgOffsetWords shape ++
          packedInteriorLocalWords shape).length := by
  unfold canonicalRelativeRmmInteriorComponentOffsets packedInteriorBaselineWords
    packedInteriorMinRelWords packedInteriorMaxRelWords
    packedInteriorArgOffsetWords packedInteriorLocalWords
    canonicalRelativeRmmLocalMachineStore
  simp
  omega

theorem packedInteriorOffsets_localLevel (shape : CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel =
      (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
        packedInteriorMaxRelWords shape ++ packedInteriorArgOffsetWords shape ++
          packedInteriorLocalWords shape ++
            packedInteriorGlobalWords shape).length := by
  unfold canonicalRelativeRmmInteriorComponentOffsets packedInteriorBaselineWords
    packedInteriorMinRelWords packedInteriorMaxRelWords
    packedInteriorArgOffsetWords packedInteriorLocalWords
    packedInteriorGlobalWords canonicalRelativeRmmLocalMachineStore
    canonicalRelativeRmmGlobalMachineStore
  simp
  omega

theorem packedInteriorOffsets_globalLevel (shape : CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).globalLevel =
      (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
        packedInteriorMaxRelWords shape ++ packedInteriorArgOffsetWords shape ++
          packedInteriorLocalWords shape ++ packedInteriorGlobalWords shape ++
            packedInteriorLocalLevelWords shape).length := by
  unfold canonicalRelativeRmmInteriorComponentOffsets packedInteriorBaselineWords
    packedInteriorMinRelWords packedInteriorMaxRelWords
    packedInteriorArgOffsetWords packedInteriorLocalWords
    packedInteriorGlobalWords packedInteriorLocalLevelWords
    canonicalRelativeRmmLocalMachineStore
    canonicalRelativeRmmGlobalMachineStore
    canonicalRelativeRmmLocalLevelMachineStore
  simp
  omega

/-! ### The close half's position inside the consumed payload -/

/--
**The consumed payload, from the close offset on, is the close half.** Everything
before the interior directory is exactly `bpCode` and the live access payload.
-/
theorem packedReviewerPayload_drop_closeOffset (shape : CartesianShape) :
    (packedReviewerPayloadBits shape).drop
        (concreteBPNativeSuccinctRMQCanonicalReviewerCloseBitOffset shape) =
      (canonicalRelativeRmmInteriorDirectory shape).payload ++
        (bpFringeChunkTable (bpFringeChunkBits shape.bpCode.length)).payload ++
          (bpChunkSelectTable (bpFringeChunkBits shape.bpCode.length)
            false).payload := by
  unfold packedReviewerPayloadBits
    concreteBPNativeSuccinctRMQCanonicalReviewerPayload
    concreteBPNativeSuccinctRMQCanonicalReviewerCloseBitOffset
    concreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout
  dsimp only
  rw [← List.length_append]
  rw [show
      shape.bpCode ++
          concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape ++
        (canonicalRelativeRmmInteriorDirectory shape).payload ++
          (bpFringeChunkTable (bpFringeChunkBits shape.bpCode.length)).payload ++
            (bpChunkSelectTable (bpFringeChunkBits shape.bpCode.length)
              false).payload =
        (shape.bpCode ++
            concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape) ++
          ((canonicalRelativeRmmInteriorDirectory shape).payload ++
            (bpFringeChunkTable
              (bpFringeChunkBits shape.bpCode.length)).payload ++
              (bpChunkSelectTable (bpFringeChunkBits shape.bpCode.length)
                false).payload) by
    simp [List.append_assoc]]
  exact List.drop_left

end PackedCellProbe
end SuccinctFinal
end RMQ
