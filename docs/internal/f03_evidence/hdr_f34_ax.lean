import RMQ.Core.SuccinctFinal

/-!
CHECKED discharge of the residual F03 obligation on rows F3/F4:
`builtRelativeSplitBPCloseRankSuperOverhead` and
`builtRelativeSplitBPCloseRankBlockOverhead` mention `shape.bpCode` CONTENTS with
zero occurrences under `List.length`, but are claimed size-only in VALUE.

If these theorems compile, the two rows are provably S (classifiable from n alone),
so they need NO header field.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace HdrF34

/-- Sample-entry COUNTS are functions of `bits.length` only. -/
theorem superEntries_length (target : Bool) (bits : List Bool) (w b : Nat) :
    (SuccinctRank.canonicalSuperRankEntries target bits w b).length =
      bits.length / w / b + 1 := by
  simp [SuccinctRank.canonicalSuperRankEntries]

theorem blockEntries_length (target : Bool) (bits : List Bool) (w b : Nat) :
    (SuccinctRank.canonicalBlockRankEntries target bits w b).length =
      bits.length / w + 1 := by
  simp [SuccinctRank.canonicalBlockRankEntries]

/-- F4: the super-sample overhead in closed form, from `bpCode.length` alone. -/
theorem superOverhead_closed_form (shape : CartesianShape) :
    builtRelativeSplitBPCloseRankSuperOverhead shape =
      (shape.bpCode.length / builtRelativeSplitBPCloseRankWordSize shape
          / builtRelativeSplitBPCloseRankWordSize shape + 1)
        * builtRelativeSplitBPCloseRankWordSize shape
      + (shape.bpCode.length / builtRelativeSplitBPCloseRankWordSize shape
          / builtRelativeSplitBPCloseRankWordSize shape + 1)
        * builtRelativeSplitBPCloseRankWordSize shape := by
  unfold builtRelativeSplitBPCloseRankSuperOverhead
  simp [SuccinctSpace.FixedWidthRankSampleTables.payload,
    SuccinctSpace.FixedWidthNatTable.payload_length,
    superEntries_length, builtRelativeSplitBPCloseRankBlocksPerSuper]

/-- F3: the block-sample overhead in closed form, from `bpCode.length` alone. -/
theorem blockOverhead_closed_form (shape : CartesianShape) :
    builtRelativeSplitBPCloseRankBlockOverhead shape =
      (shape.bpCode.length / builtRelativeSplitBPCloseRankWordSize shape + 1)
        * builtRelativeSplitBPCloseRankBlockWidth shape
      + (shape.bpCode.length / builtRelativeSplitBPCloseRankWordSize shape + 1)
        * builtRelativeSplitBPCloseRankBlockWidth shape := by
  unfold builtRelativeSplitBPCloseRankBlockOverhead
  simp [SuccinctSpace.FixedWidthRankSampleTables.payload,
    SuccinctSpace.FixedWidthNatTable.payload_length,
    blockEntries_length]

/-- THE F03 CLASSIFICATION FOR F3/F4: equal size => equal overhead. Size-only (S). -/
theorem superOverhead_size_only (s t : CartesianShape) (h : s.size = t.size) :
    builtRelativeSplitBPCloseRankSuperOverhead s =
      builtRelativeSplitBPCloseRankSuperOverhead t := by
  have hlen : s.bpCode.length = t.bpCode.length := by
    rw [CartesianShape.bpCode_length, CartesianShape.bpCode_length, h]
  rw [superOverhead_closed_form, superOverhead_closed_form,
    builtRelativeSplitBPCloseRankWordSize, builtRelativeSplitBPCloseRankWordSize,
    hlen]

theorem blockOverhead_size_only (s t : CartesianShape) (h : s.size = t.size) :
    builtRelativeSplitBPCloseRankBlockOverhead s =
      builtRelativeSplitBPCloseRankBlockOverhead t := by
  have hlen : s.bpCode.length = t.bpCode.length := by
    rw [CartesianShape.bpCode_length, CartesianShape.bpCode_length, h]
  rw [blockOverhead_closed_form, blockOverhead_closed_form,
    builtRelativeSplitBPCloseRankBlockWidth, builtRelativeSplitBPCloseRankBlockWidth,
    builtRelativeSplitBPCloseRankWordSize, builtRelativeSplitBPCloseRankWordSize,
    hlen]

end HdrF34

#print axioms HdrF34.superOverhead_size_only
#print axioms HdrF34.blockOverhead_size_only
#print axioms HdrF34.superOverhead_closed_form
#print axioms HdrF34.blockOverhead_closed_form
