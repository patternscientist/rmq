import RMQ.Core.GenericSelect.RelativeSplit

/-!
# Generic select legacy names

Compatibility aliases for older names that mentioned `false` even though the
definitions are now target-parametric or shape-free. New generic code should
prefer the neutral names from the role modules below `GenericSelect.LowLevel`.
-/

namespace RMQ.GenericSelect

abbrev sparseDenseFalseSelectQueryCost : Nat :=
  sparseDenseSelectQueryCost

abbrev sparseDenseFalseSelectOverhead :=
  sparseDenseSelectOverhead

theorem sparseDenseFalseSelectOverhead_littleO
    (superDirectorySlots longSuperExplicitSlots localDirectorySlots
      sparseLocalExplicitSlots : Nat) :
    SuccinctSpace.LittleOLinear
      (sparseDenseFalseSelectOverhead
        superDirectorySlots longSuperExplicitSlots localDirectorySlots
        sparseLocalExplicitSlots) :=
  sparseDenseSelectOverhead_littleO
    superDirectorySlots longSuperExplicitSlots localDirectorySlots
    sparseLocalExplicitSlots

abbrev falseSelectSuperSlot := selectSuperSlot
abbrev falseSelectLocalSlotsPerSuper := selectLocalSlotsPerSuper
abbrev falseSelectCeilDiv := selectCeilDiv
abbrev falseSelectLocalSlotInSuper := selectLocalSlotInSuper
abbrev falseSelectLocalSlot := selectLocalSlot
abbrev falseSelectSparseLocalExplicitSlot := selectSparseLocalExplicitSlot

theorem falseSelectCeilDiv_mul_le_add (n stride : Nat) :
    falseSelectCeilDiv n stride * stride <= n + stride :=
  selectCeilDiv_mul_le_add n stride

theorem falseSelectLocalSlotsPerSuper_mul_localStride_le_add
    (superStride localStride : Nat) :
    falseSelectLocalSlotsPerSuper superStride localStride * localStride <=
      superStride + localStride :=
  selectLocalSlotsPerSuper_mul_localStride_le_add superStride localStride

theorem falseSelectCeilDiv_mul_ge_of_pos
    {n stride : Nat} (hstride : 0 < stride) :
    n <= falseSelectCeilDiv n stride * stride :=
  selectCeilDiv_mul_ge_of_pos hstride

theorem falseSelectCeilDiv_slot_mul_lt
    {n stride slot : Nat} (hstride : 0 < stride)
    (hslot : slot < falseSelectCeilDiv n stride) :
    slot * stride < n :=
  selectCeilDiv_slot_mul_lt hstride hslot

theorem falseSelectCeilDiv_le_self_of_pos
    {n stride : Nat} (hn : 0 < n) (hstride : 0 < stride) :
    falseSelectCeilDiv n stride <= n :=
  selectCeilDiv_le_self_of_pos hn hstride

theorem falseSelectCeilDiv_mul_ge
    {n stride : Nat} (hstride : 0 < stride) :
    n <= falseSelectCeilDiv n stride * stride :=
  selectCeilDiv_mul_ge hstride

theorem falseSelectLocalSlotsPerSuper_mul_localStride_ge_superStride
    {superStride localStride : Nat}
    (hlocal : 0 < localStride) :
    superStride <=
      falseSelectLocalSlotsPerSuper superStride localStride * localStride :=
  selectLocalSlotsPerSuper_mul_localStride_ge_superStride hlocal

theorem falseSelectLocalSlotsPerSuper_le_superStride
    {superStride localStride : Nat}
    (hsuper : 0 < superStride) (hlocal : 0 < localStride) :
    falseSelectLocalSlotsPerSuper superStride localStride <= superStride :=
  selectLocalSlotsPerSuper_le_superStride hsuper hlocal

abbrev SparseDenseFalseSelectDenseLocalEntry :=
  SparseDenseSelectDenseLocalEntry

namespace SparseDenseFalseSelectDenseLocalEntry

abbrev baseOccurrences :=
  SparseDenseSelectDenseLocalEntry.baseOccurrences

abbrev baseWordIndices :=
  SparseDenseSelectDenseLocalEntry.baseWordIndices

abbrev ranksBefore :=
  SparseDenseSelectDenseLocalEntry.ranksBefore

abbrev firstOffsets :=
  SparseDenseSelectDenseLocalEntry.firstOffsets

end SparseDenseFalseSelectDenseLocalEntry

abbrev sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget :=
  sparseDenseSelectDenseLocalEntryMultiwordPayloadBudget

abbrev FixedWidthSparseDenseFalseSelectDenseLocalEntryTable :=
  FixedWidthSparseDenseSelectDenseLocalEntryTable

abbrev FalseSelectAlignedBitWords := SelectAlignedBitWords

theorem falseSelectAlignedBitWords_ofChunks
    (bits : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    FalseSelectAlignedBitWords bits wordSize
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hword) :=
  selectAlignedBitWords_ofChunks bits hword

abbrev falseSelectDenseLocalFirstStart := selectDenseLocalFirstStart
abbrev falseSelectDenseLocalSecondStart := selectDenseLocalSecondStart
abbrev falseSelectDenseLocalSpanEnd := selectDenseLocalSpanEnd
abbrev falseSelectDenseLocalFirstWord := selectDenseLocalFirstWord
abbrev falseSelectDenseLocalFirstCount
    (bits : List Bool) (wordSize baseWordIndex firstOffset : Nat) : Nat :=
  selectDenseLocalFirstCount false bits wordSize baseWordIndex firstOffset
abbrev sparseDenseFalseSelectDenseLocalEntryBasePosition :=
  sparseDenseSelectDenseLocalEntryBasePosition

abbrev relativeSplitFalseSelectEntryIsMarked :=
  relativeSplitSelectEntryIsMarked
abbrev relativeSplitFalseSelectEntryBasePosition :=
  relativeSplitSelectEntryBasePosition
abbrev relativeSplitFalseSelectLocalBaseOccurrence :=
  relativeSplitSelectLocalBaseOccurrence
abbrev relativeSplitFalseSelectLocalBasePosition :=
  relativeSplitSelectLocalBasePosition
abbrev relativeSplitFalseSelectLongExplicitSlot :=
  relativeSplitSelectLongExplicitSlot
abbrev relativeSplitFalseSelectLongFlagBits :=
  relativeSplitSelectLongFlagBits
abbrev relativeSplitFalseSelectLongCompactSlot :=
  relativeSplitSelectLongCompactSlot
abbrev relativeSplitFalseSelectSparseExplicitSlot :=
  relativeSplitSelectSparseExplicitSlot
abbrev relativeSplitFalseSelectSparseCompactSlot :=
  relativeSplitSelectSparseCompactSlot
abbrev relativeSplitFalseSelectLocalSlotInSuper :=
  relativeSplitSelectLocalSlotInSuper
abbrev relativeSplitFalseSelectLocalSlot :=
  relativeSplitSelectLocalSlot

end RMQ.GenericSelect
