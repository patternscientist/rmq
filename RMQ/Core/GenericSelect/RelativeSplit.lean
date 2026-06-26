import RMQ.Core.GenericSelect.DenseWord

/-!
# Generic select relative-split helpers

Relative-split slot and base-position helpers for compact select directories.
-/

namespace RMQ.GenericSelect

open SuccinctSpace SuccinctRank

def relativeSplitSelectEntryIsMarked
    (entry : SparseDenseSelectDenseLocalEntry) : Bool :=
  entry.rankBefore != 0

def relativeSplitSelectEntryBasePosition
    (wordSize : Nat)
    (entry : SparseDenseSelectDenseLocalEntry) : Nat :=
  entry.baseWordIndex * wordSize + entry.firstOffset

def relativeSplitSelectLocalBaseOccurrence
    (super loc : SparseDenseSelectDenseLocalEntry) : Nat :=
  super.baseOccurrence + loc.baseOccurrence

def relativeSplitSelectLocalBasePosition
    (wordSize : Nat)
    (super loc : SparseDenseSelectDenseLocalEntry) : Nat :=
  (super.baseWordIndex + loc.baseWordIndex) * wordSize + loc.firstOffset

def relativeSplitSelectLongExplicitSlot
    (q superStride : Nat)
    (super : SparseDenseSelectDenseLocalEntry) : Nat :=
  selectSuperSlot q superStride * superStride +
    (q - super.baseOccurrence)

def relativeSplitSelectLongFlagBits
    (superEntries : List SparseDenseSelectDenseLocalEntry) :
    List Bool :=
  superEntries.map relativeSplitSelectEntryIsMarked

def relativeSplitSelectLongCompactSlot
    (exceptionRank localOccurrence superStride : Nat) : Nat :=
  exceptionRank * superStride + localOccurrence

def relativeSplitSelectSparseExplicitSlot
    (localSlot q localStride : Nat)
    (super loc : SparseDenseSelectDenseLocalEntry) : Nat :=
  localSlot * localStride +
    (q - relativeSplitSelectLocalBaseOccurrence super loc)

def relativeSplitSelectSparseCompactSlot
    (exceptionRank localOccurrence localStride : Nat) : Nat :=
  exceptionRank * localStride + localOccurrence

def relativeSplitSelectLocalSlotInSuper
    (super : SparseDenseSelectDenseLocalEntry)
    (q localStride : Nat) : Nat :=
  (q - super.baseOccurrence) / localStride

def relativeSplitSelectLocalSlot
    (q superStride localSlotsPerSuper localStride : Nat)
    (super : SparseDenseSelectDenseLocalEntry) : Nat :=
  selectSuperSlot q superStride * localSlotsPerSuper +
    relativeSplitSelectLocalSlotInSuper super q localStride

end RMQ.GenericSelect
