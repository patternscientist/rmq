import RMQ.Core.GenericSelect.Slots

/-!
# Generic select entry layer

This module contains the dense/sparse entry construction and classification
flag lists used by the generic sparse-exception select directory.
-/

namespace RMQ.GenericSelect

open SuccinctSpace SuccinctRank

/-! ## Entry / table data layer (Tier 2 back half)

Target-parametric super/local entries and classification flag vectors for the
generic sparse-exception select construction. -/

/-- Super-sample dense-local entry: base occurrence at a super-stride boundary,
its word index/offset, and a `rankBefore` flag marking long supers. -/
def superEntry (bits : List Bool) (target : Bool) (superSlot : Nat) :
    SparseDenseSelectDenseLocalEntry :=
  let baseOccurrence := superSlot * superStride bits.length
  let basePosition := position bits target baseOccurrence
  let wordSize := wordBits bits.length
  { baseOccurrence := baseOccurrence
    baseWordIndex := basePosition / wordSize
    rankBefore := if superIsLong bits target superSlot then 1 else 0
    firstOffset := basePosition - (basePosition / wordSize) * wordSize }

def superEntries (bits : List Bool) (target : Bool) :
    List SparseDenseSelectDenseLocalEntry :=
  (List.range (superSlotCount bits target)).map (superEntry bits target)

theorem superEntries_length (bits : List Bool) (target : Bool) :
    (superEntries bits target).length = superSlotCount bits target := by
  simp [superEntries]

theorem superEntries_get? (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hslot : superSlot < superSlotCount bits target) :
    (superEntries bits target)[superSlot]? =
      some (superEntry bits target superSlot) := by
  simp [superEntries, List.getElem?_map, List.getElem?_range hslot]

/-- A compact local entry carries real data iff its super is short (dense) and
its base occurrence is in range. -/
def compactLocalEntryIsLive (bits : List Bool) (target : Bool)
    (globalLocalSlot : Nat) : Bool :=
  (! superIsLong bits target (localSuperSlot bits.length globalLocalSlot)) &&
    decide (localBaseOccurrence bits.length globalLocalSlot <
      occurrenceCount bits target)

/-- Compact dense-local entry, stored relative to its owning super's base. -/
def localEntry (bits : List Bool) (target : Bool) (globalLocalSlot : Nat) :
    SparseDenseSelectDenseLocalEntry :=
  if compactLocalEntryIsLive bits target globalLocalSlot then
    let superSlot := localSuperSlot bits.length globalLocalSlot
    let superBaseOcc := superSlot * superStride bits.length
    let superBasePosition := position bits target superBaseOcc
    let baseOccurrence := localBaseOccurrence bits.length globalLocalSlot
    let basePosition := position bits target baseOccurrence
    let wordSize := wordBits bits.length
    { baseOccurrence := baseOccurrence - superBaseOcc
      baseWordIndex := basePosition / wordSize - superBasePosition / wordSize
      rankBefore :=
        if localIsSparseException bits target globalLocalSlot then 1 else 0
      firstOffset := basePosition - (basePosition / wordSize) * wordSize }
  else
    { baseOccurrence := 0
      baseWordIndex := 0
      rankBefore := 0
      firstOffset := 0 }

def localEntries (bits : List Bool) (target : Bool) :
    List SparseDenseSelectDenseLocalEntry :=
  (List.range (localSlotCount bits target)).map (localEntry bits target)

theorem localEntries_length (bits : List Bool) (target : Bool) :
    (localEntries bits target).length = localSlotCount bits target := by
  simp [localEntries]

theorem localEntries_get? (bits : List Bool) (target : Bool)
    {globalLocalSlot : Nat}
    (hslot : globalLocalSlot < localSlotCount bits target) :
    (localEntries bits target)[globalLocalSlot]? =
      some (localEntry bits target globalLocalSlot) := by
  simp [localEntries, List.getElem?_map, List.getElem?_range hslot]

/-- Per-local-slot "is sparse" flag vector. -/
def sparseFlagBits (bits : List Bool) (target : Bool) : List Bool :=
  (List.range (localSlotCount bits target)).map (localIsSparse bits target)

theorem sparseFlagBits_length (bits : List Bool) (target : Bool) :
    (sparseFlagBits bits target).length = localSlotCount bits target := by
  simp [sparseFlagBits]

theorem sparseFlagBits_get? (bits : List Bool) (target : Bool)
    {globalLocalSlot : Nat}
    (hslot : globalLocalSlot < localSlotCount bits target) :
    (sparseFlagBits bits target)[globalLocalSlot]? =
      some (localIsSparse bits target globalLocalSlot) := by
  simp [sparseFlagBits, List.getElem?_map, List.getElem?_range hslot]

end RMQ.GenericSelect
