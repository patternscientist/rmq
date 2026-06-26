import RMQ.Core.SuccinctSelect.CloseSelect.Basic

/-!
# Sparse/dense slot basics

Split implementation layer for built sparse/dense close-select routing.
Public declarations stay in the historical `RMQ.SuccinctSelectProposal`
namespace until the namespace-alignment cleanup pass.
-/

namespace RMQ
namespace SuccinctSelectProposal

/-!
### Built sparse/dense false-select routing helpers

These helpers support the retained relative-split false-select construction.
The older four-field locator record and `SparseDenseFalseSelectCloseData`
profile were pruned; this section now keeps only the shared arithmetic and
counting facts still consumed by the live relative-split capstone.
-/

def falseSelectSuperSlot (q superStride : Nat) : Nat :=
  q / superStride

/-- Number of rectangular local slots reserved for each super interval. -/
def falseSelectLocalSlotsPerSuper
    (superStride localStride : Nat) : Nat :=
  (superStride + localStride - 1) / localStride

def falseSelectOccurrenceCount
    (shape : Cartesian.CartesianShape) : Nat :=
  RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length

theorem falseSelectOccurrenceCount_eq_size
    (shape : Cartesian.CartesianShape) :
    falseSelectOccurrenceCount shape = shape.size := by
  exact SuccinctSpace.bpCode_rankFalse_full shape

def falseSelectCeilDiv (n stride : Nat) : Nat :=
  (n + stride - 1) / stride

def builtRectangularFalseSelectSuperSlotCount
    (shape : Cartesian.CartesianShape) : Nat :=
  falseSelectCeilDiv (falseSelectOccurrenceCount shape)
    (sparseDenseFalseSelectSuperStride shape)

def builtRectangularFalseSelectLocalSlotsPerSuper
    (shape : Cartesian.CartesianShape) : Nat :=
  falseSelectLocalSlotsPerSuper
    (sparseDenseFalseSelectSuperStride shape)
    (sparseDenseFalseSelectLocalStride shape)

def builtRectangularFalseSelectLocalSlotCount
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRectangularFalseSelectSuperSlotCount shape *
    builtRectangularFalseSelectLocalSlotsPerSuper shape

theorem sparseDenseFalseSelectWordBits_pos
    (shape : Cartesian.CartesianShape) :
    0 < sparseDenseFalseSelectWordBits shape := by
  simp [sparseDenseFalseSelectWordBits,
    SuccinctRankProposal.machineWordBits_pos]

theorem sparseDenseFalseSelectSuperStride_pos
    (shape : Cartesian.CartesianShape) :
    0 < sparseDenseFalseSelectSuperStride shape := by
  unfold sparseDenseFalseSelectSuperStride
  exact Nat.mul_pos (sparseDenseFalseSelectWordBits_pos shape)
    (sparseDenseFalseSelectWordBits_pos shape)

theorem sparseDenseFalseSelectLocalStride_pos
    (shape : Cartesian.CartesianShape) :
    0 < sparseDenseFalseSelectLocalStride shape := by
  unfold sparseDenseFalseSelectLocalStride
  omega

theorem builtRectangularFalseSelectLocalSlotsPerSuper_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtRectangularFalseSelectLocalSlotsPerSuper shape := by
  unfold builtRectangularFalseSelectLocalSlotsPerSuper
    falseSelectLocalSlotsPerSuper
  exact Nat.div_pos
    (by
      have hsuper := sparseDenseFalseSelectSuperStride_pos shape
      omega)
    (sparseDenseFalseSelectLocalStride_pos shape)

def builtRectangularFalseSelectLocalSlotInSuperOfGlobal
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  globalLocalSlot -
    (globalLocalSlot /
      builtRectangularFalseSelectLocalSlotsPerSuper shape) *
        builtRectangularFalseSelectLocalSlotsPerSuper shape

def builtRectangularFalseSelectLocalBaseOccurrence
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  let superSlot :=
    globalLocalSlot /
      builtRectangularFalseSelectLocalSlotsPerSuper shape
  let localSlotInSuper :=
    builtRectangularFalseSelectLocalSlotInSuperOfGlobal
      shape globalLocalSlot
  superSlot * sparseDenseFalseSelectSuperStride shape +
    localSlotInSuper * sparseDenseFalseSelectLocalStride shape

theorem builtRectangularFalseSelectLocalBaseOccurrence_mod
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    builtRectangularFalseSelectLocalBaseOccurrence
        shape globalLocalSlot =
      (globalLocalSlot /
          builtRectangularFalseSelectLocalSlotsPerSuper shape) *
          sparseDenseFalseSelectSuperStride shape +
        (globalLocalSlot %
            builtRectangularFalseSelectLocalSlotsPerSuper shape) *
          sparseDenseFalseSelectLocalStride shape := by
  unfold builtRectangularFalseSelectLocalBaseOccurrence
    builtRectangularFalseSelectLocalSlotInSuperOfGlobal
  rw [Nat.mod_eq_sub_div_mul]

theorem builtRectangularFalseSelectLocalBaseOccurrence_lt_superBoundary
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    builtRectangularFalseSelectLocalBaseOccurrence
        shape globalLocalSlot <
      (globalLocalSlot /
          builtRectangularFalseSelectLocalSlotsPerSuper shape) *
          sparseDenseFalseSelectSuperStride shape +
        sparseDenseFalseSelectSuperStride shape := by
  let slots := builtRectangularFalseSelectLocalSlotsPerSuper shape
  let superStride := sparseDenseFalseSelectSuperStride shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let q := globalLocalSlot / slots
  let r := globalLocalSlot % slots
  have hslots : 0 < slots := by
    simpa [slots] using
      builtRectangularFalseSelectLocalSlotsPerSuper_pos shape
  have hlocal : 0 < localStride := by
    simpa [localStride] using sparseDenseFalseSelectLocalStride_pos shape
  have hr : r < slots := Nat.mod_lt _ hslots
  have hbase :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot =
        q * superStride + r * localStride := by
    simpa [q, r, slots, superStride, localStride] using
      builtRectangularFalseSelectLocalBaseOccurrence_mod
        shape globalLocalSlot
  have hceil :
      (r + 1) * localStride <=
        superStride + localStride - 1 := by
    have hle : r + 1 <= slots := by omega
    have hleDiv :
        r + 1 <=
          (superStride + localStride - 1) / localStride := by
      simpa [slots, superStride, localStride,
        builtRectangularFalseSelectLocalSlotsPerSuper,
        falseSelectLocalSlotsPerSuper] using hle
    exact Nat.mul_le_of_le_div localStride (r + 1)
      (superStride + localStride - 1) hleDiv
  have hrLocal : r * localStride < superStride := by
    rw [Nat.add_mul, Nat.one_mul] at hceil
    omega
  rw [hbase]
  simpa [q, slots, superStride] using (by omega :
    q * superStride + r * localStride <
      q * superStride + superStride)

theorem builtRectangularFalseSelectLocalBaseOccurrence_le_next_base
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    builtRectangularFalseSelectLocalBaseOccurrence
        shape globalLocalSlot <=
      builtRectangularFalseSelectLocalBaseOccurrence
        shape (globalLocalSlot + 1) := by
  let slots := builtRectangularFalseSelectLocalSlotsPerSuper shape
  let superStride := sparseDenseFalseSelectSuperStride shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let q := globalLocalSlot / slots
  let r := globalLocalSlot % slots
  have hslots : 0 < slots := by
    simpa [slots] using
      builtRectangularFalseSelectLocalSlotsPerSuper_pos shape
  have hlocal : 0 < localStride := by
    simpa [localStride] using sparseDenseFalseSelectLocalStride_pos shape
  have hr : r < slots := Nat.mod_lt _ hslots
  have hdecomp : globalLocalSlot = q * slots + r := by
    have h := Nat.div_add_mod globalLocalSlot slots
    simpa [q, r, Nat.mul_comm] using h.symm
  have hbase :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot =
        q * superStride + r * localStride := by
    simpa [q, r, slots, superStride, localStride] using
      builtRectangularFalseSelectLocalBaseOccurrence_mod
        shape globalLocalSlot
  by_cases hnextLocal : r + 1 < slots
  · have hn1 :
        globalLocalSlot + 1 = q * slots + (r + 1) := by
      omega
    have hdiv :
        (globalLocalSlot + 1) / slots = q := by
      calc
        (globalLocalSlot + 1) / slots =
            (q * slots + (r + 1)) / slots := by rw [hn1]
        _ = ((r + 1) + slots * q) / slots := by
              rw [Nat.mul_comm, Nat.add_comm]
        _ = (r + 1) / slots + q := by
              exact Nat.add_mul_div_left (r + 1) q hslots
        _ = q := by
              rw [Nat.div_eq_of_lt hnextLocal]
              omega
    have hmod :
        (globalLocalSlot + 1) % slots = r + 1 := by
      calc
        (globalLocalSlot + 1) % slots =
            (q * slots + (r + 1)) % slots := by rw [hn1]
        _ = r + 1 := by
              exact Nat.mul_add_mod_of_lt hnextLocal
    have hnext :
        builtRectangularFalseSelectLocalBaseOccurrence
            shape (globalLocalSlot + 1) =
          q * superStride + (r + 1) * localStride := by
      rw [builtRectangularFalseSelectLocalBaseOccurrence_mod]
      simp [q, slots, superStride, localStride, hdiv, hmod]
    rw [hbase, hnext]
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · have hlast : r + 1 = slots := by omega
    have hn1 :
        globalLocalSlot + 1 = (q + 1) * slots := by
      rw [hdecomp, Nat.add_mul, Nat.one_mul]
      omega
    have hdiv :
        (globalLocalSlot + 1) / slots = q + 1 := by
      rw [hn1]
      exact Nat.mul_div_left (q + 1) hslots
    have hmod :
        (globalLocalSlot + 1) % slots = 0 := by
      rw [hn1]
      exact Nat.mul_mod_left (q + 1) slots
    have hnext :
        builtRectangularFalseSelectLocalBaseOccurrence
            shape (globalLocalSlot + 1) =
          (q + 1) * superStride := by
      rw [builtRectangularFalseSelectLocalBaseOccurrence_mod]
      simp [q, slots, superStride, hdiv, hmod]
    have hboundary :=
      builtRectangularFalseSelectLocalBaseOccurrence_lt_superBoundary
        shape globalLocalSlot
    rw [hnext]
    rw [Nat.add_mul, Nat.one_mul]
    simpa [q, slots, superStride] using Nat.le_of_lt hboundary

def falseSelectPositions (bits : List Bool) (base count : Nat) :
    List Nat :=
  (List.range count).map fun offset =>
    (RMQ.Succinct.select false bits (base + offset)).getD bits.length

def builtRelativeSplitFalseSelectPosition
    (shape : Cartesian.CartesianShape) (occurrence : Nat) : Nat :=
  (RMQ.Succinct.select false shape.bpCode occurrence).getD
    shape.bpCode.length

def builtRelativeSplitFalseSelectLocalEndOccurrence
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  Nat.min
    (builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot +
      sparseDenseFalseSelectLocalStride shape)
    (falseSelectOccurrenceCount shape)

def builtRelativeSplitFalseSelectLocalSpan
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  let baseOccurrence :=
    builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot
  let endOccurrence :=
    builtRelativeSplitFalseSelectLocalEndOccurrence shape globalLocalSlot
  let basePosition :=
    builtRelativeSplitFalseSelectPosition shape baseOccurrence
  let lastPosition :=
    builtRelativeSplitFalseSelectPosition shape (endOccurrence - 1)
  lastPosition + 1 - basePosition

def builtRelativeSplitFalseSelectLocalIsSparse
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Bool :=
  decide
    (sparseDenseFalseSelectWordBits shape <
      builtRelativeSplitFalseSelectLocalSpan shape globalLocalSlot)

def builtRelativeSplitFalseSelectSuperBaseOccurrence
    (shape : Cartesian.CartesianShape) (superSlot : Nat) : Nat :=
  superSlot * sparseDenseFalseSelectSuperStride shape

def builtRelativeSplitFalseSelectSuperEndOccurrence
    (shape : Cartesian.CartesianShape) (superSlot : Nat) : Nat :=
  Nat.min
    (builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
      sparseDenseFalseSelectSuperStride shape)
    (falseSelectOccurrenceCount shape)

def builtRelativeSplitFalseSelectSuperSpan
    (shape : Cartesian.CartesianShape) (superSlot : Nat) : Nat :=
  let baseOccurrence :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
  let endOccurrence :=
    builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot
  let basePosition :=
    builtRelativeSplitFalseSelectPosition shape baseOccurrence
  let lastPosition :=
    builtRelativeSplitFalseSelectPosition shape (endOccurrence - 1)
  lastPosition + 1 - basePosition

def builtRelativeSplitFalseSelectSuperIsLong
    (shape : Cartesian.CartesianShape) (superSlot : Nat) : Bool :=
  decide
    (sparseDenseFalseSelectSuperLongSpan shape <
      builtRelativeSplitFalseSelectSuperSpan shape superSlot)

def builtRelativeSplitFalseSelectLocalSuperSlot
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  globalLocalSlot /
    builtRectangularFalseSelectLocalSlotsPerSuper shape

def builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  Nat.min
    (builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot +
      sparseDenseFalseSelectLocalStride shape)
    (builtRelativeSplitFalseSelectSuperEndOccurrence shape
      (builtRelativeSplitFalseSelectLocalSuperSlot
        shape globalLocalSlot))

def builtRelativeSplitFalseSelectShortSuperLocalSpan
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  let baseOccurrence :=
    builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot
  let endOccurrence :=
    builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
      shape globalLocalSlot
  let basePosition :=
    builtRelativeSplitFalseSelectPosition shape baseOccurrence
  let lastPosition :=
    builtRelativeSplitFalseSelectPosition shape (endOccurrence - 1)
  lastPosition + 1 - basePosition

theorem builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_le_next_base
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
        shape globalLocalSlot <=
      builtRectangularFalseSelectLocalBaseOccurrence
        shape (globalLocalSlot + 1) := by
  let slots := builtRectangularFalseSelectLocalSlotsPerSuper shape
  let superStride := sparseDenseFalseSelectSuperStride shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let q := globalLocalSlot / slots
  let r := globalLocalSlot % slots
  have hslots : 0 < slots := by
    simpa [slots] using
      builtRectangularFalseSelectLocalSlotsPerSuper_pos shape
  have hr : r < slots := Nat.mod_lt _ hslots
  have hdecomp : globalLocalSlot = q * slots + r := by
    have h := Nat.div_add_mod globalLocalSlot slots
    simpa [q, r, Nat.mul_comm] using h.symm
  have hbase :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot =
        q * superStride + r * localStride := by
    simpa [q, r, slots, superStride, localStride] using
      builtRectangularFalseSelectLocalBaseOccurrence_mod
        shape globalLocalSlot
  have hendBase :
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
          shape globalLocalSlot <=
        builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot +
          localStride := by
    unfold builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
    exact Nat.min_le_left _ _
  have hendSuper :
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
          shape globalLocalSlot <=
        q * superStride + superStride := by
    have hsuperEnd :
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
            (builtRelativeSplitFalseSelectLocalSuperSlot
              shape globalLocalSlot) <=
          q * superStride + superStride := by
      unfold builtRelativeSplitFalseSelectSuperEndOccurrence
        builtRelativeSplitFalseSelectSuperBaseOccurrence
        builtRelativeSplitFalseSelectLocalSuperSlot
      exact Nat.min_le_left _ _
    exact Nat.le_trans (Nat.min_le_right _ _) (by
      simpa [q, slots, superStride] using hsuperEnd)
  by_cases hnextLocal : r + 1 < slots
  · have hn1 :
        globalLocalSlot + 1 = q * slots + (r + 1) := by
      omega
    have hdiv :
        (globalLocalSlot + 1) / slots = q := by
      calc
        (globalLocalSlot + 1) / slots =
            (q * slots + (r + 1)) / slots := by rw [hn1]
        _ = ((r + 1) + slots * q) / slots := by
              rw [Nat.mul_comm, Nat.add_comm]
        _ = (r + 1) / slots + q := by
              exact Nat.add_mul_div_left (r + 1) q hslots
        _ = q := by
              rw [Nat.div_eq_of_lt hnextLocal]
              omega
    have hmod :
        (globalLocalSlot + 1) % slots = r + 1 := by
      calc
        (globalLocalSlot + 1) % slots =
            (q * slots + (r + 1)) % slots := by rw [hn1]
        _ = r + 1 := by
              exact Nat.mul_add_mod_of_lt hnextLocal
    have hnext :
        builtRectangularFalseSelectLocalBaseOccurrence
            shape (globalLocalSlot + 1) =
          q * superStride + (r + 1) * localStride := by
      rw [builtRectangularFalseSelectLocalBaseOccurrence_mod]
      simp [q, slots, superStride, localStride, hdiv, hmod]
    rw [hnext]
    have h := hendBase
    rw [hbase] at h
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h
  · have hlast : r + 1 = slots := by omega
    have hn1 :
        globalLocalSlot + 1 = (q + 1) * slots := by
      rw [hdecomp, Nat.add_mul, Nat.one_mul]
      omega
    have hdiv :
        (globalLocalSlot + 1) / slots = q + 1 := by
      rw [hn1]
      exact Nat.mul_div_left (q + 1) hslots
    have hmod :
        (globalLocalSlot + 1) % slots = 0 := by
      rw [hn1]
      exact Nat.mul_mod_left (q + 1) slots
    have hnext :
        builtRectangularFalseSelectLocalBaseOccurrence
            shape (globalLocalSlot + 1) =
          (q + 1) * superStride := by
      rw [builtRectangularFalseSelectLocalBaseOccurrence_mod]
      simp [q, slots, superStride, hdiv, hmod]
    rw [hnext]
    have h := hendSuper
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h

def builtRelativeSplitFalseSelectLocalIsSparseException
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Bool :=
  (! builtRelativeSplitFalseSelectSuperIsLong shape
      (builtRelativeSplitFalseSelectLocalSuperSlot
        shape globalLocalSlot)) &&
    decide
      (sparseDenseFalseSelectWordBits shape <
        builtRelativeSplitFalseSelectShortSuperLocalSpan
          shape globalLocalSlot)

def falseSelectRelativeOffsetsOrZero
    (bits : List Bool) (baseOccurrence count endOccurrence
      basePosition : Nat) : List Nat :=
  (List.range count).map fun offset =>
    if baseOccurrence + offset < endOccurrence then
      match RMQ.Succinct.select false bits (baseOccurrence + offset) with
      | some pos => pos - basePosition
      | none => 0
    else
      0

def builtRelativeSplitFalseSelectSparseExceptionFlagBits
    (shape : Cartesian.CartesianShape) : List Bool :=
  (List.range (builtRectangularFalseSelectLocalSlotCount shape)).map
    (builtRelativeSplitFalseSelectLocalIsSparseException shape)

def builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
    (shape : Cartesian.CartesianShape) : Nat :=
  Nat.min (builtRectangularFalseSelectLocalSlotCount shape)
    (falseSelectOccurrenceCount shape)

def builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
    (shape : Cartesian.CartesianShape) : List Bool :=
  (List.range
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
        shape)).map
    (builtRelativeSplitFalseSelectLocalIsSparseException shape)

def builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    List Nat :=
  if builtRelativeSplitFalseSelectLocalIsSparseException
      shape globalLocalSlot then
    let superSlot :=
      builtRelativeSplitFalseSelectLocalSuperSlot shape globalLocalSlot
    let baseOccurrence :=
      builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot
    let basePosition :=
      builtRelativeSplitFalseSelectPosition shape baseOccurrence
    falseSelectRelativeOffsetsOrZero shape.bpCode baseOccurrence
      (sparseDenseFalseSelectLocalStride shape)
      (builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot)
      basePosition
  else
    []

def builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
    (shape : Cartesian.CartesianShape) : List Nat :=
  (List.range (builtRectangularFalseSelectLocalSlotCount shape)).flatMap
    (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
      shape)

def builtRelativeSplitFalseSelectSparseExceptionRelativeWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRankProposal.machineWordBits
    (Nat.min shape.bpCode.length
      (sparseDenseFalseSelectSuperLongSpan shape))


end SuccinctSelectProposal
end RMQ
