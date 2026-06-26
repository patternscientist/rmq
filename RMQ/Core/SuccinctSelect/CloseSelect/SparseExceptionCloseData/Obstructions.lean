import RMQ.Core.SuccinctSelect.CloseSelect.SparseExceptionCloseData.BuildProfile

/-!
# Sparse-exception obstruction theorems

Split implementation layer for sparse-exception close-select data.
Public declarations stay in the historical `RMQ.SuccinctSelectProposal`
namespace until the namespace-alignment cleanup pass.
-/

namespace RMQ
namespace SuccinctSelectProposal

theorem builtRectangularFalseSelectPaddedLocalCapacity_ge_size
    (shape : Cartesian.CartesianShape) :
    shape.size <=
      builtRectangularFalseSelectLocalSlotCount shape *
        sparseDenseFalseSelectLocalStride shape := by
  have hsuperStride :
      0 < sparseDenseFalseSelectSuperStride shape := by
    have hword :
        0 < SuccinctRankProposal.machineWordBits shape.bpCode.length :=
      SuccinctRankProposal.machineWordBits_pos
      shape.bpCode.length
    have hmul :
        0 <
          SuccinctRankProposal.machineWordBits shape.bpCode.length *
            SuccinctRankProposal.machineWordBits shape.bpCode.length :=
      Nat.mul_pos hword hword
    simpa [sparseDenseFalseSelectSuperStride,
      sparseDenseFalseSelectWordBits] using hmul
  have hlocalStride :
      0 < sparseDenseFalseSelectLocalStride shape := by
    unfold sparseDenseFalseSelectLocalStride
    omega
  have hocc :
      falseSelectOccurrenceCount shape <=
        builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape := by
    simpa [builtRectangularFalseSelectSuperSlotCount] using
      (falseSelectCeilDiv_mul_ge
        (n := falseSelectOccurrenceCount shape)
        (stride := sparseDenseFalseSelectSuperStride shape)
        hsuperStride)
  have hsuperLocal :
      sparseDenseFalseSelectSuperStride shape <=
        builtRectangularFalseSelectLocalSlotsPerSuper shape *
          sparseDenseFalseSelectLocalStride shape := by
    simpa [builtRectangularFalseSelectLocalSlotsPerSuper] using
      (falseSelectLocalSlotsPerSuper_mul_localStride_ge_superStride
        (superStride := sparseDenseFalseSelectSuperStride shape)
        (localStride := sparseDenseFalseSelectLocalStride shape)
        hlocalStride)
  have hmul :=
    Nat.mul_le_mul_left
      (builtRectangularFalseSelectSuperSlotCount shape) hsuperLocal
  have hcap :
      builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape <=
        builtRectangularFalseSelectLocalSlotCount shape *
          sparseDenseFalseSelectLocalStride shape := by
    simpa [builtRectangularFalseSelectLocalSlotCount,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  have hsize :
      shape.size = falseSelectOccurrenceCount shape := by
    exact (falseSelectOccurrenceCount_eq_size shape).symm
  omega

theorem builtRectangularFalseSelectPaddedSuperCapacity_ge_size
    (shape : Cartesian.CartesianShape) :
    shape.size <=
      builtRectangularFalseSelectSuperSlotCount shape *
        sparseDenseFalseSelectSuperStride shape := by
  have hocc :
      falseSelectOccurrenceCount shape <=
        builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape := by
    simpa [builtRectangularFalseSelectSuperSlotCount] using
      (falseSelectCeilDiv_mul_ge
        (n := falseSelectOccurrenceCount shape)
        (stride := sparseDenseFalseSelectSuperStride shape)
        (sparseDenseFalseSelectSuperStride_pos shape))
  have hsize :
      shape.size = falseSelectOccurrenceCount shape := by
    exact (falseSelectOccurrenceCount_eq_size shape).symm
  omega

def falseSelectRightSpine : Nat -> Cartesian.CartesianShape
  | 0 => Cartesian.CartesianShape.empty
  | n + 1 =>
      Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
        (falseSelectRightSpine n)

theorem falseSelectRightSpine_shapeOfSize (n : Nat) :
    Cartesian.ShapeOfSize n (falseSelectRightSpine n) := by
  induction n with
  | zero =>
      simp [falseSelectRightSpine]
      exact Cartesian.ShapeOfSize.empty
  | succ n ih =>
      simpa [falseSelectRightSpine, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        (Cartesian.ShapeOfSize.node
          (leftSize := 0)
          (rightSize := n)
          Cartesian.ShapeOfSize.empty ih)

theorem padded_relative_sparse_local_entries_not_littleO
    {overhead : Nat -> Nat}
    (hbound :
      forall shape : Cartesian.CartesianShape,
        builtRectangularFalseSelectLocalSlotCount shape *
            sparseDenseFalseSelectLocalStride shape <=
          overhead shape.size) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_self_le
  intro n
  let shape := falseSelectRightSpine n
  have hshapeSize : shape.size = n := by
    exact Cartesian.ShapeOfSize.size_eq
      (falseSelectRightSpine_shapeOfSize n)
  have hcap :=
    builtRectangularFalseSelectPaddedLocalCapacity_ge_size shape
  have hbudget := hbound shape
  have hcombined := Nat.le_trans hcap hbudget
  simpa [hshapeSize] using hcombined

theorem padded_relative_sparse_local_payload_not_littleO
    {overhead : Nat -> Nat} {entryWidth : Nat}
    (hwidth : 0 < entryWidth)
    (hbound :
      forall shape : Cartesian.CartesianShape,
        builtRectangularFalseSelectLocalSlotCount shape *
            sparseDenseFalseSelectLocalStride shape * entryWidth <=
          overhead shape.size) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_self_le
  intro n
  let shape := falseSelectRightSpine n
  have hshapeSize : shape.size = n := by
    exact Cartesian.ShapeOfSize.size_eq
      (falseSelectRightSpine_shapeOfSize n)
  let cellCount :=
    builtRectangularFalseSelectLocalSlotCount shape *
      sparseDenseFalseSelectLocalStride shape
  have hcap :
      shape.size <= cellCount := by
    simpa [cellCount] using
      builtRectangularFalseSelectPaddedLocalCapacity_ge_size shape
  have hwidthOne : 1 <= entryWidth := by
    omega
  have hcells :
      cellCount <= cellCount * entryWidth := by
    simpa using Nat.mul_le_mul_left cellCount hwidthOne
  have hbudget :
      cellCount * entryWidth <= overhead shape.size := by
    simpa [cellCount] using hbound shape
  have hcombined := Nat.le_trans hcap (Nat.le_trans hcells hbudget)
  simpa [hshapeSize] using hcombined

theorem padded_relative_long_super_entries_not_littleO
    {overhead : Nat -> Nat}
    (hbound :
      forall shape : Cartesian.CartesianShape,
        builtRectangularFalseSelectSuperSlotCount shape *
            sparseDenseFalseSelectSuperStride shape <=
          overhead shape.size) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_self_le
  intro n
  let shape := falseSelectRightSpine n
  have hshapeSize : shape.size = n := by
    exact Cartesian.ShapeOfSize.size_eq
      (falseSelectRightSpine_shapeOfSize n)
  have hcap := builtRectangularFalseSelectPaddedSuperCapacity_ge_size shape
  have hbudget := hbound shape
  have hcombined := Nat.le_trans hcap hbudget
  simpa [hshapeSize] using hcombined

theorem padded_relative_long_super_payload_not_littleO
    {overhead : Nat -> Nat} {entryWidth : Nat}
    (hwidth : 0 < entryWidth)
    (hbound :
      forall shape : Cartesian.CartesianShape,
        builtRectangularFalseSelectSuperSlotCount shape *
            sparseDenseFalseSelectSuperStride shape * entryWidth <=
          overhead shape.size) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_self_le
  intro n
  let shape := falseSelectRightSpine n
  have hshapeSize : shape.size = n := by
    exact Cartesian.ShapeOfSize.size_eq
      (falseSelectRightSpine_shapeOfSize n)
  let cellCount :=
    builtRectangularFalseSelectSuperSlotCount shape *
      sparseDenseFalseSelectSuperStride shape
  have hcap :
      shape.size <= cellCount := by
    simpa [cellCount] using
      builtRectangularFalseSelectPaddedSuperCapacity_ge_size shape
  have hwidthOne : 1 <= entryWidth := by
    omega
  have hcells :
      cellCount <= cellCount * entryWidth := by
    simpa using Nat.mul_le_mul_left cellCount hwidthOne
  have hbudget :
      cellCount * entryWidth <= overhead shape.size := by
    simpa [cellCount] using hbound shape
  have hcombined := Nat.le_trans hcap (Nat.le_trans hcells hbudget)
  simpa [hshapeSize] using hcombined

theorem relativeSplitSparseException_long_super_padded_payload_not_littleO
    {overhead : Nat -> Nat}
    {rankSuperOverhead rankBlockOverhead :
      Cartesian.CartesianShape -> Nat}
    (builder :
      forall shape : Cartesian.CartesianShape,
        RelativeSplitSparseExceptionFalseSelectCloseData
          shape (rankSuperOverhead shape) (rankBlockOverhead shape))
    (hpadded :
      forall shape : Cartesian.CartesianShape,
        builtRectangularFalseSelectSuperSlotCount shape *
            sparseDenseFalseSelectSuperStride shape <=
          (builder shape).longSuperRelativeEntries.length)
    (hcharged :
      forall shape : Cartesian.CartesianShape,
        (builder shape).longSuperRelativeTable.payload.length <=
          overhead shape.size)
    (hwidth :
      forall shape : Cartesian.CartesianShape,
        0 < (builder shape).longSuperRelativeWidth) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_self_le
  intro n
  let shape := falseSelectRightSpine n
  let data := builder shape
  have hshapeSize : shape.size = n := by
    exact Cartesian.ShapeOfSize.size_eq
      (falseSelectRightSpine_shapeOfSize n)
  have hcap :
      shape.size <=
        builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape :=
    builtRectangularFalseSelectPaddedSuperCapacity_ge_size shape
  have hpad :
      builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape <=
        data.longSuperRelativeEntries.length := by
    simpa [data] using hpadded shape
  have hwidthPos : 0 < data.longSuperRelativeWidth := by
    simpa [data] using hwidth shape
  have hwidthOne : 1 <= data.longSuperRelativeWidth := by
    omega
  have hentriesPayload :
      data.longSuperRelativeEntries.length <=
        data.longSuperRelativeTable.payload.length := by
    calc
      data.longSuperRelativeEntries.length <=
          data.longSuperRelativeEntries.length *
            data.longSuperRelativeWidth := by
        simpa using
          Nat.mul_le_mul_left
            data.longSuperRelativeEntries.length hwidthOne
      _ = data.longSuperRelativeTable.payload.length := by
        exact data.longSuperRelativeTable.payload_length_eq.symm
  have hbudget :
      data.longSuperRelativeTable.payload.length <=
        overhead shape.size := by
    simpa [data] using hcharged shape
  have hcombined :
      shape.size <= overhead shape.size :=
    Nat.le_trans hcap
      (Nat.le_trans hpad (Nat.le_trans hentriesPayload hbudget))
  simpa [hshapeSize] using hcombined

theorem noRelativeSplitSparseExceptionFalseSelectCloseData_with_padded_long_super_payload
    {rankSuperOverhead rankBlockOverhead :
      Cartesian.CartesianShape -> Nat}
    (builder :
      forall shape : Cartesian.CartesianShape,
        RelativeSplitSparseExceptionFalseSelectCloseData
          shape (rankSuperOverhead shape) (rankBlockOverhead shape))
    (hpadded :
      forall shape : Cartesian.CartesianShape,
        builtRectangularFalseSelectSuperSlotCount shape *
            sparseDenseFalseSelectSuperStride shape <=
          (builder shape).longSuperRelativeEntries.length)
    (hwidth :
      forall shape : Cartesian.CartesianShape,
        0 < (builder shape).longSuperRelativeWidth) :
    False := by
  have hnot :
      Not
        (SuccinctSpace.LittleOLinear
          canonicalRelativeSplitSparseExceptionFalseSelectOverhead) := by
    exact
      relativeSplitSparseException_long_super_padded_payload_not_littleO
        (overhead := canonicalRelativeSplitSparseExceptionFalseSelectOverhead)
        (builder := builder)
        hpadded
        (by
          intro shape
          let data := builder shape
          have hlongLePayload :
              data.longSuperRelativeTable.payload.length <=
                (data.superTable.payload ++
                  data.longFlagBits ++
                    data.longFlagRankData.auxPayload ++
                      data.longSuperRelativeTable.payload ++
                        data.localTable.payload ++
                          data.sparseDirectory.payload).length := by
            simp [List.length_append]
            omega
          exact Nat.le_trans hlongLePayload
            data.payload_length_le_overhead)
        hwidth
  exact hnot canonicalRelativeSplitSparseExceptionFalseSelectOverhead_littleO

theorem noBuiltRelativeSplitSparseExceptionFalseSelectCloseData_with_current_long_slot_profile :
    Not
      (exists
        (rankSuperOverhead rankBlockOverhead :
          Cartesian.CartesianShape -> Nat),
        exists builder :
          forall shape : Cartesian.CartesianShape,
            RelativeSplitSparseExceptionFalseSelectCloseData
              shape (rankSuperOverhead shape) (rankBlockOverhead shape),
          (forall shape : Cartesian.CartesianShape,
            builtRectangularFalseSelectSuperSlotCount shape *
                sparseDenseFalseSelectSuperStride shape <=
              (builder shape).longSuperRelativeEntries.length) /\
          (forall shape : Cartesian.CartesianShape,
            0 < (builder shape).longSuperRelativeWidth)) := by
  rintro
    ⟨rankSuperOverhead, rankBlockOverhead, builder,
      hcurrentLongSlotCoverage, hpositiveLongWidth⟩
  exact
    noRelativeSplitSparseExceptionFalseSelectCloseData_with_padded_long_super_payload
      (rankSuperOverhead := rankSuperOverhead)
      (rankBlockOverhead := rankBlockOverhead)
      (builder := builder)
      hcurrentLongSlotCoverage
      hpositiveLongWidth


end SuccinctSelectProposal
end RMQ
