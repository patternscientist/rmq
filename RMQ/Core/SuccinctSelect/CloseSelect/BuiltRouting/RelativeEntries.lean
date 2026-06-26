import RMQ.Core.SuccinctSelect.CloseSelect.BuiltRouting.WidthBounds

/-!
# Sparse exception relative entries

Split implementation layer for built sparse/dense close-select routing.
Public declarations stay in the historical `RMQ.SuccinctSelect`
namespace.
-/

namespace RMQ
namespace SuccinctSelect

theorem falseSelectRelativeOffsetsOrZero_length
    (bits : List Bool) (baseOccurrence count endOccurrence
      basePosition : Nat) :
    (falseSelectRelativeOffsetsOrZero bits baseOccurrence count
      endOccurrence basePosition).length = count := by
  simp [falseSelectRelativeOffsetsOrZero]

theorem builtRelativeSplitFalseSelectSparseExceptionFlagBits_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape).length =
      builtRectangularFalseSelectLocalSlotCount shape := by
  simp [builtRelativeSplitFalseSelectSparseExceptionFlagBits]

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
      shape).length =
      builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
        shape := by
  simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits]

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_full
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
        shape <=
      builtRectangularFalseSelectLocalSlotCount shape := by
  unfold builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
  exact Nat.min_le_left _ _

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_count
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
        shape <=
      falseSelectOccurrenceCount shape := by
  unfold builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
  exact Nat.min_le_right _ _

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_get?
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot <
        builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
          shape) :
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
        shape)[globalLocalSlot]? =
      some
        (builtRelativeSplitFalseSelectLocalIsSparseException
          shape globalLocalSlot) := by
  simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits,
    List.getElem?_map, List.getElem?_range hslot]

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_prefix_eq
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot <=
        builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
          shape) :
    RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
          shape) globalLocalSlot =
      RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
        globalLocalSlot := by
  have htake :
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
          shape) =
        (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape).take
          (builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
            shape) := by
    apply List.ext_getElem?
    intro i
    by_cases hi :
        i <
          builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
            shape
    · have hfull :
          i < builtRectangularFalseSelectLocalSlotCount shape := by
        exact Nat.lt_of_lt_of_le hi
          (builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_full
            shape)
      simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits,
        builtRelativeSplitFalseSelectSparseExceptionFlagBits,
        List.getElem?_map, List.getElem?_range hfull, hi]
    · have heff :
          (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
            shape)[i]? = none := by
        rw [List.getElem?_eq_none_iff]
        simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits,
          Nat.le_of_not_gt hi]
      have htakeNone :
          ((builtRelativeSplitFalseSelectSparseExceptionFlagBits shape).take
            (builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
              shape))[i]? = none := by
        rw [List.getElem?_eq_none_iff]
        simp [List.length_take,
          builtRelativeSplitFalseSelectSparseExceptionFlagBits_length,
          builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_full
            shape,
          Nat.le_of_not_gt hi]
      rw [heff, htakeNone]
  rw [htake]
  exact
    RMQ.Succinct.rankPrefix_take_eq_of_le
      true (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
      (n :=
        builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
          shape)
      (limit := globalLocalSlot)
      (by
        rw [List.length_take]
        rw [builtRelativeSplitFalseSelectSparseExceptionFlagBits_length]
        exact Nat.le_min.mpr
          ⟨hslot,
            Nat.le_trans hslot
              (builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_full
                shape)⟩)

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot_length
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
      shape globalLocalSlot).length =
      if builtRelativeSplitFalseSelectLocalIsSparseException
          shape globalLocalSlot then
        sparseDenseFalseSelectLocalStride shape
      else
        0 := by
  by_cases h :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = true
  · simp [builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot,
      h, falseSelectRelativeOffsetsOrZero_length]
  · have hfalse :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = false := by
      cases hflag :
          builtRelativeSplitFalseSelectLocalIsSparseException
            shape globalLocalSlot
      · rfl
      · contradiction
    simp [builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot,
      hfalse]

theorem builtRelativeSplitFalseSelectSuperIsLong_false_span_le
    (shape : Cartesian.CartesianShape) (superSlot : Nat)
    (hshort :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = false) :
    builtRelativeSplitFalseSelectSuperSpan shape superSlot <=
      sparseDenseFalseSelectSuperLongSpan shape := by
  unfold builtRelativeSplitFalseSelectSuperIsLong at hshort
  by_cases hlt :
      sparseDenseFalseSelectSuperLongSpan shape <
        builtRelativeSplitFalseSelectSuperSpan shape superSlot
  · simp [hlt] at hshort
  · omega

theorem builtRelativeSplitFalseSelectLocalIsSparseException_true_short
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat)
    (hflag :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = true) :
    builtRelativeSplitFalseSelectSuperIsLong shape
        (builtRelativeSplitFalseSelectLocalSuperSlot
          shape globalLocalSlot) = false /\
      sparseDenseFalseSelectWordBits shape <
        builtRelativeSplitFalseSelectShortSuperLocalSpan
          shape globalLocalSlot := by
  unfold builtRelativeSplitFalseSelectLocalIsSparseException at hflag
  cases hlong :
      builtRelativeSplitFalseSelectSuperIsLong shape
        (builtRelativeSplitFalseSelectLocalSuperSlot
          shape globalLocalSlot)
  · simp [hlong] at hflag
    exact ⟨rfl, hflag⟩
  · simp [hlong] at hflag

theorem falseSelect_occurrence_lt_count_of_select
    (shape : Cartesian.CartesianShape) {occurrence pos : Nat}
    (hselect :
      RMQ.Succinct.select false shape.bpCode occurrence = some pos) :
    occurrence < falseSelectOccurrenceCount shape := by
  have hsucc := rankPrefix_succ_of_select hselect
  have hpos : pos < shape.bpCode.length :=
    RMQ.Succinct.select_bounds hselect
  have hmono :
      RMQ.Succinct.rankPrefix false shape.bpCode (pos + 1) <=
        RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length :=
    RMQ.Succinct.rankPrefix_mono_limit false shape.bpCode
      (Nat.succ_le_of_lt hpos)
  rw [hsucc] at hmono
  have hcount : occurrence + 1 <= falseSelectOccurrenceCount shape := by
    simpa [falseSelectOccurrenceCount] using hmono
  omega

theorem falseSelect_exists_of_lt_occurrence_count
    (shape : Cartesian.CartesianShape) {occurrence : Nat}
    (hocc : occurrence < falseSelectOccurrenceCount shape) :
    exists pos,
      RMQ.Succinct.select false shape.bpCode occurrence = some pos := by
  simpa [falseSelectOccurrenceCount] using
    select_exists_of_lt_rankPrefix
      (target := false) (bits := shape.bpCode)
      (occurrence := occurrence) (limit := shape.bpCode.length)
      hocc

theorem builtRelativeSplitFalseSelectPosition_eq_of_select
    (shape : Cartesian.CartesianShape) {occurrence pos : Nat}
    (hselect :
      RMQ.Succinct.select false shape.bpCode occurrence = some pos) :
    builtRelativeSplitFalseSelectPosition shape occurrence = pos := by
  simp [builtRelativeSplitFalseSelectPosition, hselect]

theorem builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
    (shape : Cartesian.CartesianShape) {occurrence : Nat}
    (hcount : falseSelectOccurrenceCount shape <= occurrence) :
    builtRelativeSplitFalseSelectPosition shape occurrence =
      shape.bpCode.length := by
  unfold builtRelativeSplitFalseSelectPosition
  have hnone :
      RMQ.Succinct.select false shape.bpCode occurrence = none :=
    select_none_of_rankPrefix_length_le (target := false)
      (bits := shape.bpCode) (occurrence := occurrence)
      (by simpa [falseSelectOccurrenceCount] using hcount)
  simp [hnone]

theorem builtRelativeSplitFalseSelectPosition_mono
    (shape : Cartesian.CartesianShape) {lo hi : Nat}
    (hle : lo <= hi) :
    builtRelativeSplitFalseSelectPosition shape lo <=
      builtRelativeSplitFalseSelectPosition shape hi := by
  by_cases hhi : hi < falseSelectOccurrenceCount shape
  · have hlo : lo < falseSelectOccurrenceCount shape := by omega
    rcases falseSelect_exists_of_lt_occurrence_count
        shape hlo with ⟨loPos, hloSelect⟩
    rcases falseSelect_exists_of_lt_occurrence_count
        shape hhi with ⟨hiPos, hhiSelect⟩
    have hmono :
        loPos <= hiPos :=
      select_index_mono (target := false) (bits := shape.bpCode)
        (lo := lo) (hi := hi) hle hloSelect hhiSelect
    rw [builtRelativeSplitFalseSelectPosition_eq_of_select
      shape hloSelect]
    rw [builtRelativeSplitFalseSelectPosition_eq_of_select
      shape hhiSelect]
    exact hmono
  · have hhiCount : falseSelectOccurrenceCount shape <= hi := by
      omega
    rw [builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
      shape hhiCount]
    by_cases hlo : lo < falseSelectOccurrenceCount shape
    · rcases falseSelect_exists_of_lt_occurrence_count
        shape hlo with ⟨loPos, hloSelect⟩
      rw [builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hloSelect]
      exact Nat.le_of_lt (RMQ.Succinct.select_bounds hloSelect)
    · have hloCount : falseSelectOccurrenceCount shape <= lo := by
        omega
      rw [builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
        shape hloCount]
      exact Nat.le_refl _

theorem falseSelectOccurrenceCount_pos_of_rectangular_local_slot
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape) :
    0 < falseSelectOccurrenceCount shape := by
  by_cases hpos : 0 < falseSelectOccurrenceCount shape
  · exact hpos
  · have hcountZero : falseSelectOccurrenceCount shape = 0 := by omega
    have hsuperZero :
        builtRectangularFalseSelectSuperSlotCount shape = 0 := by
      unfold builtRectangularFalseSelectSuperSlotCount falseSelectCeilDiv
      rw [hcountZero]
      have hstride := sparseDenseFalseSelectSuperStride_pos shape
      have hlt :
          sparseDenseFalseSelectSuperStride shape - 1 <
            sparseDenseFalseSelectSuperStride shape :=
        Nat.pred_lt (Nat.ne_of_gt hstride)
      simpa using Nat.div_eq_of_lt hlt
    have hlocalZero :
        builtRectangularFalseSelectLocalSlotCount shape = 0 := by
      simp [builtRectangularFalseSelectLocalSlotCount, hsuperZero]
    omega

theorem builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_le_count
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
        shape globalLocalSlot <=
      falseSelectOccurrenceCount shape := by
  unfold builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
  exact Nat.le_trans (Nat.min_le_right _ _) (by
    unfold builtRelativeSplitFalseSelectSuperEndOccurrence
    exact Nat.min_le_right _ _)

theorem builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_pos
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape) :
    0 <
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
        shape globalLocalSlot := by
  have hcountPos :=
    falseSelectOccurrenceCount_pos_of_rectangular_local_slot
      shape hslot
  have hlocalPos := sparseDenseFalseSelectLocalStride_pos shape
  have hsuperStridePos := sparseDenseFalseSelectSuperStride_pos shape
  have hsuperEndPos :
      0 <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          (builtRelativeSplitFalseSelectLocalSuperSlot
            shape globalLocalSlot) := by
    unfold builtRelativeSplitFalseSelectSuperEndOccurrence
      builtRelativeSplitFalseSelectSuperBaseOccurrence
    exact Nat.lt_min.mpr ⟨by omega, hcountPos⟩
  unfold builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
  exact Nat.lt_min.mpr ⟨by omega, hsuperEndPos⟩

theorem builtRelativeSplitFalseSelectShortSuperLocalBase_lt_end_of_base_lt_count
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat)
    (hbaseCount :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot <
        falseSelectOccurrenceCount shape) :
    builtRectangularFalseSelectLocalBaseOccurrence
        shape globalLocalSlot <
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
        shape globalLocalSlot := by
  have hlocalPos := sparseDenseFalseSelectLocalStride_pos shape
  have hboundary :=
    builtRectangularFalseSelectLocalBaseOccurrence_lt_superBoundary
      shape globalLocalSlot
  have hsuperEnd :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          (builtRelativeSplitFalseSelectLocalSuperSlot
            shape globalLocalSlot) := by
    unfold builtRelativeSplitFalseSelectSuperEndOccurrence
      builtRelativeSplitFalseSelectSuperBaseOccurrence
      builtRelativeSplitFalseSelectLocalSuperSlot
    exact Nat.lt_min.mpr ⟨by
      simpa using hboundary, hbaseCount⟩
  unfold builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
  exact Nat.lt_min.mpr ⟨by omega, hsuperEnd⟩

theorem builtRelativeSplitFalseSelectShortSuperLocalSpan_le_next_gap
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape) :
    builtRelativeSplitFalseSelectShortSuperLocalSpan
        shape globalLocalSlot <=
      builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape (globalLocalSlot + 1)) -
        builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot) := by
  let base :=
    builtRectangularFalseSelectLocalBaseOccurrence
      shape globalLocalSlot
  let endOcc :=
    builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
      shape globalLocalSlot
  let next :=
    builtRectangularFalseSelectLocalBaseOccurrence
      shape (globalLocalSlot + 1)
  let basePos := builtRelativeSplitFalseSelectPosition shape base
  let lastPos := builtRelativeSplitFalseSelectPosition shape (endOcc - 1)
  let nextPos := builtRelativeSplitFalseSelectPosition shape next
  have hendCount : endOcc <= falseSelectOccurrenceCount shape := by
    simpa [endOcc] using
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_le_count
        shape globalLocalSlot
  have hendPos : 0 < endOcc := by
    simpa [endOcc] using
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_pos
        shape hslot
  have hendNext : endOcc <= next := by
    simpa [endOcc, next] using
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_le_next_base
        shape globalLocalSlot
  have hbaseNext : base <= next := by
    simpa [base, next] using
      builtRectangularFalseSelectLocalBaseOccurrence_le_next_base
        shape globalLocalSlot
  have hlastCount : endOcc - 1 < falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hlastCount with ⟨lastWitness, hlastSelect⟩
  have hlastEq : lastPos = lastWitness := by
    simpa [lastPos] using
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hlastSelect
  have hlastBounds : lastWitness < shape.bpCode.length :=
    RMQ.Succinct.select_bounds hlastSelect
  by_cases hbaseCount : base < falseSelectOccurrenceCount shape
  · have hbaseEnd :
        base < endOcc := by
      simpa [base, endOcc] using
        builtRelativeSplitFalseSelectShortSuperLocalBase_lt_end_of_base_lt_count
          shape globalLocalSlot hbaseCount
    rcases falseSelect_exists_of_lt_occurrence_count
        shape hbaseCount with ⟨baseWitness, hbaseSelect⟩
    have hbaseEq : basePos = baseWitness := by
      simpa [basePos] using
        builtRelativeSplitFalseSelectPosition_eq_of_select
          shape hbaseSelect
    have hbaseLast :
        baseWitness <= lastWitness := by
      have hmono :=
        select_index_mono (target := false) (bits := shape.bpCode)
          (lo := base) (hi := endOcc - 1)
          (posLo := baseWitness) (posHi := lastWitness)
          (by omega) hbaseSelect hlastSelect
      exact hmono
    have hlastNext : lastWitness + 1 <= nextPos := by
      by_cases hnextCount : next < falseSelectOccurrenceCount shape
      · rcases falseSelect_exists_of_lt_occurrence_count
          shape hnextCount with ⟨nextWitness, hnextSelect⟩
        have hstrict :
            lastWitness < nextWitness :=
          select_index_strict_mono (target := false)
            (bits := shape.bpCode)
            (lo := endOcc - 1) (hi := next)
            (posLo := lastWitness) (posHi := nextWitness)
            (by omega) hlastSelect hnextSelect
        have hnextEq : nextPos = nextWitness := by
          simpa [nextPos] using
            builtRelativeSplitFalseSelectPosition_eq_of_select
              shape hnextSelect
        rw [hnextEq]
        omega
      · have hnextCountLe :
            falseSelectOccurrenceCount shape <= next := by
          omega
        have hnextEq :
            nextPos = shape.bpCode.length := by
          simpa [nextPos] using
            builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
              shape hnextCountLe
        rw [hnextEq]
        omega
    unfold builtRelativeSplitFalseSelectShortSuperLocalSpan
    change lastPos + 1 - basePos <= nextPos - basePos
    rw [hlastEq, hbaseEq]
    omega
  · have hbaseCountLe :
        falseSelectOccurrenceCount shape <= base := by
      omega
    have hnextCountLe :
        falseSelectOccurrenceCount shape <= next := by
      exact Nat.le_trans hbaseCountLe hbaseNext
    have hbaseEq :
        basePos = shape.bpCode.length := by
      simpa [basePos] using
        builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
          shape hbaseCountLe
    have hnextEq :
        nextPos = shape.bpCode.length := by
      simpa [nextPos] using
        builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
          shape hnextCountLe
    unfold builtRelativeSplitFalseSelectShortSuperLocalSpan
    change lastPos + 1 - basePos <= nextPos - basePos
    rw [hlastEq, hbaseEq, hnextEq]
    omega

theorem builtRelativeSplitFalseSelect_selected_offset_lt_superLongSpan
    (shape : Cartesian.CartesianShape) (superSlot : Nat)
    {localBaseOccurrence q pos : Nat}
    (hshort :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = false)
    (hsuperBase :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <=
        localBaseOccurrence)
    (hlocalBase : localBaseOccurrence <= q)
    (hqEnd :
      q <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot)
    (hselect :
      RMQ.Succinct.select false shape.bpCode q = some pos) :
    pos -
        builtRelativeSplitFalseSelectPosition
          shape localBaseOccurrence <
      sparseDenseFalseSelectSuperLongSpan shape := by
  let superBase :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
  let superEnd :=
    builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot
  have hqCount : q < falseSelectOccurrenceCount shape :=
    falseSelect_occurrence_lt_count_of_select shape hselect
  have hlocalCount : localBaseOccurrence < falseSelectOccurrenceCount shape := by
    omega
  have hsuperCount : superBase < falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hlocalCount with
    ⟨localBasePos, hlocalSelect⟩
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hsuperCount with
    ⟨superBasePos, hsuperSelect⟩
  have hsuperEndLeCount :
      superEnd <= falseSelectOccurrenceCount shape := by
    exact Nat.min_le_right
      (superBase + sparseDenseFalseSelectSuperStride shape)
      (falseSelectOccurrenceCount shape)
  have hsuperEndPos : 0 < superEnd := by
    omega
  have hlastCount : superEnd - 1 < falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hlastCount with
    ⟨lastPos, hlastSelect⟩
  have hsuperBasePos_le_localBasePos :
      superBasePos <= localBasePos := by
    exact select_index_mono
      (target := false) (bits := shape.bpCode)
      (lo := superBase) (hi := localBaseOccurrence)
      (posLo := superBasePos) (posHi := localBasePos)
      (by simpa [superBase] using hsuperBase)
      hsuperSelect hlocalSelect
  have hlocalBasePos_le_pos :
      localBasePos <= pos := by
    exact select_index_mono
      (target := false) (bits := shape.bpCode)
      (lo := localBaseOccurrence) (hi := q)
      (posLo := localBasePos) (posHi := pos)
      hlocalBase hlocalSelect hselect
  have hqLeLast : q <= superEnd - 1 := by
    omega
  have hpos_le_last :
      pos <= lastPos := by
    exact select_index_mono
      (target := false) (bits := shape.bpCode)
      (lo := q) (hi := superEnd - 1)
      (posLo := pos) (posHi := lastPos)
      hqLeLast hselect hlastSelect
  have hspanLe :=
    builtRelativeSplitFalseSelectSuperIsLong_false_span_le
      shape superSlot hshort
  have hsuperSelect' :
      RMQ.Succinct.select false shape.bpCode
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) =
        some superBasePos := by
    simpa [superBase] using hsuperSelect
  have hlastSelect' :
      RMQ.Succinct.select false shape.bpCode
          (builtRelativeSplitFalseSelectSuperEndOccurrence
            shape superSlot - 1) =
        some lastPos := by
    simpa [superEnd] using hlastSelect
  have hsuperSelectRaw :
      RMQ.Succinct.select false shape.bpCode
          (superSlot * sparseDenseFalseSelectSuperStride shape) =
        some superBasePos := by
    simpa [builtRelativeSplitFalseSelectSuperBaseOccurrence] using
      hsuperSelect'
  have hlastSelectRaw :
      RMQ.Succinct.select false shape.bpCode
          ((superSlot * sparseDenseFalseSelectSuperStride shape +
              sparseDenseFalseSelectSuperStride shape).min
            (falseSelectOccurrenceCount shape) -
            1) =
        some lastPos := by
    simpa [builtRelativeSplitFalseSelectSuperEndOccurrence,
      builtRelativeSplitFalseSelectSuperBaseOccurrence] using
      hlastSelect'
  have hspanEq :
      builtRelativeSplitFalseSelectSuperSpan shape superSlot =
        lastPos + 1 - superBasePos := by
    simp [builtRelativeSplitFalseSelectSuperSpan,
      builtRelativeSplitFalseSelectSuperBaseOccurrence,
      builtRelativeSplitFalseSelectSuperEndOccurrence,
      builtRelativeSplitFalseSelectPosition, hsuperSelectRaw,
      hlastSelectRaw]
  rw [hspanEq] at hspanLe
  have hlocalPosEq :
      builtRelativeSplitFalseSelectPosition
        shape localBaseOccurrence = localBasePos :=
    builtRelativeSplitFalseSelectPosition_eq_of_select
      shape hlocalSelect
  rw [hlocalPosEq]
  have hoffLt :
      pos - localBasePos < lastPos + 1 - superBasePos := by
    omega
  omega

theorem falseSelectRelativeOffsetsOrZero_mem_cases
    {bits : List Bool} {baseOccurrence count endOccurrence
      basePosition entry : Nat}
    (hmem :
      List.Mem entry
        (falseSelectRelativeOffsetsOrZero bits baseOccurrence count
          endOccurrence basePosition)) :
    entry = 0 \/
      exists offset pos,
        offset < count /\
          baseOccurrence + offset < endOccurrence /\
          RMQ.Succinct.select false bits
            (baseOccurrence + offset) = some pos /\
          entry = pos - basePosition := by
  unfold falseSelectRelativeOffsetsOrZero at hmem
  rcases List.mem_map.mp hmem with ⟨offset, hoffMem, hentry⟩
  have hoff : offset < count := by
    simpa using (List.mem_range.mp hoffMem)
  by_cases hlt : baseOccurrence + offset < endOccurrence
  · cases hselect :
      RMQ.Succinct.select false bits
        (baseOccurrence + offset) with
    | none =>
        left
        simpa [hlt, hselect] using hentry.symm
    | some pos =>
        right
        refine ⟨offset, pos, hoff, hlt, hselect, ?_⟩
        simpa [hlt, hselect] using hentry.symm
  · left
    simpa [hlt] using hentry.symm

theorem falseSelectRelativeOffsetsOrZero_lookup_exact
    {bits : List Bool} {baseOccurrence count endOccurrence
      basePosition localOccurrence pos : Nat}
    (hocc : localOccurrence < count)
    (hend : baseOccurrence + localOccurrence < endOccurrence)
    (hselect :
      RMQ.Succinct.select false bits
        (baseOccurrence + localOccurrence) = some pos) :
    (falseSelectRelativeOffsetsOrZero bits baseOccurrence count
      endOccurrence basePosition)[localOccurrence]? =
      some (pos - basePosition) := by
  simp [falseSelectRelativeOffsetsOrZero, List.getElem?_map,
    List.getElem?_range hocc, hend, hselect]

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot_mem_lt_width
    (shape : Cartesian.CartesianShape) {globalLocalSlot entry : Nat}
    (hmem :
      List.Mem entry
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape globalLocalSlot)) :
    entry <
      2 ^
        builtRelativeSplitFalseSelectSparseExceptionRelativeWidth
          shape := by
  by_cases hflag :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = true
  · let superSlot :=
      builtRelativeSplitFalseSelectLocalSuperSlot shape globalLocalSlot
    let localBase :=
      builtRectangularFalseSelectLocalBaseOccurrence
        shape globalLocalSlot
    let localBasePosition :=
      builtRelativeSplitFalseSelectPosition shape localBase
    have hshort :=
      (builtRelativeSplitFalseSelectLocalIsSparseException_true_short
        shape globalLocalSlot hflag).1
    have hmemOffsets :
        List.Mem entry
          (falseSelectRelativeOffsetsOrZero shape.bpCode localBase
            (sparseDenseFalseSelectLocalStride shape)
            (builtRelativeSplitFalseSelectSuperEndOccurrence
              shape superSlot)
            localBasePosition) := by
      simpa [builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot,
        hflag, superSlot, localBase, localBasePosition] using hmem
    rcases falseSelectRelativeOffsetsOrZero_mem_cases
        hmemOffsets with hzero | hsome
    · subst entry
      exact Nat.pow_pos (by omega : 0 < 2)
    · rcases hsome with
        ⟨offset, pos, _hoff, hqEnd, hselect, hentry⟩
      have hsuperBase :
          builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <=
            localBase := by
        simp [superSlot, localBase,
          builtRelativeSplitFalseSelectSuperBaseOccurrence,
          builtRelativeSplitFalseSelectLocalSuperSlot,
          builtRectangularFalseSelectLocalBaseOccurrence]
      have hoffSuper :
          pos - localBasePosition <
            sparseDenseFalseSelectSuperLongSpan shape := by
        simpa [localBase, localBasePosition, superSlot] using
          builtRelativeSplitFalseSelect_selected_offset_lt_superLongSpan
            shape superSlot hshort hsuperBase
            (by omega)
            hqEnd hselect
      have hposLen : pos < shape.bpCode.length :=
        RMQ.Succinct.select_bounds hselect
      have hentryLen : entry < shape.bpCode.length := by
        rw [hentry]
        omega
      have hentrySuper :
          entry < sparseDenseFalseSelectSuperLongSpan shape := by
        rw [hentry]
        exact hoffSuper
      have hentryMin :
          entry <
            Nat.min shape.bpCode.length
              (sparseDenseFalseSelectSuperLongSpan shape) := by
        exact Nat.lt_min.mpr ⟨hentryLen, hentrySuper⟩
      exact Nat.lt_trans hentryMin
        (by
          simpa [builtRelativeSplitFalseSelectSparseExceptionRelativeWidth,
            SuccinctRank.machineWordBits] using
            (Nat.lt_log2_self
              (n :=
                Nat.min shape.bpCode.length
                  (sparseDenseFalseSelectSuperLongSpan shape))))
  · have hfalse :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = false := by
      cases h :
          builtRelativeSplitFalseSelectLocalIsSparseException
            shape globalLocalSlot
      · rfl
      · contradiction
    simp [builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot,
      hfalse] at hmem
    cases hmem

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_mem_lt_width
    (shape : Cartesian.CartesianShape) {entry : Nat}
    (hmem :
      List.Mem entry
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
          shape)) :
    entry <
      2 ^
        builtRelativeSplitFalseSelectSparseExceptionRelativeWidth
          shape := by
  unfold builtRelativeSplitFalseSelectSparseExceptionRelativeEntries at hmem
  rcases List.mem_flatMap.mp hmem with ⟨globalLocalSlot, _hslot, hentry⟩
  exact
    builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot_mem_lt_width
      shape hentry

def builtRelativeSplitFalseSelectSparseExceptionRelativeTable
    (shape : Cartesian.CartesianShape) :
    SuccinctSpace.FixedWidthNatTable
      (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries shape)
      (builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries shape)
    (builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape)
    (by
      intro entry hmem
      exact
        builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_mem_lt_width
          shape hmem)

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeTable_profile
    (shape : Cartesian.CartesianShape) :
    let table :=
      builtRelativeSplitFalseSelectSparseExceptionRelativeTable shape
    table.payload.length =
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
          shape).length *
          builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape /\
      (forall i, (table.readCosted i).cost <= 1 /\
        (table.readCosted i).erase =
          (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
            shape)[i]?) /\
      forall {word : List Bool},
        List.Mem word table.store.words.toList ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length := by
  let table :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeTable shape
  constructor
  · exact table.payload_length_eq
  · constructor
    · intro i
      exact ⟨table.readCosted_cost_le_one i, table.readCosted_erase i⟩
    · intro word hmem
      rcases (List.mem_iff_getElem?.mp hmem) with ⟨i, hgetList⟩
      have hget : table.store.words[i]? = some word := by
        simpa [Array.getElem?_toList] using hgetList
      rw [table.read_word_length_of_some hget]
      exact
        builtRelativeSplitFalseSelectSparseExceptionRelativeWidth_le_machine
          shape


end SuccinctSelect
end RMQ
