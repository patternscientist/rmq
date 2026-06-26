import RMQ.Core.SuccinctSelect.CloseSelect.SparseExceptionCloseData.DataSurface

/-!
# Built sparse-exception exactness lemmas

Split implementation layer for sparse-exception close-select data.
Public declarations stay in the historical `RMQ.SuccinctSelect`
namespace.
-/

namespace RMQ
namespace SuccinctSelect

theorem builtRelativeSplitFalseSelectLongSuperFlagBits_eq_relativeSplitLongFlagBits
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectLongSuperFlagBits shape =
      relativeSplitFalseSelectLongFlagBits
        (builtRelativeSplitFalseSelectSuperEntries shape) := by
  simp [builtRelativeSplitFalseSelectLongSuperFlagBits,
    relativeSplitFalseSelectLongFlagBits,
    builtRelativeSplitFalseSelectSuperEntries, List.map_map,
    Function.comp, builtRelativeSplitFalseSelectSuperEntry_marked_eq_long]

theorem builtRelativeSplitFalseSelectSuperEntries_missing_exact
    (shape : Cartesian.CartesianShape) (q : Nat)
    (hmissing :
      (builtRelativeSplitFalseSelectSuperEntries shape)[
          falseSelectSuperSlot q
            (sparseDenseFalseSelectSuperStride shape)]? = none) :
    RMQ.Succinct.select false shape.bpCode q = none := by
  cases hselect :
      RMQ.Succinct.select false shape.bpCode q with
  | none =>
      rfl
  | some pos =>
      have hocc : q < falseSelectOccurrenceCount shape :=
        falseSelect_occurrence_lt_count_of_select shape hselect
      have hslotMul :
          (q / sparseDenseFalseSelectSuperStride shape) *
              sparseDenseFalseSelectSuperStride shape <
            falseSelectOccurrenceCount shape := by
        have hmul :=
          Nat.div_mul_le_self q
            (sparseDenseFalseSelectSuperStride shape)
        omega
      have hslot :
          falseSelectSuperSlot q
              (sparseDenseFalseSelectSuperStride shape) <
            builtRectangularFalseSelectSuperSlotCount shape := by
        unfold falseSelectSuperSlot
          builtRectangularFalseSelectSuperSlotCount
        by_cases hlt :
            q / sparseDenseFalseSelectSuperStride shape <
              falseSelectCeilDiv (falseSelectOccurrenceCount shape)
                (sparseDenseFalseSelectSuperStride shape)
        · exact hlt
        · have hceilLe :
              falseSelectCeilDiv (falseSelectOccurrenceCount shape)
                  (sparseDenseFalseSelectSuperStride shape) <=
                q / sparseDenseFalseSelectSuperStride shape :=
            Nat.le_of_not_gt hlt
          have hmulLe :=
            Nat.mul_le_mul_right
              (sparseDenseFalseSelectSuperStride shape) hceilLe
          have hceilGe :=
            falseSelectCeilDiv_mul_ge_of_pos
              (n := falseSelectOccurrenceCount shape)
              (stride := sparseDenseFalseSelectSuperStride shape)
              (sparseDenseFalseSelectSuperStride_pos shape)
          exact False.elim (by omega)
      have hget :=
        builtRelativeSplitFalseSelectSuperEntries_get?
          shape hslot
      rw [hget] at hmissing
      simp at hmissing

theorem builtRelativeSplitFalseSelectLongExplicit_exact
    (shape : Cartesian.CartesianShape) (q : Nat)
    (super : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (builtRelativeSplitFalseSelectSuperEntries shape)[
          falseSelectSuperSlot q
            (sparseDenseFalseSelectSuperStride shape)]? = some super)
    (hvalid :
      q < RMQ.Succinct.rankPrefix false shape.bpCode
        shape.bpCode.length)
    (hlong :
      relativeSplitFalseSelectEntryIsMarked super = true) :
    ((builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)[
        relativeSplitFalseSelectLongCompactSlot
          (RMQ.Succinct.rankPrefix true
            (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
            (falseSelectSuperSlot q
              (sparseDenseFalseSelectSuperStride shape)))
          (q - super.baseOccurrence)
          (sparseDenseFalseSelectSuperStride shape)]?).map
      (fun offset =>
        relativeSplitFalseSelectEntryBasePosition
            (sparseDenseFalseSelectWordBits shape) super +
          offset) =
      RMQ.Succinct.select false shape.bpCode q := by
  let superSlot :=
    falseSelectSuperSlot q (sparseDenseFalseSelectSuperStride shape)
  have hslot : superSlot < builtRectangularFalseSelectSuperSlotCount shape := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, builtRelativeSplitFalseSelectSuperEntries_length]
      using hlen
  have hbuilt :=
    builtRelativeSplitFalseSelectSuperEntries_get?
      shape (superSlot := superSlot) hslot
  have hsuperEq :
      super = builtRelativeSplitFalseSelectSuperEntry shape superSlot := by
    rw [hbuilt] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  have hlongBuilt :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true := by
    have hmark :=
      builtRelativeSplitFalseSelectSuperEntry_marked_eq_long
        shape superSlot
    rw [hmark] at hlong
    exact hlong
  have hoccCount : q < falseSelectOccurrenceCount shape := by
    simpa [falseSelectOccurrenceCount] using hvalid
  have hbaseLeQ :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <= q := by
    have hmul :=
      Nat.div_mul_le_self q
        (sparseDenseFalseSelectSuperStride shape)
    simpa [superSlot, falseSelectSuperSlot,
      builtRelativeSplitFalseSelectSuperBaseOccurrence] using hmul
  have hqLtBaseStride :
      q <
        builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
          sparseDenseFalseSelectSuperStride shape := by
    have hstride := sparseDenseFalseSelectSuperStride_pos shape
    have hlt :=
      Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, falseSelectSuperSlot,
      builtRelativeSplitFalseSelectSuperBaseOccurrence,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  have hlocalOcc :
      q - builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <
        sparseDenseFalseSelectSuperStride shape := by
    omega
  have hend :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
          (q - builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot := by
    have hqEq :
        builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
            (q - builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot) = q := by
      omega
    rw [hqEq]
    unfold builtRelativeSplitFalseSelectSuperEndOccurrence
    exact Nat.lt_min.mpr ⟨hqLtBaseStride, hoccCount⟩
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hoccCount with ⟨pos, hselect⟩
  have hqEqLocal :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
          (q - builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) = q := by
    omega
  have hselectLocal :
      RMQ.Succinct.select false shape.bpCode
          (builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
            (q - builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot)) =
        some pos := by
    simpa [hqEqLocal] using hselect
  have hlookup :=
    compactLongSuperRelativeTable_lookup_exact
      shape (superSlot := superSlot)
      (localOccurrence :=
        q - builtRelativeSplitFalseSelectSuperBaseOccurrence
          shape superSlot)
      (pos := pos) hslot hlongBuilt hlocalOcc hend hselectLocal
  have hbasePos :
      relativeSplitFalseSelectEntryBasePosition
          (sparseDenseFalseSelectWordBits shape)
          (builtRelativeSplitFalseSelectSuperEntry shape superSlot) =
        builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) := by
    unfold relativeSplitFalseSelectEntryBasePosition
      builtRelativeSplitFalseSelectSuperEntry
    let baseOccurrence :=
      superSlot * sparseDenseFalseSelectSuperStride shape
    let basePosition :=
      builtRelativeSplitFalseSelectPosition shape baseOccurrence
    let wordSize := sparseDenseFalseSelectWordBits shape
    have hmod :
        basePosition / wordSize * wordSize +
            (basePosition - basePosition / wordSize * wordSize) =
          basePosition := by
      have hle := Nat.div_mul_le_self basePosition wordSize
      omega
    simpa [baseOccurrence, basePosition, wordSize,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmod
  have hbaseLePos :
      builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) <= pos := by
    have hsuperCount :
        builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <
          falseSelectOccurrenceCount shape := by
      omega
    rcases falseSelect_exists_of_lt_occurrence_count
        shape hsuperCount with ⟨basePos, hbaseSelect⟩
    have hmono :=
      select_index_mono (target := false) (bits := shape.bpCode)
        (lo := builtRelativeSplitFalseSelectSuperBaseOccurrence
          shape superSlot)
        (hi := q)
        (posLo := basePos) (posHi := pos)
        hbaseLeQ hbaseSelect hselect
    have hbaseEq :
        builtRelativeSplitFalseSelectPosition shape
            (builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot) = basePos :=
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hbaseSelect
    rwa [hbaseEq]
  have hposEq :
      builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) +
        (pos -
          builtRelativeSplitFalseSelectPosition shape
            (builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot)) = pos := by
    omega
  have hqueryLookup :
      (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)[
          relativeSplitFalseSelectLongCompactSlot
            (RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
              (falseSelectSuperSlot q
                (sparseDenseFalseSelectSuperStride shape)))
            (q -
              (builtRelativeSplitFalseSelectSuperEntry
                shape superSlot).baseOccurrence)
            (sparseDenseFalseSelectSuperStride shape)]? =
        some
          (pos -
            builtRelativeSplitFalseSelectPosition shape
              (builtRelativeSplitFalseSelectSuperBaseOccurrence
                shape superSlot)) := by
    simpa [relativeSplitFalseSelectLongCompactSlot,
      builtRelativeSplitFalseSelectSuperEntry,
      builtRelativeSplitFalseSelectSuperBaseOccurrence, superSlot]
      using hlookup
  rw [hselect]
  rw [hqueryLookup]
  simp [hbasePos, hposEq]

theorem falseSelectCeilDiv_mul_ge
    {n stride : Nat} (hstride : 0 < stride) :
    n <= falseSelectCeilDiv n stride * stride := by
  unfold falseSelectCeilDiv
  cases n with
  | zero =>
      simp
  | succ n =>
      have hleStride : stride <= n + 1 + stride - 1 := by
        omega
      have hlt :
          n + 1 + stride - 1 - stride <
            (n + 1 + stride - 1) / stride * stride :=
        Nat.lt_div_mul_self hstride hleStride
      omega

theorem falseSelectLocalSlotsPerSuper_mul_localStride_ge_superStride
    {superStride localStride : Nat}
    (hlocal : 0 < localStride) :
    superStride <=
      falseSelectLocalSlotsPerSuper superStride localStride *
        localStride := by
  unfold falseSelectLocalSlotsPerSuper
  cases superStride with
  | zero =>
      simp
  | succ superStride =>
      have hleStride :
          localStride <= superStride + 1 + localStride - 1 := by
        omega
      have hlt :
          superStride + 1 + localStride - 1 - localStride <
            (superStride + 1 + localStride - 1) / localStride *
              localStride :=
        Nat.lt_div_mul_self hlocal hleStride
      omega

theorem nat_add_sub_one_le_mul_of_pos
    {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    a + b - 1 <= a * b := by
  cases a with
  | zero =>
      omega
  | succ a =>
      cases b with
      | zero =>
          omega
      | succ b =>
          simp [Nat.succ_mul, Nat.mul_succ]
          omega

theorem falseSelectLocalSlotsPerSuper_le_superStride
    {superStride localStride : Nat}
    (hsuper : 0 < superStride) (hlocal : 0 < localStride) :
    falseSelectLocalSlotsPerSuper superStride localStride <=
      superStride := by
  unfold falseSelectLocalSlotsPerSuper
  have hnum :
      superStride + localStride - 1 <=
        superStride * localStride :=
    nat_add_sub_one_le_mul_of_pos hsuper hlocal
  have hlt :
      (superStride + localStride - 1) / localStride <
        superStride + 1 := by
    rw [Nat.div_lt_iff_lt_mul hlocal]
    have hone : 1 <= localStride := by omega
    calc
      superStride + localStride - 1 <=
          superStride * localStride := hnum
      _ < (superStride + 1) * localStride := by
          rw [Nat.add_mul, Nat.one_mul]
          omega
  omega

theorem builtRelativeSplitFalseSelectLocalSlot_facts
    (shape : Cartesian.CartesianShape) (q : Nat)
    (super : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (builtRelativeSplitFalseSelectSuperEntries shape)[
          falseSelectSuperSlot q
            (sparseDenseFalseSelectSuperStride shape)]? =
        some super)
    (hvalid :
      q < RMQ.Succinct.rankPrefix false shape.bpCode
        shape.bpCode.length)
    (hshort :
      relativeSplitFalseSelectEntryIsMarked super = false) :
    let localSlot :=
      relativeSplitFalseSelectLocalSlot q
        (sparseDenseFalseSelectSuperStride shape)
        (builtRectangularFalseSelectLocalSlotsPerSuper shape)
        (sparseDenseFalseSelectLocalStride shape) super
    localSlot < builtRectangularFalseSelectLocalSlotCount shape /\
      localSlot <
        builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
          shape /\
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape localSlot = true /\
      builtRelativeSplitFalseSelectLocalSuperSlot shape localSlot =
        falseSelectSuperSlot q
          (sparseDenseFalseSelectSuperStride shape) /\
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <= q /\
      q <
        builtRectangularFalseSelectLocalBaseOccurrence shape localSlot +
          sparseDenseFalseSelectLocalStride shape := by
  let superSlot :=
    falseSelectSuperSlot q (sparseDenseFalseSelectSuperStride shape)
  let slots := builtRectangularFalseSelectLocalSlotsPerSuper shape
  let superStride := sparseDenseFalseSelectSuperStride shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  have hslot : superSlot < builtRectangularFalseSelectSuperSlotCount shape := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, builtRelativeSplitFalseSelectSuperEntries_length]
      using hlen
  have hbuilt :=
    builtRelativeSplitFalseSelectSuperEntries_get?
      shape (superSlot := superSlot) hslot
  have hsuperEq :
      super = builtRelativeSplitFalseSelectSuperEntry shape superSlot := by
    rw [hbuilt] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  have hshortBuilt :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = false := by
    have hmark :=
      builtRelativeSplitFalseSelectSuperEntry_marked_eq_long
        shape superSlot
    rw [hmark] at hshort
    exact hshort
  have hoccCount : q < falseSelectOccurrenceCount shape := by
    simpa [falseSelectOccurrenceCount] using hvalid
  have hbaseLeQ :
      superSlot * superStride <= q := by
    have hmul := Nat.div_mul_le_self q superStride
    simpa [superSlot, falseSelectSuperSlot, superStride] using hmul
  have hqLtBaseStride :
      q < superSlot * superStride + superStride := by
    have hstride := sparseDenseFalseSelectSuperStride_pos shape
    have hlt := Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, falseSelectSuperSlot, superStride,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  let localInSuper := (q - superSlot * superStride) / localStride
  have hlocalStridePos : 0 < localStride := by
    simpa [localStride] using sparseDenseFalseSelectLocalStride_pos shape
  have hslotsPos : 0 < slots := by
    simpa [slots] using
      builtRectangularFalseSelectLocalSlotsPerSuper_pos shape
  have hlocalInSuperLt : localInSuper < slots := by
    by_cases hlt : localInSuper < slots
    case pos =>
      exact hlt
    case neg =>
      have hle : slots <= localInSuper := Nat.le_of_not_gt hlt
      have hslotsMul :
          slots * localStride <= localInSuper * localStride :=
        Nat.mul_le_mul_right localStride hle
      have hdivMul :
          localInSuper * localStride <= q - superSlot * superStride := by
        simpa [localInSuper] using
          Nat.div_mul_le_self (q - superSlot * superStride) localStride
      have hcap :
          superStride <= slots * localStride := by
        simpa [slots, superStride, localStride,
          builtRectangularFalseSelectLocalSlotsPerSuper] using
          (falseSelectLocalSlotsPerSuper_mul_localStride_ge_superStride
            (superStride := sparseDenseFalseSelectSuperStride shape)
            (localStride := sparseDenseFalseSelectLocalStride shape)
            (sparseDenseFalseSelectLocalStride_pos shape))
      exact False.elim (by omega)
  let localSlot := superSlot * slots + localInSuper
  have hlocalSlotEq :
      relativeSplitFalseSelectLocalSlot q
          (sparseDenseFalseSelectSuperStride shape)
          (builtRectangularFalseSelectLocalSlotsPerSuper shape)
          (sparseDenseFalseSelectLocalStride shape)
          (builtRelativeSplitFalseSelectSuperEntry shape superSlot) =
        localSlot := by
    simp [relativeSplitFalseSelectLocalSlot,
      relativeSplitFalseSelectLocalSlotInSuper,
      builtRelativeSplitFalseSelectSuperEntry, superSlot, slots,
      superStride, localStride, localSlot, localInSuper,
      falseSelectSuperSlot]
  have hlocalSlotLt :
      localSlot < builtRectangularFalseSelectLocalSlotCount shape := by
    have hmul := Nat.mul_lt_mul_of_pos_right hslot hslotsPos
    have hnext :
        superSlot * slots + localInSuper <
          (superSlot + 1) * slots := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hle :
        (superSlot + 1) * slots <=
          builtRectangularFalseSelectSuperSlotCount shape * slots := by
      exact Nat.mul_le_mul_right slots (by omega)
    simpa [localSlot, builtRectangularFalseSelectLocalSlotCount,
      slots, Nat.mul_assoc] using Nat.lt_of_lt_of_le hnext hle
  have hsuperSlotOfLocal :
      builtRelativeSplitFalseSelectLocalSuperSlot shape localSlot =
        superSlot := by
    unfold builtRelativeSplitFalseSelectLocalSuperSlot
    calc
      (localSlot /
          builtRectangularFalseSelectLocalSlotsPerSuper shape) =
          (localInSuper + slots * superSlot) / slots := by
            simp [localSlot, slots, Nat.mul_comm, Nat.add_comm]
      _ = localInSuper / slots + superSlot := by
            exact Nat.add_mul_div_left localInSuper superSlot hslotsPos
      _ = superSlot := by
            rw [Nat.div_eq_of_lt hlocalInSuperLt]
            simp
  have hlocalRemainder :
      localSlot -
          builtRelativeSplitFalseSelectLocalSuperSlot shape localSlot *
            builtRectangularFalseSelectLocalSlotsPerSuper shape =
        localInSuper := by
    rw [hsuperSlotOfLocal]
    simp [localSlot, slots]
  have hlocalDiv :
      localSlot / builtRectangularFalseSelectLocalSlotsPerSuper shape =
        superSlot := by
    simpa [builtRelativeSplitFalseSelectLocalSuperSlot] using
      hsuperSlotOfLocal
  have hlocalRemainderRaw :
      localSlot -
          superSlot * builtRectangularFalseSelectLocalSlotsPerSuper shape =
        localInSuper := by
    simpa [hsuperSlotOfLocal] using hlocalRemainder
  have hbaseEq :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot =
        superSlot * superStride + localInSuper * localStride := by
    unfold builtRectangularFalseSelectLocalBaseOccurrence
      builtRectangularFalseSelectLocalSlotInSuperOfGlobal
    rw [hlocalDiv]
    rw [hlocalRemainderRaw]
  have hdivMul :
      localInSuper * localStride <= q - superSlot * superStride := by
    simpa [localInSuper] using
      Nat.div_mul_le_self (q - superSlot * superStride) localStride
  have hbaseLocalLeQ :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <= q := by
    rw [hbaseEq]
    omega
  have hslotsLeSuperStride :
      slots <= superStride := by
    simpa [slots, superStride, localStride,
      builtRectangularFalseSelectLocalSlotsPerSuper] using
      (falseSelectLocalSlotsPerSuper_le_superStride
        (hsuper := sparseDenseFalseSelectSuperStride_pos shape)
        (hlocal := sparseDenseFalseSelectLocalStride_pos shape))
  have hlocalSlotLeBase :
      localSlot <=
        builtRectangularFalseSelectLocalBaseOccurrence shape localSlot := by
    have hslotPart :
        superSlot * slots <= superSlot * superStride :=
      Nat.mul_le_mul_left superSlot hslotsLeSuperStride
    have hlocalStrideOne : 1 <= localStride := by omega
    have hlocalPart :
        localInSuper <= localInSuper * localStride := by
      simpa using Nat.mul_le_mul_left localInSuper hlocalStrideOne
    rw [hbaseEq]
    simp [localSlot]
    omega
  have hlocalSlotLtCount :
      localSlot < falseSelectOccurrenceCount shape := by
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans hlocalSlotLeBase hbaseLocalLeQ) hoccCount
  have hlocalSlotLtEffective :
      localSlot <
        builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
          shape := by
    unfold builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
    exact Nat.lt_min.mpr ⟨hlocalSlotLt, hlocalSlotLtCount⟩
  have hdeltaLtNext :
      q - superSlot * superStride <
        localInSuper * localStride + localStride := by
    simpa [localInSuper, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using
      Nat.lt_div_mul_add hlocalStridePos
        (a := q - superSlot * superStride)
  have hqLtLocalEnd :
      q <
        builtRectangularFalseSelectLocalBaseOccurrence shape localSlot +
          sparseDenseFalseSelectLocalStride shape := by
    rw [hbaseEq]
    simpa [localStride] using (by omega :
      q < superSlot * superStride + localInSuper * localStride +
        localStride)
  have hbaseCount :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <
        falseSelectOccurrenceCount shape := by
    omega
  have hlive :
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape localSlot = true := by
    unfold builtRelativeSplitFalseSelectCompactLocalEntryIsLive
    simp [hsuperSlotOfLocal, hshortBuilt, hbaseCount]
  rw [hlocalSlotEq]
  exact
    ⟨hlocalSlotLt, hlocalSlotLtEffective, hlive, hsuperSlotOfLocal, hbaseLocalLeQ,
      hqLtLocalEnd⟩

theorem builtRelativeSplitFalseSelectLocalEntries_missing_exact
    (shape : Cartesian.CartesianShape) (q : Nat)
    (super : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (builtRelativeSplitFalseSelectSuperEntries shape)[
          falseSelectSuperSlot q
            (sparseDenseFalseSelectSuperStride shape)]? =
        some super)
    (hvalid :
      q < RMQ.Succinct.rankPrefix false shape.bpCode
        shape.bpCode.length)
    (hshort :
      relativeSplitFalseSelectEntryIsMarked super = false)
    (hmissing :
      (builtRelativeSplitFalseSelectLocalEntries shape)[
          relativeSplitFalseSelectLocalSlot q
            (sparseDenseFalseSelectSuperStride shape)
            (builtRectangularFalseSelectLocalSlotsPerSuper shape)
            (sparseDenseFalseSelectLocalStride shape) super]? =
        none) :
    RMQ.Succinct.select false shape.bpCode q = none := by
  let localSlot :=
    relativeSplitFalseSelectLocalSlot q
      (sparseDenseFalseSelectSuperStride shape)
      (builtRectangularFalseSelectLocalSlotsPerSuper shape)
      (sparseDenseFalseSelectLocalStride shape) super
  have hfacts :=
    builtRelativeSplitFalseSelectLocalSlot_facts
      shape q super hsuper hvalid hshort
  rcases hfacts with
    ⟨hlocalSlotLt, _heff, _hlive, _hsameSuper,
      _hbaseLe, _hend⟩
  have hget :=
    builtRelativeSplitFalseSelectLocalEntries_get?
      shape (globalLocalSlot := localSlot) hlocalSlotLt
  have hmissingLocal :
      (builtRelativeSplitFalseSelectLocalEntries shape)[localSlot]? =
        none := by
    simpa [localSlot] using hmissing
  rw [hget] at hmissingLocal
  cases hmissingLocal

theorem builtRelativeSplitSparseExceptionDirectory_readCosted_lookup_exact
    (shape : Cartesian.CartesianShape)
    {globalLocalSlot localOccurrence pos : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape)
    (heff :
      globalLocalSlot <
        builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
          shape)
    (hflag :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = true)
    (hocc :
      localOccurrence < sparseDenseFalseSelectLocalStride shape)
    (hend :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot + localOccurrence <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          (builtRelativeSplitFalseSelectLocalSuperSlot
            shape globalLocalSlot))
    (hselect :
      RMQ.Succinct.select false shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence) =
        some pos) :
    ((builtRelativeSplitSparseExceptionDirectory shape).readCosted
      (builtRelativeSplitFalseSelectPosition shape
        (builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot))
      globalLocalSlot localOccurrence).erase =
      some
        (builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot) +
          (pos -
            builtRelativeSplitFalseSelectPosition shape
              (builtRectangularFalseSelectLocalBaseOccurrence
                shape globalLocalSlot))) := by
  have hread :=
    (builtRelativeSplitSparseExceptionDirectory shape).readCosted_exact
      (builtRelativeSplitFalseSelectPosition shape
        (builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot))
      globalLocalSlot localOccurrence
  rw [hread]
  change
    Option.map
      (fun offset =>
        builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot) +
          offset)
      ((builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
          shape)[
          relativeSplitFalseSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
                shape)
              globalLocalSlot)
            localOccurrence
            (sparseDenseFalseSelectLocalStride shape)]?) =
      some
        (builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot) +
          (pos -
            builtRelativeSplitFalseSelectPosition shape
              (builtRectangularFalseSelectLocalBaseOccurrence
                shape globalLocalSlot)))
  have hprefix :=
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_prefix_eq
      shape (globalLocalSlot := globalLocalSlot) (Nat.le_of_lt heff)
  rw [hprefix]
  have hlookup :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_lookup_exact
      shape hslot hflag hocc hend hselect
  rw [relativeSplitFalseSelectSparseCompactSlot]
  rw [hlookup]
  rfl

theorem builtRelativeSplitFalseSelectSparseCompact_exact
    (shape : Cartesian.CartesianShape) (q : Nat)
    (super loc : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (builtRelativeSplitFalseSelectSuperEntries shape)[
          falseSelectSuperSlot q
            (sparseDenseFalseSelectSuperStride shape)]? =
        some super)
    (hvalid :
      q < RMQ.Succinct.rankPrefix false shape.bpCode
        shape.bpCode.length)
    (hshort :
      relativeSplitFalseSelectEntryIsMarked super = false)
    (hlocal :
      (builtRelativeSplitFalseSelectLocalEntries shape)[
          relativeSplitFalseSelectLocalSlot q
            (sparseDenseFalseSelectSuperStride shape)
            (builtRectangularFalseSelectLocalSlotsPerSuper shape)
            (sparseDenseFalseSelectLocalStride shape) super]? =
        some loc)
    (hsparse :
      relativeSplitFalseSelectEntryIsMarked loc = true) :
    ((builtRelativeSplitSparseExceptionDirectory shape).readCosted
      (relativeSplitFalseSelectLocalBasePosition
        (sparseDenseFalseSelectWordBits shape) super loc)
      (relativeSplitFalseSelectLocalSlot q
        (sparseDenseFalseSelectSuperStride shape)
        (builtRectangularFalseSelectLocalSlotsPerSuper shape)
        (sparseDenseFalseSelectLocalStride shape) super)
      (q - relativeSplitFalseSelectLocalBaseOccurrence super loc)).erase =
      RMQ.Succinct.select false shape.bpCode q := by
  let superSlot :=
    falseSelectSuperSlot q (sparseDenseFalseSelectSuperStride shape)
  have hsuperSlotLt :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, builtRelativeSplitFalseSelectSuperEntries_length]
      using hlen
  have hbuiltSuper :=
    builtRelativeSplitFalseSelectSuperEntries_get?
      shape (superSlot := superSlot) hsuperSlotLt
  have hsuperEq :
      super = builtRelativeSplitFalseSelectSuperEntry shape superSlot := by
    rw [hbuiltSuper] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  let localSlot :=
    relativeSplitFalseSelectLocalSlot q
      (sparseDenseFalseSelectSuperStride shape)
      (builtRectangularFalseSelectLocalSlotsPerSuper shape)
      (sparseDenseFalseSelectLocalStride shape)
      (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
  have hfacts :=
    builtRelativeSplitFalseSelectLocalSlot_facts
      shape q (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
      hsuper hvalid hshort
  rcases hfacts with
    ⟨hlocalSlotLt, heff, hlive, hsameSuper,
      hbaseLe, hqLtLocalEnd⟩
  have hlocalGet :=
    builtRelativeSplitFalseSelectLocalEntries_get?
      shape (globalLocalSlot := localSlot) hlocalSlotLt
  have hlocalAtSlot :
      (builtRelativeSplitFalseSelectLocalEntries shape)[localSlot]? =
        some loc := by
    simpa [localSlot] using hlocal
  rw [hlocalGet] at hlocalAtSlot
  have hlocEq :
      loc = builtRelativeSplitFalseSelectLocalEntry shape localSlot := by
    exact (Option.some.inj hlocalAtSlot).symm
  subst loc
  have hmark :=
    builtRelativeSplitFalseSelectLocalEntry_marked_eq_flag
      shape localSlot
  rw [hmark] at hsparse
  have hflag :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape localSlot = true := by
    have hpair :
        builtRelativeSplitFalseSelectCompactLocalEntryIsLive
            shape localSlot = true /\
          builtRelativeSplitFalseSelectLocalIsSparseException
            shape localSlot = true := by
      simpa using hsparse
    exact hpair.2
  have hsameSuperSlot :
      builtRelativeSplitFalseSelectLocalSuperSlot shape localSlot =
        superSlot := by
    simpa [superSlot] using hsameSuper
  have hlocalDiv :
      localSlot / builtRectangularFalseSelectLocalSlotsPerSuper shape =
        superSlot := by
    simpa [builtRelativeSplitFalseSelectLocalSuperSlot] using
      hsameSuperSlot
  have hbaseOcc0 :=
    builtRelativeSplitFalseSelectLocalBaseOccurrence_exact
      shape localSlot hlive
  have hbaseOcc :
      relativeSplitFalseSelectLocalBaseOccurrence
        (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
        (builtRelativeSplitFalseSelectLocalEntry shape localSlot) =
        builtRectangularFalseSelectLocalBaseOccurrence
          shape localSlot := by
    simpa [hlocalDiv] using hbaseOcc0
  have hbasePos0 :=
    builtRelativeSplitFalseSelectLocalBasePosition_exact
      shape localSlot hlive
  have hbasePos :
      relativeSplitFalseSelectLocalBasePosition
        (sparseDenseFalseSelectWordBits shape)
        (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
        (builtRelativeSplitFalseSelectLocalEntry shape localSlot) =
        builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) := by
    simpa [hlocalDiv] using hbasePos0
  have hbaseLeLocal :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <= q := by
    simpa [localSlot] using hbaseLe
  have hqLtLocalEndLocal :
      q <
        builtRectangularFalseSelectLocalBaseOccurrence shape localSlot +
          sparseDenseFalseSelectLocalStride shape := by
    simpa [localSlot] using hqLtLocalEnd
  have hlocalOcc :
      q - builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <
        sparseDenseFalseSelectLocalStride shape := by
    omega
  have hqEq :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot +
          (q - builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) =
        q := by
    omega
  have hoccCount : q < falseSelectOccurrenceCount shape := by
    simpa [falseSelectOccurrenceCount] using hvalid
  have hbaseLeSuper :
      superSlot * sparseDenseFalseSelectSuperStride shape <= q := by
    have hmul :=
      Nat.div_mul_le_self q
        (sparseDenseFalseSelectSuperStride shape)
    simpa [superSlot, falseSelectSuperSlot] using hmul
  have hqLtBaseStride :
      q <
        superSlot * sparseDenseFalseSelectSuperStride shape +
          sparseDenseFalseSelectSuperStride shape := by
    have hstride := sparseDenseFalseSelectSuperStride_pos shape
    have hlt := Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, falseSelectSuperSlot,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  have hqLtSuperEnd :
      q < builtRelativeSplitFalseSelectSuperEndOccurrence
        shape superSlot := by
    unfold builtRelativeSplitFalseSelectSuperEndOccurrence
      builtRelativeSplitFalseSelectSuperBaseOccurrence
    exact Nat.lt_min.mpr ⟨hqLtBaseStride, hoccCount⟩
  have hend :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot +
          (q - builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          (builtRelativeSplitFalseSelectLocalSuperSlot
            shape localSlot) := by
    rw [hqEq, hsameSuperSlot]
    exact hqLtSuperEnd
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hoccCount with ⟨pos, hselect⟩
  have hselectLocal :
      RMQ.Succinct.select false shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot +
            (q - builtRectangularFalseSelectLocalBaseOccurrence
              shape localSlot)) =
        some pos := by
    simpa [hqEq] using hselect
  have hread :=
    builtRelativeSplitSparseExceptionDirectory_readCosted_lookup_exact
      shape hlocalSlotLt heff hflag hlocalOcc hend hselectLocal
  have hbaseCount :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <
        falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hbaseCount with ⟨basePos, hbaseSelect⟩
  have hbaseLePos :
      builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) <= pos := by
    have hmono :=
      select_index_mono (target := false) (bits := shape.bpCode)
        (lo := builtRectangularFalseSelectLocalBaseOccurrence
          shape localSlot)
        (hi := q) (posLo := basePos) (posHi := pos)
        hbaseLeLocal hbaseSelect hselect
    have hbaseEqPos :
        builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape localSlot) = basePos :=
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hbaseSelect
    rwa [hbaseEqPos]
  have hposEq :
      builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) +
        (pos -
          builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape localSlot)) =
        pos := by
    omega
  rw [hselect]
  simpa [localSlot, hbaseOcc, hbasePos, hposEq] using hread

theorem builtRelativeSplitFalseSelect_selected_lt_shortLocalBase_plus_span
    (shape : Cartesian.CartesianShape)
    {globalLocalSlot q pos : Nat}
    (hbaseLe :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot <= q)
    (hqEnd :
      q <
        builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
          shape globalLocalSlot)
    (hselect :
      RMQ.Succinct.select false shape.bpCode q = some pos) :
    pos <
      builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot) +
        builtRelativeSplitFalseSelectShortSuperLocalSpan
          shape globalLocalSlot := by
  let base :=
    builtRectangularFalseSelectLocalBaseOccurrence
      shape globalLocalSlot
  let endOcc :=
    builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
      shape globalLocalSlot
  let basePos := builtRelativeSplitFalseSelectPosition shape base
  let lastPos := builtRelativeSplitFalseSelectPosition shape (endOcc - 1)
  have hqCount : q < falseSelectOccurrenceCount shape :=
    falseSelect_occurrence_lt_count_of_select shape hselect
  have hbaseCount : base < falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hbaseCount with ⟨baseWitness, hbaseSelect⟩
  have hbaseEq :
      basePos = baseWitness := by
    simpa [basePos, base] using
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hbaseSelect
  have hbaseLePos : baseWitness <= pos :=
    select_index_mono (target := false) (bits := shape.bpCode)
      (lo := base) (hi := q) (posLo := baseWitness)
      (posHi := pos) hbaseLe hbaseSelect hselect
  have hendCount : endOcc <= falseSelectOccurrenceCount shape := by
    simpa [endOcc] using
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_le_count
        shape globalLocalSlot
  have hendPos : 0 < endOcc := by
    omega
  have hlastCount : endOcc - 1 < falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hlastCount with ⟨lastWitness, hlastSelect⟩
  have hlastEq :
      lastPos = lastWitness := by
    simpa [lastPos, endOcc] using
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hlastSelect
  have hqLeLast : q <= endOcc - 1 := by
    omega
  have hposLeLast : pos <= lastWitness :=
    select_index_mono (target := false) (bits := shape.bpCode)
      (lo := q) (hi := endOcc - 1) (posLo := pos)
      (posHi := lastWitness) hqLeLast hselect hlastSelect
  unfold builtRelativeSplitFalseSelectShortSuperLocalSpan
  change pos < basePos + (lastPos + 1 - basePos)
  rw [hbaseEq, hlastEq]
  omega

theorem builtRelativeSplitFalseSelectDense_exact
    (shape : Cartesian.CartesianShape) (q : Nat)
    (super loc : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (builtRelativeSplitFalseSelectSuperEntries shape)[
          falseSelectSuperSlot q
            (sparseDenseFalseSelectSuperStride shape)]? =
        some super)
    (hvalid :
      q < RMQ.Succinct.rankPrefix false shape.bpCode
        shape.bpCode.length)
    (hshort :
      relativeSplitFalseSelectEntryIsMarked super = false)
    (hlocal :
      (builtRelativeSplitFalseSelectLocalEntries shape)[
          relativeSplitFalseSelectLocalSlot q
            (sparseDenseFalseSelectSuperStride shape)
            (builtRectangularFalseSelectLocalSlotsPerSuper shape)
            (sparseDenseFalseSelectLocalStride shape) super]? =
        some loc)
    (hdense :
      relativeSplitFalseSelectEntryIsMarked loc = false) :
    (denseTwoWordFalseSelectCosted
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
        shape.bpCode (sparseDenseFalseSelectWordBits_pos shape))
      (relativeSplitFalseSelectLocalBasePosition
        (sparseDenseFalseSelectWordBits shape) super loc)
      (relativeSplitFalseSelectLocalBaseOccurrence super loc) q).erase =
      RMQ.Succinct.select false shape.bpCode q := by
  let superSlot :=
    falseSelectSuperSlot q (sparseDenseFalseSelectSuperStride shape)
  have hsuperSlotLt :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, builtRelativeSplitFalseSelectSuperEntries_length]
      using hlen
  have hbuiltSuper :=
    builtRelativeSplitFalseSelectSuperEntries_get?
      shape (superSlot := superSlot) hsuperSlotLt
  have hsuperEq :
      super = builtRelativeSplitFalseSelectSuperEntry shape superSlot := by
    rw [hbuiltSuper] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  let localSlot :=
    relativeSplitFalseSelectLocalSlot q
      (sparseDenseFalseSelectSuperStride shape)
      (builtRectangularFalseSelectLocalSlotsPerSuper shape)
      (sparseDenseFalseSelectLocalStride shape)
      (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
  have hfacts :=
    builtRelativeSplitFalseSelectLocalSlot_facts
      shape q (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
      hsuper hvalid hshort
  rcases hfacts with
    ⟨hlocalSlotLt, _heff, hlive, hsameSuper,
      hbaseLe, hqLtLocalEnd⟩
  have hlocalGet :=
    builtRelativeSplitFalseSelectLocalEntries_get?
      shape (globalLocalSlot := localSlot) hlocalSlotLt
  have hlocalAtSlot :
      (builtRelativeSplitFalseSelectLocalEntries shape)[localSlot]? =
        some loc := by
    simpa [localSlot] using hlocal
  rw [hlocalGet] at hlocalAtSlot
  have hlocEq :
      loc = builtRelativeSplitFalseSelectLocalEntry shape localSlot := by
    exact (Option.some.inj hlocalAtSlot).symm
  subst loc
  have hmark :=
    builtRelativeSplitFalseSelectLocalEntry_marked_eq_flag
      shape localSlot
  rw [hmark] at hdense
  have hliveLocal :
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape localSlot = true := by
    simpa [localSlot] using hlive
  have hflagFalse :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape localSlot = false := by
    cases hflag :
        builtRelativeSplitFalseSelectLocalIsSparseException
          shape localSlot
    · rfl
    · have hmarkedTrue :
          (builtRelativeSplitFalseSelectCompactLocalEntryIsLive
              shape localSlot &&
            builtRelativeSplitFalseSelectLocalIsSparseException
              shape localSlot) = true := by
        simp [hliveLocal, hflag]
      rw [hmarkedTrue] at hdense
      cases hdense
  have hsameSuperSlot :
      builtRelativeSplitFalseSelectLocalSuperSlot shape localSlot =
        superSlot := by
    simpa [superSlot] using hsameSuper
  have hlocalDiv :
      localSlot / builtRectangularFalseSelectLocalSlotsPerSuper shape =
        superSlot := by
    simpa [builtRelativeSplitFalseSelectLocalSuperSlot] using
      hsameSuperSlot
  have hbaseOcc0 :=
    builtRelativeSplitFalseSelectLocalBaseOccurrence_exact
      shape localSlot hliveLocal
  have hbaseOcc :
      relativeSplitFalseSelectLocalBaseOccurrence
        (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
        (builtRelativeSplitFalseSelectLocalEntry shape localSlot) =
        builtRectangularFalseSelectLocalBaseOccurrence
          shape localSlot := by
    simpa [hlocalDiv] using hbaseOcc0
  have hbasePos0 :=
    builtRelativeSplitFalseSelectLocalBasePosition_exact
      shape localSlot hliveLocal
  have hbasePos :
      relativeSplitFalseSelectLocalBasePosition
        (sparseDenseFalseSelectWordBits shape)
        (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
        (builtRelativeSplitFalseSelectLocalEntry shape localSlot) =
        builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) := by
    simpa [hlocalDiv] using hbasePos0
  have hbaseLeLocal :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <= q := by
    simpa [localSlot] using hbaseLe
  have hqLtLocalEndLocal :
      q <
        builtRectangularFalseSelectLocalBaseOccurrence shape localSlot +
          sparseDenseFalseSelectLocalStride shape := by
    simpa [localSlot] using hqLtLocalEnd
  have hoccCount : q < falseSelectOccurrenceCount shape := by
    simpa [falseSelectOccurrenceCount] using hvalid
  have hbaseLeSuper :
      superSlot * sparseDenseFalseSelectSuperStride shape <= q := by
    have hmul :=
      Nat.div_mul_le_self q
        (sparseDenseFalseSelectSuperStride shape)
    simpa [superSlot, falseSelectSuperSlot] using hmul
  have hqLtBaseStride :
      q <
        superSlot * sparseDenseFalseSelectSuperStride shape +
          sparseDenseFalseSelectSuperStride shape := by
    have hstride := sparseDenseFalseSelectSuperStride_pos shape
    have hlt := Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, falseSelectSuperSlot,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  have hqLtSuperEnd :
      q < builtRelativeSplitFalseSelectSuperEndOccurrence
        shape superSlot := by
    unfold builtRelativeSplitFalseSelectSuperEndOccurrence
      builtRelativeSplitFalseSelectSuperBaseOccurrence
    exact Nat.lt_min.mpr ⟨hqLtBaseStride, hoccCount⟩
  have hqLtShortEnd :
      q <
        builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
          shape localSlot := by
    unfold builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
    exact Nat.lt_min.mpr
      ⟨hqLtLocalEndLocal, by
        simpa [hsameSuperSlot] using hqLtSuperEnd⟩
  have hlocalSpanLeWord :
      builtRelativeSplitFalseSelectShortSuperLocalSpan shape localSlot <=
        sparseDenseFalseSelectWordBits shape := by
    unfold builtRelativeSplitFalseSelectLocalIsSparseException at hflagFalse
    have hshortBuilt :
        builtRelativeSplitFalseSelectSuperIsLong shape superSlot =
          false := by
      have hsuperMark :=
        builtRelativeSplitFalseSelectSuperEntry_marked_eq_long
          shape superSlot
      rw [hsuperMark] at hshort
      exact hshort
    have hshortAtLocal :
        builtRelativeSplitFalseSelectSuperIsLong shape
            (builtRelativeSplitFalseSelectLocalSuperSlot
              shape localSlot) = false := by
      rw [hsameSuperSlot]
      exact hshortBuilt
    rw [hshortAtLocal] at hflagFalse
    simp only [Bool.not_false, Bool.true_and] at hflagFalse
    by_cases hlt :
        sparseDenseFalseSelectWordBits shape <
          builtRelativeSplitFalseSelectShortSuperLocalSpan shape
            localSlot
    · have hdec :
          decide
              (sparseDenseFalseSelectWordBits shape <
                builtRelativeSplitFalseSelectShortSuperLocalSpan
                  shape localSlot) = true := by
        simp [hlt]
      rw [hdec] at hflagFalse
      cases hflagFalse
    · exact Nat.le_of_not_gt hlt
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hoccCount with ⟨pos, hselect⟩
  have hposLtLocalSpan :=
    builtRelativeSplitFalseSelect_selected_lt_shortLocalBase_plus_span
      shape hbaseLeLocal hqLtShortEnd hselect
  have hposSpanBuilt :
      pos <
        builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape localSlot) +
          sparseDenseFalseSelectWordBits shape := by
    omega
  have hbaseCount :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape localSlot <
        falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hbaseCount with ⟨basePos, hbaseSelect⟩
  have hbaseEqPos :
      builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) = basePos :=
    builtRelativeSplitFalseSelectPosition_eq_of_select
      shape hbaseSelect
  have hbaseSelectEntry :
      RMQ.Succinct.select false shape.bpCode
          (relativeSplitFalseSelectLocalBaseOccurrence
            (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
            (builtRelativeSplitFalseSelectLocalEntry shape localSlot)) =
        some
          (relativeSplitFalseSelectLocalBasePosition
            (sparseDenseFalseSelectWordBits shape)
            (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
            (builtRelativeSplitFalseSelectLocalEntry shape localSlot)) := by
    simpa [hbaseOcc, hbasePos, hbaseEqPos] using hbaseSelect
  have hbaseLeEntry :
      relativeSplitFalseSelectLocalBaseOccurrence
          (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
          (builtRelativeSplitFalseSelectLocalEntry shape localSlot) <= q := by
    simpa [hbaseOcc] using hbaseLeLocal
  have hposSpanEntry :
      pos <
        relativeSplitFalseSelectLocalBasePosition
            (sparseDenseFalseSelectWordBits shape)
            (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
            (builtRelativeSplitFalseSelectLocalEntry shape localSlot) +
          sparseDenseFalseSelectWordBits shape := by
    simpa [hbasePos] using hposSpanBuilt
  have hdenseFacts :
      FalseSelectDenseLocalPayloadRoutingFacts
        shape.bpCode (sparseDenseFalseSelectWordBits shape)
        (relativeSplitFalseSelectLocalBasePosition
          (sparseDenseFalseSelectWordBits shape)
          (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
          (builtRelativeSplitFalseSelectLocalEntry shape localSlot))
        (relativeSplitFalseSelectLocalBaseOccurrence
          (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
          (builtRelativeSplitFalseSelectLocalEntry shape localSlot)) q :=
    falseSelectDenseLocalPayloadRoutingFacts_of_selected_span
      (hwordSize := sparseDenseFalseSelectWordBits_pos shape)
      hbaseSelectEntry hselect hbaseLeEntry hposSpanEntry
  have haligned :
      FalseSelectAlignedBitWords shape.bpCode
        (sparseDenseFalseSelectWordBits shape)
        (SuccinctSpace.BoundedPayloadWordStore.ofChunks
          shape.bpCode (sparseDenseFalseSelectWordBits_pos shape)) :=
    falseSelectAlignedBitWords_ofChunks shape.bpCode
      (sparseDenseFalseSelectWordBits_pos shape)
  simpa [localSlot] using
    denseTwoWordFalseSelectCosted_exact_of_payload_routing_facts
      haligned hdenseFacts


end SuccinctSelect
end RMQ
