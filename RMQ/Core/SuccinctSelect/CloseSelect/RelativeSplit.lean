import RMQ.Core.SuccinctSelect.CloseSelect.BuiltRouting

/-!
# Relative-split false-select tables

Split implementation layer for the select-side close-select proposal.
Public declarations stay in the historical `RMQ.SuccinctSelect`
namespace.
-/

namespace RMQ
namespace SuccinctSelect

/-!
### Relative/split rectangular false-select close locator

This is the compact replacement surface for the old packed local locator.  It
uses the existing split four-Nat payload table for both levels:

* a low-frequency super row stores absolute `baseOccurrence`, absolute
  `baseWordIndex`, a long-super tag in `rankBefore`, and `firstOffset`;
* a high-frequency local row stores only occurrence and word-index deltas from
  its super row, a sparse-local tag in `rankBefore`, and `firstOffset`.

Long-super and sparse-local explicit tables store relative offsets in padded
blocks.  The query reconstructs absolute positions from charged table reads; it
does not use `super.pointer`, `loc.pointer`, or an absolute dense-local index.
-/

def relativeSplitFalseSelectEntryIsMarked
    (entry : SparseDenseFalseSelectDenseLocalEntry) : Bool :=
  entry.rankBefore != 0

def relativeSplitFalseSelectEntryBasePosition
    (wordSize : Nat)
    (entry : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  entry.baseWordIndex * wordSize + entry.firstOffset

def relativeSplitFalseSelectLocalBaseOccurrence
    (super loc : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  super.baseOccurrence + loc.baseOccurrence

def relativeSplitFalseSelectLocalBasePosition
    (wordSize : Nat)
    (super loc : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  (super.baseWordIndex + loc.baseWordIndex) * wordSize + loc.firstOffset

def relativeSplitFalseSelectLongExplicitSlot
    (q superStride : Nat)
    (super : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  falseSelectSuperSlot q superStride * superStride +
    (q - super.baseOccurrence)

def relativeSplitFalseSelectLongFlagBits
    (superEntries : List SparseDenseFalseSelectDenseLocalEntry) :
    List Bool :=
  superEntries.map relativeSplitFalseSelectEntryIsMarked

def relativeSplitFalseSelectLongCompactSlot
    (exceptionRank localOccurrence superStride : Nat) : Nat :=
  exceptionRank * superStride + localOccurrence

def relativeSplitFalseSelectSparseExplicitSlot
    (localSlot q localStride : Nat)
    (super loc : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  localSlot * localStride +
    (q - relativeSplitFalseSelectLocalBaseOccurrence super loc)

def relativeSplitFalseSelectSparseCompactSlot
    (exceptionRank localOccurrence localStride : Nat) : Nat :=
  exceptionRank * localStride + localOccurrence

def relativeSplitFalseSelectLocalSlotInSuper
    (super : SparseDenseFalseSelectDenseLocalEntry)
    (q localStride : Nat) : Nat :=
  (q - super.baseOccurrence) / localStride

def relativeSplitFalseSelectLocalSlot
    (q superStride localSlotsPerSuper localStride : Nat)
    (super : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  falseSelectSuperSlot q superStride * localSlotsPerSuper +
    relativeSplitFalseSelectLocalSlotInSuper super q localStride

def relativeOffsetReadCosted
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) : Costed (Option Nat) :=
  Costed.map (fun offset? => offset?.map (fun offset => base + offset))
    (table.readCosted slot)

def builtRelativeSplitSparseExceptionReadCosted
    (shape : Cartesian.CartesianShape)
    (base localSlot localOccurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind
    ((builtRelativeSplitFalseSelectFlagRankData shape).rankCosted
      true localSlot)
    fun exceptionRank =>
      relativeOffsetReadCosted
        (builtRelativeSplitFalseSelectSparseRelativeTable shape)
        base
        (relativeSplitFalseSelectSparseCompactSlot
          exceptionRank localOccurrence
          (sparseDenseFalseSelectLocalStride shape))

theorem builtRelativeSplitSparseExceptionReadCosted_cost_le_five
    (shape : Cartesian.CartesianShape)
    (base localSlot localOccurrence : Nat) :
    (builtRelativeSplitSparseExceptionReadCosted
      shape base localSlot localOccurrence).cost <= 5 := by
  unfold builtRelativeSplitSparseExceptionReadCosted
    relativeOffsetReadCosted
  have hrank :
      ((builtRelativeSplitFalseSelectFlagRankData shape).rankCosted
        true localSlot).cost <= 4 :=
    (builtRelativeSplitFalseSelectFlagRankData shape).rankCosted_cost_le_four
      true localSlot
  have hread :
      ((builtRelativeSplitFalseSelectSparseRelativeTable shape).readCosted
        (relativeSplitFalseSelectSparseCompactSlot
          (((builtRelativeSplitFalseSelectFlagRankData shape).rankCosted
            true localSlot).value)
          localOccurrence
          (sparseDenseFalseSelectLocalStride shape))).cost <= 1 :=
    (builtRelativeSplitFalseSelectSparseRelativeTable shape).readCosted_cost_le_one
      _
  simp [Costed.bind] at *
  omega

theorem builtRelativeSplitSparseExceptionReadCosted_erase
    (shape : Cartesian.CartesianShape)
    (base localSlot localOccurrence : Nat) :
    (builtRelativeSplitSparseExceptionReadCosted
      shape base localSlot localOccurrence).erase =
      ((builtRelativeSplitFalseSelectSparseRelativeEntries shape)[
          relativeSplitFalseSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectSparseFlagBits shape)
              localSlot)
            localOccurrence
            (sparseDenseFalseSelectLocalStride shape)]?).map
        (fun offset => base + offset) := by
  have hrank :=
    (builtRelativeSplitFalseSelectFlagRankData shape).rankCosted_exact
      true localSlot
  change
      ((builtRelativeSplitFalseSelectFlagRankData shape).rankCosted
        true localSlot).value =
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseFlagBits shape)
          localSlot at hrank
  let slot :=
    relativeSplitFalseSelectSparseCompactSlot
      (RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseFlagBits shape)
        localSlot)
      localOccurrence
      (sparseDenseFalseSelectLocalStride shape)
  have hread :
      ((builtRelativeSplitFalseSelectSparseRelativeTable shape).readCosted
        slot).value =
        (builtRelativeSplitFalseSelectSparseRelativeEntries shape)[slot]? := by
    simpa [Costed.erase] using
      (builtRelativeSplitFalseSelectSparseRelativeTable shape).readCosted_erase
        slot
  unfold builtRelativeSplitSparseExceptionReadCosted
    relativeOffsetReadCosted
  simp [Costed.bind, Costed.erase, hrank, slot, hread]

theorem builtRelativeSplitSparseExceptionReadCosted_lookup_exact
    (shape : Cartesian.CartesianShape)
    {globalLocalSlot localOccurrence pos : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape)
    (hsparse :
      builtRelativeSplitFalseSelectLocalIsSparse
        shape globalLocalSlot = true)
    (hocc :
      localOccurrence < sparseDenseFalseSelectLocalStride shape)
    (hselect :
      RMQ.Succinct.select false shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence) =
        some pos) :
    (builtRelativeSplitSparseExceptionReadCosted
      shape
      (builtRelativeSplitFalseSelectPosition shape
        (builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot))
      globalLocalSlot
      localOccurrence).erase =
      some
        (builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot) +
          (pos -
            builtRelativeSplitFalseSelectPosition shape
              (builtRectangularFalseSelectLocalBaseOccurrence
                shape globalLocalSlot))) := by
  rw [builtRelativeSplitSparseExceptionReadCosted_erase]
  have hlookup :=
    builtRelativeSplitFalseSelectSparseRelativeEntries_lookup_exact
      shape hslot hsparse hocc hselect
  simpa [relativeSplitFalseSelectSparseCompactSlot] using
    congrArg
      (Option.map
        (fun offset =>
          builtRelativeSplitFalseSelectPosition shape
              (builtRectangularFalseSelectLocalBaseOccurrence
                shape globalLocalSlot) +
            offset))
      hlookup

def builtRelativeSplitSparseExceptionNarrowReadCosted
    (shape : Cartesian.CartesianShape)
    (base localSlot localOccurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind
    ((builtRelativeSplitFalseSelectSparseExceptionFlagRankData
      shape).rankCosted true localSlot)
    fun exceptionRank =>
      relativeOffsetReadCosted
        (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
          shape)
        base
        (relativeSplitFalseSelectSparseCompactSlot
          exceptionRank localOccurrence
          (sparseDenseFalseSelectLocalStride shape))

theorem builtRelativeSplitSparseExceptionNarrowReadCosted_cost_le_five
    (shape : Cartesian.CartesianShape)
    (base localSlot localOccurrence : Nat) :
    (builtRelativeSplitSparseExceptionNarrowReadCosted
      shape base localSlot localOccurrence).cost <= 5 := by
  unfold builtRelativeSplitSparseExceptionNarrowReadCosted
    relativeOffsetReadCosted
  have hrank :
      ((builtRelativeSplitFalseSelectSparseExceptionFlagRankData
        shape).rankCosted true localSlot).cost <= 4 :=
    (builtRelativeSplitFalseSelectSparseExceptionFlagRankData
      shape).rankCosted_cost_le_four true localSlot
  have hread :
      ((builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).readCosted
        (relativeSplitFalseSelectSparseCompactSlot
          (((builtRelativeSplitFalseSelectSparseExceptionFlagRankData
            shape).rankCosted true localSlot).value)
          localOccurrence
          (sparseDenseFalseSelectLocalStride shape))).cost <= 1 :=
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
      shape).readCosted_cost_le_one _
  simp [Costed.bind, Costed.map] at *
  omega

theorem builtRelativeSplitSparseExceptionNarrowReadCosted_erase
    (shape : Cartesian.CartesianShape)
    (base localSlot localOccurrence : Nat) :
    (builtRelativeSplitSparseExceptionNarrowReadCosted
      shape base localSlot localOccurrence).erase =
      ((builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
          shape)[
          relativeSplitFalseSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectSparseExceptionFlagBits
                shape)
              localSlot)
            localOccurrence
            (sparseDenseFalseSelectLocalStride shape)]?).map
        (fun offset => base + offset) := by
  have hrank :=
    (builtRelativeSplitFalseSelectSparseExceptionFlagRankData
      shape).rankCosted_exact true localSlot
  change
      ((builtRelativeSplitFalseSelectSparseExceptionFlagRankData
        shape).rankCosted true localSlot).value =
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
          localSlot at hrank
  let slot :=
    relativeSplitFalseSelectSparseCompactSlot
      (RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
        localSlot)
      localOccurrence
      (sparseDenseFalseSelectLocalStride shape)
  have hread :
      ((builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).readCosted slot).value =
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
          shape)[slot]? := by
    simpa [Costed.erase] using
      (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).readCosted_erase slot
  unfold builtRelativeSplitSparseExceptionNarrowReadCosted
    relativeOffsetReadCosted
  simp [Costed.bind, Costed.map, Costed.erase, hrank, slot, hread]

theorem builtRelativeSplitSparseExceptionNarrowReadCosted_lookup_exact
    (shape : Cartesian.CartesianShape)
    {globalLocalSlot localOccurrence pos : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape)
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
    (builtRelativeSplitSparseExceptionNarrowReadCosted
      shape
      (builtRelativeSplitFalseSelectPosition shape
        (builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot))
      globalLocalSlot
      localOccurrence).erase =
      some
        (builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot) +
          (pos -
            builtRelativeSplitFalseSelectPosition shape
              (builtRectangularFalseSelectLocalBaseOccurrence
                shape globalLocalSlot))) := by
  rw [builtRelativeSplitSparseExceptionNarrowReadCosted_erase]
  have hlookup :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_lookup_exact
      shape hslot hflag hocc hend hselect
  simpa [relativeSplitFalseSelectSparseCompactSlot] using
    congrArg
      (Option.map
        (fun offset =>
          builtRelativeSplitFalseSelectPosition shape
              (builtRectangularFalseSelectLocalBaseOccurrence
                shape globalLocalSlot) +
            offset))
      hlookup

theorem builtRelativeSplitFalseSelectSuperEntry_marked_eq_long
    (shape : Cartesian.CartesianShape) (superSlot : Nat) :
    relativeSplitFalseSelectEntryIsMarked
      (builtRelativeSplitFalseSelectSuperEntry shape superSlot) =
        builtRelativeSplitFalseSelectSuperIsLong shape superSlot := by
  unfold builtRelativeSplitFalseSelectSuperEntry
  by_cases hlong :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true
  · simp [relativeSplitFalseSelectEntryIsMarked, hlong]
  · have hfalse :
        builtRelativeSplitFalseSelectSuperIsLong shape superSlot =
          false := by
      cases h :
          builtRelativeSplitFalseSelectSuperIsLong shape superSlot
      · rfl
      · contradiction
    simp [relativeSplitFalseSelectEntryIsMarked, hfalse]

theorem builtRelativeSplitFalseSelectLocalEntry_marked_eq_flag
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    relativeSplitFalseSelectEntryIsMarked
      (builtRelativeSplitFalseSelectLocalEntry shape globalLocalSlot) =
        (builtRelativeSplitFalseSelectCompactLocalEntryIsLive
            shape globalLocalSlot &&
          builtRelativeSplitFalseSelectLocalIsSparseException
            shape globalLocalSlot) := by
  unfold builtRelativeSplitFalseSelectLocalEntry
  by_cases hlive :
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape globalLocalSlot = true
  · by_cases hflag :
        builtRelativeSplitFalseSelectLocalIsSparseException
          shape globalLocalSlot = true
    · simp [relativeSplitFalseSelectEntryIsMarked, hlive, hflag]
    · have hfalse :
          builtRelativeSplitFalseSelectLocalIsSparseException
            shape globalLocalSlot = false := by
        cases h :
            builtRelativeSplitFalseSelectLocalIsSparseException
              shape globalLocalSlot
        · rfl
        · contradiction
      simp [relativeSplitFalseSelectEntryIsMarked, hlive, hfalse]
  · have hfalse :
        builtRelativeSplitFalseSelectCompactLocalEntryIsLive
          shape globalLocalSlot = false := by
      cases h :
          builtRelativeSplitFalseSelectCompactLocalEntryIsLive
            shape globalLocalSlot
      · rfl
      · exact False.elim (hlive h)
    simp [relativeSplitFalseSelectEntryIsMarked, hfalse]

theorem builtRelativeSplitFalseSelectLocalBaseOccurrence_exact
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat)
    (hlive :
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape globalLocalSlot = true) :
    relativeSplitFalseSelectLocalBaseOccurrence
      (builtRelativeSplitFalseSelectSuperEntry shape
        (globalLocalSlot /
          builtRectangularFalseSelectLocalSlotsPerSuper shape))
      (builtRelativeSplitFalseSelectLocalEntry shape globalLocalSlot) =
      builtRectangularFalseSelectLocalBaseOccurrence
        shape globalLocalSlot := by
  let superBase :=
    globalLocalSlot /
        builtRectangularFalseSelectLocalSlotsPerSuper shape *
      sparseDenseFalseSelectSuperStride shape
  let base :=
    builtRectangularFalseSelectLocalBaseOccurrence
      shape globalLocalSlot
  have hbase_ge :
      superBase <= base := by
    simp [superBase, base, builtRectangularFalseSelectLocalBaseOccurrence,
      builtRectangularFalseSelectLocalSlotInSuperOfGlobal]
  simp [relativeSplitFalseSelectLocalBaseOccurrence,
    builtRelativeSplitFalseSelectSuperEntry,
    builtRelativeSplitFalseSelectLocalEntry, hlive,
    builtRelativeSplitFalseSelectLocalSuperSlot]
  omega

theorem builtRelativeSplitFalseSelectLocalBasePosition_exact
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat)
    (hlive :
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape globalLocalSlot = true) :
    relativeSplitFalseSelectLocalBasePosition
      (sparseDenseFalseSelectWordBits shape)
      (builtRelativeSplitFalseSelectSuperEntry shape
        (globalLocalSlot /
          builtRectangularFalseSelectLocalSlotsPerSuper shape))
      (builtRelativeSplitFalseSelectLocalEntry shape globalLocalSlot) =
      builtRelativeSplitFalseSelectPosition shape
        (builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot) := by
  let superSlot :=
    globalLocalSlot /
      builtRectangularFalseSelectLocalSlotsPerSuper shape
  let superBase :=
    superSlot * sparseDenseFalseSelectSuperStride shape
  let base :=
    builtRectangularFalseSelectLocalBaseOccurrence
      shape globalLocalSlot
  let superPos := builtRelativeSplitFalseSelectPosition shape superBase
  let basePos := builtRelativeSplitFalseSelectPosition shape base
  let wordSize := sparseDenseFalseSelectWordBits shape
  have hbase_ge : superBase <= base := by
    simp [superBase, base, superSlot,
      builtRectangularFalseSelectLocalBaseOccurrence,
      builtRectangularFalseSelectLocalSlotInSuperOfGlobal]
  have hposMono : superPos <= basePos := by
    simpa [superPos, basePos] using
      builtRelativeSplitFalseSelectPosition_mono shape hbase_ge
  have hdivMono :
      superPos / wordSize <= basePos / wordSize := by
    exact Nat.div_le_div_right hposMono
  have hmod :
      basePos / wordSize * wordSize +
          (basePos - basePos / wordSize * wordSize) =
        basePos := by
    have hle := Nat.div_mul_le_self basePos wordSize
    omega
  have hwordIndexEq :
      superPos / wordSize +
          (basePos / wordSize - superPos / wordSize) =
        basePos / wordSize := by
    omega
  have hassembled :
      (superPos / wordSize +
          (basePos / wordSize - superPos / wordSize)) * wordSize +
          (basePos - basePos / wordSize * wordSize) =
        basePos := by
    rw [hwordIndexEq]
    exact hmod
  simpa [relativeSplitFalseSelectLocalBasePosition,
    builtRelativeSplitFalseSelectSuperEntry,
    builtRelativeSplitFalseSelectLocalEntry, hlive,
    builtRelativeSplitFalseSelectLocalSuperSlot,
    superSlot, superBase, base, superPos, basePos, wordSize]
    using hassembled

theorem falseSelectOccurrenceCount_le_bpCode_length
    (shape : Cartesian.CartesianShape) :
    falseSelectOccurrenceCount shape <= shape.bpCode.length := by
  have hcount : falseSelectOccurrenceCount shape = shape.size :=
    falseSelectOccurrenceCount_eq_size shape
  have hbp : shape.bpCode.length = 2 * shape.size :=
    Cartesian.CartesianShape.bpCode_length shape
  omega

theorem builtRelativeSplitFalseSelectPosition_le_length
    (shape : Cartesian.CartesianShape) (occurrence : Nat) :
    builtRelativeSplitFalseSelectPosition shape occurrence <=
      shape.bpCode.length := by
  unfold builtRelativeSplitFalseSelectPosition
  cases hselect :
      RMQ.Succinct.select false shape.bpCode occurrence with
  | none =>
      simp
  | some pos =>
      have hpos : pos < shape.bpCode.length :=
        RMQ.Succinct.select_bounds hselect
      simp
      omega

theorem builtRelativeSplitFalseSelectPosition_lt_length_of_lt_count
    (shape : Cartesian.CartesianShape) {occurrence : Nat}
    (hocc : occurrence < falseSelectOccurrenceCount shape) :
    builtRelativeSplitFalseSelectPosition shape occurrence <
      shape.bpCode.length := by
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hocc with ⟨pos, hselect⟩
  rw [builtRelativeSplitFalseSelectPosition_eq_of_select shape hselect]
  exact RMQ.Succinct.select_bounds hselect

def builtRelativeSplitFalseSelectSuperFieldWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  sparseDenseFalseSelectWordBits shape

def builtRelativeSplitFalseSelectLocalFieldWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape

theorem builtRelativeSplitFalseSelectSuperEntries_mem_fields_lt_width
    {shape : Cartesian.CartesianShape}
    {entry : SparseDenseFalseSelectDenseLocalEntry}
    (hmem :
      List.Mem entry
        (builtRelativeSplitFalseSelectSuperEntries shape)) :
    entry.baseOccurrence <
        2 ^ builtRelativeSplitFalseSelectSuperFieldWidth shape /\
      entry.baseWordIndex <
        2 ^ builtRelativeSplitFalseSelectSuperFieldWidth shape /\
        entry.rankBefore <
          2 ^ builtRelativeSplitFalseSelectSuperFieldWidth shape /\
          entry.firstOffset <
            2 ^ builtRelativeSplitFalseSelectSuperFieldWidth shape := by
  rcases List.mem_map.mp hmem with ⟨superSlot, hslotMem, rfl⟩
  have hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape :=
    List.mem_range.mp hslotMem
  let wordSize := sparseDenseFalseSelectWordBits shape
  let baseOccurrence :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
  let basePosition :=
    builtRelativeSplitFalseSelectPosition shape baseOccurrence
  have hwordPos : 0 < wordSize := by
    simpa [wordSize] using sparseDenseFalseSelectWordBits_pos shape
  have hbaseCount :
      baseOccurrence < falseSelectOccurrenceCount shape := by
    simpa [baseOccurrence] using
      builtRelativeSplitFalseSelectSuperBaseOccurrence_lt_count
        shape hslot
  have hbaseLen :
      baseOccurrence < shape.bpCode.length := by
    exact Nat.lt_of_lt_of_le hbaseCount
      (falseSelectOccurrenceCount_le_bpCode_length shape)
  have hlenPow :
      shape.bpCode.length < 2 ^ wordSize := by
    simpa [wordSize, sparseDenseFalseSelectWordBits,
      SuccinctRank.machineWordBits] using
      (Nat.lt_log2_self (n := shape.bpCode.length))
  have hbasePow : baseOccurrence < 2 ^ wordSize :=
    Nat.lt_trans hbaseLen hlenPow
  have hpositionLen : basePosition <= shape.bpCode.length := by
    simpa [basePosition] using
      builtRelativeSplitFalseSelectPosition_le_length
        shape baseOccurrence
  have hwordIndexPow :
      basePosition / wordSize < 2 ^ wordSize := by
    have hdivLe : basePosition / wordSize <= basePosition :=
      Nat.div_le_self basePosition wordSize
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans hdivLe hpositionLen) hlenPow
  have hmarkPow :
      (if builtRelativeSplitFalseSelectSuperIsLong shape superSlot then
          1 else 0) < 2 ^ wordSize := by
    by_cases hlong :
        builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true
    · simp [hlong, one_lt_two_pow_of_pos hwordPos]
    · have hfalse :
          builtRelativeSplitFalseSelectSuperIsLong shape superSlot =
            false := by
        cases h :
            builtRelativeSplitFalseSelectSuperIsLong shape superSlot
        · rfl
        · contradiction
      simp [hfalse, Nat.pow_pos (by omega : 0 < 2)]
  have hoffsetLtWord :
      basePosition - basePosition / wordSize * wordSize < wordSize := by
    simpa [Nat.mod_eq_sub_div_mul] using
      Nat.mod_lt basePosition hwordPos
  have hoffsetPow : basePosition - basePosition / wordSize * wordSize <
      2 ^ wordSize :=
    Nat.lt_trans hoffsetLtWord
      (by
        have hsucc := SuccinctSpace.nat_succ_le_two_pow wordSize
        omega)
  simpa [builtRelativeSplitFalseSelectSuperEntry,
    builtRelativeSplitFalseSelectSuperFieldWidth, wordSize,
    baseOccurrence, basePosition] using
    ⟨hbasePow, hwordIndexPow, hmarkPow, hoffsetPow⟩

def builtRelativeSplitFalseSelectSuperTable
    (shape : Cartesian.CartesianShape) :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      (builtRelativeSplitFalseSelectSuperEntries shape)
      (builtRelativeSplitFalseSelectSuperFieldWidth shape) :=
  FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.ofEntries
    (builtRelativeSplitFalseSelectSuperEntries shape)
    (builtRelativeSplitFalseSelectSuperFieldWidth shape)
    (by
      intro entry hmem
      exact
        builtRelativeSplitFalseSelectSuperEntries_mem_fields_lt_width hmem)

theorem builtRelativeSplitFalseSelectSuperTable_payload_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSuperTable shape).payload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        40 shape.bpCode.length := by
  let payload := (builtRelativeSplitFalseSelectSuperTable shape).payload.length
  let superCount := builtRectangularFalseSelectSuperSlotCount shape
  let wordBits := sparseDenseFalseSelectWordBits shape
  let superStride := sparseDenseFalseSelectSuperStride shape
  let ell := sparseDenseFalseSelectEll shape
  let ell3 := ell * (ell * ell)
  let n := shape.bpCode.length
  have hellOne : 1 <= ell3 := by
    have hell : 1 <= ell := by
      simp [ell, sparseDenseFalseSelectEll]
    have hmul := Nat.mul_le_mul hell (Nat.mul_le_mul hell hell)
    simpa [ell3] using hmul
  have hpayload :
      payload = 4 * (superCount * wordBits) := by
    have hlen := (builtRelativeSplitFalseSelectSuperTable shape).payload_length
    simp [payload, superCount, wordBits,
      builtRelativeSplitFalseSelectSuperTable,
      builtRelativeSplitFalseSelectSuperFieldWidth,
      sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget,
      builtRelativeSplitFalseSelectSuperEntries_length] at hlen ⊢
    omega
  by_cases hnZero : n = 0
  · have hcountZero : falseSelectOccurrenceCount shape = 0 := by
      have hbp : shape.bpCode.length = 2 * shape.size :=
        Cartesian.CartesianShape.bpCode_length shape
      have hcount : falseSelectOccurrenceCount shape = shape.size :=
        falseSelectOccurrenceCount_eq_size shape
      omega
    have hsuperZero : superCount = 0 := by
      unfold superCount builtRectangularFalseSelectSuperSlotCount
        falseSelectCeilDiv
      rw [hcountZero]
      have hstride_pos : 0 < superStride := by
        simpa [superStride] using sparseDenseFalseSelectSuperStride_pos shape
      have hpred_lt : superStride - 1 < superStride :=
        Nat.pred_lt (Nat.ne_of_gt hstride_pos)
      simpa [superStride] using Nat.div_eq_of_lt hpred_lt
    simp [payload, hpayload, hsuperZero,
      SuccinctSpace.logLogCubedSampledDirectoryOverhead]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
    have hcountLe : falseSelectOccurrenceCount shape <= n := by
      simpa [n] using falseSelectOccurrenceCount_le_bpCode_length shape
    have hsuperStrideLe : superStride <= 4 * n := by
      have hsq :=
        machineWordBits_sq_le_four_mul_self_of_pos
          (n := shape.bpCode.length) hnPos
      simpa [superStride, wordBits, n,
        sparseDenseFalseSelectSuperStride,
        sparseDenseFalseSelectWordBits] using hsq
    have hsuperCountMul :
        superCount * superStride <=
          falseSelectOccurrenceCount shape + superStride := by
      simpa [superCount, superStride,
        builtRectangularFalseSelectSuperSlotCount] using
        falseSelectCeilDiv_mul_le_add
          (falseSelectOccurrenceCount shape) superStride
    have hpayloadMul :
        payload * wordBits <= 20 * (ell3 * n) := by
      rw [hpayload]
      calc
        4 * (superCount * wordBits) * wordBits =
            4 * (superCount * superStride) := by
              simp [superStride, wordBits,
                sparseDenseFalseSelectSuperStride,
                Nat.mul_left_comm, Nat.mul_comm]
        _ <= 4 * (falseSelectOccurrenceCount shape + superStride) := by
              exact Nat.mul_le_mul_left 4 hsuperCountMul
        _ <= 4 * (n + 4 * n) := by
              exact Nat.mul_le_mul_left 4
                (Nat.add_le_add hcountLe hsuperStrideLe)
        _ = 20 * n := by omega
        _ <= 20 * (ell3 * n) := by
              have hmul := Nat.mul_le_mul_right n hellOne
              have hscaled := Nat.mul_le_mul_left 20 hmul
              simpa [Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm] using hscaled
    exact
      payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
        (shape := shape) (payload := payload) (scale := 20)
        (by
          simpa [wordBits, ell, ell3, n, Nat.mul_assoc,
            Nat.mul_left_comm, Nat.mul_comm] using hpayloadMul)

theorem builtRelativeSplitFalseSelectLocalEntries_mem_fields_lt_width
    {shape : Cartesian.CartesianShape}
    {entry : SparseDenseFalseSelectDenseLocalEntry}
    (hmem :
      List.Mem entry
        (builtRelativeSplitFalseSelectLocalEntries shape)) :
    entry.baseOccurrence <
        2 ^ builtRelativeSplitFalseSelectLocalFieldWidth shape /\
      entry.baseWordIndex <
        2 ^ builtRelativeSplitFalseSelectLocalFieldWidth shape /\
        entry.rankBefore <
          2 ^ builtRelativeSplitFalseSelectLocalFieldWidth shape /\
          entry.firstOffset <
            2 ^ builtRelativeSplitFalseSelectLocalFieldWidth shape := by
  rcases List.mem_map.mp hmem with ⟨globalLocalSlot, hslotMem, rfl⟩
  let superSlot :=
    builtRelativeSplitFalseSelectLocalSuperSlot shape globalLocalSlot
  let superBase :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
  let base :=
    builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot
  let superPos := builtRelativeSplitFalseSelectPosition shape superBase
  let basePos := builtRelativeSplitFalseSelectPosition shape base
  let wordSize := sparseDenseFalseSelectWordBits shape
  let superLongSpan := sparseDenseFalseSelectSuperLongSpan shape
  let relWidth := builtRelativeSplitFalseSelectLocalFieldWidth shape
  have hwordPos : 0 < wordSize := by
    simpa [wordSize] using sparseDenseFalseSelectWordBits_pos shape
  have hellPos : 0 < sparseDenseFalseSelectEll shape := by
    simp [sparseDenseFalseSelectEll]
  have hrelPos : 0 < relWidth := by
    simp [relWidth, builtRelativeSplitFalseSelectLocalFieldWidth,
      builtRelativeSplitFalseSelectSparseExceptionRelativeWidth,
      SuccinctRank.machineWordBits_pos]
  have hpowPos : 0 < 2 ^ relWidth := Nat.pow_pos (by omega : 0 < 2)
  have hfield_of_lt_min :
      forall {x : Nat},
        x < shape.bpCode.length ->
        x < superLongSpan ->
          x < 2 ^ relWidth := by
    intro x hbp hlong
    have hmin :
        x <
          Nat.min shape.bpCode.length
            (sparseDenseFalseSelectSuperLongSpan shape) :=
      Nat.lt_min.mpr ⟨hbp, by simpa [superLongSpan] using hlong⟩
    simpa [relWidth, builtRelativeSplitFalseSelectLocalFieldWidth,
      builtRelativeSplitFalseSelectSparseExceptionRelativeWidth] using
      lt_two_pow_machineWordBits_of_lt hmin
  by_cases hlive :
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape globalLocalSlot = true
  · have hliveFacts :
        builtRelativeSplitFalseSelectSuperIsLong shape superSlot = false /\
          base < falseSelectOccurrenceCount shape := by
      unfold builtRelativeSplitFalseSelectCompactLocalEntryIsLive at hlive
      by_cases hlong :
          builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true
      · simp [superSlot, hlong] at hlive
      · have hfalse :
            builtRelativeSplitFalseSelectSuperIsLong shape superSlot =
              false := by
          cases h :
              builtRelativeSplitFalseSelectSuperIsLong shape superSlot
          · rfl
          · contradiction
        simp [superSlot, hfalse] at hlive
        exact ⟨hfalse, hlive⟩
    rcases hliveFacts with ⟨hshort, hbaseCount⟩
    have hsuperBaseLeBase : superBase <= base := by
      simp [superBase, base, superSlot,
        builtRelativeSplitFalseSelectSuperBaseOccurrence,
        builtRelativeSplitFalseSelectLocalSuperSlot,
        builtRectangularFalseSelectLocalBaseOccurrence,
        builtRectangularFalseSelectLocalSlotInSuperOfGlobal]
    have hbaseBoundary :
        base <
          superBase + sparseDenseFalseSelectSuperStride shape := by
      simpa [base, superBase, superSlot,
        builtRelativeSplitFalseSelectSuperBaseOccurrence] using
        builtRectangularFalseSelectLocalBaseOccurrence_lt_superBoundary
          shape globalLocalSlot
    have hbaseEnd :
        base <
          builtRelativeSplitFalseSelectSuperEndOccurrence
            shape superSlot := by
      unfold builtRelativeSplitFalseSelectSuperEndOccurrence
      exact Nat.lt_min.mpr
        ⟨by
          simpa [superBase,
            builtRelativeSplitFalseSelectSuperBaseOccurrence] using
            hbaseBoundary,
          hbaseCount⟩
    have hbaseBp :
        base < shape.bpCode.length := by
      exact Nat.lt_of_lt_of_le hbaseCount
        (falseSelectOccurrenceCount_le_bpCode_length shape)
    have hdeltaBp :
        base - superBase < shape.bpCode.length := by
      omega
    have hstrideLeLong :
        sparseDenseFalseSelectSuperStride shape <= superLongSpan := by
      have hwordOne : 1 <= wordSize := by omega
      have hellOne : 1 <= sparseDenseFalseSelectEll shape := by omega
      have h1 :
          sparseDenseFalseSelectSuperStride shape <=
            sparseDenseFalseSelectSuperStride shape * wordSize := by
        simpa using
          Nat.mul_le_mul_left
            (sparseDenseFalseSelectSuperStride shape) hwordOne
      have h2 :
          sparseDenseFalseSelectSuperStride shape * wordSize <=
            sparseDenseFalseSelectSuperStride shape * wordSize *
              sparseDenseFalseSelectEll shape := by
        simpa using
          Nat.mul_le_mul_left
            (sparseDenseFalseSelectSuperStride shape * wordSize) hellOne
      exact Nat.le_trans h1 (by
        simpa [superLongSpan, sparseDenseFalseSelectSuperLongSpan,
          sparseDenseFalseSelectSuperStride, wordSize,
          Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h2)
    have hdeltaLong :
        base - superBase < superLongSpan := by
      have hdeltaStride :
          base - superBase < sparseDenseFalseSelectSuperStride shape := by
        omega
      exact Nat.lt_of_lt_of_le hdeltaStride hstrideLeLong
    have hbaseField :
        base - superBase < 2 ^ relWidth :=
      hfield_of_lt_min hdeltaBp hdeltaLong
    have hsuperCount :
        superBase < falseSelectOccurrenceCount shape := by
      omega
    have hbasePosLt :
        basePos < shape.bpCode.length := by
      simpa [basePos] using
        builtRelativeSplitFalseSelectPosition_lt_length_of_lt_count
          shape hbaseCount
    have hsuperPosLt :
        superPos < shape.bpCode.length := by
      simpa [superPos] using
        builtRelativeSplitFalseSelectPosition_lt_length_of_lt_count
          shape hsuperCount
    have hposMono : superPos <= basePos := by
      simpa [superPos, basePos] using
        builtRelativeSplitFalseSelectPosition_mono
          shape hsuperBaseLeBase
    have hindexDeltaLe :
        basePos / wordSize - superPos / wordSize <=
          basePos - superPos :=
      nat_div_sub_div_le_sub hwordPos hposMono
    have hindexBp :
        basePos / wordSize - superPos / wordSize <
          shape.bpCode.length := by
      have hdivLe : basePos / wordSize <= basePos :=
        Nat.div_le_self basePos wordSize
      omega
    rcases falseSelect_exists_of_lt_occurrence_count
        shape hbaseCount with ⟨baseWitness, hbaseSelect⟩
    have hbasePosEq : basePos = baseWitness := by
      simpa [basePos] using
        builtRelativeSplitFalseSelectPosition_eq_of_select
          shape hbaseSelect
    have hoffLongWitness :
        baseWitness - superPos < superLongSpan := by
      have hraw :=
        builtRelativeSplitFalseSelect_selected_offset_lt_superLongSpan
          shape superSlot
          (localBaseOccurrence := superBase)
          (q := base) (pos := baseWitness)
          hshort (by simp [superBase])
          hsuperBaseLeBase hbaseEnd hbaseSelect
      simpa [superPos, superBase, superLongSpan] using hraw
    have hoffLong :
        basePos - superPos < superLongSpan := by
      simpa [hbasePosEq] using hoffLongWitness
    have hindexLong :
        basePos / wordSize - superPos / wordSize < superLongSpan :=
      Nat.lt_of_le_of_lt hindexDeltaLe hoffLong
    have hindexField :
        basePos / wordSize - superPos / wordSize < 2 ^ relWidth :=
      hfield_of_lt_min hindexBp hindexLong
    have hmarkField :
        (if builtRelativeSplitFalseSelectLocalIsSparseException
              shape globalLocalSlot then 1 else 0) < 2 ^ relWidth := by
      by_cases hflag :
          builtRelativeSplitFalseSelectLocalIsSparseException
            shape globalLocalSlot = true
      · have hone : 1 < 2 ^ relWidth :=
          one_lt_two_pow_of_pos hrelPos
        simpa [hflag] using hone
      · have hfalse :
            builtRelativeSplitFalseSelectLocalIsSparseException
              shape globalLocalSlot = false := by
          cases h :
              builtRelativeSplitFalseSelectLocalIsSparseException
                shape globalLocalSlot
          · rfl
          · contradiction
        simp [hfalse, hpowPos]
    have hoffsetLtWord :
        basePos - basePos / wordSize * wordSize < wordSize := by
      simpa [Nat.mod_eq_sub_div_mul] using
        Nat.mod_lt basePos hwordPos
    have hbpLenPos : 0 < shape.bpCode.length := by
      omega
    have hwordLeBp : wordSize <= shape.bpCode.length := by
      simpa [wordSize, sparseDenseFalseSelectWordBits] using
        machineWordBits_le_self_of_pos hbpLenPos
    have hwordLeLong : wordSize <= superLongSpan := by
      have hstridePos := sparseDenseFalseSelectSuperStride_pos shape
      have hwordOne : 1 <= wordSize := by omega
      have hellOne : 1 <= sparseDenseFalseSelectEll shape := by omega
      have hleStride : wordSize <=
          sparseDenseFalseSelectSuperStride shape * wordSize := by
        have hmul :=
          Nat.mul_le_mul_right wordSize
            (by exact (show 1 <= sparseDenseFalseSelectSuperStride shape by omega))
        simpa [Nat.mul_comm] using hmul
      have hleLong :
          sparseDenseFalseSelectSuperStride shape * wordSize <=
            superLongSpan := by
        have hmul :=
          Nat.mul_le_mul_left
            (sparseDenseFalseSelectSuperStride shape * wordSize)
            hellOne
        simpa [superLongSpan, sparseDenseFalseSelectSuperLongSpan,
          sparseDenseFalseSelectSuperStride, wordSize,
          Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      exact Nat.le_trans hleStride hleLong
    have hoffsetBp :
        basePos - basePos / wordSize * wordSize <
          shape.bpCode.length :=
      Nat.lt_of_lt_of_le hoffsetLtWord hwordLeBp
    have hoffsetLong :
        basePos - basePos / wordSize * wordSize < superLongSpan :=
      Nat.lt_of_lt_of_le hoffsetLtWord hwordLeLong
    have hoffsetField :
        basePos - basePos / wordSize * wordSize < 2 ^ relWidth :=
      hfield_of_lt_min hoffsetBp hoffsetLong
    simpa [builtRelativeSplitFalseSelectLocalEntry, hlive,
      builtRelativeSplitFalseSelectLocalFieldWidth, relWidth,
      superSlot, superBase, base, superPos, basePos, wordSize] using
      ⟨hbaseField, hindexField, hmarkField, hoffsetField⟩
  · have hfalse :
        builtRelativeSplitFalseSelectCompactLocalEntryIsLive
          shape globalLocalSlot = false := by
      cases h :
          builtRelativeSplitFalseSelectCompactLocalEntryIsLive
            shape globalLocalSlot
      · rfl
      · exact False.elim (hlive h)
    have hzero : 0 < 2 ^ relWidth := hpowPos
    have htuple :
        0 < 2 ^ relWidth /\
          0 < 2 ^ relWidth /\
            0 < 2 ^ relWidth /\
              0 < 2 ^ relWidth := by
      exact ⟨hzero, hzero, hzero, hzero⟩
    simpa [builtRelativeSplitFalseSelectLocalEntry, hfalse,
      builtRelativeSplitFalseSelectLocalFieldWidth, relWidth] using
      htuple

def builtRelativeSplitFalseSelectLocalTable
    (shape : Cartesian.CartesianShape) :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      (builtRelativeSplitFalseSelectLocalEntries shape)
      (builtRelativeSplitFalseSelectLocalFieldWidth shape) :=
  FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.ofEntries
    (builtRelativeSplitFalseSelectLocalEntries shape)
    (builtRelativeSplitFalseSelectLocalFieldWidth shape)
    (by
      intro entry hmem
      exact
        builtRelativeSplitFalseSelectLocalEntries_mem_fields_lt_width hmem)

theorem builtRelativeSplitFalseSelectLocalTable_payload_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLocalTable shape).payload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        640 shape.bpCode.length := by
  let payload := (builtRelativeSplitFalseSelectLocalTable shape).payload.length
  let m := builtRectangularFalseSelectLocalSlotCount shape
  let relWidth := builtRelativeSplitFalseSelectLocalFieldWidth shape
  let wordBits := sparseDenseFalseSelectWordBits shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let ell := sparseDenseFalseSelectEll shape
  let ell2 := ell * ell
  let ell3 := ell * (ell * ell)
  let n := shape.bpCode.length
  have hpayload :
      payload = 4 * (m * relWidth) := by
    have hlen :=
      (builtRelativeSplitFalseSelectLocalTable shape).payload_length
    simp [payload, m, relWidth,
      builtRelativeSplitFalseSelectLocalTable,
      builtRelativeSplitFalseSelectLocalFieldWidth,
      sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget,
      builtRelativeSplitFalseSelectLocalEntries_length] at hlen ⊢
    omega
  have hslots :
      m * localStride <= 10 * n := by
    simpa [m, localStride, n] using
      builtRectangularFalseSelectLocalSlotCount_mul_localStride_le_const_bpCode_length
        shape
  have hwidth : relWidth <= 4 * ell := by
    simpa [relWidth, ell, builtRelativeSplitFalseSelectLocalFieldWidth] using
      builtRelativeSplitFalseSelectSparseExceptionRelativeWidth_le_four_ell
        shape
  have hwordLower :
      wordBits <= 2 * localStride * ell2 := by
    simpa [wordBits, localStride, ell, ell2,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      sparseDenseFalseSelectWordBits_le_two_mul_localStride_mul_ell_sq
        shape
  have hcore :
      m * relWidth * wordBits <= 80 * (ell3 * n) := by
    calc
      m * relWidth * wordBits <=
          m * relWidth * (2 * localStride * ell2) := by
            exact Nat.mul_le_mul_left (m * relWidth) hwordLower
      _ = 2 * (m * localStride) * relWidth * ell2 := by
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ <= 2 * (10 * n) * (4 * ell) * ell2 := by
            have hmul := Nat.mul_le_mul hslots hwidth
            have hmul2 := Nat.mul_le_mul_left 2 hmul
            have hmul3 := Nat.mul_le_mul_right ell2 hmul2
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul3
      _ = 80 * (ell3 * n) := by
            simp [ell2, ell3, Nat.mul_assoc, Nat.mul_left_comm,
              Nat.mul_comm]
            let t := ell * (ell * (ell * n))
            change 2 * (4 * (10 * t)) = 80 * t
            omega
  have hpayloadMul :
      payload * wordBits <= 320 * (ell3 * n) := by
    rw [hpayload]
    have hmul := Nat.mul_le_mul_left 4 hcore
    calc
      4 * (m * relWidth) * wordBits <=
          4 * (80 * (ell3 * n)) := by
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      _ = 320 * (ell3 * n) := by
            let t := ell3 * n
            change 4 * (80 * t) = 320 * t
            omega
  exact
    payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
      (shape := shape) (payload := payload) (scale := 320)
      (by
        simpa [payload, wordBits, ell, ell3, n, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using hpayloadMul)

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_mul_wordBits_le
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
        shape).length *
        sparseDenseFalseSelectWordBits shape <=
      20 * ((sparseDenseFalseSelectEll shape *
        (sparseDenseFalseSelectEll shape *
          sparseDenseFalseSelectEll shape)) *
        shape.bpCode.length) := by
  let flagLen :=
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
      shape).length
  let m := builtRectangularFalseSelectLocalSlotCount shape
  let wordBits := sparseDenseFalseSelectWordBits shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let ell := sparseDenseFalseSelectEll shape
  let ell2 := ell * ell
  let ell3 := ell * (ell * ell)
  let n := shape.bpCode.length
  have hellOne : 1 <= ell := by
    simp [ell, sparseDenseFalseSelectEll]
  have hflagLe : flagLen <= m := by
    simpa [flagLen, m,
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length]
      using
      builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_full
        shape
  have hslots :
      m * localStride <= 10 * n := by
    simpa [m, localStride, n] using
      builtRectangularFalseSelectLocalSlotCount_mul_localStride_le_const_bpCode_length
        shape
  have hwordLower :
      wordBits <= 2 * localStride * ell2 := by
    simpa [wordBits, localStride, ell, ell2,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      sparseDenseFalseSelectWordBits_le_two_mul_localStride_mul_ell_sq
        shape
  have hmul :
      flagLen * wordBits <= 20 * (ell3 * n) := by
    calc
      flagLen * wordBits <= m * wordBits := by
        exact Nat.mul_le_mul_right wordBits hflagLe
      _ <= m * (2 * localStride * ell2) := by
        exact Nat.mul_le_mul_left m hwordLower
      _ = 2 * (m * localStride) * ell2 := by
        simp [Nat.mul_left_comm, Nat.mul_comm]
      _ <= 2 * (10 * n) * ell2 := by
        have hscaled := Nat.mul_le_mul_left 2 hslots
        exact Nat.mul_le_mul_right ell2 hscaled
      _ <= 20 * (ell3 * n) := by
        have hell2Le : ell2 <= ell3 := by
          have hmul := Nat.mul_le_mul_left ell2 hellOne
          simpa [ell2, ell3, Nat.mul_left_comm,
            Nat.mul_comm] using hmul
        have hright := Nat.mul_le_mul_left (20 * n) hell2Le
        calc
          2 * (10 * n) * ell2 = 20 * n * ell2 := by
            let t := ell2 * n
            simp [Nat.mul_left_comm, Nat.mul_comm]
            change 2 * (10 * t) = 20 * t
            omega
          _ <= 20 * n * ell3 := by
            simpa using hright
          _ = 20 * (ell3 * n) := by
            simp [Nat.mul_left_comm, Nat.mul_comm]
  simpa [flagLen, wordBits, ell, ell3, n, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm] using hmul

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
        shape).length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        40 shape.bpCode.length := by
  let flagLen :=
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
      shape).length
  let m := builtRectangularFalseSelectLocalSlotCount shape
  let wordBits := sparseDenseFalseSelectWordBits shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let ell := sparseDenseFalseSelectEll shape
  let ell2 := ell * ell
  let ell3 := ell * (ell * ell)
  let n := shape.bpCode.length
  have hellOne : 1 <= ell := by
    simp [ell, sparseDenseFalseSelectEll]
  have hflagLe : flagLen <= m := by
    simpa [flagLen, m,
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length]
      using
      builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_full
        shape
  have hslots :
      m * localStride <= 10 * n := by
    simpa [m, localStride, n] using
      builtRectangularFalseSelectLocalSlotCount_mul_localStride_le_const_bpCode_length
        shape
  have hwordLower :
      wordBits <= 2 * localStride * ell2 := by
    simpa [wordBits, localStride, ell, ell2,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      sparseDenseFalseSelectWordBits_le_two_mul_localStride_mul_ell_sq
        shape
  have hmul :
      flagLen * wordBits <= 20 * (ell3 * n) := by
    calc
      flagLen * wordBits <= m * wordBits := by
        exact Nat.mul_le_mul_right wordBits hflagLe
      _ <= m * (2 * localStride * ell2) := by
        exact Nat.mul_le_mul_left m hwordLower
      _ = 2 * (m * localStride) * ell2 := by
        simp [Nat.mul_left_comm, Nat.mul_comm]
      _ <= 2 * (10 * n) * ell2 := by
        have hscaled := Nat.mul_le_mul_left 2 hslots
        exact Nat.mul_le_mul_right ell2 hscaled
      _ <= 20 * (ell3 * n) := by
        have hell2Le : ell2 <= ell3 := by
          have hmul := Nat.mul_le_mul_left ell2 hellOne
          simpa [ell2, ell3, Nat.mul_left_comm,
            Nat.mul_comm] using hmul
        have hright := Nat.mul_le_mul_left (20 * n) hell2Le
        calc
          2 * (10 * n) * ell2 = 20 * n * ell2 := by
            let t := ell2 * n
            simp [Nat.mul_left_comm, Nat.mul_comm]
            change 2 * (10 * t) = 20 * t
            omega
          _ <= 20 * n * ell3 := by
            simpa using hright
          _ = 20 * (ell3 * n) := by
            simp [Nat.mul_left_comm, Nat.mul_comm]
  exact
    payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
      (shape := shape) (payload := flagLen) (scale := 20)
      (by
        simpa [flagLen, wordBits, ell, ell3, n, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using hmul)

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData_auxPayload_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData
        shape).auxPayload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        192 shape.bpCode.length + 16 := by
  let flagBits :=
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits shape
  let flagLen := flagBits.length
  let rankWord :=
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
      shape
  let bpWord := sparseDenseFalseSelectWordBits shape
  let ell := sparseDenseFalseSelectEll shape
  let ell3 := ell * (ell * ell)
  let n := shape.bpCode.length
  let data :=
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData shape
  have hrankWordPos : 0 < rankWord := by
    simpa [rankWord] using
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize_pos
        shape
  have hrankWordLeBp : rankWord <= bpWord := by
    simpa [rankWord, bpWord, sparseDenseFalseSelectWordBits] using
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize_le_machine
        shape
  have hauxEq :
      data.auxPayload.length =
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
            shape +
          builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
            shape := by
    have hprofile :=
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData_profile
        shape
    simpa [data] using hprofile.1
  have hsuperLe :
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
          shape <=
        2 * (flagLen + rankWord) := by
    unfold builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
    rw [SuccinctRank.canonicalSuperRankSampleTables_payload_length]
    have hentryLen :
        (SuccinctRank.canonicalSuperRankEntries true flagBits
            rankWord
            (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord,
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper]
    have hentryLenFalse :
        (SuccinctRank.canonicalSuperRankEntries false flagBits
            rankWord
            (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord,
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper]
    rw [hentryLen, hentryLenFalse]
    have hdiv : flagLen / rankWord * rankWord <= flagLen :=
      Nat.div_mul_le_self flagLen rankWord
    calc
      (flagLen / rankWord + 1) * rankWord +
          (flagLen / rankWord + 1) * rankWord <=
        (flagLen + rankWord) + (flagLen + rankWord) := by
          have hone :
              (flagLen / rankWord + 1) * rankWord <=
                flagLen + rankWord := by
            rw [Nat.add_mul, Nat.one_mul]
            exact Nat.add_le_add_right hdiv rankWord
          exact Nat.add_le_add hone hone
      _ = 2 * (flagLen + rankWord) := by omega
  have hblockLe :
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
          shape <=
        2 * (flagLen + rankWord) := by
    unfold builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
    rw [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length]
    have hentryLen :
        (SuccinctRank.canonicalBlockRankEntries true flagBits
            rankWord
            (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalBlockRankEntries, flagBits,
        flagLen, rankWord]
    have hentryLenFalse :
        (SuccinctRank.canonicalBlockRankEntries false flagBits
            rankWord
            (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalBlockRankEntries, flagBits,
        flagLen, rankWord]
    rw [hentryLen, hentryLenFalse]
    have hdiv : flagLen / rankWord * rankWord <= flagLen :=
      Nat.div_mul_le_self flagLen rankWord
    calc
      (flagLen / rankWord + 1) * rankWord +
          (flagLen / rankWord + 1) * rankWord <=
        (flagLen + rankWord) + (flagLen + rankWord) := by
          have hone :
              (flagLen / rankWord + 1) * rankWord <=
                flagLen + rankWord := by
            rw [Nat.add_mul, Nat.one_mul]
            exact Nat.add_le_add_right hdiv rankWord
          exact Nat.add_le_add hone hone
      _ = 2 * (flagLen + rankWord) := by omega
  have hauxLe :
      data.auxPayload.length <= 4 * (flagLen + rankWord) := by
    rw [hauxEq]
    calc
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
            shape +
          builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
            shape <=
        2 * (flagLen + rankWord) + 2 * (flagLen + rankWord) :=
          Nat.add_le_add hsuperLe hblockLe
      _ = 4 * (flagLen + rankWord) := by omega
  by_cases hnZero : n = 0
  · have hflagZero : flagLen = 0 := by
      have hlen :=
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length
          shape
      have hcountZero :
          builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
            shape = 0 := by
        have hbp : shape.size = 0 := by
          have hbpLen : shape.bpCode.length = 2 * shape.size :=
            Cartesian.CartesianShape.bpCode_length shape
          omega
        unfold builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
        simp [falseSelectOccurrenceCount_eq_size, hbp]
      simpa [flagBits, flagLen, hcountZero] using hlen
    have hbpWord : bpWord = 1 := by
      simp [bpWord, sparseDenseFalseSelectWordBits,
        SuccinctRank.machineWordBits, n, hnZero]
    have hrankSmall : rankWord <= 1 := by
      simpa [hbpWord] using hrankWordLeBp
    have hauxSmall : data.auxPayload.length <= 4 := by
      have h := hauxLe
      rw [hflagZero] at h
      omega
    have hoverNonneg :
        0 <=
          SuccinctSpace.logLogCubedSampledDirectoryOverhead
            192 shape.bpCode.length := Nat.zero_le _
    exact Nat.le_trans hauxSmall (by omega)
  have hflagMul :
      flagLen * bpWord <= 20 * (ell3 * n) := by
    simpa [flagBits, flagLen, bpWord, ell, ell3, n,
      sparseDenseFalseSelectWordBits, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_mul_wordBits_le
        shape
  have hrankMul :
      rankWord * bpWord <= 4 * (ell3 * n) := by
    have hbpSq :
        bpWord * bpWord <= 4 * n := by
      have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
      simpa [bpWord, sparseDenseFalseSelectWordBits, n] using
        machineWordBits_sq_le_four_mul_self_of_pos hnPos
    have hrankBp :
        rankWord * bpWord <= bpWord * bpWord :=
      Nat.mul_le_mul_right bpWord hrankWordLeBp
    have hellOne : 1 <= ell3 := by
      have hell : 1 <= ell := by simp [ell, sparseDenseFalseSelectEll]
      have h1 := Nat.mul_le_mul hell (Nat.mul_le_mul hell hell)
      simpa [ell3] using h1
    calc
      rankWord * bpWord <= bpWord * bpWord := hrankBp
      _ <= 4 * n := hbpSq
      _ <= 4 * (ell3 * n) := by
        have hmul := Nat.mul_le_mul_right n hellOne
        have hscaled := Nat.mul_le_mul_left 4 hmul
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled
  have hauxMul :
      data.auxPayload.length * bpWord <= 96 * (ell3 * n) := by
    calc
      data.auxPayload.length * bpWord <=
          4 * (flagLen + rankWord) * bpWord := by
            exact Nat.mul_le_mul_right bpWord hauxLe
      _ = 4 * (flagLen * bpWord + rankWord * bpWord) := by
            simp [Nat.add_mul, Nat.mul_assoc]
      _ <= 4 * (20 * (ell3 * n) + 4 * (ell3 * n)) := by
            exact Nat.mul_le_mul_left 4
              (Nat.add_le_add hflagMul hrankMul)
      _ = 96 * (ell3 * n) := by
            let t := ell3 * n
            change 4 * (20 * t + 4 * t) = 96 * t
            omega
  exact
    Nat.le_trans
      (payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
        (shape := shape) (payload := data.auxPayload.length) (scale := 96)
        (by
          simpa [bpWord, ell, ell3, n, sparseDenseFalseSelectWordBits,
            Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hauxMul))
      (Nat.le_add_right _ _)

def sparseExceptionDirectoryOverhead
    (flagSlots rankSuperSlots rankBlockSlots explicitSlots : Nat)
    (n : Nat) : Nat :=
  SuccinctSpace.logLogCubedSampledDirectoryOverhead flagSlots n +
    SuccinctSpace.sampledDirectoryOverhead rankSuperSlots n +
      SuccinctSpace.sampledDirectoryOverhead rankBlockSlots n +
        SuccinctSpace.idDivLogLogOverhead explicitSlots n

theorem sparseExceptionDirectoryOverhead_littleO
    (flagSlots rankSuperSlots rankBlockSlots explicitSlots : Nat) :
    SuccinctSpace.LittleOLinear
      (sparseExceptionDirectoryOverhead
        flagSlots rankSuperSlots rankBlockSlots explicitSlots) := by
  unfold sparseExceptionDirectoryOverhead
  simpa [Nat.add_assoc] using
    (((SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO
        flagSlots).add
      (SuccinctSpace.sampledDirectoryOverhead_littleO
        rankSuperSlots)).add
      (SuccinctSpace.sampledDirectoryOverhead_littleO
        rankBlockSlots)).add
      (SuccinctSpace.idDivLogLogOverhead_littleO explicitSlots)

def canonicalSparseExceptionDirectoryOverhead (n : Nat) : Nat :=
  SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 (2 * n) +
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 (2 * n) + 16) +
      sparseExceptionRelativeTableOverhead n

theorem canonicalSparseExceptionDirectoryOverhead_littleO :
    SuccinctSpace.LittleOLinear
      canonicalSparseExceptionDirectoryOverhead := by
  unfold canonicalSparseExceptionDirectoryOverhead
  have hflags :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 40
            (2 * n)) :=
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 40)
      |>.comp_two_mul_arg
  have hrank :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 192
            (2 * n) + 16) :=
    ((SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 192)
      |>.comp_two_mul_arg).add_const 16
  exact (hflags.add hrank).add sparseExceptionRelativeTableOverhead_littleO

theorem fixedWidthNatTable_word_length_le_of_mem
    {entries : List Nat} {width n : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (hwidth : width <= SuccinctRank.machineWordBits n)
    {word : List Bool}
    (hmem : List.Mem word table.store.words.toList) :
    word.length <= SuccinctRank.machineWordBits n := by
  rcases (List.mem_iff_getElem?.mp hmem) with ⟨i, hgetList⟩
  have hget : table.store.words[i]? = some word := by
    simpa [Array.getElem?_toList] using hgetList
  rw [table.read_word_length_of_some hget]
  exact hwidth


end SuccinctSelect
end RMQ
