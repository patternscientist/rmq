import RMQ.Core.SuccinctSelect.CloseSelect.BuiltRouting.SpanBudgets

/-!
# Sparse/dense lookup and dense routing facts

Split implementation layer for built sparse/dense close-select routing.
Public declarations stay in the historical `RMQ.SuccinctSelect`
namespace.
-/

namespace RMQ
namespace SuccinctSelect

def builtRelativeSplitFalseSelectLongFlagRankWordSize
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits
    (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length

def builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper
    (_shape : Cartesian.CartesianShape) : Nat := 1

def builtRelativeSplitFalseSelectLongFlagRankBlockWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRelativeSplitFalseSelectLongFlagRankWordSize shape

theorem builtRelativeSplitFalseSelectLongFlagRankWordSize_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtRelativeSplitFalseSelectLongFlagRankWordSize shape := by
  simp [builtRelativeSplitFalseSelectLongFlagRankWordSize,
    SuccinctRank.machineWordBits_pos]

theorem builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper shape := by
  simp [builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper]

theorem builtRelativeSplitFalseSelectLongSuperFlagBits_length_lt_rank_word_pow
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length <
      2 ^ builtRelativeSplitFalseSelectLongFlagRankWordSize shape := by
  simpa [builtRelativeSplitFalseSelectLongFlagRankWordSize,
    SuccinctRank.machineWordBits] using
    (Nat.lt_log2_self
      (n := (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length))

theorem builtRelativeSplitFalseSelectLongFlagRankBlockSpan_lt_pow
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper shape *
        builtRelativeSplitFalseSelectLongFlagRankWordSize shape <
      2 ^ builtRelativeSplitFalseSelectLongFlagRankBlockWidth shape := by
  have hsucc :=
    SuccinctSpace.nat_succ_le_two_pow
      (builtRelativeSplitFalseSelectLongFlagRankWordSize shape)
  simpa [builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper,
    builtRelativeSplitFalseSelectLongFlagRankBlockWidth] using
    (by omega :
      builtRelativeSplitFalseSelectLongFlagRankWordSize shape <
        2 ^ builtRelativeSplitFalseSelectLongFlagRankWordSize shape)

def builtRelativeSplitFalseSelectLongFlagRankSuperOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRank.canonicalSuperRankSampleTables
      (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
      (builtRelativeSplitFalseSelectLongFlagRankWordSize shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper shape)
      (builtRelativeSplitFalseSelectLongFlagRankWordSize shape)
      (builtRelativeSplitFalseSelectLongSuperFlagBits_length_lt_rank_word_pow
        shape)).payload.length

def builtRelativeSplitFalseSelectLongFlagRankBlockOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan
      (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
      (builtRelativeSplitFalseSelectLongFlagRankWordSize shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlockWidth shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper_pos shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlockSpan_lt_pow
        shape)).payload.length

def builtRelativeSplitFalseSelectLongFlagRankData
    (shape : Cartesian.CartesianShape) :
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
      (builtRelativeSplitFalseSelectLongFlagRankSuperOverhead shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlockOverhead shape)
      4 :=
  SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock
    (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
    (builtRelativeSplitFalseSelectLongFlagRankWordSize_pos shape)
    (by simp [builtRelativeSplitFalseSelectLongFlagRankWordSize])
    (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper_pos shape)
    (builtRelativeSplitFalseSelectLongSuperFlagBits_length_lt_rank_word_pow
      shape)
    (builtRelativeSplitFalseSelectLongFlagRankBlockSpan_lt_pow shape)
    (by omega)

theorem builtRelativeSplitFalseSelectLongFlagRankData_profile
    (shape : Cartesian.CartesianShape) :
    let data := builtRelativeSplitFalseSelectLongFlagRankData shape
    data.auxPayload.length =
        builtRelativeSplitFalseSelectLongFlagRankSuperOverhead shape +
          builtRelativeSplitFalseSelectLongFlagRankBlockOverhead shape /\
      data.wordSize <=
        SuccinctRank.machineWordBits
          (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        builtRelativeSplitFalseSelectLongSuperFlagBits shape /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <=
            SuccinctRank.machineWordBits
              (builtRelativeSplitFalseSelectLongSuperFlagBits
                shape).length) /\
      forall target pos,
        (data.rankCosted target pos).cost <= 4 /\
          (data.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target
              (builtRelativeSplitFalseSelectLongSuperFlagBits
                shape) pos := by
  exact
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
      (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
      (builtRelativeSplitFalseSelectLongFlagRankWordSize_pos shape)
      (by simp [builtRelativeSplitFalseSelectLongFlagRankWordSize])
      (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper_pos shape)
      (builtRelativeSplitFalseSelectLongSuperFlagBits_length_lt_rank_word_pow
        shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlockSpan_lt_pow shape)
      (by omega)

def builtRelativeSplitCompactLongSuperReadCosted
    (shape : Cartesian.CartesianShape)
    (base superSlot localOccurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind
    ((builtRelativeSplitFalseSelectLongFlagRankData shape).rankCosted
      true superSlot)
    fun exceptionRank =>
      Costed.map (fun offset? => offset?.map (fun offset => base + offset))
        ((builtRelativeSplitFalseSelectLongSuperRelativeTable shape).readCosted
          (exceptionRank * sparseDenseFalseSelectSuperStride shape +
            localOccurrence))

theorem builtRelativeSplitCompactLongSuperReadCosted_cost_le_five
    (shape : Cartesian.CartesianShape)
    (base superSlot localOccurrence : Nat) :
    (builtRelativeSplitCompactLongSuperReadCosted
      shape base superSlot localOccurrence).cost <= 5 := by
  unfold builtRelativeSplitCompactLongSuperReadCosted
  have hrank :
      ((builtRelativeSplitFalseSelectLongFlagRankData shape).rankCosted
        true superSlot).cost <= 4 :=
    (builtRelativeSplitFalseSelectLongFlagRankData shape).rankCosted_cost_le_four
      true superSlot
  have hread :
      ((builtRelativeSplitFalseSelectLongSuperRelativeTable shape).readCosted
        (((builtRelativeSplitFalseSelectLongFlagRankData shape).rankCosted
            true superSlot).value *
          sparseDenseFalseSelectSuperStride shape +
            localOccurrence)).cost <= 1 :=
    (builtRelativeSplitFalseSelectLongSuperRelativeTable
      shape).readCosted_cost_le_one _
  simp [Costed.bind] at *
  omega

theorem builtRelativeSplitCompactLongSuperReadCosted_erase
    (shape : Cartesian.CartesianShape)
    (base superSlot localOccurrence : Nat) :
    (builtRelativeSplitCompactLongSuperReadCosted
      shape base superSlot localOccurrence).erase =
      ((builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)[
          RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
              superSlot *
            sparseDenseFalseSelectSuperStride shape +
            localOccurrence]?).map
        (fun offset => base + offset) := by
  have hrank :=
    (builtRelativeSplitFalseSelectLongFlagRankData shape).rankCosted_exact
      true superSlot
  change
      ((builtRelativeSplitFalseSelectLongFlagRankData shape).rankCosted
        true superSlot).value =
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
          superSlot at hrank
  let slot :=
    RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
        superSlot *
      sparseDenseFalseSelectSuperStride shape +
      localOccurrence
  have hread :
      ((builtRelativeSplitFalseSelectLongSuperRelativeTable shape).readCosted
        slot).value =
        (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)[
          slot]? := by
    simpa [Costed.erase] using
      (builtRelativeSplitFalseSelectLongSuperRelativeTable
        shape).readCosted_erase slot
  unfold builtRelativeSplitCompactLongSuperReadCosted
  simp [Costed.bind, Costed.erase, hrank, slot, hread]

theorem compactLongSuperRelativeTable_lookup_exact
    (shape : Cartesian.CartesianShape)
    {superSlot localOccurrence pos : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape)
    (hlong :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true)
    (hocc : localOccurrence < sparseDenseFalseSelectSuperStride shape)
    (hend :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
          localOccurrence <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot)
    (hselect :
      RMQ.Succinct.select false shape.bpCode
          (builtRelativeSplitFalseSelectSuperBaseOccurrence shape
              superSlot +
            localOccurrence) =
        some pos) :
    (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)[
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
          superSlot *
            sparseDenseFalseSelectSuperStride shape +
          localOccurrence]? =
      some
        (pos -
          builtRelativeSplitFalseSelectPosition shape
            (builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot)) := by
  let pre :=
    (List.range superSlot).flatMap
      (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
        shape)
  let slotEntries :=
    builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
      shape superSlot
  let post :=
    ((List.range
        (builtRectangularFalseSelectSuperSlotCount shape -
          superSlot - 1)).map
      (fun offset => superSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)
  have hentries :
      builtRelativeSplitFalseSelectLongSuperRelativeEntries shape =
        pre ++ slotEntries ++ post := by
    simpa [pre, slotEntries, post] using
      builtRelativeSplitFalseSelectLongSuperRelativeEntries_decompose
        shape hslot
  have hpre :
      pre.length =
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
          superSlot *
            sparseDenseFalseSelectSuperStride shape := by
    simpa [pre] using
      compactLongSuperFlagRank_eq_segmentIndex
        shape (Nat.le_of_lt hslot)
  have hslotEntries :
      slotEntries =
        falseSelectRelativeOffsetsOrZero shape.bpCode
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot)
          (sparseDenseFalseSelectSuperStride shape)
          (builtRelativeSplitFalseSelectSuperEndOccurrence shape
            superSlot)
          (builtRelativeSplitFalseSelectPosition shape
            (builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot)) := by
    simp [slotEntries,
      builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot,
      hlong]
  have hslotLen :
      localOccurrence < slotEntries.length := by
    rw [builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot_length]
    simp [hlong]
    exact hocc
  have hidx :
      RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
          superSlot *
            sparseDenseFalseSelectSuperStride shape +
          localOccurrence =
        pre.length + localOccurrence := by
    simp [hpre]
  rw [hentries, hidx]
  rw [List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  have hsub :
      pre.length + localOccurrence - pre.length =
        localOccurrence := by
    omega
  rw [hsub]
  rw [List.getElem?_append_left hslotLen]
  rw [hslotEntries]
  exact
    falseSelectRelativeOffsetsOrZero_lookup_exact
      (bits := shape.bpCode)
      (baseOccurrence :=
        builtRelativeSplitFalseSelectSuperBaseOccurrence
          shape superSlot)
      (count := sparseDenseFalseSelectSuperStride shape)
      (endOccurrence :=
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          superSlot)
      (basePosition :=
        builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot))
      (localOccurrence := localOccurrence)
      (pos := pos)
      hocc hend hselect

theorem builtRelativeSplitCompactLongSuperReadCosted_lookup_exact
    (shape : Cartesian.CartesianShape)
    {superSlot localOccurrence pos : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape)
    (hlong :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true)
    (hocc : localOccurrence < sparseDenseFalseSelectSuperStride shape)
    (hend :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
          localOccurrence <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot)
    (hselect :
      RMQ.Succinct.select false shape.bpCode
          (builtRelativeSplitFalseSelectSuperBaseOccurrence shape
              superSlot +
            localOccurrence) =
        some pos) :
    (builtRelativeSplitCompactLongSuperReadCosted
      shape
      (builtRelativeSplitFalseSelectPosition shape
        (builtRelativeSplitFalseSelectSuperBaseOccurrence
          shape superSlot))
      superSlot
      localOccurrence).erase =
      some
        (builtRelativeSplitFalseSelectPosition shape
            (builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot) +
          (pos -
            builtRelativeSplitFalseSelectPosition shape
              (builtRelativeSplitFalseSelectSuperBaseOccurrence
                shape superSlot))) := by
  rw [builtRelativeSplitCompactLongSuperReadCosted_erase]
  have hlookup :=
    compactLongSuperRelativeTable_lookup_exact
      shape hslot hlong hocc hend hselect
  simpa using
    congrArg
      (Option.map
        (fun offset =>
          builtRelativeSplitFalseSelectPosition shape
              (builtRelativeSplitFalseSelectSuperBaseOccurrence
                shape superSlot) +
            offset))
      hlookup

theorem builtRelativeSplitFalseSelectSparseRelativeEntries_decompose
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape) :
    builtRelativeSplitFalseSelectSparseRelativeEntries shape =
      ((List.range globalLocalSlot).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape)) ++
      builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
        shape globalLocalSlot ++
      (((List.range
            (builtRectangularFalseSelectLocalSlotCount shape -
              globalLocalSlot - 1)).map
          (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
          shape)) := by
  unfold builtRelativeSplitFalseSelectSparseRelativeEntries
  let tailCount :=
    builtRectangularFalseSelectLocalSlotCount shape -
      globalLocalSlot - 1
  have hcount :
      builtRectangularFalseSelectLocalSlotCount shape =
        globalLocalSlot + (1 + tailCount) := by
    simp [tailCount]
    omega
  calc
    (List.range (builtRectangularFalseSelectLocalSlotCount shape)).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape) =
      (List.range (globalLocalSlot + (1 + tailCount))).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape) := by
        rw [hcount]
    _ =
      ((List.range globalLocalSlot ++
          (List.range (1 + tailCount)).map
            (fun offset => globalLocalSlot + offset)).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape)) := by
        rw [List.range_add]
    _ =
      ((List.range globalLocalSlot).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape)) ++
      ((List.range (1 + tailCount)).map
          (fun offset => globalLocalSlot + offset)).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape) := by
        simp [List.flatMap_append]
    _ =
      ((List.range globalLocalSlot).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape)) ++
      builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
        shape globalLocalSlot ++
      (((List.range tailCount).map
          (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
          shape)) := by
        have hsucc : 1 + tailCount = tailCount + 1 := by omega
        rw [hsucc, List.range_succ_eq_map]
        simp [List.map, List.flatMap, List.map_map]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro offset _hmem
        rfl

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_decompose
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape) :
    builtRelativeSplitFalseSelectSparseExceptionRelativeEntries shape =
      ((List.range globalLocalSlot).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)) ++
      builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
        shape globalLocalSlot ++
      (((List.range
            (builtRectangularFalseSelectLocalSlotCount shape -
              globalLocalSlot - 1)).map
          (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)) := by
  unfold builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
  let tailCount :=
    builtRectangularFalseSelectLocalSlotCount shape -
      globalLocalSlot - 1
  have hcount :
      builtRectangularFalseSelectLocalSlotCount shape =
        globalLocalSlot + (1 + tailCount) := by
    simp [tailCount]
    omega
  calc
    (List.range (builtRectangularFalseSelectLocalSlotCount shape)).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape) =
      (List.range (globalLocalSlot + (1 + tailCount))).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape) := by
        rw [hcount]
    _ =
      ((List.range globalLocalSlot ++
          (List.range (1 + tailCount)).map
            (fun offset => globalLocalSlot + offset)).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)) := by
        rw [List.range_add]
    _ =
      ((List.range globalLocalSlot).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)) ++
      ((List.range (1 + tailCount)).map
          (fun offset => globalLocalSlot + offset)).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape) := by
        simp [List.flatMap_append]
    _ =
      ((List.range globalLocalSlot).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)) ++
      builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
        shape globalLocalSlot ++
      (((List.range tailCount).map
          (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)) := by
        have hsucc : 1 + tailCount = tailCount + 1 := by omega
        rw [hsucc, List.range_succ_eq_map]
        simp [List.map, List.flatMap, List.map_map]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro offset _hmem
        rfl

theorem falseSelectPositions_length
    (bits : List Bool) (base count : Nat) :
    (falseSelectPositions bits base count).length = count := by
  simp [falseSelectPositions]

theorem falseSelectPositions_mem_le_length
    {bits : List Bool} {base count pos : Nat}
    (hmem : List.Mem pos (falseSelectPositions bits base count)) :
    pos <= bits.length := by
  rcases List.mem_map.mp hmem with ⟨offset, _hoffset, rfl⟩
  cases hselect : RMQ.Succinct.select false bits (base + offset) with
  | none =>
      simp
  | some selected =>
      have hbound : selected < bits.length :=
        RMQ.Succinct.select_bounds hselect
      simp
      omega

theorem builtRelativeSplitFalseSelectSparseRelativeEntries_mem_lt_word_pow
    {shape : Cartesian.CartesianShape} {entry : Nat}
    (hmem :
      List.Mem entry
        (builtRelativeSplitFalseSelectSparseRelativeEntries shape)) :
    entry < 2 ^ sparseDenseFalseSelectWordBits shape := by
  unfold builtRelativeSplitFalseSelectSparseRelativeEntries at hmem
  rcases List.mem_flatMap.mp hmem with
    ⟨globalLocalSlot, _hslotMem, hentryMem⟩
  unfold builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot at hentryMem
  by_cases hsparse :
      builtRelativeSplitFalseSelectLocalIsSparse shape globalLocalSlot = true
  · simp [hsparse] at hentryMem
    rcases hentryMem with ⟨pos, hposMem, hentryEq⟩
    subst entry
    have hposLe :
        pos <= shape.bpCode.length :=
      falseSelectPositions_mem_le_length hposMem
    have hlenLt :
        shape.bpCode.length < 2 ^ sparseDenseFalseSelectWordBits shape := by
      simpa [sparseDenseFalseSelectWordBits,
        SuccinctRank.machineWordBits] using
        (Nat.lt_log2_self (n := shape.bpCode.length))
    omega
  · simp [hsparse] at hentryMem

def builtRelativeSplitFalseSelectSparseRelativeTable
    (shape : Cartesian.CartesianShape) :
    SuccinctSpace.FixedWidthNatTable
      (builtRelativeSplitFalseSelectSparseRelativeEntries shape)
      (sparseDenseFalseSelectWordBits shape) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (builtRelativeSplitFalseSelectSparseRelativeEntries shape)
    (sparseDenseFalseSelectWordBits shape)
    (by
      intro entry hmem
      exact
        builtRelativeSplitFalseSelectSparseRelativeEntries_mem_lt_word_pow
          hmem)

theorem builtRelativeSplitFalseSelectSparseRelativeTable_profile
    (shape : Cartesian.CartesianShape) :
    let table :=
      builtRelativeSplitFalseSelectSparseRelativeTable shape
    table.payload.length =
        (builtRelativeSplitFalseSelectSparseRelativeEntries shape).length *
          sparseDenseFalseSelectWordBits shape /\
      (forall i, (table.readCosted i).cost <= 1 /\
        (table.readCosted i).erase =
          (builtRelativeSplitFalseSelectSparseRelativeEntries shape)[i]?) /\
      forall {word : List Bool},
        List.Mem word table.store.words.toList ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length := by
  let table := builtRelativeSplitFalseSelectSparseRelativeTable shape
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
      simp [sparseDenseFalseSelectWordBits]

theorem builtRelativeSplitFalseSelectSparseRelativeTable_payload_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseRelativeTable shape).payload.length =
      (builtRelativeSplitFalseSelectSparseRelativeEntries shape).length *
        sparseDenseFalseSelectWordBits shape := by
  exact
    (builtRelativeSplitFalseSelectSparseRelativeTable
      shape).payload_length_eq

theorem fullWidthSparseRelativePayload_not_littleO_of_linear_family
    {overhead : Nat -> Nat}
    (hlinear :
      forall n : Nat,
        exists shape : Cartesian.CartesianShape,
          shape.size = n /\
            n <=
              (builtRelativeSplitFalseSelectSparseRelativeTable
                shape).payload.length)
    (hbound :
      forall shape : Cartesian.CartesianShape,
        (builtRelativeSplitFalseSelectSparseRelativeTable
          shape).payload.length <= overhead shape.size) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_self_le
  intro n
  rcases hlinear n with ⟨shape, hsize, hpayload⟩
  have hbudget := hbound shape
  have hle : n <= overhead shape.size :=
    Nat.le_trans hpayload hbudget
  simpa [hsize] using hle

theorem falseSelectPositions_lookup_exact
    {bits : List Bool} {base count q pos : Nat}
    (hlo : base <= q)
    (hhi : q < base + count)
    (hselect : RMQ.Succinct.select false bits q = some pos) :
    (falseSelectPositions bits base count)[q - base]? =
      RMQ.Succinct.select false bits q := by
  have hoff : q - base < count := by omega
  have hq : base + (q - base) = q := by omega
  simp [falseSelectPositions, List.getElem?_map,
    List.getElem?_range hoff, hq, hselect]

theorem falseSelectExplicitTable_lookup_exact
    {bits : List Bool} {pre post entries : List Nat}
    {base count q pos : Nat}
    (hentries :
      entries =
        pre ++ falseSelectPositions bits base count ++ post)
    (hlo : base <= q)
    (hhi : q < base + count)
    (hselect : RMQ.Succinct.select false bits q = some pos) :
    entries[pre.length + (q - base)]? =
      RMQ.Succinct.select false bits q := by
  rw [hentries]
  rw [List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  have hidx : pre.length + (q - base) - pre.length = q - base := by
    omega
  rw [hidx]
  have hoff : q - base < (falseSelectPositions bits base count).length := by
    rw [falseSelectPositions_length]
    omega
  rw [List.getElem?_append_left hoff]
  exact falseSelectPositions_lookup_exact hlo hhi hselect

theorem builtRelativeSplitFalseSelectSparseRelativeEntries_lookup_exact
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
    (builtRelativeSplitFalseSelectSparseRelativeEntries shape)[
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseFlagBits shape)
          globalLocalSlot *
            sparseDenseFalseSelectLocalStride shape +
          localOccurrence]? =
      some
        (pos -
          builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot)) := by
  let pre :=
    (List.range globalLocalSlot).flatMap
      (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape)
  let slotEntries :=
    builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
      shape globalLocalSlot
  let post :=
    ((List.range
        (builtRectangularFalseSelectLocalSlotCount shape -
          globalLocalSlot - 1)).map
      (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
          shape)
  have hentries :
      builtRelativeSplitFalseSelectSparseRelativeEntries shape =
        pre ++ slotEntries ++ post := by
    simpa [pre, slotEntries, post] using
      builtRelativeSplitFalseSelectSparseRelativeEntries_decompose
        shape hslot
  have hpre :
      pre.length =
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseFlagBits shape)
          globalLocalSlot *
            sparseDenseFalseSelectLocalStride shape := by
    simpa [pre] using
      builtRelativeSplitFalseSelectSparseRelativePrefix_length
        shape (Nat.le_of_lt hslot)
  have hslotEntries :
      slotEntries =
        (falseSelectPositions shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot)
          (sparseDenseFalseSelectLocalStride shape)).map
          (fun selected =>
            selected -
              builtRelativeSplitFalseSelectPosition shape
                (builtRectangularFalseSelectLocalBaseOccurrence
                  shape globalLocalSlot)) := by
    simp [slotEntries,
      builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot,
      hsparse]
  have hslotLen :
      localOccurrence < slotEntries.length := by
    rw [hslotEntries]
    simp [falseSelectPositions_length]
    exact hocc
  have hidx :
      RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseFlagBits shape)
          globalLocalSlot *
            sparseDenseFalseSelectLocalStride shape +
          localOccurrence =
        pre.length + localOccurrence := by
    simp [hpre]
  rw [hentries, hidx]
  rw [List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  have hsub :
      pre.length + localOccurrence - pre.length =
        localOccurrence := by
    omega
  rw [hsub]
  rw [List.getElem?_append_left hslotLen]
  rw [hslotEntries]
  have hlookup :
      (falseSelectPositions shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot)
          (sparseDenseFalseSelectLocalStride shape))[localOccurrence]? =
        RMQ.Succinct.select false shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence) := by
    have hlo :
        builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot <=
          builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence := by
      omega
    have hhi :
        builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence <
          builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot +
            sparseDenseFalseSelectLocalStride shape := by
      omega
    simpa using
      falseSelectPositions_lookup_exact
        (bits := shape.bpCode)
        (base :=
          builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot)
        (count := sparseDenseFalseSelectLocalStride shape)
        (q :=
          builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence)
        (pos := pos)
        hlo hhi hselect
  simp [List.getElem?_map, hlookup, hselect]

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_lookup_exact
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
    (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries shape)[
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
          globalLocalSlot *
            sparseDenseFalseSelectLocalStride shape +
          localOccurrence]? =
      some
        (pos -
          builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot)) := by
  let pre :=
    (List.range globalLocalSlot).flatMap
      (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
        shape)
  let slotEntries :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
      shape globalLocalSlot
  let post :=
    ((List.range
        (builtRectangularFalseSelectLocalSlotCount shape -
          globalLocalSlot - 1)).map
      (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)
  have hentries :
      builtRelativeSplitFalseSelectSparseExceptionRelativeEntries shape =
        pre ++ slotEntries ++ post := by
    simpa [pre, slotEntries, post] using
      builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_decompose
        shape hslot
  have hpre :
      pre.length =
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
          globalLocalSlot *
            sparseDenseFalseSelectLocalStride shape := by
    simpa [pre] using
      builtRelativeSplitFalseSelectSparseExceptionRelativePrefix_length
        shape (Nat.le_of_lt hslot)
  have hslotEntries :
      slotEntries =
        falseSelectRelativeOffsetsOrZero shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot)
          (sparseDenseFalseSelectLocalStride shape)
          (builtRelativeSplitFalseSelectSuperEndOccurrence shape
            (builtRelativeSplitFalseSelectLocalSuperSlot
              shape globalLocalSlot))
          (builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot)) := by
    simp [slotEntries,
      builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot,
      hflag]
  have hslotLen :
      localOccurrence < slotEntries.length := by
    rw [builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot_length]
    simp [hflag]
    exact hocc
  have hidx :
      RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
          globalLocalSlot *
            sparseDenseFalseSelectLocalStride shape +
          localOccurrence =
        pre.length + localOccurrence := by
    simp [hpre]
  rw [hentries, hidx]
  rw [List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  have hsub :
      pre.length + localOccurrence - pre.length =
        localOccurrence := by
    omega
  rw [hsub]
  rw [List.getElem?_append_left hslotLen]
  rw [hslotEntries]
  exact
    falseSelectRelativeOffsetsOrZero_lookup_exact
      (bits := shape.bpCode)
      (baseOccurrence :=
        builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot)
      (count := sparseDenseFalseSelectLocalStride shape)
      (endOccurrence :=
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          (builtRelativeSplitFalseSelectLocalSuperSlot
            shape globalLocalSlot))
      (basePosition :=
        builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot))
      (localOccurrence := localOccurrence)
      (pos := pos)
      hocc hend hselect

structure FalseSelectAlignedBitWords
    (bits : List Bool) (wordSize : Nat)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize) :
    Prop where
  get_eq_take_drop :
    forall {i : Nat} {word : List Bool},
      bitWords.store.words[i]? = some word ->
        word = (bits.drop (i * wordSize)).take wordSize
  get_some_of_mul_lt :
    forall {i : Nat},
      i * wordSize < bits.length ->
        exists word, bitWords.store.words[i]? = some word

theorem falseSelectAlignedBitWords_ofChunks
    (bits : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    FalseSelectAlignedBitWords bits wordSize
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hword) := by
  exact {
    get_eq_take_drop := by
      intro i word hget
      have hchunk :
          (SuccinctSpace.chunkPayloadWords wordSize bits)[i]? =
            some word := by
        simpa [SuccinctSpace.BoundedPayloadWordStore.ofChunks,
          Array.getElem?_toList] using hget
      exact SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hchunk
    get_some_of_mul_lt := by
      intro i hi
      have h :=
        SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
          (wordSize := wordSize) hword (payload := bits) (i := i) hi
      cases h with
      | intro word hchunk =>
          exact Exists.intro word (by
            simpa [SuccinctSpace.BoundedPayloadWordStore.ofChunks,
              Array.getElem?_toList] using hchunk) }

def falseSelectDenseLocalFirstStart
    (wordSize baseWordIndex : Nat) : Nat :=
  baseWordIndex * wordSize

def falseSelectDenseLocalSecondStart
    (wordSize baseWordIndex : Nat) : Nat :=
  (baseWordIndex + 1) * wordSize

def falseSelectDenseLocalSpanEnd
    (wordSize baseWordIndex : Nat) : Nat :=
  (baseWordIndex + 2) * wordSize

def falseSelectDenseLocalFirstWord
    (bits : List Bool) (wordSize baseWordIndex : Nat) : List Bool :=
  (bits.drop (falseSelectDenseLocalFirstStart wordSize baseWordIndex)).take
    wordSize

def falseSelectDenseLocalFirstCount
    (bits : List Bool) (wordSize baseWordIndex firstOffset : Nat) : Nat :=
  RMQ.RAM.boolRankPrefix false
      (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
      (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex).length -
    RMQ.RAM.boolRankPrefix false
      (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
      firstOffset

structure FalseSelectDenseLocalPayloadRoutingFacts
    (bits : List Bool) (wordSize basePosition baseOccurrence q : Nat) where
  baseWordIndex : Nat
  rankBefore : Nat
  firstOffset : Nat
  baseWordIndex_eq :
    baseWordIndex = basePosition / wordSize
  rankBefore_eq :
    rankBefore =
      RMQ.Succinct.rankPrefix false bits
        (falseSelectDenseLocalFirstStart wordSize baseWordIndex)
  firstOffset_eq :
    firstOffset =
      basePosition - falseSelectDenseLocalFirstStart wordSize baseWordIndex
  firstWordStart_readable :
    falseSelectDenseLocalFirstStart wordSize baseWordIndex < bits.length
  rankBefore_le_query :
    rankBefore <= q
  first_branch_rank :
    q - baseOccurrence <
        falseSelectDenseLocalFirstCount
          bits wordSize baseWordIndex firstOffset ->
      q <
        RMQ.Succinct.rankPrefix false bits
          (falseSelectDenseLocalSecondStart wordSize baseWordIndex)
  first_local_occurrence :
    RMQ.RAM.boolRankPrefix false
        (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
        firstOffset +
        (q - baseOccurrence) =
      q - rankBefore
  second_branch_rank :
    Not (q - baseOccurrence <
        falseSelectDenseLocalFirstCount
          bits wordSize baseWordIndex firstOffset) ->
      RMQ.Succinct.rankPrefix false bits
          (falseSelectDenseLocalSecondStart wordSize baseWordIndex) <= q /\
        q <
          RMQ.Succinct.rankPrefix false bits
            (falseSelectDenseLocalSpanEnd wordSize baseWordIndex) /\
          falseSelectDenseLocalSecondStart wordSize baseWordIndex <
            bits.length
  second_local_occurrence :
    Not (q - baseOccurrence <
        falseSelectDenseLocalFirstCount
          bits wordSize baseWordIndex firstOffset) ->
      q - baseOccurrence -
          falseSelectDenseLocalFirstCount
            bits wordSize baseWordIndex firstOffset =
        q -
          RMQ.Succinct.rankPrefix false bits
            (falseSelectDenseLocalSecondStart wordSize baseWordIndex)

structure FalseSelectDenseLocalSpanCertificate
    (bits : List Bool) (wordSize : Nat)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) where
  firstWord : List Bool
  first_read :
    bitWords.store.words[basePosition / wordSize]? = some firstWord
  first_branch_exact :
    q - baseOccurrence <
      RMQ.RAM.boolRankPrefix false firstWord firstWord.length -
        RMQ.RAM.boolRankPrefix false firstWord
          (basePosition - basePosition / wordSize * wordSize) ->
      (RMQ.RAM.boolSelectInWord false firstWord
        (RMQ.RAM.boolRankPrefix false firstWord
            (basePosition - basePosition / wordSize * wordSize) +
          (q - baseOccurrence))).map
        (fun offset => basePosition / wordSize * wordSize + offset) =
          RMQ.Succinct.select false bits q
  second_branch_exact :
    Not (q - baseOccurrence <
      RMQ.RAM.boolRankPrefix false firstWord firstWord.length -
        RMQ.RAM.boolRankPrefix false firstWord
          (basePosition - basePosition / wordSize * wordSize)) ->
      exists secondWord,
        bitWords.store.words[basePosition / wordSize + 1]? =
            some secondWord /\
          (RMQ.RAM.boolSelectInWord false secondWord
            (q - baseOccurrence -
              (RMQ.RAM.boolRankPrefix false firstWord firstWord.length -
                RMQ.RAM.boolRankPrefix false firstWord
                  (basePosition -
                    basePosition / wordSize * wordSize)))).map
            (fun offset =>
              (basePosition / wordSize + 1) * wordSize + offset) =
              RMQ.Succinct.select false bits q

def falseSelectDenseLocalSpanCertificate_of_payload_routing_facts
    {bits : List Bool} {wordSize : Nat}
    {bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize}
    {basePosition baseOccurrence q : Nat}
    (haligned : FalseSelectAlignedBitWords bits wordSize bitWords)
    (hfacts :
      FalseSelectDenseLocalPayloadRoutingFacts
        bits wordSize basePosition baseOccurrence q) :
    FalseSelectDenseLocalSpanCertificate
      bits wordSize bitWords basePosition baseOccurrence q := by
  let firstStart :=
    falseSelectDenseLocalFirstStart wordSize hfacts.baseWordIndex
  let secondStart :=
    falseSelectDenseLocalSecondStart wordSize hfacts.baseWordIndex
  let spanEnd :=
    falseSelectDenseLocalSpanEnd wordSize hfacts.baseWordIndex
  let firstWord :=
    falseSelectDenseLocalFirstWord bits wordSize hfacts.baseWordIndex
  have hfirstReadAtBase :
      bitWords.store.words[hfacts.baseWordIndex]? = some firstWord := by
    cases haligned.get_some_of_mul_lt
        hfacts.firstWordStart_readable with
    | intro word hread =>
        have hword := haligned.get_eq_take_drop hread
        simpa [firstWord, falseSelectDenseLocalFirstWord, firstStart,
          falseSelectDenseLocalFirstStart, hword] using hread
  have hfirstRead :
      bitWords.store.words[basePosition / wordSize]? = some firstWord := by
    rw [<- hfacts.baseWordIndex_eq]
    exact hfirstReadAtBase
  have hoffset :
      basePosition - basePosition / wordSize * wordSize =
        hfacts.firstOffset := by
    rw [<- hfacts.baseWordIndex_eq]
    simpa [firstStart, falseSelectDenseLocalFirstStart] using
      hfacts.firstOffset_eq.symm
  have hfirstStartDiv :
      basePosition / wordSize * wordSize = firstStart := by
    rw [<- hfacts.baseWordIndex_eq]
    rfl
  have hsecondStartDiv :
      (basePosition / wordSize + 1) * wordSize = secondStart := by
    rw [<- hfacts.baseWordIndex_eq]
    rfl
  have hfirstEnd :
      secondStart = firstStart + wordSize := by
    simp [secondStart, firstStart, falseSelectDenseLocalSecondStart,
      falseSelectDenseLocalFirstStart, Nat.succ_mul]
  have hspanEnd :
      spanEnd = secondStart + wordSize := by
    simp [spanEnd, secondStart, falseSelectDenseLocalSpanEnd,
      falseSelectDenseLocalSecondStart, Nat.add_assoc, Nat.succ_mul]
  refine {
    firstWord := firstWord
    first_read := hfirstRead
    first_branch_exact := ?_
    second_branch_exact := ?_ }
  · intro hchoose
    have hchoiceFacts :
        q - baseOccurrence <
          falseSelectDenseLocalFirstCount
            bits wordSize hfacts.baseWordIndex hfacts.firstOffset := by
      simpa [firstWord, falseSelectDenseLocalFirstCount,
        falseSelectDenseLocalFirstWord, hoffset] using hchoose
    have hqFirstRank := hfacts.first_branch_rank hchoiceFacts
    have hqFirstRankAtSecond :
        q < RMQ.Succinct.rankPrefix false bits secondStart := by
      simpa [secondStart] using hqFirstRank
    cases select_exists_of_lt_rankPrefix
        (target := false) (bits := bits) (occurrence := q)
        (limit := secondStart) hqFirstRankAtSecond with
    | intro pos hselect =>
        have hrankBeforeLe :
            RMQ.Succinct.rankPrefix false bits firstStart <= q := by
          simpa [firstStart] using
            (by
              rw [<- hfacts.rankBefore_eq]
              exact hfacts.rankBefore_le_query)
        have hstart_le_pos : firstStart <= pos := by
          by_cases hle : firstStart <= pos
          · exact hle
          · have hpos_lt_start : pos < firstStart :=
              Nat.lt_of_not_ge hle
            have hocc_lt :=
              occurrence_lt_rankPrefix_of_select_lt hselect hpos_lt_start
            omega
        have hpos_lt_second : pos < secondStart := by
          by_cases hlt : pos < secondStart
          · exact hlt
          · have hsecond_le_pos : secondStart <= pos := Nat.le_of_not_gt hlt
            have hprefix_le :=
              RMQ.Succinct.rankPrefix_le_occurrence_of_le_select
                hselect hsecond_le_pos
            omega
        have hpos_lt_word : pos < firstStart + wordSize := by
          omega
        have hstartLen : firstStart <= bits.length :=
          Nat.le_of_lt hfacts.firstWordStart_readable
        have hlocal :=
          RMQ.Succinct.select_drop_take_eq_sub_of_select
            (target := false) (bits := bits) (occurrence := q)
            (idx := pos) (start := firstStart) (width := wordSize)
            hselect hstart_le_pos hpos_lt_word hstartLen hrankBeforeLe
        have hlocalOccurrence :
            RMQ.RAM.boolRankPrefix false firstWord hfacts.firstOffset +
                (q - baseOccurrence) =
              q - RMQ.Succinct.rankPrefix false bits firstStart := by
          simpa [firstWord, falseSelectDenseLocalFirstWord, firstStart,
            hfacts.rankBefore_eq] using hfacts.first_local_occurrence
        have hlocalOccurrenceCert :
            RMQ.RAM.boolRankPrefix false firstWord
                (basePosition - basePosition / wordSize * wordSize) +
                (q - baseOccurrence) =
              q - RMQ.Succinct.rankPrefix false bits firstStart := by
          simpa [hoffset] using hlocalOccurrence
        have hselectWord :
            RMQ.Succinct.select false firstWord
                (RMQ.RAM.boolRankPrefix false firstWord
                    (basePosition -
                      basePosition / wordSize * wordSize) +
                  (q - baseOccurrence)) =
              some (pos - firstStart) := by
          rw [hlocalOccurrenceCert]
          simpa [firstWord, falseSelectDenseLocalFirstWord, firstStart,
            falseSelectDenseLocalFirstStart] using hlocal
        calc
          (RMQ.RAM.boolSelectInWord false firstWord
              (RMQ.RAM.boolRankPrefix false firstWord
                  (basePosition -
                    basePosition / wordSize * wordSize) +
                (q - baseOccurrence))).map
              (fun offset =>
                basePosition / wordSize * wordSize + offset) =
            (RMQ.Succinct.select false firstWord
              (RMQ.RAM.boolRankPrefix false firstWord
                  (basePosition -
                    basePosition / wordSize * wordSize) +
                (q - baseOccurrence))).map
              (fun offset =>
                basePosition / wordSize * wordSize + offset) := by
              simp [RMQ.Succinct.ram_boolSelectInWord_eq_select]
          _ = some
              (basePosition / wordSize * wordSize +
                (pos - firstStart)) := by
              simp [hselectWord]
          _ = some pos := by
              have hposEq :
                  basePosition / wordSize * wordSize +
                      (pos - firstStart) = pos := by
                omega
              simp [hposEq]
          _ = RMQ.Succinct.select false bits q := hselect.symm
  · intro hnot
    have hnotFacts :
        Not (q - baseOccurrence <
          falseSelectDenseLocalFirstCount
            bits wordSize hfacts.baseWordIndex hfacts.firstOffset) := by
      intro hchoice
      exact hnot (by
        simpa [firstWord, falseSelectDenseLocalFirstCount,
          falseSelectDenseLocalFirstWord, hoffset] using hchoice)
    have hbranch := hfacts.second_branch_rank hnotFacts
    cases hbranch with
    | intro hsecondRankLe hbranch =>
        cases hbranch with
        | intro hqSpan hsecondReadable =>
            have hsecondRankLeAt :
                RMQ.Succinct.rankPrefix false bits secondStart <= q := by
              simpa [secondStart] using hsecondRankLe
            have hqSpanAt :
                q < RMQ.Succinct.rankPrefix false bits spanEnd := by
              simpa [spanEnd] using hqSpan
            cases haligned.get_some_of_mul_lt hsecondReadable with
            | intro secondWord hsecondReadAtBase =>
                have hsecondWord :=
                  haligned.get_eq_take_drop hsecondReadAtBase
                have hsecondRead :
                    bitWords.store.words[basePosition / wordSize + 1]? =
                      some secondWord := by
                  rw [<- hfacts.baseWordIndex_eq]
                  exact hsecondReadAtBase
                refine ⟨secondWord, hsecondRead, ?_⟩
                cases select_exists_of_lt_rankPrefix
                    (target := false) (bits := bits) (occurrence := q)
                    (limit := spanEnd) hqSpanAt with
                | intro pos hselect =>
                    have hsecond_le_pos : secondStart <= pos := by
                      by_cases hle : secondStart <= pos
                      · exact hle
                      · have hpos_lt_second :
                            pos < secondStart := Nat.lt_of_not_ge hle
                        have hocc_lt :=
                          occurrence_lt_rankPrefix_of_select_lt
                            hselect hpos_lt_second
                        omega
                    have hpos_lt_span : pos < spanEnd := by
                      by_cases hlt : pos < spanEnd
                      · exact hlt
                      · have hend_le_pos : spanEnd <= pos :=
                          Nat.le_of_not_gt hlt
                        have hprefix_le :=
                          RMQ.Succinct.rankPrefix_le_occurrence_of_le_select
                            hselect hend_le_pos
                        omega
                    have hpos_lt_word : pos < secondStart + wordSize := by
                      omega
                    have hstartLen : secondStart <= bits.length :=
                      Nat.le_of_lt hsecondReadable
                    have hlocal :=
                      RMQ.Succinct.select_drop_take_eq_sub_of_select
                        (target := false) (bits := bits) (occurrence := q)
                        (idx := pos) (start := secondStart)
                        (width := wordSize) hselect hsecond_le_pos
                        hpos_lt_word hstartLen hsecondRankLeAt
                    have hlocalOccurrence :
                        q - baseOccurrence -
                            (RMQ.RAM.boolRankPrefix false firstWord
                                firstWord.length -
                              RMQ.RAM.boolRankPrefix false firstWord
                                (basePosition -
                                  basePosition / wordSize * wordSize)) =
                          q -
                            RMQ.Succinct.rankPrefix false bits
                              secondStart := by
                      simpa [firstWord, falseSelectDenseLocalFirstCount,
                        falseSelectDenseLocalFirstWord, secondStart,
                        hoffset] using
                        hfacts.second_local_occurrence hnotFacts
                    have hselectWord :
                        RMQ.Succinct.select false secondWord
                            (q - baseOccurrence -
                              (RMQ.RAM.boolRankPrefix false firstWord
                                  firstWord.length -
                                RMQ.RAM.boolRankPrefix false firstWord
                                  (basePosition -
                                    basePosition / wordSize *
                                      wordSize))) =
                          some (pos - secondStart) := by
                      rw [hsecondWord]
                      rw [hlocalOccurrence]
                      simpa [secondStart,
                        falseSelectDenseLocalSecondStart] using hlocal
                    calc
                      (RMQ.RAM.boolSelectInWord false secondWord
                          (q - baseOccurrence -
                            (RMQ.RAM.boolRankPrefix false firstWord
                                firstWord.length -
                              RMQ.RAM.boolRankPrefix false firstWord
                                (basePosition -
                                  basePosition / wordSize *
                                    wordSize)))).map
                          (fun offset =>
                            (basePosition / wordSize + 1) * wordSize +
                              offset) =
                        (RMQ.Succinct.select false secondWord
                          (q - baseOccurrence -
                            (RMQ.RAM.boolRankPrefix false firstWord
                                firstWord.length -
                              RMQ.RAM.boolRankPrefix false firstWord
                                (basePosition -
                                  basePosition / wordSize *
                                    wordSize)))).map
                          (fun offset =>
                            (basePosition / wordSize + 1) * wordSize +
                              offset) := by
                          simp [RMQ.Succinct.ram_boolSelectInWord_eq_select]
                      _ = some
                          ((basePosition / wordSize + 1) * wordSize +
                            (pos - secondStart)) := by
                          simp [hselectWord]
                      _ = some pos := by
                          have hposEq :
                              (basePosition / wordSize + 1) * wordSize +
                                  (pos - secondStart) = pos := by
                            omega
                          simp [hposEq]
                      _ = RMQ.Succinct.select false bits q := hselect.symm

set_option linter.unusedSimpArgs false in
theorem denseTwoWordFalseSelectCosted_exact_of_local_span
    {bits : List Bool} {wordSize : Nat}
    {bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize}
    {basePosition baseOccurrence q : Nat}
    (hcert :
      FalseSelectDenseLocalSpanCertificate
        bits wordSize bitWords basePosition baseOccurrence q) :
    (denseTwoWordFalseSelectCosted
      bitWords basePosition baseOccurrence q).erase =
      RMQ.Succinct.select false bits q := by
  by_cases hchoose :
      q - baseOccurrence <
        RMQ.RAM.boolRankPrefix false hcert.firstWord
          hcert.firstWord.length -
          RMQ.RAM.boolRankPrefix false hcert.firstWord
            (basePosition - basePosition / wordSize * wordSize)
  case pos =>
    have hexact := hcert.first_branch_exact hchoose
    simp [denseTwoWordFalseSelectCosted,
      SuccinctSpace.PayloadWordStore.readWordCosted,
      RMQ.RAM.readArray?, Costed.bind, Costed.map,
      Costed.pure, Costed.erase, RMQ.RAM.Exec.toCosted,
      hcert.first_read, hchoose, hexact]
  case neg =>
    have hsecond := hcert.second_branch_exact hchoose
    cases hsecond with
    | intro secondWord hpair =>
        cases hpair with
        | intro hread hexact =>
            simp [denseTwoWordFalseSelectCosted,
              SuccinctSpace.PayloadWordStore.readWordCosted,
              RMQ.RAM.readArray?, Costed.bind, Costed.map,
              Costed.pure, Costed.erase, RMQ.RAM.Exec.toCosted,
              hcert.first_read, hchoose, hread, hexact]

theorem denseTwoWordFalseSelectCosted_exact_of_payload_routing_facts
    {bits : List Bool} {wordSize : Nat}
    {bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize}
    {basePosition baseOccurrence q : Nat}
    (haligned : FalseSelectAlignedBitWords bits wordSize bitWords)
    (hfacts :
      FalseSelectDenseLocalPayloadRoutingFacts
        bits wordSize basePosition baseOccurrence q) :
    (denseTwoWordFalseSelectCosted
      bitWords basePosition baseOccurrence q).erase =
      RMQ.Succinct.select false bits q := by
  exact
    denseTwoWordFalseSelectCosted_exact_of_local_span
      (falseSelectDenseLocalSpanCertificate_of_payload_routing_facts
        haligned hfacts)

def falseSelectDenseLocalPayloadRoutingFacts_of_selected_span
    {bits : List Bool} {wordSize basePosition baseOccurrence q pos : Nat}
    (hwordSize : 0 < wordSize)
    (hbaseSelect :
      RMQ.Succinct.select false bits baseOccurrence = some basePosition)
    (hselect : RMQ.Succinct.select false bits q = some pos)
    (hbaseLe : baseOccurrence <= q)
    (hposSpan : pos < basePosition + wordSize) :
    FalseSelectDenseLocalPayloadRoutingFacts
      bits wordSize basePosition baseOccurrence q := by
  let baseWordIndex := basePosition / wordSize
  let firstStart := falseSelectDenseLocalFirstStart wordSize baseWordIndex
  let secondStart := falseSelectDenseLocalSecondStart wordSize baseWordIndex
  let spanEnd := falseSelectDenseLocalSpanEnd wordSize baseWordIndex
  let firstOffset := basePosition - firstStart
  let rankBefore := RMQ.Succinct.rankPrefix false bits firstStart
  have hfirstStartLeBase : firstStart <= basePosition := by
    simpa [firstStart, baseWordIndex, falseSelectDenseLocalFirstStart] using
      Nat.div_mul_le_self basePosition wordSize
  have hbaseLtSecond : basePosition < secondStart := by
    have hmodLt : basePosition % wordSize < wordSize :=
      Nat.mod_lt basePosition hwordSize
    have hdecomp :
        basePosition / wordSize * wordSize +
            basePosition % wordSize = basePosition := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod basePosition wordSize
    simp [secondStart, baseWordIndex,
      falseSelectDenseLocalSecondStart, Nat.succ_mul]
    omega
  have hsecondEq : secondStart = firstStart + wordSize := by
    simp [secondStart, firstStart, falseSelectDenseLocalSecondStart,
      falseSelectDenseLocalFirstStart, Nat.succ_mul]
  have hspanEndEq : spanEnd = secondStart + wordSize := by
    simp [spanEnd, secondStart, falseSelectDenseLocalSpanEnd,
      falseSelectDenseLocalSecondStart, Nat.add_assoc, Nat.succ_mul]
  have hfirstStartReadable : firstStart < bits.length := by
    have hbaseBounds : basePosition < bits.length :=
      RMQ.Succinct.select_bounds hbaseSelect
    exact Nat.lt_of_le_of_lt hfirstStartLeBase hbaseBounds
  have hrankBeforeLeBase : rankBefore <= baseOccurrence := by
    simpa [rankBefore] using
      RMQ.Succinct.rankPrefix_le_occurrence_of_le_select
        hbaseSelect hfirstStartLeBase
  have hrankBeforeLeQ : rankBefore <= q := by
    omega
  have hposLtSpanEnd : pos < spanEnd := by
    have hbaseLtFirstEnd : basePosition < firstStart + wordSize := by
      omega
    rw [hspanEndEq, hsecondEq]
    omega
  have hqLtSpanRank :
      q < RMQ.Succinct.rankPrefix false bits spanEnd := by
    exact occurrence_lt_rankPrefix_of_select_lt hselect hposLtSpanEnd
  let hi := Nat.min secondStart bits.length
  have hhiLen : hi <= bits.length := Nat.min_le_right _ _
  have hfirstStartHi : firstStart <= hi := by
    exact Nat.le_min.mpr
      ⟨by omega, Nat.le_of_lt hfirstStartReadable⟩
  have hhiSub :
      hi - firstStart =
        Nat.min wordSize (bits.drop firstStart).length := by
    by_cases hcase : secondStart <= bits.length
    · have hhiEq : hi = secondStart := by
        exact Nat.min_eq_left hcase
      have hdropLenGe :
          wordSize <= (bits.drop firstStart).length := by
        simp [List.length_drop]
        omega
      have hminEq :
          Nat.min wordSize (bits.drop firstStart).length = wordSize :=
        Nat.min_eq_left hdropLenGe
      rw [hhiEq, hminEq, hsecondEq]
      omega
    · have hhiEq : hi = bits.length := by
        exact Nat.min_eq_right (Nat.le_of_not_ge hcase)
      have hdropLenLe :
          (bits.drop firstStart).length <= wordSize := by
        simp [List.length_drop]
        omega
      have hminEq :
          Nat.min wordSize (bits.drop firstStart).length =
            (bits.drop firstStart).length :=
        Nat.min_eq_right hdropLenLe
      rw [hhiEq, hminEq]
      simp [List.length_drop]
  have hdrop :=
    RMQ.Succinct.rankPrefix_drop_eq_sub_of_le
      false bits hfirstStartHi hhiLen
  have hbitsHiRank :
      RMQ.Succinct.rankPrefix false bits hi =
        RMQ.Succinct.rankPrefix false bits secondStart := by
    simpa [hi] using
      RMQ.Succinct.rankPrefix_min_length_eq false bits secondStart
  have hdropWordRank :
      RMQ.Succinct.rankPrefix false (bits.drop firstStart)
          wordSize =
        RMQ.Succinct.rankPrefix false (bits.drop firstStart)
          (hi - firstStart) := by
    have hmin :=
      RMQ.Succinct.rankPrefix_min_length_eq
        false (bits.drop firstStart) wordSize
    rw [<- hmin]
    rw [hhiSub]
  have hfirstTotal :
      RMQ.RAM.boolRankPrefix false
          (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
          (falseSelectDenseLocalFirstWord bits wordSize
            baseWordIndex).length =
        RMQ.Succinct.rankPrefix false bits secondStart -
          RMQ.Succinct.rankPrefix false bits firstStart := by
    rw [RMQ.Succinct.ram_boolRankPrefix_eq_rankPrefix]
    change
      RMQ.Succinct.rankPrefix false
          ((bits.drop firstStart).take wordSize)
          ((bits.drop firstStart).take wordSize).length =
        RMQ.Succinct.rankPrefix false bits secondStart -
          RMQ.Succinct.rankPrefix false bits firstStart
    rw [rankPrefix_take_length_eq]
    change
      RMQ.Succinct.rankPrefix false
          (bits.drop firstStart) wordSize =
        RMQ.Succinct.rankPrefix false bits secondStart -
          RMQ.Succinct.rankPrefix false bits firstStart
    rw [hdropWordRank]
    rw [hdrop]
    rw [hbitsHiRank]
  have hfirstOffsetRank :
      RMQ.RAM.boolRankPrefix false
          (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
          firstOffset =
        baseOccurrence -
          RMQ.Succinct.rankPrefix false bits firstStart := by
    rw [RMQ.Succinct.ram_boolRankPrefix_eq_rankPrefix]
    change
      RMQ.Succinct.rankPrefix false
          ((bits.drop firstStart).take wordSize)
          firstOffset =
        baseOccurrence -
          RMQ.Succinct.rankPrefix false bits firstStart
    have hoffLen : firstOffset <=
        (falseSelectDenseLocalFirstWord bits wordSize
          baseWordIndex).length := by
      have hbaseLen : basePosition < bits.length :=
        RMQ.Succinct.select_bounds hbaseSelect
      have hoffWord : firstOffset <= wordSize := by
        omega
      have hoffDrop : firstOffset <= (bits.drop firstStart).length := by
        simp [List.length_drop]
        omega
      simpa [falseSelectDenseLocalFirstWord] using
        (Nat.le_min.mpr ⟨hoffWord, hoffDrop⟩)
    have htake :=
      RMQ.Succinct.rankPrefix_take_eq_of_le
        false (bits.drop firstStart) (n := wordSize)
        (limit := firstOffset) hoffLen
    rw [htake]
    have hlimit : firstStart + firstOffset <= bits.length := by
      have hbaseLen : basePosition < bits.length :=
        RMQ.Succinct.select_bounds hbaseSelect
      omega
    have hdropOffset :=
      RMQ.Succinct.rankPrefix_drop_eq_sub_of_le
        false bits (start := firstStart)
        (limit := firstStart + firstOffset)
        (by omega) hlimit
    have hbaseEq : firstStart + firstOffset = basePosition := by
      simp [firstOffset]
      omega
    rw [hbaseEq] at hdropOffset
    have hbaseRank :
        RMQ.Succinct.rankPrefix false bits basePosition =
          baseOccurrence := by
      exact RMQ.Succinct.select_rankPrefix_eq hbaseSelect
    rw [hdropOffset, hbaseRank]
  have hbaseLtSecondRank :
      baseOccurrence <
        RMQ.Succinct.rankPrefix false bits secondStart :=
    occurrence_lt_rankPrefix_of_select_lt hbaseSelect hbaseLtSecond
  have hfirstCountEq :
      falseSelectDenseLocalFirstCount
          bits wordSize baseWordIndex firstOffset =
        RMQ.Succinct.rankPrefix false bits secondStart - baseOccurrence := by
    unfold falseSelectDenseLocalFirstCount
    rw [hfirstTotal, hfirstOffsetRank]
    omega
  refine {
    baseWordIndex := baseWordIndex
    rankBefore := rankBefore
    firstOffset := firstOffset
    baseWordIndex_eq := rfl
    rankBefore_eq := rfl
    firstOffset_eq := rfl
    firstWordStart_readable := hfirstStartReadable
    rankBefore_le_query := hrankBeforeLeQ
    first_branch_rank := ?_
    first_local_occurrence := ?_
    second_branch_rank := ?_
    second_local_occurrence := ?_ }
  · intro hchoice
    rw [hfirstCountEq] at hchoice
    have hq :
        q < RMQ.Succinct.rankPrefix false bits secondStart := by
      omega
    simpa [secondStart] using hq
  · rw [hfirstOffsetRank]
    have hcalc :
        baseOccurrence -
            RMQ.Succinct.rankPrefix false bits firstStart +
            (q - baseOccurrence) =
          q - rankBefore := by
      simp [rankBefore]
      omega
    exact hcalc
  · intro hnot
    have hsecondLe :
        RMQ.Succinct.rankPrefix false bits secondStart <= q := by
      by_cases hlt :
          q < RMQ.Succinct.rankPrefix false bits secondStart
      · have hchoice :
            q - baseOccurrence <
              falseSelectDenseLocalFirstCount
                bits wordSize baseWordIndex firstOffset := by
          rw [hfirstCountEq]
          omega
        exact False.elim (hnot hchoice)
      · exact Nat.le_of_not_gt hlt
    have hsecondReadable :
        secondStart < bits.length := by
      by_cases hle : secondStart <= pos
      · exact Nat.lt_of_le_of_lt hle (RMQ.Succinct.select_bounds hselect)
      · have hposLtSecond : pos < secondStart := Nat.lt_of_not_ge hle
        have hoccLt :=
          occurrence_lt_rankPrefix_of_select_lt hselect hposLtSecond
        omega
    exact
      ⟨by simpa [secondStart] using hsecondLe,
        by simpa [spanEnd] using hqLtSpanRank,
        by simpa [secondStart] using hsecondReadable⟩
  · intro hnot
    have hsecondLe :
        RMQ.Succinct.rankPrefix false bits secondStart <= q := by
      by_cases hlt :
          q < RMQ.Succinct.rankPrefix false bits secondStart
      · have hchoice :
            q - baseOccurrence <
              falseSelectDenseLocalFirstCount
                bits wordSize baseWordIndex firstOffset := by
          rw [hfirstCountEq]
          omega
        exact False.elim (hnot hchoice)
      · exact Nat.le_of_not_gt hlt
    rw [hfirstCountEq]
    simpa [secondStart] using
      (by
        omega :
          q - baseOccurrence -
              (RMQ.Succinct.rankPrefix false bits secondStart -
                baseOccurrence) =
            q - RMQ.Succinct.rankPrefix false bits secondStart)


end SuccinctSelect
end RMQ
