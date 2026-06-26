import RMQ.Core.SuccinctSelect.CloseSelect.SparseExceptionDirectory

/-!
# Sparse-exception close-select data surface

Split implementation layer for sparse-exception close-select data.
Public declarations stay in the historical `RMQ.SuccinctSelectProposal`
namespace until the namespace-alignment cleanup pass.
-/

namespace RMQ
namespace SuccinctSelectProposal

structure RelativeSplitSparseExceptionFalseSelectCloseData
    (shape : Cartesian.CartesianShape)
    (rankSuperOverhead rankBlockOverhead : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  wordSize_le_machine :
    wordSize <= SuccinctRankProposal.machineWordBits shape.bpCode.length
  superStride : Nat
  superStride_pos : 0 < superStride
  localStride : Nat
  localStride_pos : 0 < localStride
  localSlotsPerSuper : Nat
  superEntries : List SparseDenseFalseSelectDenseLocalEntry
  longFlagBits : List Bool
  longFlagBits_eq :
    longFlagBits = relativeSplitFalseSelectLongFlagBits superEntries
  longFlagRankSuperOverhead : Nat
  longFlagRankBlockOverhead : Nat
  longFlagRankData :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      longFlagBits longFlagRankSuperOverhead longFlagRankBlockOverhead 4
  longFlagRank_wordSize_le_machine :
    longFlagRankData.wordSize <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length
  longFlagRank_superWidth_le_machine :
    longFlagRankData.superWidth <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length
  longFlagRank_blockWidth_le_machine :
    longFlagRankData.blockWidth <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length
  longSuperRelativeEntries : List Nat
  localEntries : List SparseDenseFalseSelectDenseLocalEntry
  superFieldWidth : Nat
  longSuperRelativeWidth : Nat
  localFieldWidth : Nat
  superTable :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      superEntries superFieldWidth
  longSuperRelativeTable :
    SuccinctSpace.FixedWidthNatTable
      longSuperRelativeEntries longSuperRelativeWidth
  localTable :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      localEntries localFieldWidth
  sparseDirectory :
    RelativeSplitSparseExceptionDirectory
      shape rankSuperOverhead rankBlockOverhead
  bitWords : SuccinctSpace.BoundedPayloadWordStore shape.bpCode wordSize
  super_read_words_length_le_machine :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.ReadWordsLengthLeMachine
      superTable shape.bpCode.length
  long_read_words_length_le_machine :
    forall {i : Nat} {word : List Bool},
      longSuperRelativeTable.store.words[i]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length
  local_read_words_length_le_machine :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.ReadWordsLengthLeMachine
      localTable shape.bpCode.length
  payload_length_le_overhead :
    (superTable.payload ++ longFlagBits ++
      longFlagRankData.auxPayload ++ longSuperRelativeTable.payload ++
        localTable.payload ++ sparseDirectory.payload).length <=
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead shape.size
  super_missing_exact :
    forall q,
      superEntries[falseSelectSuperSlot q superStride]? = none ->
        RMQ.Succinct.select false shape.bpCode q = none
  long_explicit_exact :
    forall q super,
      superEntries[falseSelectSuperSlot q superStride]? = some super ->
      q < RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length ->
      relativeSplitFalseSelectEntryIsMarked super = true ->
        (longSuperRelativeEntries[
            relativeSplitFalseSelectLongCompactSlot
              (RMQ.Succinct.rankPrefix true longFlagBits
                (falseSelectSuperSlot q superStride))
              (q - super.baseOccurrence) superStride]?).map
          (fun offset =>
            relativeSplitFalseSelectEntryBasePosition wordSize super +
              offset) =
          RMQ.Succinct.select false shape.bpCode q
  local_missing_exact :
    forall q super,
      superEntries[falseSelectSuperSlot q superStride]? = some super ->
      q < RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length ->
      relativeSplitFalseSelectEntryIsMarked super = false ->
      localEntries[
          relativeSplitFalseSelectLocalSlot q superStride
            localSlotsPerSuper localStride super]? = none ->
        RMQ.Succinct.select false shape.bpCode q = none
  sparse_compact_exact :
    forall q super loc,
      superEntries[falseSelectSuperSlot q superStride]? = some super ->
      q < RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length ->
      relativeSplitFalseSelectEntryIsMarked super = false ->
      localEntries[
          relativeSplitFalseSelectLocalSlot q superStride
            localSlotsPerSuper localStride super]? = some loc ->
      relativeSplitFalseSelectEntryIsMarked loc = true ->
        (sparseDirectory.readCosted
          (relativeSplitFalseSelectLocalBasePosition wordSize super loc)
          (relativeSplitFalseSelectLocalSlot q superStride
            localSlotsPerSuper localStride super)
          (q - relativeSplitFalseSelectLocalBaseOccurrence super loc)).erase =
          RMQ.Succinct.select false shape.bpCode q
  dense_exact :
    forall q super loc,
      superEntries[falseSelectSuperSlot q superStride]? = some super ->
      q < RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length ->
      relativeSplitFalseSelectEntryIsMarked super = false ->
      localEntries[
          relativeSplitFalseSelectLocalSlot q superStride
            localSlotsPerSuper localStride super]? = some loc ->
      relativeSplitFalseSelectEntryIsMarked loc = false ->
        (denseTwoWordFalseSelectCosted bitWords
          (relativeSplitFalseSelectLocalBasePosition wordSize super loc)
          (relativeSplitFalseSelectLocalBaseOccurrence super loc) q).erase =
          RMQ.Succinct.select false shape.bpCode q

namespace RelativeSplitSparseExceptionFalseSelectCloseData

def payload
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) :
    List Bool :=
  data.superTable.payload ++ data.longFlagBits ++
    data.longFlagRankData.auxPayload ++
      data.longSuperRelativeTable.payload ++
        data.localTable.payload ++ data.sparseDirectory.payload

def longFlagRankReadWords
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) :
    List (List Bool) :=
  (((data.longFlagRankData.superTables.trueTable.store.words.toList ++
      data.longFlagRankData.superTables.falseTable.store.words.toList) ++
    data.longFlagRankData.blockTables.trueTable.store.words.toList ++
      data.longFlagRankData.blockTables.falseTable.store.words.toList) ++
        data.longFlagRankData.bitWords.store.words.toList)

def readWords
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) :
    List (List Bool) :=
  data.superTable.readWords ++
    data.longFlagRankReadWords ++
      data.longSuperRelativeTable.store.words.toList ++
        data.localTable.readWords ++
          data.sparseDirectory.readWords ++
            data.bitWords.store.words.toList

def queryOccurrence
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (_data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (idx : Nat) : Nat :=
  idx

def selectCloseCosted
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (idx : Nat) : Costed (Option Nat) :=
  let q := data.queryOccurrence idx
  if idx < shape.size then
    Costed.bind
      (data.superTable.readCosted
        (falseSelectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => Costed.pure none
      | some super =>
          if relativeSplitFalseSelectEntryIsMarked super then
            Costed.bind
              (data.longFlagRankData.rankCosted true
                (falseSelectSuperSlot q data.superStride))
              fun exceptionRank =>
                relativeOffsetReadCosted data.longSuperRelativeTable
                  (relativeSplitFalseSelectEntryBasePosition
                    data.wordSize super)
                  (relativeSplitFalseSelectLongCompactSlot
                    exceptionRank (q - super.baseOccurrence)
                    data.superStride)
          else
            let localSlot :=
              relativeSplitFalseSelectLocalSlot q data.superStride
                data.localSlotsPerSuper data.localStride super
            Costed.bind (data.localTable.readCosted localSlot) fun loc? =>
              match loc? with
              | none => Costed.pure none
              | some loc =>
                  if relativeSplitFalseSelectEntryIsMarked loc then
                    data.sparseDirectory.readCosted
                      (relativeSplitFalseSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        relativeSplitFalseSelectLocalBaseOccurrence
                          super loc)
                  else
                    denseTwoWordFalseSelectCosted data.bitWords
                      (relativeSplitFalseSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitFalseSelectLocalBaseOccurrence
                        super loc)
                      q
  else
    Costed.pure none

theorem payload_length_le_canonical
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) :
    data.payload.length <=
      canonicalRelativeSplitSparseExceptionFalseSelectOverhead
        shape.size := by
  simpa [payload] using data.payload_length_le_overhead

theorem selectCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) (idx : Nat) :
    (data.selectCloseCosted idx).cost <=
      sparseDenseFalseSelectQueryCost := by
  unfold selectCloseCosted queryOccurrence sparseDenseFalseSelectQueryCost
  by_cases hvalid : idx < shape.size
  case pos =>
    cases hsuperValue :
        (data.superTable.readCosted
          (falseSelectSuperSlot
            idx data.superStride)).value with
    | none =>
        simp [Costed.bind, Costed.pure, hvalid, hsuperValue] <;> omega
    | some super =>
        by_cases hlong :
            relativeSplitFalseSelectEntryIsMarked super = true
        case pos =>
          have hrankCost :=
            data.longFlagRankData.rankCosted_cost_le true
              (falseSelectSuperSlot
                idx data.superStride)
          have hlongCost :
              (data.longSuperRelativeTable.readCosted
                (relativeSplitFalseSelectLongCompactSlot
                  (data.longFlagRankData.rankCosted true
                    (falseSelectSuperSlot
                      idx data.superStride)).value
                  (idx - super.baseOccurrence)
                  data.superStride)).cost <= 1 := by
            exact data.longSuperRelativeTable.readCosted_cost_le_one _
          simp [relativeOffsetReadCosted, Costed.bind, Costed.map,
            Costed.pure, hvalid, hsuperValue, hlong] <;> omega
        case neg =>
          let localSlot :=
            relativeSplitFalseSelectLocalSlot
              idx data.superStride
              data.localSlotsPerSuper data.localStride super
          cases hlocalValue :
              (data.localTable.readCosted localSlot).value with
          | none =>
              simp [Costed.bind, Costed.pure, hvalid, hsuperValue, hlong,
                localSlot, hlocalValue] <;> omega
          | some loc =>
              by_cases hsparse :
                  relativeSplitFalseSelectEntryIsMarked loc = true
              case pos =>
                have hsparseCost :
                  (data.sparseDirectory.readCosted
                    (relativeSplitFalseSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitFalseSelectLocalSlot
                      idx data.superStride
                      data.localSlotsPerSuper data.localStride super)
                    (idx -
                      relativeSplitFalseSelectLocalBaseOccurrence super loc)).cost
                      <= 5 := by
                  simpa [localSlot] using
                    data.sparseDirectory.readCosted_cost_le_five
                      (relativeSplitFalseSelectLocalBasePosition
                      data.wordSize super loc)
                      localSlot
                      (idx -
                        relativeSplitFalseSelectLocalBaseOccurrence super loc)
                simp [Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse] <;> omega
              case neg =>
                have hdenseCost :=
                  denseTwoWordFalseSelectCosted_cost_le_five
                    data.bitWords
                    (relativeSplitFalseSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitFalseSelectLocalBaseOccurrence super loc)
                    idx
                simp [Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse] <;> omega
  case neg =>
    simp [Costed.pure, hvalid]

theorem selectCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) (idx : Nat) :
    (data.selectCloseCosted idx).erase =
      SuccinctSpace.bpCloseOfInorder? shape idx := by
  let q := idx
  have hclamp :
      RMQ.Succinct.select false shape.bpCode q =
        SuccinctSpace.bpCloseOfInorder? shape idx := by
    simpa [q] using
      SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx
  unfold selectCloseCosted queryOccurrence
  dsimp only
  by_cases hvalid : idx < shape.size
  case pos =>
    have hvalidQ :
        q < RMQ.Succinct.rankPrefix false shape.bpCode
          shape.bpCode.length := by
      simpa [q, SuccinctSpace.bpCode_rankFalse_full] using hvalid
    cases hsuper :
        data.superEntries[
          falseSelectSuperSlot
            idx data.superStride]? with
    | none =>
        have hsuperQ :
            data.superEntries[
                falseSelectSuperSlot q data.superStride]? =
              none := by
          simpa [q] using hsuper
        simp [hvalid, hsuper, Costed.erase_bind,
          FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase]
        rw [<- hclamp]
        exact (data.super_missing_exact q hsuperQ).symm
    | some super =>
        have hsuperQ :
            data.superEntries[
                falseSelectSuperSlot q data.superStride]? =
              some super := by
          simpa [q] using hsuper
        by_cases hlong :
            relativeSplitFalseSelectEntryIsMarked super = true
        case pos =>
          have hrank :=
            data.longFlagRankData.rankCosted_exact true
              (falseSelectSuperSlot
                idx data.superStride)
          simp [hvalid, hsuper, hlong, relativeOffsetReadCosted,
            Costed.erase_bind, Costed.erase_map,
            FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase,
            SuccinctSpace.FixedWidthNatTable.readCosted_erase, hrank]
          rw [<- hclamp]
          simpa [q] using
            data.long_explicit_exact q super hsuperQ hvalidQ hlong
        case neg =>
          let localSlot :=
            relativeSplitFalseSelectLocalSlot
              idx data.superStride
              data.localSlotsPerSuper data.localStride super
          have hlongFalse :
              relativeSplitFalseSelectEntryIsMarked super = false := by
            cases hmark : relativeSplitFalseSelectEntryIsMarked super
            case false =>
              rfl
            case true =>
              exact False.elim (hlong hmark)
          cases hlocal :
              data.localEntries[localSlot]? with
          | none =>
              simp [hvalid, hsuper, hlong, localSlot, hlocal,
                Costed.erase_bind,
                FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase]
              have hlocal' :
                data.localEntries[
                    relativeSplitFalseSelectLocalSlot q data.superStride
                      data.localSlotsPerSuper data.localStride super]? =
                  none := by
                simpa [q, localSlot] using hlocal
              rw [<- hclamp]
              exact (data.local_missing_exact q super hsuperQ hvalidQ hlongFalse
                hlocal').symm
          | some loc =>
              by_cases hsparse :
                  relativeSplitFalseSelectEntryIsMarked loc = true
              case pos =>
                simp [hvalid, hsuper, hlong, localSlot, hlocal,
                  Costed.erase_bind,
                  FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase]
                have hlocal' :
                    data.localEntries[
                        relativeSplitFalseSelectLocalSlot q data.superStride
                        data.localSlotsPerSuper data.localStride super]? =
                      some loc := by
                  simpa [q, localSlot] using hlocal
                simp [hsparse]
                rw [<- hclamp]
                simpa [q] using
                  data.sparse_compact_exact q super loc hsuperQ hvalidQ
                    hlongFalse hlocal' hsparse
              case neg =>
                have hsparseFalse :
                    relativeSplitFalseSelectEntryIsMarked loc = false := by
                  cases hmark : relativeSplitFalseSelectEntryIsMarked loc
                  case false =>
                    rfl
                  case true =>
                    exact False.elim (hsparse hmark)
                simp [hvalid, hsuper, hlong, localSlot, hlocal,
                  Costed.erase_bind,
                  FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase]
                have hlocal' :
                    data.localEntries[
                        relativeSplitFalseSelectLocalSlot q data.superStride
                        data.localSlotsPerSuper data.localStride super]? =
                      some loc := by
                  simpa [q, localSlot] using hlocal
                simp [hsparse]
                rw [<- hclamp]
                simpa [q] using
                  data.dense_exact q super loc hsuperQ hvalidQ hlongFalse
                    hlocal' hsparseFalse
  case neg =>
    have hnotQ :
        ¬ q < RMQ.Succinct.rankPrefix false shape.bpCode
          shape.bpCode.length := by
      simpa [q, SuccinctSpace.bpCode_rankFalse_full] using hvalid
    simp [hvalid, Costed.pure]
    rw [<- SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx]
    exact
      (select_none_of_rankPrefix_length_le
        (target := false) (bits := shape.bpCode) (occurrence := idx)
        (by
          rw [SuccinctSpace.bpCode_rankFalse_full]
          omega)).symm

theorem longFlagRank_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    (hmem : List.Mem word data.longFlagRankReadWords) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  rw [longFlagRankReadWords] at hmem
  cases List.mem_append.mp hmem with
  | inl hsampleMem =>
      cases List.mem_append.mp hsampleMem with
      | inl hsamplePrefix =>
          cases List.mem_append.mp hsamplePrefix with
          | inl hsuperMem =>
              cases List.mem_append.mp hsuperMem with
              | inl hsuperTrueMem =>
                  cases (List.mem_iff_getElem?.mp hsuperTrueMem) with
                  | intro i hgetList =>
                    have hget :
                        data.longFlagRankData.superTables.trueTable.store.words[i]? =
                          some word := by
                      simpa [Array.getElem?_toList] using hgetList
                    rw [data.longFlagRankData.superTables.trueTable.read_word_length_of_some
                      hget]
                    exact data.longFlagRank_superWidth_le_machine
              | inr hsuperFalseMem =>
                  cases (List.mem_iff_getElem?.mp hsuperFalseMem) with
                  | intro i hgetList =>
                    have hget :
                        data.longFlagRankData.superTables.falseTable.store.words[i]? =
                          some word := by
                      simpa [Array.getElem?_toList] using hgetList
                    rw [data.longFlagRankData.superTables.falseTable.read_word_length_of_some
                      hget]
                    exact data.longFlagRank_superWidth_le_machine
          | inr hblockTrueMem =>
              cases (List.mem_iff_getElem?.mp hblockTrueMem) with
              | intro i hgetList =>
                have hget :
                    data.longFlagRankData.blockTables.trueTable.store.words[i]? =
                      some word := by
                  simpa [Array.getElem?_toList] using hgetList
                rw [data.longFlagRankData.blockTables.trueTable.read_word_length_of_some
                  hget]
                exact data.longFlagRank_blockWidth_le_machine
      | inr hblockFalseMem =>
          cases (List.mem_iff_getElem?.mp hblockFalseMem) with
          | intro i hgetList =>
            have hget :
                data.longFlagRankData.blockTables.falseTable.store.words[i]? =
                  some word := by
              simpa [Array.getElem?_toList] using hgetList
            rw [data.longFlagRankData.blockTables.falseTable.read_word_length_of_some
              hget]
            exact data.longFlagRank_blockWidth_le_machine
  | inr hflagMem =>
      exact Nat.le_trans
        (data.longFlagRankData.bitWords.word_length_le hflagMem)
        data.longFlagRank_wordSize_le_machine

theorem read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    (hmem : List.Mem word data.readWords) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  rw [readWords] at hmem
  cases List.mem_append.mp hmem with
  | inl hprefix0 =>
      cases List.mem_append.mp hprefix0 with
      | inl hprefix1 =>
          cases List.mem_append.mp hprefix1 with
          | inl hprefix2 =>
              cases List.mem_append.mp hprefix2 with
              | inl hsuperOrRank =>
                  cases List.mem_append.mp hsuperOrRank with
                  | inl hsuperMem =>
                      exact data.superTable.read_word_length_le_machine
                        data.super_read_words_length_le_machine hsuperMem
                  | inr hrankMem =>
                      exact data.longFlagRank_read_word_length_le_machine
                        hrankMem
              | inr hlongMem =>
                  cases (List.mem_iff_getElem?.mp hlongMem) with
                  | intro i hgetList =>
                    have hget :
                        data.longSuperRelativeTable.store.words[i]? =
                          some word := by
                      simpa [Array.getElem?_toList] using hgetList
                    exact data.long_read_words_length_le_machine hget
          | inr hlocalMem =>
              exact data.localTable.read_word_length_le_machine
                data.local_read_words_length_le_machine hlocalMem
      | inr hsparseMem =>
          exact data.sparseDirectory.read_words_length_le_machine hsparseMem
  | inr hbitsMem =>
      exact Nat.le_trans (data.bitWords.word_length_le hbitsMem)
        data.wordSize_le_machine

theorem profile
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) :
    data.payload.length <=
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead shape.size /\
      SuccinctSpace.LittleOLinear
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead /\
      (forall idx,
        (data.selectCloseCosted idx).cost <=
          sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (data.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      forall {word : List Bool},
        List.Mem word data.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact
    ⟨data.payload_length_le_canonical,
      canonicalRelativeSplitSparseExceptionFalseSelectOverhead_littleO,
      data.selectCloseCosted_cost_le,
      data.selectCloseCosted_exact,
      fun {word} hmem => data.read_word_length_le_machine hmem⟩

def toChargedSelectPositionSource
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) :
    ChargedSelectPositionSource false shape.bpCode
      canonicalRelativeSplitSparseExceptionFalseSelectOverhead
      sparseDenseFalseSelectQueryCost where
  domainSize := shape.size
  payload := data.payload
  readWords := data.readWords
  selectPositionCosted := data.selectCloseCosted
  payload_length_le := data.payload_length_le_canonical
  overhead_littleO :=
    canonicalRelativeSplitSparseExceptionFalseSelectOverhead_littleO
  selectPositionCosted_cost_le := data.selectCloseCosted_cost_le
  selectPositionCosted_exact := by
    intro idx
    rw [data.selectCloseCosted_exact idx]
    rw [<- SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx]
  read_word_length_le_machine := by
    intro word hmem
    exact data.read_word_length_le_machine hmem

def relativeSplitDescriptorIndexCosted
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (idx : Nat) : Costed (Option Nat) :=
  Costed.map
    (fun pos? =>
      pos?.map
        (fun pos =>
          clarkSelectTwoWordDescriptorIndexOfPos data.wordSize pos))
    (data.selectCloseCosted idx)

theorem relativeSplitDescriptorIndexCosted_eq_chargedSource
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (idx : Nat) :
    data.relativeSplitDescriptorIndexCosted idx =
      (data.toChargedSelectPositionSource.descriptorIndexCosted
        data.wordSize idx) := by
  rfl

theorem toChargedSelectPositionSource_descriptorIndexCosted_profile
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {occurrencesPerChunk : Nat}
    (hchunk : 0 < occurrencesPerChunk) :
    let source := data.toChargedSelectPositionSource
    source.payload.length <=
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead
          source.domainSize /\
      SuccinctSpace.LittleOLinear
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead /\
      (forall idx,
        (source.descriptorIndexCosted data.wordSize idx).cost <=
          sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (source.descriptorIndexCosted data.wordSize idx).erase =
          (RMQ.Succinct.select false shape.bpCode idx).map
            (fun pos =>
              clarkSelectTwoWordDescriptorIndexOfPos data.wordSize pos)) /\
      (forall {idx descriptorIndex : Nat},
        (source.descriptorIndexCosted data.wordSize idx).erase =
          some descriptorIndex ->
          ClarkSelectTwoWordChunkCovers false shape.bpCode data.wordSize
            descriptorIndex occurrencesPerChunk idx) /\
      forall {word : List Bool},
        List.Mem word source.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  intro source
  exact
    source.descriptorIndexCosted_profile data.wordSize_pos hchunk

theorem relativeSplitDescriptorIndexCosted_table_backed_sample_exact
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    {fieldWidth count occurrencesPerChunk idx pos descriptorIndex
      firstWordCount : Nat}
    (hfield : data.wordSize < 2 ^ fieldWidth)
    (hchunk : 0 < occurrencesPerChunk)
    (hdescriptorRead :
      (data.relativeSplitDescriptorIndexCosted idx).erase =
        some descriptorIndex)
    (hfirstRead :
      ((twoWordDescriptorFirstCountTables
          shape.bpCode data.wordSize fieldWidth count hfield).sampleCosted
          false descriptorIndex).erase = some firstWordCount)
    (hselect : RMQ.Succinct.select false shape.bpCode idx = some pos)
    (hword :
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
          shape.bpCode data.wordSize_pos).store.words[
            (clarkSelectTwoWordDescriptorSample false shape.bpCode
              data.wordSize descriptorIndex firstWordCount idx).wordIndex]? =
        some word) :
    SelectSampleWordExact false shape.bpCode idx
      (clarkSelectTwoWordDescriptorSample false shape.bpCode data.wordSize
        descriptorIndex firstWordCount idx) word := by
  rw [relativeSplitDescriptorIndexCosted_eq_chargedSource] at hdescriptorRead
  exact
    data.toChargedSelectPositionSource
      |>.descriptorIndexCosted_table_backed_sample_exact
        hfield data.wordSize_pos hchunk hdescriptorRead hfirstRead hselect
        hword

theorem relativeSplitDescriptorIndexCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (idx : Nat) :
    (data.relativeSplitDescriptorIndexCosted idx).cost <=
      sparseDenseFalseSelectQueryCost := by
  rw [relativeSplitDescriptorIndexCosted, Costed.map_cost]
  exact data.selectCloseCosted_cost_le idx

theorem relativeSplitDescriptorIndexCosted_erase
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (idx : Nat) :
    (data.relativeSplitDescriptorIndexCosted idx).erase =
      (RMQ.Succinct.select false shape.bpCode idx).map
        (fun pos =>
          clarkSelectTwoWordDescriptorIndexOfPos data.wordSize pos) := by
  rw [relativeSplitDescriptorIndexCosted, Costed.erase_map]
  rw [data.selectCloseCosted_exact idx]
  rw [<- SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx]

theorem relativeSplitDescriptorIndexCosted_covers
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {occurrencesPerChunk idx descriptorIndex : Nat}
    (hchunk : 0 < occurrencesPerChunk)
    (hread :
      (data.relativeSplitDescriptorIndexCosted idx).erase =
        some descriptorIndex) :
    ClarkSelectTwoWordChunkCovers false shape.bpCode data.wordSize
      descriptorIndex occurrencesPerChunk idx := by
  rw [relativeSplitDescriptorIndexCosted_erase] at hread
  cases hselect : RMQ.Succinct.select false shape.bpCode idx with
  | none =>
      simp [hselect] at hread
  | some pos =>
      simp [hselect] at hread
      exact
        clarkSelectTwoWordDescriptorIndexOfPos_covers
          (target := false) (bits := shape.bpCode)
          (wordSize := data.wordSize)
          (occurrencesPerChunk := occurrencesPerChunk)
          (occurrence := idx) (pos := pos)
          (descriptorIndex := descriptorIndex)
          data.wordSize_pos hchunk hselect hread.symm

theorem relativeSplitDescriptorIndexCosted_profile
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {occurrencesPerChunk : Nat}
    (hchunk : 0 < occurrencesPerChunk) :
    data.payload.length <=
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead shape.size /\
      SuccinctSpace.LittleOLinear
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead /\
      (forall idx,
        (data.relativeSplitDescriptorIndexCosted idx).cost <=
          sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (data.relativeSplitDescriptorIndexCosted idx).erase =
          (RMQ.Succinct.select false shape.bpCode idx).map
            (fun pos =>
              clarkSelectTwoWordDescriptorIndexOfPos data.wordSize pos)) /\
      (forall {idx descriptorIndex : Nat},
        (data.relativeSplitDescriptorIndexCosted idx).erase =
          some descriptorIndex ->
          ClarkSelectTwoWordChunkCovers false shape.bpCode data.wordSize
            descriptorIndex occurrencesPerChunk idx) /\
      forall {word : List Bool},
        List.Mem word data.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hprofile := data.profile
  exact
    ⟨hprofile.1, hprofile.2.1,
      data.relativeSplitDescriptorIndexCosted_cost_le,
      data.relativeSplitDescriptorIndexCosted_erase,
      fun {idx descriptorIndex} hread =>
        data.relativeSplitDescriptorIndexCosted_covers hchunk hread,
      hprofile.2.2.2.2⟩

theorem long_explicit_slot_lt_length_of_select
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {q pos : Nat} {super : SparseDenseFalseSelectDenseLocalEntry}
    (hsuper :
      data.superEntries[falseSelectSuperSlot q data.superStride]? =
        some super)
    (hlong :
      relativeSplitFalseSelectEntryIsMarked super = true)
    (hselect :
      RMQ.Succinct.select false shape.bpCode q = some pos) :
    relativeSplitFalseSelectLongCompactSlot
        (RMQ.Succinct.rankPrefix true data.longFlagBits
          (falseSelectSuperSlot q data.superStride))
        (q - super.baseOccurrence) data.superStride <
      data.longSuperRelativeEntries.length := by
  have hvalid :
      q < RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length := by
    have hpos : pos < shape.bpCode.length :=
      RMQ.Succinct.select_bounds hselect
    have hsucc :=
      rankPrefix_succ_of_select
        (target := false) (bits := shape.bpCode)
        (occurrence := q) (pos := pos) hselect
    have hmono :
        RMQ.Succinct.rankPrefix false shape.bpCode (pos + 1) <=
          RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length :=
      RMQ.Succinct.rankPrefix_mono_limit false shape.bpCode (by omega)
    omega
  have hexact :=
    data.long_explicit_exact q super hsuper hvalid hlong
  rw [hselect] at hexact
  cases hentry :
      data.longSuperRelativeEntries[
        relativeSplitFalseSelectLongCompactSlot
          (RMQ.Succinct.rankPrefix true data.longFlagBits
            (falseSelectSuperSlot q data.superStride))
          (q - super.baseOccurrence) data.superStride]? with
  | none =>
      simp [hentry] at hexact
  | some offset =>
      exact (List.getElem?_eq_some_iff.mp hentry).1

end RelativeSplitSparseExceptionFalseSelectCloseData

end SuccinctSelectProposal
end RMQ
