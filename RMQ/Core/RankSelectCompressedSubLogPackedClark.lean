import RMQ.Core.RankSelectCompressedSubLogDenseWord

/-!
# Packed sub-log Clark select source

This module replaces the raw-bitword dense branch of the generic
sparse-exception Clark source with the packed sub-log local decoder.
-/

namespace RMQ

namespace RankSelectSpec

open GenericSelect

set_option linter.unusedSimpArgs false

def subLogPackedClarkSelectQueryCost : Nat :=
  GenericSelect.sparseDenseSelectQueryCost +
    2 * fixedWeightSubLogDenseWindowReadCost

def subLogPackedClarkSelectCosted
    (bits : List Bool) (target : Bool) (idx : Nat) :
    Costed (Option Nat) :=
  let data := GenericSelect.sparseExceptionSelectData bits target
  let q := idx
  if idx < GenericSelect.occurrenceCount bits target then
    Costed.bind
      (data.superTable.readCosted
        (GenericSelect.selectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => Costed.pure none
      | some super =>
          if GenericSelect.relativeSplitSelectEntryIsMarked super then
            Costed.bind
              (data.longFlagRankData.rankCosted true
                (GenericSelect.selectSuperSlot q data.superStride))
              fun exceptionRank =>
                GenericSelect.relativeOffsetReadCosted
                  data.longSuperRelativeTable
                  (GenericSelect.relativeSplitSelectEntryBasePosition
                    data.wordSize super)
                  (GenericSelect.relativeSplitSelectLongCompactSlot
                    exceptionRank (q - super.baseOccurrence)
                    data.superStride)
          else
            let localSlot :=
              GenericSelect.relativeSplitSelectLocalSlot q data.superStride
                data.localSlotsPerSuper data.localStride super
            Costed.bind (data.localTable.readCosted localSlot) fun loc? =>
              match loc? with
              | none => Costed.pure none
              | some loc =>
                  if GenericSelect.relativeSplitSelectEntryIsMarked loc then
                    data.sparseDirectory.readCosted
                      (GenericSelect.relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        GenericSelect.relativeSplitSelectLocalBaseOccurrence
                          super loc)
                  else
                    subLogDenseTwoWordSelectCosted target bits
                      (GenericSelect.relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                        super loc) q
  else
    Costed.pure none

theorem subLogPackedClarkSelectCosted_cost_le
    (bits : List Bool) (target : Bool) (idx : Nat) :
    (subLogPackedClarkSelectCosted bits target idx).cost <=
      subLogPackedClarkSelectQueryCost := by
  unfold subLogPackedClarkSelectCosted subLogPackedClarkSelectQueryCost
  let data := GenericSelect.sparseExceptionSelectData bits target
  by_cases hvalid : idx < GenericSelect.occurrenceCount bits target
  · cases hsuperValue :
        (data.superTable.readCosted
          (GenericSelect.selectSuperSlot idx data.superStride)).value with
    | none =>
        simp [data, Costed.bind, Costed.pure, hvalid, hsuperValue]
        simp [GenericSelect.sparseDenseSelectQueryCost,
          fixedWeightSubLogDenseWindowReadCost,
          fixedWeightSubLogDenseWindowBlockCount]
    | some super =>
        by_cases hlong :
            GenericSelect.relativeSplitSelectEntryIsMarked super = true
        · have hrankCost :=
            data.longFlagRankData.rankCosted_cost_le true
              (GenericSelect.selectSuperSlot idx data.superStride)
          have hlongCost :
              (data.longSuperRelativeTable.readCosted
                (GenericSelect.relativeSplitSelectLongCompactSlot
                  (data.longFlagRankData.rankCosted true
                    (GenericSelect.selectSuperSlot
                      idx data.superStride)).value
                  (idx - super.baseOccurrence)
                  data.superStride)).cost <= 1 := by
            exact data.longSuperRelativeTable.readCosted_cost_le_one _
          have hrankCostCanonical := hrankCost
          simp [data] at hrankCostCanonical
          simp [data, GenericSelect.relativeOffsetReadCosted, Costed.bind,
            Costed.map, Costed.pure, hvalid, hsuperValue, hlong]
          simp [GenericSelect.sparseDenseSelectQueryCost,
            fixedWeightSubLogDenseWindowReadCost,
            fixedWeightSubLogDenseWindowBlockCount] at *
          omega
        · let localSlot :=
            GenericSelect.relativeSplitSelectLocalSlot
              idx data.superStride
              data.localSlotsPerSuper data.localStride super
          cases hlocalValue :
              (data.localTable.readCosted localSlot).value with
          | none =>
              simp [data, Costed.bind, Costed.pure, hvalid, hsuperValue, hlong,
                localSlot, hlocalValue]
              simp [GenericSelect.sparseDenseSelectQueryCost,
                fixedWeightSubLogDenseWindowReadCost,
                fixedWeightSubLogDenseWindowBlockCount]
          | some loc =>
              by_cases hsparse :
                  GenericSelect.relativeSplitSelectEntryIsMarked loc = true
              · have hsparseCost :
                    (data.sparseDirectory.readCosted
                      (GenericSelect.relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (idx -
                        GenericSelect.relativeSplitSelectLocalBaseOccurrence
                          super loc)).cost <= 5 := by
                  exact
                    data.sparseDirectory.readCosted_cost_le_five
                      (GenericSelect.relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (idx -
                        GenericSelect.relativeSplitSelectLocalBaseOccurrence
                          super loc)
                have hsparseCostCanonical := hsparseCost
                simp [data, localSlot] at hsparseCostCanonical
                simp [data, Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse]
                simp [GenericSelect.sparseDenseSelectQueryCost,
                  fixedWeightSubLogDenseWindowReadCost,
                  fixedWeightSubLogDenseWindowBlockCount] at *
                omega
              · have hdenseCost :=
                  subLogDenseTwoWordSelectCosted_cost_le target bits
                    (GenericSelect.relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                      super loc) idx
                have hdenseCostCanonical := hdenseCost
                simp [data] at hdenseCostCanonical
                simp [data, Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse]
                simp [GenericSelect.sparseDenseSelectQueryCost,
                  fixedWeightSubLogDenseWindowReadCost,
                  fixedWeightSubLogDenseWindowBlockCount] at *
                omega
  · simp [Costed.pure, hvalid]

theorem subLogPackedClarkSelectCosted_exact
    (bits : List Bool) (target : Bool) (idx : Nat) :
    (subLogPackedClarkSelectCosted bits target idx).erase =
      Succinct.select target bits idx := by
  let data := GenericSelect.sparseExceptionSelectData bits target
  let q := idx
  unfold subLogPackedClarkSelectCosted
  dsimp only
  by_cases hvalid : idx < GenericSelect.occurrenceCount bits target
  · have hvalidQ : q < GenericSelect.occurrenceCount bits target := by
      simpa [q] using hvalid
    cases hsuper :
        data.superEntries[
          GenericSelect.selectSuperSlot
            idx data.superStride]? with
    | none =>
        have hsuperQ :
            data.superEntries[
                GenericSelect.selectSuperSlot q data.superStride]? =
              none := by
          simpa [q] using hsuper
        simp [data, hvalid, hsuper, Costed.erase_bind,
          GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readCosted_erase]
        exact (data.super_missing_exact q hsuperQ).symm
    | some super =>
        have hsuperQ :
            data.superEntries[
                GenericSelect.selectSuperSlot q data.superStride]? =
              some super := by
          simpa [q] using hsuper
        by_cases hlong :
            GenericSelect.relativeSplitSelectEntryIsMarked super = true
        · have hrank :=
            data.longFlagRankData.rankCosted_exact true
              (GenericSelect.selectSuperSlot
                idx data.superStride)
          simp [data, hvalid, hsuper, hlong,
            GenericSelect.relativeOffsetReadCosted,
            Costed.erase_bind, Costed.erase_map,
            GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readCosted_erase,
            SuccinctSpace.FixedWidthNatTable.readCosted_erase, hrank]
          simpa [q] using
            data.long_explicit_exact q super hsuperQ hvalidQ hlong
        · let localSlot :=
            GenericSelect.relativeSplitSelectLocalSlot
              idx data.superStride
              data.localSlotsPerSuper data.localStride super
          have hlongFalse :
              GenericSelect.relativeSplitSelectEntryIsMarked super = false := by
            cases hmark :
                GenericSelect.relativeSplitSelectEntryIsMarked super
            · rfl
            · exact False.elim (hlong hmark)
          cases hlocal :
              data.localEntries[localSlot]? with
          | none =>
              simp [data, hvalid, hsuper, hlong, localSlot, hlocal,
                Costed.erase_bind,
                GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readCosted_erase]
              have hlocal' :
                data.localEntries[
                    GenericSelect.relativeSplitSelectLocalSlot
                      q data.superStride data.localSlotsPerSuper
                      data.localStride super]? = none := by
                simpa [q, localSlot] using hlocal
              exact
                (data.local_missing_exact q super hsuperQ hvalidQ
                  hlongFalse hlocal').symm
          | some loc =>
              by_cases hsparse :
                  GenericSelect.relativeSplitSelectEntryIsMarked loc = true
              · simp [data, hvalid, hsuper, hlong, localSlot, hlocal,
                  Costed.erase_bind,
                  GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readCosted_erase]
                have hlocal' :
                    data.localEntries[
                        GenericSelect.relativeSplitSelectLocalSlot
                          q data.superStride data.localSlotsPerSuper
                          data.localStride super]? = some loc := by
                  simpa [q, localSlot] using hlocal
                simp [hsparse]
                simpa [q] using
                  data.sparse_compact_exact q super loc hsuperQ hvalidQ
                    hlongFalse hlocal' hsparse
              · have hsparseFalse :
                    GenericSelect.relativeSplitSelectEntryIsMarked loc =
                      false := by
                  cases hmark :
                      GenericSelect.relativeSplitSelectEntryIsMarked loc
                  · rfl
                  · exact False.elim (hsparse hmark)
                simp [data, hvalid, hsuper, hlong, localSlot, hlocal,
                  Costed.erase_bind,
                  GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readCosted_erase]
                have hlocal' :
                    data.localEntries[
                        GenericSelect.relativeSplitSelectLocalSlot
                          q data.superStride data.localSlotsPerSuper
                          data.localStride super]? = some loc := by
                  simpa [q, localSlot] using hlocal
                simp [hsparse]
                have hgeneric :
                    (GenericSelect.denseTwoWordSelectCosted target
                      (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits
                        (GenericSelect.wordBits_pos bits.length))
                      (GenericSelect.relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                        super loc) q).erase =
                      Succinct.select target bits q := by
                  have h := data.dense_exact q super loc hsuperQ hvalidQ
                    hlongFalse hlocal' hsparseFalse
                  simpa [data, GenericSelect.sparseExceptionSelectData]
                    using h
                exact
                  subLogDenseTwoWordSelectCosted_exact_of_canonical_dense_exact
                    target bits
                    (GenericSelect.relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                      super loc) q hvalidQ hgeneric
  · simp [hvalid, Costed.pure]
    exact
      (GenericSelect.select_none_of_rankPrefix_length_le
        (target := target) (bits := bits) (occurrence := idx)
        (by
          simpa [GenericSelect.occurrenceCount] using
            Nat.le_of_not_gt hvalid)).symm

def fixedWeightSubLogPackedClarkSelectRouteFieldsCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    Costed (Option FixedWeightSubLogClarkSelectRouteFields) :=
  Costed.map
    (fun pos? =>
      pos?.map
        (fixedWeightSubLogSelectRouteFieldsOfPosition
          bits target occurrence))
    (subLogPackedClarkSelectCosted bits target occurrence)

theorem fixedWeightSubLogPackedClarkSelectRouteFieldsCosted_cost_le
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (fixedWeightSubLogPackedClarkSelectRouteFieldsCosted
      bits target occurrence).cost <=
      subLogPackedClarkSelectQueryCost := by
  simpa [fixedWeightSubLogPackedClarkSelectRouteFieldsCosted] using
    subLogPackedClarkSelectCosted_cost_le bits target occurrence

theorem fixedWeightSubLogPackedClarkSelectRouteFieldsCosted_erase
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (fixedWeightSubLogPackedClarkSelectRouteFieldsCosted
      bits target occurrence).erase =
      (Succinct.select target bits occurrence).map
        (fixedWeightSubLogSelectRouteFieldsOfPosition
          bits target occurrence) := by
  have h := subLogPackedClarkSelectCosted_exact bits target occurrence
  simpa [fixedWeightSubLogPackedClarkSelectRouteFieldsCosted,
    Costed.erase_map] using congrArg
      (fun pos? =>
        pos?.map
          (fixedWeightSubLogSelectRouteFieldsOfPosition
            bits target occurrence)) h

theorem fixedWeightSubLogPackedClarkSelectRouteFieldsCosted_select_exact
    {bits : List Bool} {target : Bool} {occurrence : Nat}
    {fields : FixedWeightSubLogClarkSelectRouteFields}
    (hfields :
      (fixedWeightSubLogPackedClarkSelectRouteFieldsCosted
        bits target occurrence).erase = some fields) :
    exists block,
      (fixedWeightSubLogChunkBlocksWithSentinel bits)[
          fields.blockIndex]? = some block /\
        (Succinct.select target block fields.localOccurrence).map
            (fun offset => fields.blockStart + offset) =
          Succinct.select target bits occurrence := by
  have herase :=
    fixedWeightSubLogPackedClarkSelectRouteFieldsCosted_erase
      bits target occurrence
  rw [hfields] at herase
  cases hselect : Succinct.select target bits occurrence with
  | none =>
      simp [hselect] at herase
  | some idx =>
      have hfields_eq :
          fields =
            fixedWeightSubLogSelectRouteFieldsOfPosition
              bits target occurrence idx := by
        simpa [hselect] using herase
      subst fields
      simpa [hselect] using
        fixedWeightSubLogSelectRouteFieldsOfPosition_select_exact hselect

def subLogSelectFromPackedClarkRouteCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind
    (fixedWeightSubLogPackedClarkSelectRouteFieldsCosted
      bits target occurrence)
    fun fields? =>
      match fields? with
      | none => Costed.pure none
      | some fields => subLogSelectWithFieldsCosted bits target fields

theorem subLogSelectFromPackedClarkRouteCosted_cost_le
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromPackedClarkRouteCosted
      bits target occurrence).cost <=
      subLogPackedClarkSelectQueryCost + 4 := by
  have hroute :=
    fixedWeightSubLogPackedClarkSelectRouteFieldsCosted_cost_le
      bits target occurrence
  unfold subLogSelectFromPackedClarkRouteCosted
  rw [Costed.cost_bind]
  cases hfields :
      (fixedWeightSubLogPackedClarkSelectRouteFieldsCosted
        bits target occurrence).erase with
  | none =>
      simp [Costed.erase] at hfields
      simp [hfields]
      omega
  | some fields =>
      simp [Costed.erase] at hfields
      simp [hfields, subLogSelectWithFieldsCosted_cost bits target fields]
      omega

theorem subLogSelectFromPackedClarkRouteCosted_erase
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromPackedClarkRouteCosted
      bits target occurrence).erase =
      Succinct.select target bits occurrence := by
  have herase :=
    fixedWeightSubLogPackedClarkSelectRouteFieldsCosted_erase
      bits target occurrence
  unfold subLogSelectFromPackedClarkRouteCosted
  simp only [Costed.erase_bind]
  cases hfields :
      (fixedWeightSubLogPackedClarkSelectRouteFieldsCosted
        bits target occurrence).erase with
  | none =>
      rw [hfields] at herase
      cases hselect : Succinct.select target bits occurrence with
      | none =>
          simp
      | some idx =>
          simp [hselect] at herase
  | some fields =>
      simpa using subLogSelectWithFieldsCosted_erase_of_exact
        (fixedWeightSubLogPackedClarkSelectRouteFieldsCosted_select_exact
          hfields)

abbrev fixedWeightSubLogPackedClarkSelectRoutePayload :=
  fixedWeightSubLogClarkSelectRoutePayload

abbrev fixedWeightSubLogPackedClarkSelectRouteOverhead :=
  fixedWeightSubLogClarkSelectRouteOverhead

def fixedWeightSubLogConcretePackedClarkPayload
    (bits : List Bool) : List Bool :=
  fixedWeightSubLogConcreteRankPayload bits ++
    fixedWeightSubLogPackedClarkSelectRoutePayload bits

def fixedWeightSubLogConcretePackedClarkOverhead : Nat -> Nat := fun n =>
  fixedWeightSubLogConcreteRankOverhead n +
    fixedWeightSubLogPackedClarkSelectRouteOverhead n

def fixedWeightSubLogConcretePackedClarkQueryCost : Nat :=
  Nat.max 6 (subLogPackedClarkSelectQueryCost + 4)

theorem fixedWeightSubLogConcretePackedClarkPayload_length_le
    (bits : List Bool) :
    (fixedWeightSubLogConcretePackedClarkPayload bits).length <=
      fixedWeightPayloadBudget bits +
        fixedWeightSubLogConcretePackedClarkOverhead bits.length := by
  have hrank := fixedWeightSubLogConcreteRankPayload_length_le bits
  have hselect :
      (fixedWeightSubLogPackedClarkSelectRoutePayload bits).length <=
        fixedWeightSubLogPackedClarkSelectRouteOverhead bits.length := by
    simpa [fixedWeightSubLogPackedClarkSelectRoutePayload,
      fixedWeightSubLogPackedClarkSelectRouteOverhead] using
      fixedWeightSubLogClarkSelectRoutePayload_length_le bits
  simp [fixedWeightSubLogConcretePackedClarkPayload,
    fixedWeightSubLogConcretePackedClarkOverhead, List.length_append]
  omega

theorem fixedWeightSubLogConcretePackedClarkOverhead_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogConcretePackedClarkOverhead := by
  simpa [fixedWeightSubLogConcretePackedClarkOverhead] using
    fixedWeightSubLogConcreteRankOverhead_littleO.add
      fixedWeightSubLogClarkSelectRouteOverhead_littleO

theorem fixedWeightSubLogConcretePackedClarkProfile
    (bits : List Bool) :
    (fixedWeightSubLogConcretePackedClarkPayload bits).length <=
        fixedWeightPayloadBudget bits +
          fixedWeightSubLogConcretePackedClarkOverhead bits.length /\
      SuccinctSpace.LittleOLinear
        fixedWeightSubLogConcretePackedClarkOverhead /\
      (forall i,
        (subLogAccessCosted bits i).cost <=
            fixedWeightSubLogConcretePackedClarkQueryCost /\
          (subLogAccessCosted bits i).erase = bits[i]?) /\
      (forall target pos,
        (subLogRankCosted bits target pos).cost <=
            fixedWeightSubLogConcretePackedClarkQueryCost /\
          (subLogRankCosted bits target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      forall target occurrence,
        (subLogSelectFromPackedClarkRouteCosted
          bits target occurrence).cost <=
            fixedWeightSubLogConcretePackedClarkQueryCost /\
          (subLogSelectFromPackedClarkRouteCosted
            bits target occurrence).erase =
            Succinct.select target bits occurrence := by
  refine
    ⟨fixedWeightSubLogConcretePackedClarkPayload_length_le bits,
      fixedWeightSubLogConcretePackedClarkOverhead_littleO,
      ?_, ?_, ?_⟩
  · intro i
    exact
      ⟨by
        rw [subLogAccessCosted_cost]
        exact Nat.le_trans (by omega : 4 <= 6)
          (Nat.le_max_left 6 (subLogPackedClarkSelectQueryCost + 4)),
        subLogAccessCosted_erase bits i⟩
  · intro target pos
    exact
      ⟨by
        rw [subLogRankCosted_cost]
        exact Nat.le_max_left 6 (subLogPackedClarkSelectQueryCost + 4),
        subLogRankCosted_erase bits target pos⟩
  · intro target occurrence
    exact
      ⟨Nat.le_trans
        (subLogSelectFromPackedClarkRouteCosted_cost_le
          bits target occurrence)
        (Nat.le_max_right 6 (subLogPackedClarkSelectQueryCost + 4)),
        subLogSelectFromPackedClarkRouteCosted_erase
          bits target occurrence⟩

end RankSelectSpec

end RMQ
