import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedWordChunks
import RMQ.Core.GenericSelect.Source

/-!
# Charged chunked rank/select leaves (B3 Costed layer)

Chunked twins of the accepted route's word-primitive leaves, mirroring each
accepted evaluator's exact branch structure with only the in-word
`wordRank`/`wordSelect` sub-computations replaced by the charged chunk
folds of `ChargedWordChunks.lean`:

* `TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankCosted` — the
  two-level rank seed (3 accepted sample/word reads + at most 8 chunk
  reads, so `<= 11`);
* `GenericSelect.bpChunkedDenseTwoWordSelectCosted` — the dense two-word
  select leaf (`<= 27`);
* `SparseExceptionDirectory.bpChunkedReadCosted` — the sparse-exception
  directory leaf (`<= 12`);
* `SparseExceptionSelectData.bpChunkedSelectCosted` — the whole accepted
  select-close execution (`<= 35`).

Every twin carries an exact-value equivalence with its accepted evaluator,
universally quantified over the accepted consumer's own invocations, under
word-size hypotheses (`wordSize <= 8 * c`) that each accepted call site
discharges from its structure's own `wordSize_le_machine` field plus
`machineWordBits_le_8_mul_bpFringeChunkBits`.
-/

namespace RMQ

/-! ## Word length of a successful bounded-store read -/

namespace SuccinctSpace

namespace BoundedPayloadWordStore

theorem read_word_length_le
    {payload : List Bool} {wordSize : Nat}
    (bitWords : BoundedPayloadWordStore payload wordSize)
    {i : Nat} {word : List Bool}
    (hread : (bitWords.store.readWordCosted i).value = some word) :
    word.length <= wordSize := by
  apply bitWords.word_length_le
  have hget : bitWords.store.words[i]? = some word := hread
  exact List.mem_of_getElem? (by simpa [Array.getElem?_toList] using hget)

end BoundedPayloadWordStore

end SuccinctSpace

/-! ## Chunked two-level rank seed -/

namespace SuccinctRank

namespace TwoLevelPayloadLiveStoredWordRankData

/--
Charged chunked twin of `rankCosted`: the same three accepted sample/word
reads, with the trailing `wordRank` primitive replaced by the charged
chunked in-word rank fold at chunk width `c`.
-/
def bpChunkedRankCosted
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (c : Nat) (target : Bool) (pos : Nat) : RMQ.Costed Nat :=
  RMQ.Costed.bind
    (data.superTables.sampleCosted target (data.superIndex pos))
    fun super? =>
      RMQ.Costed.bind
        (data.blockTables.sampleCosted target (data.wordIndex pos))
        fun delta? =>
          RMQ.Costed.bind
            (data.bitWords.store.readWordCosted (data.wordIndex pos))
            fun word? =>
              match super?, delta?, word? with
              | some super, some delta, some word =>
                  RMQ.Costed.map
                    (fun localRank => super + delta + localRank)
                    (SuccinctClose.bpChunkedWordRankCosted
                      (SuccinctClose.bpFringeChunkTable c) c target word
                      (data.wordOffset pos))
              | _, _, _ => RMQ.Costed.pure 0

/-- Literal all-size read bound: 3 accepted reads + at most 8 chunk reads. -/
theorem bpChunkedRankCosted_cost_le
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (c : Nat) (target : Bool) (pos : Nat) :
    (data.bpChunkedRankCosted c target pos).cost <= 11 := by
  unfold bpChunkedRankCosted
  have hfold :=
    SuccinctClose.bpChunkedWordRankCosted_cost_le
      (SuccinctClose.bpFringeChunkTable c) c target
  cases hsuper :
      (data.superTables.sampleCosted target (data.superIndex pos)).value with
  | none =>
      cases hblock :
          (data.blockTables.sampleCosted target
            (data.wordIndex pos)).value <;>
        cases hword :
          (data.bitWords.store.readWordCosted
            (data.wordIndex pos)).value <;>
        simp [RMQ.Costed.bind, RMQ.Costed.pure, hsuper, hblock, hword] <;>
        all_goals omega
  | some super =>
      cases hblock :
          (data.blockTables.sampleCosted target
            (data.wordIndex pos)).value with
      | none =>
          cases hword :
              (data.bitWords.store.readWordCosted
                (data.wordIndex pos)).value <;>
            simp [RMQ.Costed.bind, RMQ.Costed.pure, hsuper, hblock,
              hword] <;>
            all_goals omega
      | some delta =>
          cases hword :
              (data.bitWords.store.readWordCosted
                (data.wordIndex pos)).value with
          | none =>
              simp [RMQ.Costed.bind, RMQ.Costed.pure, hsuper, hblock,
                hword]
          | some word =>
              have h := hfold word (data.wordOffset pos)
              simp [RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
                hsuper, hblock, hword]
              all_goals omega

/--
Exact-value substitution at every invocation: the chunked rank seed
returns exactly the accepted `rankCosted` value, for every target and
position, under the structure's own word-size bound.
-/
theorem bpChunkedRankCosted_value_eq
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    {c : Nat} (hc : 0 < c) (hword8 : data.wordSize <= 8 * c)
    (target : Bool) (pos : Nat) :
    (data.bpChunkedRankCosted c target pos).value =
      (data.rankCosted target pos).value := by
  unfold bpChunkedRankCosted rankCosted
  cases hsuper :
      (data.superTables.sampleCosted target (data.superIndex pos)).value with
  | none =>
      cases hblock :
          (data.blockTables.sampleCosted target
            (data.wordIndex pos)).value <;>
        cases hword :
          (data.bitWords.store.readWordCosted
            (data.wordIndex pos)).value <;>
        simp [RMQ.Costed.bind, RMQ.Costed.pure,
          hsuper, hblock, hword]
  | some super =>
      cases hblock :
          (data.blockTables.sampleCosted target
            (data.wordIndex pos)).value with
      | none =>
          cases hword :
              (data.bitWords.store.readWordCosted
                (data.wordIndex pos)).value <;>
            simp [RMQ.Costed.bind, RMQ.Costed.pure,
              hsuper, hblock, hword]
      | some delta =>
          cases hword :
              (data.bitWords.store.readWordCosted
                (data.wordIndex pos)).value with
          | none =>
              simp [RMQ.Costed.bind, RMQ.Costed.pure,
                hsuper, hblock, hword]
          | some word =>
              have hlen : word.length <= 8 * c := by
                have hle := data.bitWords.read_word_length_le hword
                omega
              have hval :=
                SuccinctClose.bpChunkedWordRankCosted_value c hc target
                  word (data.wordOffset pos) hlen
              simp [RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
                hsuper, hblock, hword, hval]

/-- Chunked rank-seed exactness, inherited from the accepted seed. -/
theorem bpChunkedRankCosted_exact
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    {c : Nat} (hc : 0 < c) (hword8 : data.wordSize <= 8 * c)
    (target : Bool) (pos : Nat) :
    (data.bpChunkedRankCosted c target pos).erase =
      RMQ.Succinct.rankPrefix target bits pos := by
  show (data.bpChunkedRankCosted c target pos).value = _
  rw [data.bpChunkedRankCosted_value_eq hc hword8 target pos]
  exact data.rankCosted_exact target pos

end TwoLevelPayloadLiveStoredWordRankData

end SuccinctRank

namespace GenericSelect

open SuccinctSpace SuccinctRank

/-! ## Chunked dense two-word select leaf -/

/--
Charged chunked twin of `denseTwoWordSelectCosted`: identical branch
structure, with the two in-word ranks and the in-word select replaced by
the charged chunk folds.
-/
def bpChunkedDenseTwoWordSelectCosted
    (c : Nat) (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) : Costed (Option Nat) :=
  let firstWordIndex := basePosition / wordSize
  let firstWordStart := firstWordIndex * wordSize
  let firstOffset := basePosition - firstWordStart
  let localOccurrence := q - baseOccurrence
  Costed.bind (bitWords.store.readWordCosted firstWordIndex) fun firstWord? =>
    match firstWord? with
    | none => Costed.pure none
    | some firstWord =>
        Costed.bind
          (SuccinctClose.bpChunkedWordRankCosted
            (SuccinctClose.bpFringeChunkTable c) c target firstWord
            firstOffset)
          fun beforeFirst =>
            Costed.bind
              (SuccinctClose.bpChunkedWordRankCosted
                (SuccinctClose.bpFringeChunkTable c) c target firstWord
                firstWord.length)
              fun uptoFirst =>
                let firstCount := uptoFirst - beforeFirst
                if localOccurrence < firstCount then
                  Costed.map
                    (fun local? =>
                      local?.map fun offset => firstWordStart + offset)
                    (SuccinctClose.bpChunkedWordSelectCosted
                      (SuccinctClose.bpFringeChunkTable c)
                      (SuccinctClose.bpChunkSelectTable c target) c target
                      firstWord (beforeFirst + localOccurrence))
                else
                  Costed.bind
                    (bitWords.store.readWordCosted (firstWordIndex + 1))
                    fun secondWord? =>
                      match secondWord? with
                      | none => Costed.pure none
                      | some secondWord =>
                          Costed.map
                            (fun local? =>
                              local?.map fun offset =>
                                (firstWordIndex + 1) * wordSize + offset)
                            (SuccinctClose.bpChunkedWordSelectCosted
                              (SuccinctClose.bpFringeChunkTable c)
                              (SuccinctClose.bpChunkSelectTable c target)
                              c target secondWord
                              (localOccurrence - firstCount))

/-- Literal all-size read bound for the chunked dense leaf. -/
theorem bpChunkedDenseTwoWordSelectCosted_cost_le
    (c : Nat) (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    (bpChunkedDenseTwoWordSelectCosted c target bitWords basePosition
        baseOccurrence q).cost <= 27 := by
  unfold bpChunkedDenseTwoWordSelectCosted
  have hrank :=
    SuccinctClose.bpChunkedWordRankCosted_cost_le
      (SuccinctClose.bpFringeChunkTable c) c target
  have hsel :=
    SuccinctClose.bpChunkedWordSelectCosted_cost_le
      (SuccinctClose.bpFringeChunkTable c)
      (SuccinctClose.bpChunkSelectTable c target) c target
  cases hfirst :
      (bitWords.store.readWordCosted (basePosition / wordSize)).value with
  | none =>
      simp [Costed.bind, Costed.pure, hfirst]
  | some firstWord =>
      by_cases hchoose :
          q - baseOccurrence <
            (SuccinctClose.bpChunkedWordRankCosted
                (SuccinctClose.bpFringeChunkTable c) c target firstWord
                firstWord.length).value -
              (SuccinctClose.bpChunkedWordRankCosted
                (SuccinctClose.bpFringeChunkTable c) c target firstWord
                (basePosition - basePosition / wordSize * wordSize)).value
      · have h1 := hrank firstWord
          (basePosition - basePosition / wordSize * wordSize)
        have h2 := hrank firstWord firstWord.length
        have h3 := hsel firstWord
          ((SuccinctClose.bpChunkedWordRankCosted
              (SuccinctClose.bpFringeChunkTable c) c target firstWord
              (basePosition - basePosition / wordSize * wordSize)).value +
            (q - baseOccurrence))
        simp [Costed.bind, Costed.map, Costed.pure, hfirst, hchoose]
        omega
      · cases hsecond :
            (bitWords.store.readWordCosted
              (basePosition / wordSize + 1)).value with
        | none =>
            have h1 := hrank firstWord
              (basePosition - basePosition / wordSize * wordSize)
            have h2 := hrank firstWord firstWord.length
            simp [Costed.bind, Costed.pure, hfirst, hchoose, hsecond]
            omega
        | some secondWord =>
            have h1 := hrank firstWord
              (basePosition - basePosition / wordSize * wordSize)
            have h2 := hrank firstWord firstWord.length
            have h3 := hsel secondWord
              (q - baseOccurrence -
                ((SuccinctClose.bpChunkedWordRankCosted
                    (SuccinctClose.bpFringeChunkTable c) c target
                    firstWord firstWord.length).value -
                  (SuccinctClose.bpChunkedWordRankCosted
                    (SuccinctClose.bpFringeChunkTable c) c target
                    firstWord
                    (basePosition -
                      basePosition / wordSize * wordSize)).value))
            simp [Costed.bind, Costed.map, Costed.pure, hfirst, hchoose,
              hsecond]
            omega

/--
Exact-value substitution at every invocation of the accepted dense leaf.
-/
theorem bpChunkedDenseTwoWordSelectCosted_value_eq
    (c : Nat) (hc : 0 < c) (target : Bool)
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (hws : wordSize <= 8 * c)
    (basePosition baseOccurrence q : Nat) :
    (bpChunkedDenseTwoWordSelectCosted c target bitWords basePosition
        baseOccurrence q).value =
      (denseTwoWordSelectCosted target bitWords basePosition
        baseOccurrence q).value := by
  unfold bpChunkedDenseTwoWordSelectCosted denseTwoWordSelectCosted
  cases hfirst :
      (bitWords.store.readWordCosted (basePosition / wordSize)).value with
  | none =>
      simp [Costed.bind, Costed.pure, hfirst]
  | some firstWord =>
      have hlen1 : firstWord.length <= 8 * c := by
        have hle := bitWords.read_word_length_le hfirst
        omega
      have hbf :=
        SuccinctClose.bpChunkedWordRankCosted_value c hc target firstWord
          (basePosition - basePosition / wordSize * wordSize) hlen1
      have huf :=
        SuccinctClose.bpChunkedWordRankCosted_value c hc target firstWord
          firstWord.length hlen1
      by_cases hchoose :
          q - baseOccurrence <
            RMQ.RAM.boolRankPrefix target firstWord firstWord.length -
              RMQ.RAM.boolRankPrefix target firstWord
                (basePosition - basePosition / wordSize * wordSize)
      · have hsel :=
          SuccinctClose.bpChunkedWordSelectCosted_value c hc target
            firstWord
            (RMQ.RAM.boolRankPrefix target firstWord
                (basePosition - basePosition / wordSize * wordSize) +
              (q - baseOccurrence)) hlen1
        simp [Costed.bind, Costed.map, Costed.pure, hfirst, hbf, huf,
          hchoose, hsel]
      · cases hsecond :
            (bitWords.store.readWordCosted
              (basePosition / wordSize + 1)).value with
        | none =>
            simp [Costed.bind, Costed.pure, hfirst, hbf, huf, hchoose,
              hsecond]
        | some secondWord =>
            have hlen2 : secondWord.length <= 8 * c := by
              have hle := bitWords.read_word_length_le hsecond
              omega
            have hsel :=
              SuccinctClose.bpChunkedWordSelectCosted_value c hc target
                secondWord
                (q - baseOccurrence -
                  (RMQ.RAM.boolRankPrefix target firstWord
                      firstWord.length -
                    RMQ.RAM.boolRankPrefix target firstWord
                      (basePosition -
                        basePosition / wordSize * wordSize))) hlen2
            simp [Costed.bind, Costed.map, Costed.pure, hfirst, hbf, huf,
              hchoose, hsecond, hsel]

/-! ## Chunked sparse-exception directory leaf -/

namespace SparseExceptionDirectory

/--
Charged chunked twin of `SparseExceptionDirectory.readCosted`: the flag
rank is replaced by the chunked rank seed; the relative-table read is
unchanged.
-/
def bpChunkedReadCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (c : Nat) (base localSlot localOccurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.rankData.bpChunkedRankCosted c true localSlot)
    fun exceptionRank =>
      relativeOffsetReadCosted directory.relativeTable base
        (relativeSplitSelectSparseCompactSlot
          exceptionRank localOccurrence directory.localStride)

theorem bpChunkedReadCosted_cost_le
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (c : Nat) (base localSlot localOccurrence : Nat) :
    (directory.bpChunkedReadCosted c base localSlot
        localOccurrence).cost <= 12 := by
  unfold bpChunkedReadCosted relativeOffsetReadCosted
  have hrank :=
    directory.rankData.bpChunkedRankCosted_cost_le c true localSlot
  have hrelative :=
    directory.relativeTable.readCosted_cost_le_one
      (relativeSplitSelectSparseCompactSlot
        (directory.rankData.bpChunkedRankCosted c true localSlot).value
        localOccurrence directory.localStride)
  simp [Costed.bind] at *
  omega

theorem bpChunkedReadCosted_value_eq
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    {c : Nat} (hc : 0 < c)
    (hrk : directory.rankData.wordSize <= 8 * c)
    (base localSlot localOccurrence : Nat) :
    (directory.bpChunkedReadCosted c base localSlot
        localOccurrence).value =
      (directory.readCosted base localSlot localOccurrence).value := by
  unfold bpChunkedReadCosted readCosted
  have hr :=
    directory.rankData.bpChunkedRankCosted_value_eq hc hrk true localSlot
  simp [Costed.bind, hr]

end SparseExceptionDirectory

/-! ## Chunked accepted select-close execution -/

namespace SparseExceptionSelectData

/--
Charged chunked twin of `SparseExceptionSelectData.selectCosted`: identical
routing (validity branch, super entry, long/local/sparse/dense dispatch),
with the flag ranks and the dense leaf replaced by their chunked twins.
-/
def bpChunkedSelectCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (c : Nat) (idx : Nat) : Costed (Option Nat) :=
  let q := data.queryOccurrence idx
  if idx < occurrenceCount bits target then
    Costed.bind
      (data.superTable.readCosted
        (selectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => Costed.pure none
      | some super =>
          if relativeSplitSelectEntryIsMarked super then
            Costed.bind
              (data.longFlagRankData.bpChunkedRankCosted c true
                (selectSuperSlot q data.superStride))
              fun exceptionRank =>
                relativeOffsetReadCosted data.longSuperRelativeTable
                  (relativeSplitSelectEntryBasePosition
                    data.wordSize super)
                  (relativeSplitSelectLongCompactSlot
                    exceptionRank (q - super.baseOccurrence)
                    data.superStride)
          else
            let localSlot :=
              relativeSplitSelectLocalSlot q data.superStride
                data.localSlotsPerSuper data.localStride super
            Costed.bind (data.localTable.readCosted localSlot) fun loc? =>
              match loc? with
              | none => Costed.pure none
              | some loc =>
                  if relativeSplitSelectEntryIsMarked loc then
                    data.sparseDirectory.bpChunkedReadCosted c
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        relativeSplitSelectLocalBaseOccurrence
                          super loc)
                  else
                    bpChunkedDenseTwoWordSelectCosted c target
                      data.bitWords
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitSelectLocalBaseOccurrence
                        super loc) q
  else
    Costed.pure none

/-- Literal all-size read bound for the chunked select-close execution. -/
theorem bpChunkedSelectCosted_cost_le
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (c : Nat) (idx : Nat) :
    (data.bpChunkedSelectCosted c idx).cost <= 35 := by
  unfold bpChunkedSelectCosted queryOccurrence
  by_cases hvalid : idx < occurrenceCount bits target
  case pos =>
    cases hsuperValue :
        (data.superTable.readCosted
          (selectSuperSlot idx data.superStride)).value with
    | none =>
        simp [Costed.bind, Costed.pure, hvalid, hsuperValue] <;> omega
    | some super =>
        by_cases hlong : relativeSplitSelectEntryIsMarked super = true
        case pos =>
          have hrankCost :=
            data.longFlagRankData.bpChunkedRankCosted_cost_le c true
              (selectSuperSlot idx data.superStride)
          have hlongCost :
              (data.longSuperRelativeTable.readCosted
                (relativeSplitSelectLongCompactSlot
                  (data.longFlagRankData.bpChunkedRankCosted c true
                    (selectSuperSlot idx data.superStride)).value
                  (idx - super.baseOccurrence)
                  data.superStride)).cost <= 1 := by
            exact data.longSuperRelativeTable.readCosted_cost_le_one _
          simp [relativeOffsetReadCosted, Costed.bind, Costed.map,
            Costed.pure, hvalid, hsuperValue, hlong] <;> omega
        case neg =>
          let localSlot :=
            relativeSplitSelectLocalSlot
              idx data.superStride
              data.localSlotsPerSuper data.localStride super
          cases hlocalValue :
              (data.localTable.readCosted localSlot).value with
          | none =>
              simp [Costed.bind, Costed.pure, hvalid, hsuperValue, hlong,
                localSlot, hlocalValue] <;> omega
          | some loc =>
              by_cases hsparse :
                  relativeSplitSelectEntryIsMarked loc = true
              case pos =>
                have hsparseCost :
                    (data.sparseDirectory.bpChunkedReadCosted c
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitSelectLocalSlot
                        idx data.superStride
                        data.localSlotsPerSuper data.localStride super)
                      (idx -
                        relativeSplitSelectLocalBaseOccurrence
                          super loc)).cost <= 12 := by
                  simpa [localSlot] using
                    data.sparseDirectory.bpChunkedReadCosted_cost_le c
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (idx -
                        relativeSplitSelectLocalBaseOccurrence super loc)
                simp [Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse] <;> omega
              case neg =>
                have hdenseCost :=
                  bpChunkedDenseTwoWordSelectCosted_cost_le c target
                    data.bitWords
                    (relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitSelectLocalBaseOccurrence super loc)
                    idx
                simp [Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse] <;> omega
  case neg =>
    simp [Costed.pure, hvalid]

/--
Exact-value substitution at every invocation of the accepted select-close
execution, under the structure's own word-size bounds.
-/
theorem bpChunkedSelectCosted_value_eq
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    {c : Nat} (hc : 0 < c)
    (hbw : data.wordSize <= 8 * c)
    (hlf : data.longFlagRankData.wordSize <= 8 * c)
    (hsd : data.sparseDirectory.rankData.wordSize <= 8 * c)
    (idx : Nat) :
    (data.bpChunkedSelectCosted c idx).value =
      (data.selectCosted idx).value := by
  unfold bpChunkedSelectCosted selectCosted queryOccurrence
  by_cases hvalid : idx < occurrenceCount bits target
  case pos =>
    cases hsuperValue :
        (data.superTable.readCosted
          (selectSuperSlot idx data.superStride)).value with
    | none =>
        simp [Costed.bind, Costed.pure, hvalid, hsuperValue]
    | some super =>
        by_cases hlong : relativeSplitSelectEntryIsMarked super = true
        case pos =>
          have hr :=
            data.longFlagRankData.bpChunkedRankCosted_value_eq hc hlf
              true (selectSuperSlot idx data.superStride)
          simp [relativeOffsetReadCosted, Costed.bind, Costed.map,
            Costed.pure, hvalid, hsuperValue, hlong, hr]
        case neg =>
          let localSlot :=
            relativeSplitSelectLocalSlot
              idx data.superStride
              data.localSlotsPerSuper data.localStride super
          cases hlocalValue :
              (data.localTable.readCosted localSlot).value with
          | none =>
              simp [Costed.bind, Costed.pure, hvalid, hsuperValue, hlong,
                localSlot, hlocalValue]
          | some loc =>
              by_cases hsparse :
                  relativeSplitSelectEntryIsMarked loc = true
              case pos =>
                have hs :=
                  data.sparseDirectory.bpChunkedReadCosted_value_eq hc
                    hsd
                    (relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitSelectLocalSlot
                      idx data.superStride
                      data.localSlotsPerSuper data.localStride super)
                    (idx -
                      relativeSplitSelectLocalBaseOccurrence super loc)
                simp [Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse, hs]
              case neg =>
                have hd :=
                  bpChunkedDenseTwoWordSelectCosted_value_eq c hc target
                    data.bitWords hbw
                    (relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitSelectLocalBaseOccurrence super loc)
                    idx
                simp [Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse, hd]
  case neg =>
    simp [Costed.pure, hvalid]

/-- Chunked select-close exactness, inherited from the accepted execution. -/
theorem bpChunkedSelectCosted_exact
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    {c : Nat} (hc : 0 < c)
    (hbw : data.wordSize <= 8 * c)
    (hlf : data.longFlagRankData.wordSize <= 8 * c)
    (hsd : data.sparseDirectory.rankData.wordSize <= 8 * c)
    (idx : Nat) :
    (data.bpChunkedSelectCosted c idx).erase =
      RMQ.Succinct.select target bits idx := by
  show (data.bpChunkedSelectCosted c idx).value = _
  rw [data.bpChunkedSelectCosted_value_eq hc hbw hlf hsd idx]
  exact data.selectCosted_exact idx

end SparseExceptionSelectData

end GenericSelect

end RMQ
