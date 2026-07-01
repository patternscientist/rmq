import RMQ.Core.RankSelectCompressedSubLogPackedClark
import RMQ.Core.GenericSelect.RAM

/-!
# Word-RAM replay for the sub-log compressed/FID rank/select path

The existing compressed/FID capstone already charges reads through concrete
payload stores.  This module adds an additive replay layer: every code,
length/class, rank-base, decoder, and packed-Clark local read is routed through
the current first-order `WordRAM` read bridges, then proved equal to the
existing `Costed` query.
-/

namespace RMQ

namespace SuccinctSpace

/-- Interpreted two-level read over two bounded payload-word stores. -/
def twoLevelReadInterpretedCosted2 {ps : List Bool} {ws : Nat}
    (superStore : BoundedPayloadWordStore ps ws)
    {pb : List Bool} {wb : Nat} (blockStore : BoundedPayloadWordStore pb wb)
    (superIdx blockIdx : Nat) : Costed Nat :=
  Costed.bind
      ((superStore.store.readProgram superIdx).eval
        superStore.wordRAMStore).toCosted fun base? =>
    Costed.bind
      ((blockStore.store.readProgram blockIdx).eval
        blockStore.wordRAMStore).toCosted fun rel? =>
      Costed.pure
        (bitsToNatLE (base?.getD []) + bitsToNatLE (rel?.getD []))

theorem twoLevelReadInterpretedCosted2_refines_twoLevelReadCosted2
    {ps : List Bool} {ws : Nat}
    (superStore : BoundedPayloadWordStore ps ws)
    {pb : List Bool} {wb : Nat}
    (blockStore : BoundedPayloadWordStore pb wb)
    (superIdx blockIdx : Nat) :
    twoLevelReadInterpretedCosted2 superStore blockStore superIdx blockIdx =
      twoLevelReadCosted2 superStore blockStore superIdx blockIdx := by
  unfold twoLevelReadInterpretedCosted2 twoLevelReadCosted2
  unfold BoundedPayloadWordStore.wordRAMStore
  rw [PayloadWordStore.readProgram_refines_readWordCosted
      superStore.store superIdx,
    PayloadWordStore.readProgram_refines_readWordCosted
      blockStore.store blockIdx]
  rfl

end SuccinctSpace

namespace RankSelectSpec

open GenericSelect

/-- Interpreted read from a bounded payload-word store. -/
def boundedWordReadInterpretedCosted
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (i : Nat) : Costed (Option (List Bool)) :=
  ((store.store.readProgram i).eval store.wordRAMStore).toCosted

theorem boundedWordReadInterpretedCosted_refines_readWordCosted
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (i : Nat) :
    boundedWordReadInterpretedCosted store i =
      store.store.readWordCosted i := by
  exact SuccinctSpace.PayloadWordStore.readProgram_refines_readWordCosted
    store.store i

/-- Interpreted shared-decoder read for the sub-log fixed-weight decoder. -/
def subLogDecodeReadInterpretedCosted (bits : List Bool) (slot : Nat) :
    Costed (Option (List Bool)) :=
  boundedWordReadInterpretedCosted
    (fixedWeightSubLogSharedDecoderStore bits) slot

theorem subLogDecodeReadInterpretedCosted_refines_subLogDecodeReadCosted
    (bits : List Bool) (slot : Nat) :
    subLogDecodeReadInterpretedCosted bits slot =
      subLogDecodeReadCosted bits slot := by
  unfold subLogDecodeReadInterpretedCosted subLogDecodeReadCosted
  exact boundedWordReadInterpretedCosted_refines_readWordCosted
    (fixedWeightSubLogSharedDecoderStore bits) slot

/-- Interpreted access query for the sub-log compressed/FID local decoder. -/
def subLogAccessInterpretedCosted (bits : List Bool) (i : Nat) :
    Costed (Option Bool) :=
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogCodeStore bits) (subLogChunkAccessRoute bits i).blockIndex)
      fun code? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogLenStore bits) (subLogChunkAccessRoute bits i).blockIndex)
      fun len? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogClassStore bits) (subLogChunkAccessRoute bits i).blockIndex)
      fun class? =>
  Costed.bind
      (subLogDecodeReadInterpretedCosted bits
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    Costed.pure ((decoded?.getD [])[(subLogChunkAccessRoute bits i).offset]?)

theorem subLogAccessInterpretedCosted_refines_subLogAccessCosted
    (bits : List Bool) (i : Nat) :
    subLogAccessInterpretedCosted bits i = subLogAccessCosted bits i := by
  unfold subLogAccessInterpretedCosted subLogAccessCosted
  simp [boundedWordReadInterpretedCosted_refines_readWordCosted,
    subLogDecodeReadInterpretedCosted_refines_subLogDecodeReadCosted]

theorem subLogAccessInterpretedCosted_cost
    (bits : List Bool) (i : Nat) :
    (subLogAccessInterpretedCosted bits i).cost = 4 := by
  rw [subLogAccessInterpretedCosted_refines_subLogAccessCosted,
    subLogAccessCosted_cost]

theorem subLogAccessInterpretedCosted_erase
    (bits : List Bool) (i : Nat) :
    (subLogAccessInterpretedCosted bits i).erase = bits[i]? := by
  rw [subLogAccessInterpretedCosted_refines_subLogAccessCosted]
  exact subLogAccessCosted_erase bits i

/-- Interpreted two-level rank-base read for sub-log rank. -/
def subLogRankBaseInterpretedCosted
    (bits : List Bool) (target : Bool) (blockIndex : Nat) : Costed Nat :=
  SuccinctSpace.twoLevelReadInterpretedCosted2
    (subLogRankSuperStore bits target)
    (subLogRankRelativeStore bits target)
    (blockIndex / subLogRankSuperblockSpan bits)
    blockIndex

theorem subLogRankBaseInterpretedCosted_refines_subLogRankBaseCosted
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    subLogRankBaseInterpretedCosted bits target blockIndex =
      subLogRankBaseCosted bits target blockIndex := by
  unfold subLogRankBaseInterpretedCosted subLogRankBaseCosted
  exact
    SuccinctSpace.twoLevelReadInterpretedCosted2_refines_twoLevelReadCosted2
      (subLogRankSuperStore bits target)
      (subLogRankRelativeStore bits target)
      (blockIndex / subLogRankSuperblockSpan bits)
      blockIndex

/-- Interpreted rank query for the concrete sub-log rank route. -/
def subLogRankInterpretedCosted
    (bits : List Bool) (target : Bool) (pos : Nat) : Costed Nat :=
  let blockIndex := subLogRankBlockIndex bits pos
  Costed.bind
    (subLogRankBaseInterpretedCosted bits target blockIndex) fun base =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogCodeStore bits) blockIndex) fun code? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogLenStore bits) blockIndex) fun len? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogClassStore bits) blockIndex) fun class? =>
  Costed.bind
      (subLogDecodeReadInterpretedCosted bits
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    Costed.pure
      (base +
        Succinct.rankPrefix target (decoded?.getD [])
          (subLogRankLocalLimit bits pos))

theorem subLogRankInterpretedCosted_refines_subLogRankCosted
    (bits : List Bool) (target : Bool) (pos : Nat) :
    subLogRankInterpretedCosted bits target pos =
      subLogRankCosted bits target pos := by
  unfold subLogRankInterpretedCosted subLogRankCosted
  simp [subLogRankBaseInterpretedCosted_refines_subLogRankBaseCosted,
    boundedWordReadInterpretedCosted_refines_readWordCosted,
    subLogDecodeReadInterpretedCosted_refines_subLogDecodeReadCosted]

theorem subLogRankInterpretedCosted_cost
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (subLogRankInterpretedCosted bits target pos).cost = 6 := by
  rw [subLogRankInterpretedCosted_refines_subLogRankCosted,
    subLogRankCosted_cost]

theorem subLogRankInterpretedCosted_erase
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (subLogRankInterpretedCosted bits target pos).erase =
      Succinct.rankPrefix target bits pos := by
  rw [subLogRankInterpretedCosted_refines_subLogRankCosted]
  exact subLogRankCosted_erase bits target pos

/-- Interpreted decode of one sub-log block by index. -/
def subLogDecodeBlockByIndexInterpretedCosted
    (bits : List Bool) (blockIndex : Nat) : Costed (List Bool) :=
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogCodeStore bits) blockIndex) fun code? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogLenStore bits) blockIndex) fun len? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogClassStore bits) blockIndex) fun class? =>
  Costed.bind
      (subLogDecodeReadInterpretedCosted bits
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    Costed.pure (decoded?.getD [])

theorem subLogDecodeBlockByIndexInterpretedCosted_refines
    (bits : List Bool) (blockIndex : Nat) :
    subLogDecodeBlockByIndexInterpretedCosted bits blockIndex =
      subLogDecodeBlockByIndexCosted bits blockIndex := by
  unfold subLogDecodeBlockByIndexInterpretedCosted
    subLogDecodeBlockByIndexCosted
  simp [boundedWordReadInterpretedCosted_refines_readWordCosted,
    subLogDecodeReadInterpretedCosted_refines_subLogDecodeReadCosted]

/-- Interpreted decode of a constant-size sub-log block window. -/
def subLogDecodeBlockWindowInterpretedCosted
    (bits : List Bool) (startBlock count : Nat) :
    Costed (List (List Bool)) :=
  match count with
  | 0 => Costed.pure []
  | count' + 1 =>
      Costed.bind
          (subLogDecodeBlockByIndexInterpretedCosted bits startBlock)
          fun block =>
        Costed.map
          (fun rest => block :: rest)
          (subLogDecodeBlockWindowInterpretedCosted bits
            (startBlock + 1) count')

theorem subLogDecodeBlockWindowInterpretedCosted_refines
    (bits : List Bool) (startBlock count : Nat) :
    subLogDecodeBlockWindowInterpretedCosted bits startBlock count =
      subLogDecodeBlockWindowCosted bits startBlock count := by
  induction count generalizing startBlock with
  | zero =>
      rfl
  | succ count ih =>
      simp [subLogDecodeBlockWindowInterpretedCosted,
        subLogDecodeBlockWindowCosted,
        subLogDecodeBlockByIndexInterpretedCosted_refines, ih]

/-- Interpreted reconstruction of one machine word from sub-log blocks. -/
def subLogMachineWordReadInterpretedCosted
    (bits : List Bool) (wordIndex : Nat) : Costed (List Bool) :=
  let wordSize := SuccinctRank.machineWordBits bits.length
  let start := wordIndex * wordSize
  let startBlock := start / fixedWeightSubLogChunkBlockSize bits.length
  Costed.bind
    (subLogDecodeBlockWindowInterpretedCosted bits startBlock
      fixedWeightSubLogDenseWindowBlockCount)
    fun decodedWindow =>
      Costed.pure
        (subLogMachineWordFromDecodedWindow bits wordIndex decodedWindow)

theorem subLogMachineWordReadInterpretedCosted_refines
    (bits : List Bool) (wordIndex : Nat) :
    subLogMachineWordReadInterpretedCosted bits wordIndex =
      subLogMachineWordReadCosted bits wordIndex := by
  unfold subLogMachineWordReadInterpretedCosted
    subLogMachineWordReadCosted
  simp [subLogDecodeBlockWindowInterpretedCosted_refines]

/-- Interpreted dense two-word select branch over sub-log decoded windows. -/
def subLogDenseTwoWordSelectInterpretedCosted
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat) : Costed (Option Nat) :=
  let wordSize := SuccinctRank.machineWordBits bits.length
  let firstWordIndex := basePosition / wordSize
  let firstWordStart := firstWordIndex * wordSize
  let firstOffset := basePosition - firstWordStart
  let localOccurrence := q - baseOccurrence
  Costed.bind
      (subLogMachineWordReadInterpretedCosted bits firstWordIndex)
      fun firstWord =>
    Costed.bind
      (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
        target firstWord firstOffset)
      fun beforeFirst =>
        Costed.bind
          (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
            target firstWord firstWord.length)
          fun uptoFirst =>
            let firstCount := uptoFirst - beforeFirst
            if localOccurrence < firstCount then
              Costed.map
                (fun local? =>
                  local?.map fun offset => firstWordStart + offset)
                (GenericSelect.wordSelectInterpretedCosted target firstWord
                  (beforeFirst + localOccurrence))
            else
              Costed.bind
                (subLogMachineWordReadInterpretedCosted bits
                  (firstWordIndex + 1))
                fun secondWord =>
                  Costed.map
                    (fun local? =>
                      local?.map fun offset =>
                        (firstWordIndex + 1) * wordSize + offset)
                    (GenericSelect.wordSelectInterpretedCosted target
                      secondWord (localOccurrence - firstCount))

theorem subLogDenseTwoWordSelectInterpretedCosted_refines
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat) :
    subLogDenseTwoWordSelectInterpretedCosted
        target bits basePosition baseOccurrence q =
      subLogDenseTwoWordSelectCosted
        target bits basePosition baseOccurrence q := by
  unfold subLogDenseTwoWordSelectInterpretedCosted
    subLogDenseTwoWordSelectCosted
  simp [subLogMachineWordReadInterpretedCosted_refines,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted_refines_rankBoolWordPrefix,
    GenericSelect.wordSelectInterpretedCosted_refines_selectBoolWord]

/-- Interpreted final local select from already-computed packed-Clark fields. -/
def subLogSelectWithFieldsInterpretedCosted
    (bits : List Bool) (target : Bool)
    (fields : FixedWeightSubLogClarkSelectRouteFields) :
    Costed (Option Nat) :=
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogCodeStore bits) fields.blockIndex) fun code? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogLenStore bits) fields.blockIndex) fun len? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogClassStore bits) fields.blockIndex) fun class? =>
  Costed.bind
      (subLogDecodeReadInterpretedCosted bits
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    Costed.pure
      ((Succinct.select target
          (decoded?.getD []) fields.localOccurrence).map
        (fun offset => fields.blockStart + offset))

theorem subLogSelectWithFieldsInterpretedCosted_refines
    (bits : List Bool) (target : Bool)
    (fields : FixedWeightSubLogClarkSelectRouteFields) :
    subLogSelectWithFieldsInterpretedCosted bits target fields =
      subLogSelectWithFieldsCosted bits target fields := by
  unfold subLogSelectWithFieldsInterpretedCosted
    subLogSelectWithFieldsCosted
  simp [boundedWordReadInterpretedCosted_refines_readWordCosted,
    subLogDecodeReadInterpretedCosted_refines_subLogDecodeReadCosted]

/--
Interpreted packed-Clark select source.

This mirrors `subLogPackedClarkSelectCosted`, replacing every concrete table,
rank, sparse-directory, and dense-window leaf by its interpreted counterpart.
-/
def subLogPackedClarkSelectInterpretedCosted
    (bits : List Bool) (target : Bool) (idx : Nat) :
    Costed (Option Nat) :=
  let data := GenericSelect.sparseExceptionSelectData bits target
  let q := idx
  if idx < GenericSelect.occurrenceCount bits target then
    Costed.bind
      (data.superTable.readInterpretedCosted
        (GenericSelect.selectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => Costed.pure none
      | some super =>
          if GenericSelect.relativeSplitSelectEntryIsMarked super then
            Costed.bind
              (data.longFlagRankData.rankInterpretedCosted true
                (GenericSelect.selectSuperSlot q data.superStride))
              fun exceptionRank =>
                GenericSelect.relativeOffsetReadInterpretedCosted
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
            Costed.bind
              (data.localTable.readInterpretedCosted localSlot) fun loc? =>
              match loc? with
              | none => Costed.pure none
              | some loc =>
                  if GenericSelect.relativeSplitSelectEntryIsMarked loc then
                    data.sparseDirectory.readInterpretedCosted
                      (GenericSelect.relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        GenericSelect.relativeSplitSelectLocalBaseOccurrence
                          super loc)
                  else
                    subLogDenseTwoWordSelectInterpretedCosted target bits
                      (GenericSelect.relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                        super loc) q
  else
    Costed.pure none

theorem subLogPackedClarkSelectInterpretedCosted_refines
    (bits : List Bool) (target : Bool) (idx : Nat) :
    subLogPackedClarkSelectInterpretedCosted bits target idx =
      subLogPackedClarkSelectCosted bits target idx := by
  unfold subLogPackedClarkSelectInterpretedCosted
    subLogPackedClarkSelectCosted
  let data := GenericSelect.sparseExceptionSelectData bits target
  by_cases hvalid : idx < GenericSelect.occurrenceCount bits target
  · simp [hvalid]
    rw [data.superTable.readInterpretedCosted_refines_readCosted
      (GenericSelect.selectSuperSlot idx data.superStride)]
    cases hsuper :
        (data.superTable.readCosted
          (GenericSelect.selectSuperSlot idx data.superStride)).value with
    | none =>
        simp [data, Costed.bind, Costed.pure, hsuper]
    | some super =>
        by_cases hlong :
            GenericSelect.relativeSplitSelectEntryIsMarked super = true
        · rw [data.longFlagRankData.rankInterpretedCosted_refines_rankCosted
            true (GenericSelect.selectSuperSlot idx data.superStride)]
          simp [Costed.bind, hsuper, hlong]
          rw [GenericSelect.relativeOffsetReadInterpretedCosted_refines]
          simp [data, hsuper, hlong]
        · let localSlot :=
            GenericSelect.relativeSplitSelectLocalSlot idx data.superStride
              data.localSlotsPerSuper data.localStride super
          simp [Costed.bind, hsuper, hlong]
          rw [data.localTable.readInterpretedCosted_refines_readCosted
            localSlot]
          cases hlocal :
              (data.localTable.readCosted localSlot).value with
          | none =>
              simp [data, Costed.pure, hsuper, hlong,
                localSlot, hlocal]
          | some loc =>
              by_cases hsparse :
                  GenericSelect.relativeSplitSelectEntryIsMarked loc = true
              · simp [hsparse]
                rw [data.sparseDirectory.readInterpretedCosted_refines_readCosted]
                simp [data, hsuper, hlong, localSlot,
                  hlocal, hsparse]
              · simp [hsparse]
                rw [subLogDenseTwoWordSelectInterpretedCosted_refines]
                simp [data, hsuper, hlong, localSlot,
                  hlocal, hsparse]
  · simp [hvalid, Costed.pure]

/-- Interpreted packed-Clark route-field read. -/
def fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    Costed (Option FixedWeightSubLogClarkSelectRouteFields) :=
  Costed.map
    (fun pos? =>
      pos?.map
        (fixedWeightSubLogSelectRouteFieldsOfPosition
          bits target occurrence))
    (subLogPackedClarkSelectInterpretedCosted bits target occurrence)

theorem fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted_refines
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted
        bits target occurrence =
      fixedWeightSubLogPackedClarkSelectRouteFieldsCosted
        bits target occurrence := by
  unfold fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted
    fixedWeightSubLogPackedClarkSelectRouteFieldsCosted
  rw [subLogPackedClarkSelectInterpretedCosted_refines]

/-- Interpreted select query for the public packed-Clark compressed/FID path. -/
def subLogSelectFromPackedClarkRouteInterpretedCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind
    (fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted
      bits target occurrence)
    fun fields? =>
      match fields? with
      | none => Costed.pure none
      | some fields =>
          subLogSelectWithFieldsInterpretedCosted bits target fields

theorem subLogSelectFromPackedClarkRouteInterpretedCosted_refines
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    subLogSelectFromPackedClarkRouteInterpretedCosted bits target occurrence =
      subLogSelectFromPackedClarkRouteCosted bits target occurrence := by
  unfold subLogSelectFromPackedClarkRouteInterpretedCosted
    subLogSelectFromPackedClarkRouteCosted
  rw [fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted_refines]
  cases hfields :
      (fixedWeightSubLogPackedClarkSelectRouteFieldsCosted
        bits target occurrence).value with
  | none =>
      simp [Costed.bind, Costed.pure, hfields]
  | some fields =>
      simp [Costed.bind, hfields]
      rw [subLogSelectWithFieldsInterpretedCosted_refines]
      exact ⟨rfl, rfl⟩

theorem subLogSelectFromPackedClarkRouteInterpretedCosted_cost_le
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromPackedClarkRouteInterpretedCosted
      bits target occurrence).cost <=
        fixedWeightSubLogConcretePackedClarkQueryCost := by
  rw [subLogSelectFromPackedClarkRouteInterpretedCosted_refines]
  exact
    (fixedWeightSubLogConcretePackedClarkProfile bits).2.2.2.2
      target occurrence |>.1

theorem subLogSelectFromPackedClarkRouteInterpretedCosted_erase
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromPackedClarkRouteInterpretedCosted
      bits target occurrence).erase =
        Succinct.select target bits occurrence := by
  rw [subLogSelectFromPackedClarkRouteInterpretedCosted_refines]
  exact subLogSelectFromPackedClarkRouteCosted_erase bits target occurrence

theorem fixedWeightSubLogConcretePackedClarkInterpretedProfile
    (bits : List Bool) :
    (fixedWeightSubLogConcretePackedClarkPayload bits).length <=
        fixedWeightPayloadBudget bits +
          fixedWeightSubLogConcretePackedClarkOverhead bits.length /\
      SuccinctSpace.LittleOLinear
        fixedWeightSubLogConcretePackedClarkOverhead /\
      (forall i,
        (subLogAccessInterpretedCosted bits i).cost <=
            fixedWeightSubLogConcretePackedClarkQueryCost /\
          (subLogAccessInterpretedCosted bits i).erase = bits[i]?) /\
      (forall target pos,
        (subLogRankInterpretedCosted bits target pos).cost <=
            fixedWeightSubLogConcretePackedClarkQueryCost /\
          (subLogRankInterpretedCosted bits target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      forall target occurrence,
        (subLogSelectFromPackedClarkRouteInterpretedCosted
          bits target occurrence).cost <=
            fixedWeightSubLogConcretePackedClarkQueryCost /\
          (subLogSelectFromPackedClarkRouteInterpretedCosted
            bits target occurrence).erase =
            Succinct.select target bits occurrence := by
  refine
    ⟨fixedWeightSubLogConcretePackedClarkPayload_length_le bits,
      fixedWeightSubLogConcretePackedClarkOverhead_littleO,
      ?_, ?_, ?_⟩
  · intro i
    exact
      ⟨by
        rw [subLogAccessInterpretedCosted_cost]
        exact Nat.le_trans (by omega : 4 <= 6)
          (Nat.le_max_left 6 (subLogPackedClarkSelectQueryCost + 4)),
        subLogAccessInterpretedCosted_erase bits i⟩
  · intro target pos
    exact
      ⟨by
        rw [subLogRankInterpretedCosted_cost]
        exact Nat.le_max_left 6 (subLogPackedClarkSelectQueryCost + 4),
        subLogRankInterpretedCosted_erase bits target pos⟩
  · intro target occurrence
    exact
      ⟨subLogSelectFromPackedClarkRouteInterpretedCosted_cost_le
        bits target occurrence,
        subLogSelectFromPackedClarkRouteInterpretedCosted_erase
          bits target occurrence⟩

end RankSelectSpec

end RMQ
