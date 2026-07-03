import RMQ.Core.RankSelectCompressedSubLogRAM.AccessRank

namespace RMQ

namespace RankSelectSpec

open GenericSelect

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

/-! ### Trace-result select replay -/

def subLogSelectSuperTableTraceSegments :
    GenericSelect.SparseDenseEntryTableTraceSegmentBases where
  baseOccurrence := 0
  baseWordIndex := 1
  rankBefore := 2
  firstOffset := 3
  deadSegment := 20

def subLogSelectLocalTableTraceSegments :
    GenericSelect.SparseDenseEntryTableTraceSegmentBases where
  baseOccurrence := 4
  baseWordIndex := 5
  rankBefore := 6
  firstOffset := 7
  deadSegment := 20

def subLogSelectLongFlagRankBase : Nat := 8
def subLogSelectLongRelativeSegment : Nat := 11

def subLogSelectSparseDirectoryTraceSegments :
    GenericSelect.SparseExceptionDirectoryTraceSegmentBases where
  rankBase := 12
  relativeBase := 15
  deadSegment := 20

def subLogSelectCodeSegment : Nat := 16
def subLogSelectLengthSegment : Nat := 17
def subLogSelectClassSegment : Nat := 18
def subLogSelectDecoderSegment : Nat := 19
def subLogSelectDeadSegment : Nat := 20

/--
Concrete read-only store for the compressed/FID select trace replay.

Segments 0-15 contain the sparse-exception Clark routing tables; segments
16-19 contain the sub-log block code/length/class/shared-decoder stores used
by both the dense two-word branch and the final local block select.
-/
def subLogSelectFromPackedClarkRouteTraceReadStore
    (bits : List Bool) (target : Bool) : WordRAM.ReadStore where
  readWord? segment index :=
    let data := GenericSelect.sparseExceptionSelectData bits target
    match segment with
    | 0 => data.superTable.baseOccurrenceTable.wordRAMStore.readWord? 0 index
    | 1 => data.superTable.baseWordIndexTable.wordRAMStore.readWord? 0 index
    | 2 => data.superTable.rankBeforeTable.wordRAMStore.readWord? 0 index
    | 3 => data.superTable.firstOffsetTable.wordRAMStore.readWord? 0 index
    | 4 => data.localTable.baseOccurrenceTable.wordRAMStore.readWord? 0 index
    | 5 => data.localTable.baseWordIndexTable.wordRAMStore.readWord? 0 index
    | 6 => data.localTable.rankBeforeTable.wordRAMStore.readWord? 0 index
    | 7 => data.localTable.firstOffsetTable.wordRAMStore.readWord? 0 index
    | 8 => (data.longFlagRankData.rankRegisterWordRAMStore true).readWord? 0 index
    | 9 => (data.longFlagRankData.rankRegisterWordRAMStore true).readWord? 1 index
    | 10 => (data.longFlagRankData.rankRegisterWordRAMStore true).readWord? 2 index
    | 11 => data.longSuperRelativeTable.wordRAMStore.readWord? 0 index
    | 12 => (data.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord? 0 index
    | 13 => (data.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord? 1 index
    | 14 => (data.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord? 2 index
    | 15 => data.sparseDirectory.relativeTable.wordRAMStore.readWord? 0 index
    | 16 => (subLogCodeStore bits).wordRAMStore.readWord? 0 index
    | 17 => (subLogLenStore bits).wordRAMStore.readWord? 0 index
    | 18 => (subLogClassStore bits).wordRAMStore.readWord? 0 index
    | 19 =>
        (fixedWeightSubLogSharedDecoderStore bits).wordRAMStore.readWord?
          0 index
    | _ + 20 => none

private theorem subLogSelectTraceReadStore_code_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectCodeSegment subLogSelectDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogCodeStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectCodeSegment, subLogSelectDeadSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_len_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectLengthSegment subLogSelectDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogLenStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectLengthSegment, subLogSelectDeadSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_class_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectClassSegment subLogSelectDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogClassStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectClassSegment, subLogSelectDeadSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_decoder_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectDecoderSegment subLogSelectDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (fixedWeightSubLogSharedDecoderStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectDecoderSegment, subLogSelectDeadSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_super_baseOccurrence_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectSuperTableTraceSegments.baseOccurrence
            subLogSelectSuperTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.superTable.baseOccurrenceTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectSuperTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_super_baseWordIndex_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectSuperTableTraceSegments.baseWordIndex
            subLogSelectSuperTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.superTable.baseWordIndexTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectSuperTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_super_rankBefore_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectSuperTableTraceSegments.rankBefore
            subLogSelectSuperTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.superTable.rankBeforeTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectSuperTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_super_firstOffset_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectSuperTableTraceSegments.firstOffset
            subLogSelectSuperTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.superTable.firstOffsetTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectSuperTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_local_baseOccurrence_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectLocalTableTraceSegments.baseOccurrence
            subLogSelectLocalTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.localTable.baseOccurrenceTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectLocalTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_local_baseWordIndex_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectLocalTableTraceSegments.baseWordIndex
            subLogSelectLocalTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.localTable.baseWordIndexTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectLocalTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_local_rankBefore_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectLocalTableTraceSegments.rankBefore
            subLogSelectLocalTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.localTable.rankBeforeTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectLocalTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_local_firstOffset_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectLocalTableTraceSegments.firstOffset
            subLogSelectLocalTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.localTable.firstOffsetTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectLocalTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_longFlagRank_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.tripleSegmentMap
            subLogSelectLongFlagRankBase subLogSelectDeadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        (data.longFlagRankData.rankRegisterWordRAMStore true).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment with
  | zero =>
      simp [subLogSelectFromPackedClarkRouteTraceReadStore,
        subLogSelectLongFlagRankBase,
        WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
        WordRAM.Store.readWord?]
  | succ localSegment =>
      cases localSegment with
      | zero =>
          simp [subLogSelectFromPackedClarkRouteTraceReadStore,
            subLogSelectLongFlagRankBase,
            WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
            WordRAM.Store.readWord?]
      | succ localSegment =>
          cases localSegment with
          | zero =>
              simp [subLogSelectFromPackedClarkRouteTraceReadStore,
                subLogSelectLongFlagRankBase,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap,
                WordRAM.Store.readWord?]
          | succ localSegment =>
              simp [subLogSelectFromPackedClarkRouteTraceReadStore,
                subLogSelectDeadSegment,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap,
                SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_longRelative_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectLongRelativeSegment subLogSelectDeadSegment
            localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.longSuperRelativeTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectLongRelativeSegment, subLogSelectDeadSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_sparseRank_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.tripleSegmentMap
            subLogSelectSparseDirectoryTraceSegments.rankBase
            subLogSelectSparseDirectoryTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        (data.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment with
  | zero =>
      simp [subLogSelectFromPackedClarkRouteTraceReadStore,
        subLogSelectSparseDirectoryTraceSegments,
        WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
        WordRAM.Store.readWord?]
  | succ localSegment =>
      cases localSegment with
      | zero =>
          simp [subLogSelectFromPackedClarkRouteTraceReadStore,
            subLogSelectSparseDirectoryTraceSegments,
            WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
            WordRAM.Store.readWord?]
      | succ localSegment =>
          cases localSegment with
          | zero =>
              simp [subLogSelectFromPackedClarkRouteTraceReadStore,
                subLogSelectSparseDirectoryTraceSegments,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap,
                WordRAM.Store.readWord?]
          | succ localSegment =>
              simp [subLogSelectFromPackedClarkRouteTraceReadStore,
                subLogSelectSparseDirectoryTraceSegments,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap,
                SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_sparseRelative_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectSparseDirectoryTraceSegments.relativeBase
            subLogSelectSparseDirectoryTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.sparseDirectory.relativeTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectSparseDirectoryTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

/-- Trace-result decode of one sub-log block by index. -/
def subLogDecodeBlockByIndexTraceResult
    (bits : List Bool) (_target : Bool) (blockIndex : Nat) :
    WordRAM.TraceResult (List Bool) :=
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectCodeSegment subLogSelectDeadSegment
        (subLogCodeStore bits) blockIndex)
      fun code? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectLengthSegment subLogSelectDeadSegment
        (subLogLenStore bits) blockIndex)
      fun len? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectClassSegment subLogSelectDeadSegment
        (subLogClassStore bits) blockIndex)
      fun class? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectDecoderSegment subLogSelectDeadSegment
        (fixedWeightSubLogSharedDecoderStore bits)
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    WordRAM.TraceResult.pure (decoded?.getD [])

theorem subLogDecodeBlockByIndexTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    (subLogDecodeBlockByIndexTraceResult
      bits target blockIndex).toCosted =
        subLogDecodeBlockByIndexInterpretedCosted bits blockIndex := by
  simp [subLogDecodeBlockByIndexTraceResult,
    subLogDecodeBlockByIndexInterpretedCosted,
    boundedWordReadTraceResultAtSegment_refines_interpretedCosted,
    subLogDecodeReadInterpretedCosted,
    WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.pure_toCosted]

theorem subLogDecodeBlockByIndexTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    forall event,
      event ∈
          (subLogDecodeBlockByIndexTraceResult
            bits target blockIndex).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogDecodeBlockByIndexTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      boundedWordReadTraceResultAtSegment_matchesReadStore
        subLogSelectCodeSegment subLogSelectDeadSegment
        (subLogCodeStore bits)
        (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
        (subLogSelectTraceReadStore_code_read bits target)
        blockIndex
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        boundedWordReadTraceResultAtSegment_matchesReadStore
          subLogSelectLengthSegment subLogSelectDeadSegment
          (subLogLenStore bits)
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
          (subLogSelectTraceReadStore_len_read bits target)
          blockIndex
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          boundedWordReadTraceResultAtSegment_matchesReadStore
            subLogSelectClassSegment subLogSelectDeadSegment
            (subLogClassStore bits)
            (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
            (subLogSelectTraceReadStore_class_read bits target)
            blockIndex
      · apply WordRAM.TraceResult.bind_trace_forall
        · exact
            boundedWordReadTraceResultAtSegment_matchesReadStore
              subLogSelectDecoderSegment subLogSelectDeadSegment
              (fixedWeightSubLogSharedDecoderStore bits)
              (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
              (subLogSelectTraceReadStore_decoder_read bits target)
              (fixedWeightSharedDecodeSlotFromReadValues [_, _] [_])
        · exact WordRAM.TraceResult.pure_trace_forall
            (fun event =>
              event.matchesReadStore
                (subLogSelectFromPackedClarkRouteTraceReadStore bits target))
            _

/-- Trace-result decode of a constant-size sub-log block window. -/
def subLogDecodeBlockWindowTraceResult
    (bits : List Bool) (target : Bool) (startBlock count : Nat) :
    WordRAM.TraceResult (List (List Bool)) :=
  match count with
  | 0 => WordRAM.TraceResult.pure []
  | count' + 1 =>
      WordRAM.TraceResult.bind
          (subLogDecodeBlockByIndexTraceResult bits target startBlock)
          fun block =>
        WordRAM.TraceResult.map
          (fun rest => block :: rest)
          (subLogDecodeBlockWindowTraceResult bits target
            (startBlock + 1) count')

theorem subLogDecodeBlockWindowTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (startBlock count : Nat) :
    (subLogDecodeBlockWindowTraceResult
      bits target startBlock count).toCosted =
        subLogDecodeBlockWindowInterpretedCosted
          bits startBlock count := by
  induction count generalizing startBlock with
  | zero =>
      rfl
  | succ count ih =>
      simp [subLogDecodeBlockWindowTraceResult,
        subLogDecodeBlockWindowInterpretedCosted,
        subLogDecodeBlockByIndexTraceResult_refines_interpretedCosted,
        ih, WordRAM.TraceResult.bind_toCosted,
        WordRAM.TraceResult.map_toCosted]

theorem subLogDecodeBlockWindowTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (startBlock count : Nat) :
    forall event,
      event ∈
          (subLogDecodeBlockWindowTraceResult
            bits target startBlock count).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  induction count generalizing startBlock with
  | zero =>
      exact WordRAM.TraceResult.pure_trace_forall
        (fun event =>
          event.matchesReadStore
            (subLogSelectFromPackedClarkRouteTraceReadStore bits target)) []
  | succ count ih =>
      unfold subLogDecodeBlockWindowTraceResult
      apply WordRAM.TraceResult.bind_trace_forall
      · exact subLogDecodeBlockByIndexTraceResult_matchesReadStore
          bits target startBlock
      · apply WordRAM.TraceResult.map_trace_forall
        exact ih (startBlock + 1)

/-- Trace-result reconstruction of one machine word from sub-log blocks. -/
def subLogMachineWordReadTraceResult
    (bits : List Bool) (target : Bool) (wordIndex : Nat) :
    WordRAM.TraceResult (List Bool) :=
  let wordSize := SuccinctRank.machineWordBits bits.length
  let start := wordIndex * wordSize
  let startBlock := start / fixedWeightSubLogChunkBlockSize bits.length
  WordRAM.TraceResult.bind
    (subLogDecodeBlockWindowTraceResult bits target startBlock
      fixedWeightSubLogDenseWindowBlockCount)
    fun decodedWindow =>
      WordRAM.TraceResult.pure
        (subLogMachineWordFromDecodedWindow bits wordIndex decodedWindow)

theorem subLogMachineWordReadTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (wordIndex : Nat) :
    (subLogMachineWordReadTraceResult bits target wordIndex).toCosted =
      subLogMachineWordReadInterpretedCosted bits wordIndex := by
  simp [subLogMachineWordReadTraceResult,
    subLogMachineWordReadInterpretedCosted,
    subLogDecodeBlockWindowTraceResult_refines_interpretedCosted,
    WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.pure_toCosted]

theorem subLogMachineWordReadTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (wordIndex : Nat) :
    forall event,
      event ∈ (subLogMachineWordReadTraceResult bits target wordIndex).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogMachineWordReadTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact subLogDecodeBlockWindowTraceResult_matchesReadStore
      bits target
      ((wordIndex * SuccinctRank.machineWordBits bits.length) /
        fixedWeightSubLogChunkBlockSize bits.length)
      fixedWeightSubLogDenseWindowBlockCount
  · exact WordRAM.TraceResult.pure_trace_forall
      (fun event =>
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)) _

def subLogDenseTwoWordSelectTailTraceResult
    (target : Bool) (bits : List Bool)
    (wordSize firstWordIndex firstWordStart localOccurrence : Nat)
    (firstWord : List Bool) (beforeFirst uptoFirst : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  let firstCount := uptoFirst - beforeFirst
  if localOccurrence < firstCount then
    WordRAM.TraceResult.map
      (fun local? =>
        local?.map fun offset => firstWordStart + offset)
      (GenericSelect.wordSelectTraceResult target firstWord
        (beforeFirst + localOccurrence))
  else
    WordRAM.TraceResult.bind
      (subLogMachineWordReadTraceResult bits target (firstWordIndex + 1))
      fun secondWord =>
        WordRAM.TraceResult.map
          (fun local? =>
            local?.map fun offset =>
              (firstWordIndex + 1) * wordSize + offset)
          (GenericSelect.wordSelectTraceResult target
            secondWord (localOccurrence - firstCount))

theorem subLogDenseTwoWordSelectTailTraceResult_refines_interpretedCosted
    (target : Bool) (bits : List Bool)
    (wordSize firstWordIndex firstWordStart localOccurrence : Nat)
    (firstWord : List Bool) (beforeFirst uptoFirst : Nat) :
    (subLogDenseTwoWordSelectTailTraceResult
      target bits wordSize firstWordIndex firstWordStart
      localOccurrence firstWord beforeFirst uptoFirst).toCosted =
        (let firstCount := uptoFirst - beforeFirst
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
                   secondWord (localOccurrence - firstCount))) := by
  unfold subLogDenseTwoWordSelectTailTraceResult
  by_cases hlocal : localOccurrence < uptoFirst - beforeFirst
  · simp [hlocal,
      GenericSelect.wordSelectTraceResult_refines_interpretedCosted,
      WordRAM.TraceResult.map_toCosted]
  · simp [hlocal,
      subLogMachineWordReadTraceResult_refines_interpretedCosted,
      GenericSelect.wordSelectTraceResult_refines_interpretedCosted,
      WordRAM.TraceResult.bind_toCosted,
      WordRAM.TraceResult.map_toCosted]

theorem subLogDenseTwoWordSelectTailTraceResult_matchesReadStore
    (target : Bool) (bits : List Bool)
    (wordSize firstWordIndex firstWordStart localOccurrence : Nat)
    (firstWord : List Bool) (beforeFirst uptoFirst : Nat) :
    forall event,
      event ∈
          (subLogDenseTwoWordSelectTailTraceResult
            target bits wordSize firstWordIndex firstWordStart
            localOccurrence firstWord beforeFirst uptoFirst).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogDenseTwoWordSelectTailTraceResult
  by_cases hlocal : localOccurrence < uptoFirst - beforeFirst
  · intro event hmem
    exact
      GenericSelect.wordSelectTraceResult_matchesReadStore
        target firstWord (beforeFirst + localOccurrence)
        (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
        event
        (by simpa [hlocal] using hmem)
  · intro event hmem
    simp [hlocal, WordRAM.TraceResult.bind] at hmem
    rcases hmem with hmem | hmem
    · exact subLogMachineWordReadTraceResult_matchesReadStore
        bits target (firstWordIndex + 1) event hmem
    · exact
        GenericSelect.wordSelectTraceResult_matchesReadStore
          target
          (subLogMachineWordReadTraceResult bits target
            (firstWordIndex + 1)).value
          (localOccurrence - (uptoFirst - beforeFirst))
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
          event hmem

/-- Trace-result dense two-word select branch over sub-log decoded windows. -/
def subLogDenseTwoWordSelectTraceResult
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat) : WordRAM.TraceResult (Option Nat) :=
  let wordSize := SuccinctRank.machineWordBits bits.length
  let firstWordIndex := basePosition / wordSize
  let firstWordStart := firstWordIndex * wordSize
  let firstOffset := basePosition - firstWordStart
  let localOccurrence := q - baseOccurrence
  WordRAM.TraceResult.bind
      (subLogMachineWordReadTraceResult bits target firstWordIndex)
      fun firstWord =>
    WordRAM.TraceResult.bind
      (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
        target firstWord firstOffset)
      fun beforeFirst =>
        WordRAM.TraceResult.bind
          (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
            target firstWord firstWord.length)
          fun uptoFirst =>
            subLogDenseTwoWordSelectTailTraceResult
              target bits wordSize firstWordIndex firstWordStart
              localOccurrence firstWord beforeFirst uptoFirst

theorem subLogDenseTwoWordSelectTraceResult_refines_interpretedCosted
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat) :
    (subLogDenseTwoWordSelectTraceResult
      target bits basePosition baseOccurrence q).toCosted =
        subLogDenseTwoWordSelectInterpretedCosted
          target bits basePosition baseOccurrence q := by
  unfold subLogDenseTwoWordSelectTraceResult
    subLogDenseTwoWordSelectInterpretedCosted
  simp [subLogMachineWordReadTraceResult_refines_interpretedCosted,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_refines_interpretedCosted,
    subLogDenseTwoWordSelectTailTraceResult_refines_interpretedCosted,
    WordRAM.TraceResult.bind_toCosted]

theorem subLogDenseTwoWordSelectTraceResult_matchesReadStore
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat) :
    forall event,
      event ∈
          (subLogDenseTwoWordSelectTraceResult
            target bits basePosition baseOccurrence q).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogDenseTwoWordSelectTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact subLogMachineWordReadTraceResult_matchesReadStore bits target
      (basePosition / SuccinctRank.machineWordBits bits.length)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_matchesReadStore
          target _ _
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_matchesReadStore
            target _ _
            (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
      · exact
          subLogDenseTwoWordSelectTailTraceResult_matchesReadStore
            target bits (SuccinctRank.machineWordBits bits.length)
            (basePosition / SuccinctRank.machineWordBits bits.length)
            ((basePosition / SuccinctRank.machineWordBits bits.length) *
              SuccinctRank.machineWordBits bits.length)
            (q - baseOccurrence)
            (subLogMachineWordReadTraceResult bits target
              (basePosition /
                SuccinctRank.machineWordBits bits.length)).value
            (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
              target
              (subLogMachineWordReadTraceResult bits target
                (basePosition /
                  SuccinctRank.machineWordBits bits.length)).value
              (basePosition -
                (basePosition /
                    SuccinctRank.machineWordBits bits.length) *
                  SuccinctRank.machineWordBits bits.length)).value
            (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
              target
              (subLogMachineWordReadTraceResult bits target
                (basePosition /
                  SuccinctRank.machineWordBits bits.length)).value
              (subLogMachineWordReadTraceResult bits target
                (basePosition /
                  SuccinctRank.machineWordBits bits.length)).value.length).value

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

/-- Trace-result final local select from already-computed packed-Clark fields. -/
def subLogSelectWithFieldsTraceResult
    (bits : List Bool) (target : Bool)
    (fields : FixedWeightSubLogClarkSelectRouteFields) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectCodeSegment subLogSelectDeadSegment
        (subLogCodeStore bits) fields.blockIndex)
      fun code? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectLengthSegment subLogSelectDeadSegment
        (subLogLenStore bits) fields.blockIndex)
      fun len? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectClassSegment subLogSelectDeadSegment
        (subLogClassStore bits) fields.blockIndex)
      fun class? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectDecoderSegment subLogSelectDeadSegment
        (fixedWeightSubLogSharedDecoderStore bits)
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    WordRAM.TraceResult.pure
      ((Succinct.select target
          (decoded?.getD []) fields.localOccurrence).map
        (fun offset => fields.blockStart + offset))

theorem subLogSelectWithFieldsTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool)
    (fields : FixedWeightSubLogClarkSelectRouteFields) :
    (subLogSelectWithFieldsTraceResult bits target fields).toCosted =
      subLogSelectWithFieldsInterpretedCosted bits target fields := by
  simp [subLogSelectWithFieldsTraceResult,
    subLogSelectWithFieldsInterpretedCosted,
    boundedWordReadTraceResultAtSegment_refines_interpretedCosted,
    subLogDecodeReadInterpretedCosted,
    WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.pure_toCosted]

theorem subLogSelectWithFieldsTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool)
    (fields : FixedWeightSubLogClarkSelectRouteFields) :
    forall event,
      event ∈ (subLogSelectWithFieldsTraceResult bits target fields).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogSelectWithFieldsTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      boundedWordReadTraceResultAtSegment_matchesReadStore
        subLogSelectCodeSegment subLogSelectDeadSegment
        (subLogCodeStore bits)
        (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
        (subLogSelectTraceReadStore_code_read bits target)
        fields.blockIndex
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        boundedWordReadTraceResultAtSegment_matchesReadStore
          subLogSelectLengthSegment subLogSelectDeadSegment
          (subLogLenStore bits)
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
          (subLogSelectTraceReadStore_len_read bits target)
          fields.blockIndex
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          boundedWordReadTraceResultAtSegment_matchesReadStore
            subLogSelectClassSegment subLogSelectDeadSegment
            (subLogClassStore bits)
            (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
            (subLogSelectTraceReadStore_class_read bits target)
            fields.blockIndex
      · apply WordRAM.TraceResult.bind_trace_forall
        · exact
            boundedWordReadTraceResultAtSegment_matchesReadStore
              subLogSelectDecoderSegment subLogSelectDeadSegment
              (fixedWeightSubLogSharedDecoderStore bits)
              (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
              (subLogSelectTraceReadStore_decoder_read bits target)
              (fixedWeightSharedDecodeSlotFromReadValues [_, _] [_])
        · exact WordRAM.TraceResult.pure_trace_forall
            (fun event =>
              event.matchesReadStore
                (subLogSelectFromPackedClarkRouteTraceReadStore bits target))
            _

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

/-- Trace-result packed-Clark select source with the packed sub-log dense branch. -/
def subLogPackedClarkSelectTraceResult
    (bits : List Bool) (target : Bool) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  let data := GenericSelect.sparseExceptionSelectData bits target
  let q := idx
  if idx < GenericSelect.occurrenceCount bits target then
    WordRAM.TraceResult.bind
      (data.superTable.readTraceResultRelabeled
        subLogSelectSuperTableTraceSegments
        (GenericSelect.selectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => WordRAM.TraceResult.pure none
      | some super =>
          if GenericSelect.relativeSplitSelectEntryIsMarked super then
            WordRAM.TraceResult.bind
              (WordRAM.TraceResult.relabelReadSegmentsWith
                (WordRAM.tripleSegmentMap
                  subLogSelectLongFlagRankBase subLogSelectDeadSegment)
                (data.longFlagRankData.rankTraceResult true
                  (GenericSelect.selectSuperSlot q data.superStride)))
              fun exceptionRank =>
                GenericSelect.relativeOffsetReadTraceResultRelabeled
                  subLogSelectLongRelativeSegment subLogSelectDeadSegment
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
            WordRAM.TraceResult.bind
              (data.localTable.readTraceResultRelabeled
                subLogSelectLocalTableTraceSegments localSlot) fun loc? =>
              match loc? with
              | none => WordRAM.TraceResult.pure none
              | some loc =>
                  if GenericSelect.relativeSplitSelectEntryIsMarked loc then
                    data.sparseDirectory.readTraceResultRelabeled
                      subLogSelectSparseDirectoryTraceSegments
                      (GenericSelect.relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        GenericSelect.relativeSplitSelectLocalBaseOccurrence
                          super loc)
                  else
                    subLogDenseTwoWordSelectTraceResult target bits
                      (GenericSelect.relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                        super loc) q
  else
    WordRAM.TraceResult.pure none

set_option linter.unusedSimpArgs false in
theorem subLogPackedClarkSelectTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (idx : Nat) :
    (subLogPackedClarkSelectTraceResult bits target idx).toCosted =
      subLogPackedClarkSelectInterpretedCosted bits target idx := by
  unfold subLogPackedClarkSelectTraceResult
    subLogPackedClarkSelectInterpretedCosted
  let data := GenericSelect.sparseExceptionSelectData bits target
  by_cases hvalid : idx < GenericSelect.occurrenceCount bits target
  · simp [data, hvalid, WordRAM.TraceResult.bind_toCosted,
      data.superTable.readTraceResultRelabeled_refines_interpretedCosted
        subLogSelectSuperTableTraceSegments
        (GenericSelect.selectSuperSlot idx data.superStride)]
    cases hsuper :
        (data.superTable.readInterpretedCosted
          (GenericSelect.selectSuperSlot idx data.superStride)).value with
    | none =>
        simp [data, Costed.bind, Costed.pure, hsuper]
    | some super =>
        by_cases hlong :
            GenericSelect.relativeSplitSelectEntryIsMarked super = true
        · simp [data, Costed.bind, hsuper, hlong,
            WordRAM.TraceResult.bind_toCosted,
            WordRAM.TraceResult.relabelReadSegmentsWith_toCosted,
            data.longFlagRankData.rankTraceResult_refines_rankInterpretedCosted,
            GenericSelect.relativeOffsetReadTraceResultRelabeled_refines_interpretedCosted]
        · let localSlot :=
            GenericSelect.relativeSplitSelectLocalSlot idx data.superStride
              data.localSlotsPerSuper data.localStride super
          simp [data, Costed.bind, hsuper, hlong,
            WordRAM.TraceResult.bind_toCosted,
            localSlot,
            data.localTable.readTraceResultRelabeled_refines_interpretedCosted
              subLogSelectLocalTableTraceSegments localSlot]
          cases hlocal :
              (data.localTable.readInterpretedCosted localSlot).value with
          | none =>
              have hlocalTrace :=
                data.localTable.readTraceResultRelabeled_refines_interpretedCosted
                  subLogSelectLocalTableTraceSegments localSlot
              have hlocalTraceValue :
                  (data.localTable.readTraceResultRelabeled
                    subLogSelectLocalTableTraceSegments localSlot).value =
                    none := by
                have hv := congrArg Costed.value hlocalTrace
                simpa [WordRAM.TraceResult.toCosted, hlocal] using hv
              have hlocalTraceCost :
                  (data.localTable.readTraceResultRelabeled
                    subLogSelectLocalTableTraceSegments localSlot).trace.length =
                    (data.localTable.readInterpretedCosted localSlot).cost := by
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using
                  congrArg Costed.cost hlocalTrace
              simp [data, Costed.pure, hlocalTraceValue,
                hlocalTraceCost]
          | some loc =>
              have hlocalTrace :=
                data.localTable.readTraceResultRelabeled_refines_interpretedCosted
                  subLogSelectLocalTableTraceSegments localSlot
              have hlocalTraceValue :
                  (data.localTable.readTraceResultRelabeled
                    subLogSelectLocalTableTraceSegments localSlot).value =
                    some loc := by
                have hv := congrArg Costed.value hlocalTrace
                simpa [WordRAM.TraceResult.toCosted, hlocal] using hv
              have hlocalTraceCost :
                  (data.localTable.readTraceResultRelabeled
                    subLogSelectLocalTableTraceSegments localSlot).trace.length =
                    (data.localTable.readInterpretedCosted localSlot).cost := by
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using
                  congrArg Costed.cost hlocalTrace
              by_cases hsparse :
                  GenericSelect.relativeSplitSelectEntryIsMarked loc = true
              · simp [data, Costed.bind, hlocal, hsparse, localSlot,
                  hlocalTraceValue, hlocalTraceCost]
                have hchild :=
                  data.sparseDirectory.readTraceResultRelabeled_refines_interpretedCosted
                    subLogSelectSparseDirectoryTraceSegments
                    (GenericSelect.relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (GenericSelect.relativeSplitSelectLocalSlot idx
                      data.superStride data.localSlotsPerSuper
                      data.localStride super)
                    (idx -
                      GenericSelect.relativeSplitSelectLocalBaseOccurrence
                        super loc)
                constructor
                · simpa [WordRAM.TraceResult.toCosted] using
                    congrArg Costed.value hchild
                · simpa [WordRAM.TraceResult.toCosted,
                    WordRAM.TraceResult.steps] using
                    congrArg Costed.cost hchild
              · simp [data, Costed.bind, hlocal, hsparse, localSlot,
                  hlocalTraceValue, hlocalTraceCost]
                have hchild :=
                  subLogDenseTwoWordSelectTraceResult_refines_interpretedCosted
                    target bits
                    (GenericSelect.relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                      super loc) idx
                constructor
                · simpa [WordRAM.TraceResult.toCosted] using
                    congrArg Costed.value hchild
                · simpa [WordRAM.TraceResult.toCosted,
                    WordRAM.TraceResult.steps] using
                    congrArg Costed.cost hchild
  · simp [data, hvalid, WordRAM.TraceResult.pure_toCosted, Costed.pure]

theorem subLogPackedClarkSelectTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (idx : Nat) :
    forall event,
      event ∈ (subLogPackedClarkSelectTraceResult bits target idx).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogPackedClarkSelectTraceResult
  let data := GenericSelect.sparseExceptionSelectData bits target
  by_cases hvalid : idx < GenericSelect.occurrenceCount bits target
  · intro event hmem
    simp [hvalid, WordRAM.TraceResult.bind] at hmem
    rcases hmem with hmem | hmem
    · exact
        data.superTable.readTraceResultRelabeled_matchesReadStore
          subLogSelectSuperTableTraceSegments
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
          (by
            intro segment index
            simpa [data] using
              subLogSelectTraceReadStore_super_baseOccurrence_read
                bits target segment index)
          (by
            intro segment index
            simpa [data] using
              subLogSelectTraceReadStore_super_baseWordIndex_read
                bits target segment index)
          (by
            intro segment index
            simpa [data] using
              subLogSelectTraceReadStore_super_rankBefore_read
                bits target segment index)
          (by
            intro segment index
            simpa [data] using
              subLogSelectTraceReadStore_super_firstOffset_read
                bits target segment index)
          (GenericSelect.selectSuperSlot idx data.superStride)
          event hmem
    · cases hsuperValue :
        (data.superTable.readTraceResultRelabeled
          subLogSelectSuperTableTraceSegments
          (GenericSelect.selectSuperSlot idx data.superStride)).value with
      | none =>
          simp [data, hsuperValue] at hmem
      | some super =>
          by_cases hlong :
              GenericSelect.relativeSplitSelectEntryIsMarked super = true
          · simp [data, hsuperValue, hlong] at hmem
            rcases hmem with hmem | hmem
            · have hmemRelabeled :
                  event ∈
                    (WordRAM.TraceResult.relabelReadSegmentsWith
                      (WordRAM.tripleSegmentMap
                        subLogSelectLongFlagRankBase
                        subLogSelectDeadSegment)
                      (data.longFlagRankData.rankTraceResult true
                        (GenericSelect.selectSuperSlot idx
                          data.superStride))).trace := by
                simpa [WordRAM.TraceResult.relabelReadSegmentsWith] using
                  (List.mem_map.mpr hmem)
              exact
                WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
                  (data.longFlagRankData.rankTraceResult true
                    (GenericSelect.selectSuperSlot idx data.superStride))
                  (WordRAM.ReadStore.ofStore
                    (data.longFlagRankData.rankRegisterWordRAMStore true))
                  (subLogSelectFromPackedClarkRouteTraceReadStore
                    bits target)
                  (WordRAM.tripleSegmentMap
                    subLogSelectLongFlagRankBase
                    subLogSelectDeadSegment)
                  (by
                    intro segment index
                    simpa [data, WordRAM.ReadStore.ofStore] using
                      subLogSelectTraceReadStore_longFlagRank_read
                        bits target segment index)
                  (data.longFlagRankData.rankTraceResult_matchesReadStore
                    true
                    (GenericSelect.selectSuperSlot idx data.superStride))
                  event hmemRelabeled
            · exact
                GenericSelect.relativeOffsetReadTraceResultRelabeled_matchesReadStore
                  subLogSelectLongRelativeSegment
                  subLogSelectDeadSegment
                  data.longSuperRelativeTable
                  (subLogSelectFromPackedClarkRouteTraceReadStore
                    bits target)
                  (by
                    intro segment index
                    simpa [data] using
                      subLogSelectTraceReadStore_longRelative_read
                        bits target segment index)
                  (GenericSelect.relativeSplitSelectEntryBasePosition
                    data.wordSize super)
                  (GenericSelect.relativeSplitSelectLongCompactSlot
                    (data.longFlagRankData.rankTraceResult true
                      (GenericSelect.selectSuperSlot idx
                        data.superStride)).value
                    (idx - super.baseOccurrence)
                    data.superStride)
                  event hmem
          · simp [data, hsuperValue, hlong] at hmem
            let localSlot :=
              GenericSelect.relativeSplitSelectLocalSlot idx
                data.superStride data.localSlotsPerSuper
                data.localStride super
            rcases hmem with hmem | hmem
            · exact
                data.localTable.readTraceResultRelabeled_matchesReadStore
                  subLogSelectLocalTableTraceSegments
                  (subLogSelectFromPackedClarkRouteTraceReadStore
                    bits target)
                  (by
                    intro segment index
                    simpa [data] using
                      subLogSelectTraceReadStore_local_baseOccurrence_read
                        bits target segment index)
                  (by
                    intro segment index
                    simpa [data] using
                      subLogSelectTraceReadStore_local_baseWordIndex_read
                        bits target segment index)
                  (by
                    intro segment index
                    simpa [data] using
                      subLogSelectTraceReadStore_local_rankBefore_read
                        bits target segment index)
                  (by
                    intro segment index
                    simpa [data] using
                      subLogSelectTraceReadStore_local_firstOffset_read
                        bits target segment index)
                  localSlot event hmem
            · cases hlocalValue :
                (data.localTable.readTraceResultRelabeled
                  subLogSelectLocalTableTraceSegments localSlot).value with
              | none =>
                  simp [data, hlocalValue, localSlot] at hmem
              | some loc =>
                  by_cases hsparse :
                      GenericSelect.relativeSplitSelectEntryIsMarked loc =
                        true
                  · exact
                      data.sparseDirectory.readTraceResultRelabeled_matchesReadStore
                        subLogSelectSparseDirectoryTraceSegments
                        (subLogSelectFromPackedClarkRouteTraceReadStore
                          bits target)
                        (by
                          intro segment index
                          simpa [data] using
                            subLogSelectTraceReadStore_sparseRank_read
                              bits target segment index)
                        (by
                          intro segment index
                          simpa [data] using
                            subLogSelectTraceReadStore_sparseRelative_read
                              bits target segment index)
                        (GenericSelect.relativeSplitSelectLocalBasePosition
                          data.wordSize super loc)
                        localSlot
                        (idx -
                          GenericSelect.relativeSplitSelectLocalBaseOccurrence
                            super loc)
                        event
                        (by
                          simpa [data, hlocalValue, hsparse, localSlot]
                            using hmem)
                  · exact
                      subLogDenseTwoWordSelectTraceResult_matchesReadStore
                        target bits
                        (GenericSelect.relativeSplitSelectLocalBasePosition
                          data.wordSize super loc)
                        (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                          super loc)
                        idx event
                        (by
                          simpa [data, hlocalValue, hsparse, localSlot]
                            using hmem)
  · intro event hmem
    simp [hvalid] at hmem

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

/-- Trace-result packed-Clark route-field read. -/
def fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    WordRAM.TraceResult (Option FixedWeightSubLogClarkSelectRouteFields) :=
  WordRAM.TraceResult.map
    (fun pos? =>
      pos?.map
        (fixedWeightSubLogSelectRouteFieldsOfPosition
          bits target occurrence))
    (subLogPackedClarkSelectTraceResult bits target occurrence)

theorem fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult
      bits target occurrence).toCosted =
        fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted
          bits target occurrence := by
  simp [fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult,
    fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted,
    subLogPackedClarkSelectTraceResult_refines_interpretedCosted,
    WordRAM.TraceResult.map_toCosted, Costed.map]

theorem fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    forall event,
      event ∈
          (fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult
            bits target occurrence).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult
  apply WordRAM.TraceResult.map_trace_forall
  exact subLogPackedClarkSelectTraceResult_matchesReadStore
    bits target occurrence

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

/-- Trace-result select query for the public packed-Clark compressed/FID path. -/
def subLogSelectFromPackedClarkRouteTraceResult
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult
      bits target occurrence)
    fun fields? =>
      match fields? with
      | none => WordRAM.TraceResult.pure none
      | some fields =>
          subLogSelectWithFieldsTraceResult bits target fields

theorem subLogSelectFromPackedClarkRouteTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromPackedClarkRouteTraceResult
      bits target occurrence).toCosted =
        subLogSelectFromPackedClarkRouteInterpretedCosted
          bits target occurrence := by
  unfold subLogSelectFromPackedClarkRouteTraceResult
    subLogSelectFromPackedClarkRouteInterpretedCosted
  rw [WordRAM.TraceResult.bind_toCosted]
  rw [fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult_refines_interpretedCosted]
  cases hfields :
      (fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted
        bits target occurrence).value with
  | none =>
      simp [Costed.bind, Costed.pure, hfields,
        WordRAM.TraceResult.pure_toCosted]
  | some fields =>
      simp [Costed.bind, hfields]
      have hchild :=
        subLogSelectWithFieldsTraceResult_refines_interpretedCosted
          bits target fields
      constructor
      · simpa [WordRAM.TraceResult.toCosted] using
          congrArg Costed.value hchild
      · simpa [WordRAM.TraceResult.toCosted,
          WordRAM.TraceResult.steps] using
          congrArg Costed.cost hchild

theorem subLogSelectFromPackedClarkRouteTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    forall event,
      event ∈
          (subLogSelectFromPackedClarkRouteTraceResult
            bits target occurrence).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogSelectFromPackedClarkRouteTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult_matchesReadStore
        bits target occurrence
  · cases hfields :
      (fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult
        bits target occurrence).value with
    | none =>
        simp
    | some fields =>
        simpa [hfields] using
          subLogSelectWithFieldsTraceResult_matchesReadStore
            bits target fields

theorem subLogSelectFromPackedClarkRouteTraceResult_event_read_or_primitive
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    forall event,
      event ∈
          (subLogSelectFromPackedClarkRouteTraceResult
            bits target occurrence).trace ->
        event.isReadWord \/ event.isWordPrimitive := by
  intro event _hmem
  exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event

/--
Execution-story packet for the select leg of the compressed/FID sub-log path.

The trace first reads the charged packed-Clark route directory, then performs
the constant local fixed-weight block decode through code/length/class/shared
decoder payload reads.
-/
theorem subLogSelectFromPackedClarkRouteTraceResult_execution_story
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromPackedClarkRouteTraceResult
      bits target occurrence).toCosted =
        subLogSelectFromPackedClarkRouteInterpretedCosted
          bits target occurrence /\
      (subLogSelectFromPackedClarkRouteTraceResult
        bits target occurrence).toCosted =
        subLogSelectFromPackedClarkRouteCosted bits target occurrence /\
      (forall event,
        event ∈
            (subLogSelectFromPackedClarkRouteTraceResult
              bits target occurrence).trace ->
          event.isReadWord \/ event.isWordPrimitive) /\
      (forall event,
        event ∈
            (subLogSelectFromPackedClarkRouteTraceResult
              bits target occurrence).trace ->
          event.matchesReadStore
            (subLogSelectFromPackedClarkRouteTraceReadStore bits target)) := by
  constructor
  · exact
      subLogSelectFromPackedClarkRouteTraceResult_refines_interpretedCosted
        bits target occurrence
  constructor
  · rw [subLogSelectFromPackedClarkRouteTraceResult_refines_interpretedCosted,
      subLogSelectFromPackedClarkRouteInterpretedCosted_refines]
  constructor
  · exact
      subLogSelectFromPackedClarkRouteTraceResult_event_read_or_primitive
        bits target occurrence
  · exact
      subLogSelectFromPackedClarkRouteTraceResult_matchesReadStore
        bits target occurrence


end RankSelectSpec

end RMQ
