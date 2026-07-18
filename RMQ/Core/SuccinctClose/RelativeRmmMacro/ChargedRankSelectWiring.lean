import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedRankSelectLeafTrace
import RMQ.Core.SuccinctFinal.RAM.Segments

/-!
# Charged chunked rank/select: route-level glue (B3, parallel layer)

Route-level chunked consumers at the accepted route's chunk scale
`c = bpFringeChunkBits shape.bpCode.length`, with every word-size
hypothesis of the M3 exact-value substitutions discharged from the built
structures' own `wordSize_le_machine`-family fields plus the B3 geometry
lemma `machineWordBits_le_8_mul_bpFringeChunkBits`.

This is the parallel layer the M5 atomic swap consumes: the accepted route
consumers (`concreteBPNativeSelectCloseInterpretedCosted`,
`concreteBPNativeRankCloseInterpretedCosted` and their trace twins) are
NOT touched here.  The rank-close leg additionally gets its chunked global
word trace against the canonical reviewer/global read store now (all of
its segments — 17/18/19 for the samples and 21 for the chunk table —
already exist); the select-close global trace lands with the M5 store
extension, which introduces the select-table segment 22.
-/

namespace RMQ

namespace SuccinctFinal

/-! ## Shape-level chunk-scale word-size bounds -/

theorem concreteBPNativeSelectCloseData_wordSize_le_8_chunk
    (shape : Cartesian.CartesianShape) :
    (GenericSelect.sparseExceptionSelectData shape.bpCode false).wordSize <=
      8 * SuccinctClose.bpFringeChunkBits shape.bpCode.length :=
  Nat.le_trans
    (GenericSelect.sparseExceptionSelectData
      shape.bpCode false).wordSize_le_machine
    (SuccinctClose.machineWordBits_le_8_mul_bpFringeChunkBits
      shape.bpCode.length)

theorem concreteBPNativeSelectCloseLongFlagRank_wordSize_le_8_chunk
    (shape : Cartesian.CartesianShape) :
    (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).longFlagRankData.wordSize <=
      8 * SuccinctClose.bpFringeChunkBits shape.bpCode.length :=
  Nat.le_trans
    (GenericSelect.sparseExceptionSelectData
      shape.bpCode false).longFlagRank_wordSize_le_machine
    (SuccinctClose.machineWordBits_le_8_mul_bpFringeChunkBits
      shape.bpCode.length)

theorem concreteBPNativeSelectCloseSparseRank_wordSize_le_8_chunk
    (shape : Cartesian.CartesianShape) :
    (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).sparseDirectory.rankData.wordSize <=
      8 * SuccinctClose.bpFringeChunkBits shape.bpCode.length :=
  Nat.le_trans
    (GenericSelect.sparseExceptionSelectData
      shape.bpCode false).sparseDirectory.rank_wordSize_le_machine
    (SuccinctClose.machineWordBits_le_8_mul_bpFringeChunkBits
      shape.bpCode.length)

theorem concreteBPNativeRankCloseData_wordSize_le_8_chunk
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).wordSize <=
      8 * SuccinctClose.bpFringeChunkBits shape.bpCode.length :=
  Nat.le_trans
    (builtRelativeSplitBPCloseRankData shape).wordSize_le_machine
    (SuccinctClose.machineWordBits_le_8_mul_bpFringeChunkBits
      shape.bpCode.length)

/-! ## Chunked route Costed consumers (parallel) -/

/--
Chunked route select-close execution at the route chunk scale (parallel
consumer; the M5 swap point for
`concreteBPNativeSelectCloseInterpretedCosted`).
-/
def concreteBPNativeChunkedSelectCloseCosted
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    Costed (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    |>.bpChunkedSelectCosted
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) idx

theorem concreteBPNativeChunkedSelectCloseCosted_value_eq
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeChunkedSelectCloseCosted shape idx).value =
      ((GenericSelect.sparseExceptionSelectData shape.bpCode
          false).selectCosted idx).value :=
  (GenericSelect.sparseExceptionSelectData
      shape.bpCode false).bpChunkedSelectCosted_value_eq
    (SuccinctClose.bpFringeChunkBits_pos shape.bpCode.length)
    (concreteBPNativeSelectCloseData_wordSize_le_8_chunk shape)
    (concreteBPNativeSelectCloseLongFlagRank_wordSize_le_8_chunk shape)
    (concreteBPNativeSelectCloseSparseRank_wordSize_le_8_chunk shape)
    idx

theorem concreteBPNativeChunkedSelectCloseCosted_cost_le
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeChunkedSelectCloseCosted shape idx).cost <= 35 :=
  (GenericSelect.sparseExceptionSelectData
      shape.bpCode false).bpChunkedSelectCosted_cost_le
    (SuccinctClose.bpFringeChunkBits shape.bpCode.length) idx

theorem concreteBPNativeChunkedSelectCloseCosted_exact
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeChunkedSelectCloseCosted shape idx).erase =
      RMQ.Succinct.select false shape.bpCode idx :=
  (GenericSelect.sparseExceptionSelectData
      shape.bpCode false).bpChunkedSelectCosted_exact
    (SuccinctClose.bpFringeChunkBits_pos shape.bpCode.length)
    (concreteBPNativeSelectCloseData_wordSize_le_8_chunk shape)
    (concreteBPNativeSelectCloseLongFlagRank_wordSize_le_8_chunk shape)
    (concreteBPNativeSelectCloseSparseRank_wordSize_le_8_chunk shape)
    idx

/--
Chunked route rank-close seed at the route chunk scale (parallel
consumer; the M5 swap point for
`concreteBPNativeRankCloseInterpretedCosted`).
-/
def concreteBPNativeChunkedRankCloseCosted
    (shape : Cartesian.CartesianShape) (pos : Nat) : Costed Nat :=
  (builtRelativeSplitBPCloseRankData shape)
    |>.bpChunkedRankCosted
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false pos

theorem concreteBPNativeChunkedRankCloseCosted_value_eq
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeChunkedRankCloseCosted shape pos).value =
      ((builtRelativeSplitBPCloseRankData shape).rankCosted
        false pos).value :=
  (builtRelativeSplitBPCloseRankData shape).bpChunkedRankCosted_value_eq
    (SuccinctClose.bpFringeChunkBits_pos shape.bpCode.length)
    (concreteBPNativeRankCloseData_wordSize_le_8_chunk shape)
    false pos

theorem concreteBPNativeChunkedRankCloseCosted_cost_le
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeChunkedRankCloseCosted shape pos).cost <= 11 :=
  (builtRelativeSplitBPCloseRankData shape).bpChunkedRankCosted_cost_le
    (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false pos

theorem concreteBPNativeChunkedRankCloseCosted_exact
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeChunkedRankCloseCosted shape pos).erase =
      RMQ.Succinct.rankPrefix false shape.bpCode pos :=
  (builtRelativeSplitBPCloseRankData shape).bpChunkedRankCosted_exact
    (SuccinctClose.bpFringeChunkBits_pos shape.bpCode.length)
    (concreteBPNativeRankCloseData_wordSize_le_8_chunk shape)
    false pos

/-! ## Canonical-store agreement facts for the rank-close leg -/

theorem concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseSuper
    (shape : Cartesian.CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        concreteBPNativeRankCloseTraceSegmentBase address =
      ((builtRelativeSplitBPCloseRankData shape).superSampleWords
        false)[address]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    concreteBPNativeRankCloseTraceSegmentBase,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
    WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseBlock
    (shape : Cartesian.CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        (concreteBPNativeRankCloseTraceSegmentBase + 1) address =
      ((builtRelativeSplitBPCloseRankData shape).blockSampleWords
        false)[address]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    concreteBPNativeRankCloseTraceSegmentBase,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
    WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseWord
    (shape : Cartesian.CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        (concreteBPNativeRankCloseTraceSegmentBase + 2) address =
      (builtRelativeSplitBPCloseRankData
        shape).bitWords.store.words[address]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    concreteBPNativeRankCloseTraceSegmentBase,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
    WordRAM.Store.readWord?]

/-! ## Chunked rank-close global word trace (canonical store) -/

/--
Chunked route rank-close trace against the canonical reviewer/global read
store: three sample/word `readWord` events at segments 17/18/19 plus
chunk-table `readWord` events at the fringe chunk segment 21 (parallel;
the M5 swap point for the rank-close trace twins).
-/
def concreteBPNativeChunkedRankCloseGlobalWordTraceResult
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    WordRAM.TraceResult Nat :=
  (builtRelativeSplitBPCloseRankData shape)
    |>.bpChunkedRankTraceResultWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      concreteBPNativeRankCloseTraceSegmentBase
      (concreteBPNativeRankCloseTraceSegmentBase + 1)
      (concreteBPNativeRankCloseTraceSegmentBase + 2)
      concreteBPNativeFringeChunkTraceSegment
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false pos

theorem concreteBPNativeChunkedRankCloseGlobalWordTraceResult_refines
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeChunkedRankCloseGlobalWordTraceResult
        shape pos).toCosted =
      concreteBPNativeChunkedRankCloseCosted shape pos :=
  (builtRelativeSplitBPCloseRankData
      shape).bpChunkedRankTraceResultWithStore_toCosted_of_agree
    (concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseSuper shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseBlock shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseWord shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable shape)
    pos

theorem concreteBPNativeChunkedRankCloseGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeChunkedRankCloseGlobalWordTraceResult
            shape pos).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) :=
  (builtRelativeSplitBPCloseRankData
      shape).bpChunkedRankTraceResultWithStore_matchesReadStore
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    concreteBPNativeRankCloseTraceSegmentBase
    (concreteBPNativeRankCloseTraceSegmentBase + 1)
    (concreteBPNativeRankCloseTraceSegmentBase + 2)
    concreteBPNativeFringeChunkTraceSegment
    (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false pos

theorem concreteBPNativeChunkedRankCloseGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeChunkedRankCloseGlobalWordTraceResult
            shape pos).trace ->
        Not event.isSyntheticCostOnlyPrimitive :=
  (builtRelativeSplitBPCloseRankData
      shape).bpChunkedRankTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    concreteBPNativeRankCloseTraceSegmentBase
    (concreteBPNativeRankCloseTraceSegmentBase + 1)
    (concreteBPNativeRankCloseTraceSegmentBase + 2)
    concreteBPNativeFringeChunkTraceSegment
    (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false pos

/--
Vocabulary fact for the chunked rank-close leg: every event of the
chunked rank-close global word trace is a `readWord` (no `wordRank`, no
`wordSelect`, no synthetic marker).  This is the rank-leg component of
the B3 whole-query vocabulary theorem (REQ-B3-10); the whole-query
statement lands with the M5 swap.
-/
theorem concreteBPNativeChunkedRankCloseGlobalWordTraceResult_events_readWord
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeChunkedRankCloseGlobalWordTraceResult
            shape pos).trace ->
        event.isReadWord := by
  apply
    (builtRelativeSplitBPCloseRankData
        shape).bpChunkedRankTraceResultWithStore_trace_forall
  · intro address
    trivial
  · intro address
    trivial
  · intro address
    trivial
  · intro address _hlt
    trivial

/-! ## Canonical-store per-address agreement facts for the select-close leg -/

theorem concreteBPNativeSuccinctRMQGlobalReadStore_selectBitWords
    (shape : Cartesian.CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase address =
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).bitWords.store.words[address]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    concreteBPNativeSelectCloseTraceSegmentLayout,
    SuccinctSpace.PayloadWordStore.wordRAMStore,
    WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagSuper
    (shape : Cartesian.CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
        address =
      ((GenericSelect.sparseExceptionSelectData
        shape.bpCode false).longFlagRankData.superSampleWords
          true)[address]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    concreteBPNativeSelectCloseTraceSegmentLayout,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
    WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagBlock
    (shape : Cartesian.CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        (concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase + 1)
        address =
      ((GenericSelect.sparseExceptionSelectData
        shape.bpCode false).longFlagRankData.blockSampleWords
          true)[address]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    concreteBPNativeSelectCloseTraceSegmentLayout,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
    WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagWord
    (shape : Cartesian.CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        (concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase + 2)
        address =
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode
          false).longFlagRankData.bitWords.store.words[address]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    concreteBPNativeSelectCloseTraceSegmentLayout,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
    WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_selectLongRelative
    (shape : Cartesian.CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
        address =
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode
          false).longSuperRelativeTable.store.words[address]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    concreteBPNativeSelectCloseTraceSegmentLayout,
    SuccinctSpace.FixedWidthNatTable.wordRAMStore,
    SuccinctSpace.PayloadWordStore.wordRAMStore,
    WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankSuper
    (shape : Cartesian.CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
        address =
      ((GenericSelect.sparseExceptionSelectData
        shape.bpCode
          false).sparseDirectory.rankData.superSampleWords
          true)[address]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    concreteBPNativeSelectCloseTraceSegmentLayout,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
    WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankBlock
    (shape : Cartesian.CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        (concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase +
          1)
        address =
      ((GenericSelect.sparseExceptionSelectData
        shape.bpCode
          false).sparseDirectory.rankData.blockSampleWords
          true)[address]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    concreteBPNativeSelectCloseTraceSegmentLayout,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
    WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankWord
    (shape : Cartesian.CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        (concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase +
          2)
        address =
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode
          false).sparseDirectory.rankData.bitWords.store.words[address]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    concreteBPNativeSelectCloseTraceSegmentLayout,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
    WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRelative
    (shape : Cartesian.CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.relativeBase
        address =
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode
          false).sparseDirectory.relativeTable.store.words[address]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    concreteBPNativeSelectCloseTraceSegmentLayout,
    SuccinctSpace.FixedWidthNatTable.wordRAMStore,
    SuccinctSpace.PayloadWordStore.wordRAMStore,
    WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_routeSelectChunkTable
    (shape : Cartesian.CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        concreteBPNativeSelectChunkTraceSegment address =
      (SuccinctClose.bpChunkSelectTable
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        false).store.words[address]? :=
  concreteBPNativeSuccinctRMQGlobalReadStore_selectChunkTable shape address

/-! ## Canonical-store pullback facts for the accepted entry tables -/

section SelectClosePullbacks

variable (shape : Cartesian.CartesianShape)

theorem concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superBaseOccurrence :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseOccurrence
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).superTable.baseOccurrenceTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superBaseWordIndex :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseWordIndex
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).superTable.baseWordIndexTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superRankBefore :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.rankBefore
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).superTable.rankBeforeTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superFirstOffset :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.firstOffset
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).superTable.firstOffsetTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localBaseOccurrence :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseOccurrence
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).localTable.baseOccurrenceTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localBaseWordIndex :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseWordIndex
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).localTable.baseWordIndexTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localRankBefore :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.rankBefore
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).localTable.rankBeforeTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

theorem concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localFirstOffset :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.firstOffset
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).localTable.firstOffsetTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

end SelectClosePullbacks

/-! ## readWord-only vocabulary helpers for the accepted entry-table reads -/

theorem concreteBPNativeOfProgramWithStore_natTableRead_events_readWord
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (segmentMap : Nat -> Nat) (store : WordRAM.ReadStore) (i : Nat) :
    forall event,
      List.Mem event
          (WordRAM.TraceResult.ofProgramWithStore segmentMap store
            (table.readProgram i)).trace ->
        event.isReadWord := by
  intro event hmem
  simp only [WordRAM.TraceResult.ofProgramWithStore,
    WordRAM.TraceResult.relabelReadSegmentsWith_trace,
    WordRAM.TraceResult.ofResult_trace] at hmem
  rcases List.mem_map.mp hmem with ⟨inner, hinner, rfl⟩
  rw [WordRAM.TraceEvent.relabelReadSegmentWith_isReadWord]
  simp only [SuccinctSpace.FixedWidthNatTable.readProgram,
    SuccinctSpace.PayloadWordStore.readProgram,
    WordRAM.Program.evalR, List.mem_singleton] at hinner
  subst inner
  trivial

theorem concreteBPNativeSelectEntryTableWithStore_events_readWord
    {entries : List GenericSelect.SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (store : WordRAM.ReadStore) (i : Nat) :
    forall event,
      List.Mem event
          (table.readTraceResultRelabeledWithStore layout store i).trace ->
        event.isReadWord := by
  unfold
    GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readTraceResultRelabeledWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      concreteBPNativeOfProgramWithStore_natTableRead_events_readWord
        table.baseOccurrenceTable _ store i
  · intro baseOccurrence?
    apply WordRAM.TraceResult.bind_trace_forall
    · exact
        concreteBPNativeOfProgramWithStore_natTableRead_events_readWord
          table.baseWordIndexTable _ store i
    · intro baseWordIndex?
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          concreteBPNativeOfProgramWithStore_natTableRead_events_readWord
            table.rankBeforeTable _ store i
      · intro rankBefore?
        apply WordRAM.TraceResult.map_trace_forall
        exact
          concreteBPNativeOfProgramWithStore_natTableRead_events_readWord
            table.firstOffsetTable _ store i

/-! ## Chunked select-close global word trace (canonical store) -/

/--
Chunked route select-close trace against the canonical reviewer/global read
store: accepted entry-table `readWord`s at their existing segments, chunked
flag-rank and dense legs with chunk-table `readWord`s at segment 21, and
select-table `readWord`s at the new segment 22 (the M5 swap point for the
select-close trace twins).
-/
def concreteBPNativeChunkedSelectCloseGlobalWordTraceResult
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    |>.bpChunkedSelectTraceResultWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) idx

theorem concreteBPNativeChunkedSelectCloseGlobalWordTraceResult_refines
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeChunkedSelectCloseGlobalWordTraceResult
        shape idx).toCosted =
      concreteBPNativeChunkedSelectCloseCosted shape idx :=
  (GenericSelect.sparseExceptionSelectData
      shape.bpCode false).bpChunkedSelectTraceResultWithStore_toCosted_of_agree
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superBaseOccurrence
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superBaseWordIndex
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superRankBefore
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superFirstOffset
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localBaseOccurrence
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localBaseWordIndex
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localRankBefore
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localFirstOffset
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagSuper shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagBlock shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagWord shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_selectLongRelative shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankSuper shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankBlock shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankWord shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRelative shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_selectBitWords shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_routeSelectChunkTable shape)
    idx

theorem concreteBPNativeChunkedSelectCloseGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeChunkedSelectCloseGlobalWordTraceResult
            shape idx).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) :=
  (GenericSelect.sparseExceptionSelectData
      shape.bpCode false).bpChunkedSelectTraceResultWithStore_matchesReadStore
    concreteBPNativeSelectCloseTraceSegmentLayout
    concreteBPNativeFringeChunkTraceSegment
    concreteBPNativeSelectChunkTraceSegment
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (SuccinctClose.bpFringeChunkBits shape.bpCode.length) idx

theorem concreteBPNativeChunkedSelectCloseGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeChunkedSelectCloseGlobalWordTraceResult
            shape idx).trace ->
        Not event.isSyntheticCostOnlyPrimitive :=
  (GenericSelect.sparseExceptionSelectData
      shape.bpCode
        false).bpChunkedSelectTraceResultWithStore_no_syntheticCostOnlyPrimitive
    concreteBPNativeSelectCloseTraceSegmentLayout
    concreteBPNativeFringeChunkTraceSegment
    concreteBPNativeSelectChunkTraceSegment
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (SuccinctClose.bpFringeChunkBits shape.bpCode.length) idx

/--
Vocabulary fact for the chunked select-close leg: every event of the
chunked select-close global word trace is a `readWord` (no `wordRank`, no
`wordSelect`, no synthetic marker).  This is the select-leg component of
the B3 whole-query vocabulary theorem (REQ-B3-10).
-/
theorem concreteBPNativeChunkedSelectCloseGlobalWordTraceResult_events_readWord
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeChunkedSelectCloseGlobalWordTraceResult
            shape idx).trace ->
        event.isReadWord := by
  apply
    (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).bpChunkedSelectTraceResultWithStore_trace_forall
  · intro slot
    exact
      concreteBPNativeSelectEntryTableWithStore_events_readWord
        (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).superTable
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) slot
  · intro slot
    apply
      (GenericSelect.sparseExceptionSelectData
          shape.bpCode
            false).longFlagRankData.bpChunkedRankTraceResultWithStore_trace_forall
    · intro address
      trivial
    · intro address
      trivial
    · intro address
      trivial
    · intro address _hlt
      trivial
  · intro base slot
    apply GenericSelect.bpRelativeOffsetReadTraceResultWithStore_trace_forall
    intro address
    trivial
  · intro slot
    exact
      concreteBPNativeSelectEntryTableWithStore_events_readWord
        (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).localTable
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) slot
  · intro base localSlot localOccurrence
    apply
      (GenericSelect.sparseExceptionSelectData
          shape.bpCode
            false).sparseDirectory.bpChunkedReadTraceResultWithStore_trace_forall
    · apply
        (GenericSelect.sparseExceptionSelectData
            shape.bpCode
              false).sparseDirectory.rankData.bpChunkedRankTraceResultWithStore_trace_forall
      · intro address
        trivial
      · intro address
        trivial
      · intro address
        trivial
      · intro address _hlt
        trivial
    · intro slot
      apply
        GenericSelect.bpRelativeOffsetReadTraceResultWithStore_trace_forall
      intro address
      trivial
  · intro basePosition baseOccurrence q
    apply
      GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore_trace_forall
    · intro address
      trivial
    · intro address _hlt
      trivial
    · intro address
      trivial

/--
The chunked in-word select fold actually reads the select chunk table: on
the witness word `[false]` at occurrence `0`, the first chunk's routing
count is `1 > 0`, so the fold's found branch issues a genuine
segment-`22` read of the canonical store (the select-table liveness
witness for `ReviewerSource.selectChunkTable`).
-/
theorem concreteBPNativeChunkedInWordSelect_selectTable_mayRead
    (shape : Cartesian.CartesianShape) :
    ∃ index word?,
      WordRAM.TraceEvent.readWord concreteBPNativeSelectChunkTraceSegment
          index word? ∈
        (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          concreteBPNativeFringeChunkTraceSegment
          concreteBPNativeSelectChunkTraceSegment
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
          false [false] 0).trace := by
  have hcpos : 0 < SuccinctClose.bpFringeChunkBits shape.bpCode.length :=
    SuccinctClose.bpFringeChunkBits_pos shape.bpCode.length
  have hv :=
    SuccinctClose.bpFringeWindowChunkValue_lt
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
      ([false] : List Bool) 0
  have ht :=
    SuccinctClose.bpWordChunkSliceLen_le
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
      ([false] : List Bool).length 0
  have ht1 :
      SuccinctClose.bpWordChunkSliceLen
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        ([false] : List Bool).length 0 = 1 := by
    show Nat.min (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        (([false] : List Bool).length -
          0 * SuccinctClose.bpFringeChunkBits shape.bpCode.length) = 1
    simp only [List.length_singleton, Nat.zero_mul, Nat.sub_zero]
    exact Nat.min_eq_right hcpos
  refine ⟨SuccinctClose.bpChunkSelectSlot
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
      (SuccinctClose.bpFringeWindowChunkValue
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        ([false] : List Bool) 0) 0,
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
      concreteBPNativeSelectChunkTraceSegment
      (SuccinctClose.bpChunkSelectSlot
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        (SuccinctClose.bpFringeWindowChunkValue
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
          ([false] : List Bool) 0) 0), ?_⟩
  have hcount :
      SuccinctClose.bpWordChunkCount
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        ([false] : List Bool).length = 1 := by
    unfold SuccinctClose.bpWordChunkCount
    simp
  unfold SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
  rw [hcount]
  have hreadVal :
      (SuccinctClose.bpChunkReadTraceResult
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          concreteBPNativeFringeChunkTraceSegment
          (SuccinctClose.bpFringeChunkSlot
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
            (SuccinctClose.bpFringeWindowChunkValue
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
              ([false] : List Bool) 0)
            (SuccinctClose.bpWordChunkSliceLen
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
              ([false] : List Bool).length 0)
            (SuccinctClose.bpWordChunkSliceLen
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
              ([false] : List Bool).length 0))).value =
        some
          (SuccinctClose.bpFringeChunkPacked
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
            (SuccinctClose.bpFringeWindowChunkValue
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
              ([false] : List Bool) 0)
            (SuccinctClose.bpWordChunkSliceLen
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
              ([false] : List Bool).length 0)
            (SuccinctClose.bpWordChunkSliceLen
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
              ([false] : List Bool).length 0)) := by
    show
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          concreteBPNativeFringeChunkTraceSegment
          (SuccinctClose.bpFringeChunkSlot _ _ _ _)).map
        SuccinctSpace.bitsToNatLE = _
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable]
    rw [(SuccinctClose.bpFringeChunkTable
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).read_exact]
    exact SuccinctClose.bpFringeChunkEntries_getElem hv ht ht
  have hdecode :
      SuccinctClose.bpChunkRankOfEntry
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false
          (SuccinctClose.bpWordChunkSliceLen
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
            ([false] : List Bool).length 0)
          (SuccinctClose.bpFringeChunkPacked
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
            (SuccinctClose.bpFringeWindowChunkValue
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
              ([false] : List Bool) 0)
            (SuccinctClose.bpWordChunkSliceLen
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
              ([false] : List Bool).length 0)
            (SuccinctClose.bpWordChunkSliceLen
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
              ([false] : List Bool).length 0)) = 1 := by
    rw [SuccinctClose.bpChunkRankOfEntry_packed _ false hv ht]
    have hstep :=
      SuccinctClose.bpWordChunkRank_step
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false
        ([false] : List Bool)
        (e := ([false] : List Bool).length) (Nat.le_refl _) 0
    rw [hstep]
    have hmin1 :
        Nat.min ((0 + 1) *
            SuccinctClose.bpFringeChunkBits shape.bpCode.length)
          ([false] : List Bool).length = 1 := by
      simp only [Nat.zero_add, Nat.one_mul, List.length_singleton]
      exact Nat.min_eq_right hcpos
    have hmin0 :
        Nat.min (0 * SuccinctClose.bpFringeChunkBits shape.bpCode.length)
          ([false] : List Bool).length = 0 := by
      simp
    rw [hmin1, hmin0]
    decide
  show WordRAM.TraceEvent.readWord _ _ _ ∈
    (WordRAM.TraceResult.bind
      (SuccinctClose.bpChunkReadTraceResult
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        concreteBPNativeFringeChunkTraceSegment
        (SuccinctClose.bpFringeChunkSlot
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
          (SuccinctClose.bpFringeWindowChunkValue
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
            ([false] : List Bool) 0)
          (SuccinctClose.bpWordChunkSliceLen
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
            ([false] : List Bool).length 0)
          (SuccinctClose.bpWordChunkSliceLen
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
            ([false] : List Bool).length 0)))
      _).trace
  rw [WordRAM.TraceResult.bind_trace]
  apply List.mem_append_right
  rw [hreadVal]
  dsimp only
  rw [if_pos (by
    simp only [Option.getD_some]
    rw [hdecode]
    omega)]
  rw [WordRAM.TraceResult.map_trace]
  exact List.Mem.head _

/-! ## Base-parameterized chunked rank-close seed store -/

/--
Purpose-built read store for the base-parameterized chunked rank-close
trace: the three rank sample/word components at `rankSegmentBase ..
rankSegmentBase + 2` and the charged fringe chunk table at
`rankSegmentBase + 4`.  The offset `4` is chosen so that the canonical
base `17` places the chunk-table reads at the counted global segment `21`
(`concreteBPNativeFringeChunkTraceSegment`) with no collision at any base.
-/
def concreteBPNativeChunkedRankCloseSeedReadStore
    (shape : Cartesian.CartesianShape) (rankSegmentBase : Nat) :
    WordRAM.ReadStore where
  readWord? segment index :=
    if segment = rankSegmentBase then
      ((builtRelativeSplitBPCloseRankData shape).superSampleWords
        false)[index]?
    else if segment = rankSegmentBase + 1 then
      ((builtRelativeSplitBPCloseRankData shape).blockSampleWords
        false)[index]?
    else if segment = rankSegmentBase + 2 then
      (builtRelativeSplitBPCloseRankData shape).bitWords.store.words[index]?
    else if segment = rankSegmentBase + 4 then
      (SuccinctClose.bpFringeChunkTable
        (SuccinctClose.bpFringeChunkBits
          shape.bpCode.length)).store.words[index]?
    else
      none

theorem concreteBPNativeChunkedRankCloseSeedReadStore_super
    (shape : Cartesian.CartesianShape) (rankSegmentBase address : Nat) :
    (concreteBPNativeChunkedRankCloseSeedReadStore
        shape rankSegmentBase).readWord? rankSegmentBase address =
      ((builtRelativeSplitBPCloseRankData shape).superSampleWords
        false)[address]? := by
  simp [concreteBPNativeChunkedRankCloseSeedReadStore]

theorem concreteBPNativeChunkedRankCloseSeedReadStore_block
    (shape : Cartesian.CartesianShape) (rankSegmentBase address : Nat) :
    (concreteBPNativeChunkedRankCloseSeedReadStore
        shape rankSegmentBase).readWord? (rankSegmentBase + 1) address =
      ((builtRelativeSplitBPCloseRankData shape).blockSampleWords
        false)[address]? := by
  simp [concreteBPNativeChunkedRankCloseSeedReadStore]

theorem concreteBPNativeChunkedRankCloseSeedReadStore_word
    (shape : Cartesian.CartesianShape) (rankSegmentBase address : Nat) :
    (concreteBPNativeChunkedRankCloseSeedReadStore
        shape rankSegmentBase).readWord? (rankSegmentBase + 2) address =
      (builtRelativeSplitBPCloseRankData
        shape).bitWords.store.words[address]? := by
  simp [concreteBPNativeChunkedRankCloseSeedReadStore]

theorem concreteBPNativeChunkedRankCloseSeedReadStore_chunk
    (shape : Cartesian.CartesianShape) (rankSegmentBase address : Nat) :
    (concreteBPNativeChunkedRankCloseSeedReadStore
        shape rankSegmentBase).readWord? (rankSegmentBase + 4) address =
      (SuccinctClose.bpFringeChunkTable
        (SuccinctClose.bpFringeChunkBits
          shape.bpCode.length)).store.words[address]? := by
  simp [concreteBPNativeChunkedRankCloseSeedReadStore]

end SuccinctFinal

end RMQ
