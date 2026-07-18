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

end SuccinctFinal

end RMQ
