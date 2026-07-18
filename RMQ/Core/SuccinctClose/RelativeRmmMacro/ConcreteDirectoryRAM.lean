import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectory
import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorRAM
import RMQ.Core.SuccinctSpace.RankSelectRAM

/-!
# Word-RAM rank-seed bridge for compact BP close/LCA

This module connects the concrete compact close/LCA directory to the
interpreter-backed stored-word rank leaf.  The existing seeded close wrapper is
kept unchanged; the rank callback it consumes is now built directly from
`PayloadLiveStoredWordRankData.rankProgramClamped` and the corresponding
payload-only Word-RAM store.
-/

namespace RMQ
namespace SuccinctClose

open SuccinctSpace
open RMQ.WordRAM.Register

namespace ConcreteCompactBPCloseLCADirectory

/-- The chunked BP payload store used by local BP decoder traces. -/
def bpCodeWordStore (shape : Cartesian.CartesianShape) :
    SuccinctSpace.BoundedPayloadWordStore shape.bpCode
      (SuccinctRank.machineWordBits shape.bpCode.length) :=
  SuccinctSpace.BoundedPayloadWordStore.ofChunks shape.bpCode
    (SuccinctRank.machineWordBits_pos shape.bpCode.length)

/-- Trace event for reading one BP payload word from the chunked BP code. -/
def bpCodeReadWordTraceEvent
    (shape : Cartesian.CartesianShape) (index : Nat) : WordRAM.TraceEvent :=
  WordRAM.TraceEvent.readWord 0 index
    ((SuccinctSpace.chunkPayloadWords
      (SuccinctRank.machineWordBits shape.bpCode.length)
      shape.bpCode).toArray[index]?)

/-- A payload-word trace for one BP code word. -/
def bpCodeWordReadTraceResult
    (shape : Cartesian.CartesianShape) (index : Nat) :
    WordRAM.TraceResult (List (List Bool)) where
  value :=
    payloadWordReadOfGet?
      (SuccinctSpace.chunkPayloadWords
        (SuccinctRank.machineWordBits shape.bpCode.length)
        shape.bpCode).toArray index
  trace := [bpCodeReadWordTraceEvent shape index]

theorem bpCodeWordReadTraceResult_value
    (shape : Cartesian.CartesianShape) (index : Nat) :
    (bpCodeWordReadTraceResult shape index).value =
      payloadWordReadOfGet?
        (SuccinctSpace.chunkPayloadWords
          (SuccinctRank.machineWordBits shape.bpCode.length)
          shape.bpCode).toArray index := by
  rfl

theorem bpCodeWordReadTraceResult_event_value
    (shape : Cartesian.CartesianShape) (index : Nat) :
    (bpCodeReadWordTraceEvent shape index) =
      WordRAM.TraceEvent.readWord 0 index
      (SuccinctSpace.chunkPayloadWords
        (SuccinctRank.machineWordBits shape.bpCode.length)
        shape.bpCode).toArray[index]? := by
  rfl

theorem bpCodeWordReadTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (index : Nat)
    (store : WordRAM.ReadStore)
    (hread :
      store.readWord? 0 index =
        (SuccinctSpace.chunkPayloadWords
          (SuccinctRank.machineWordBits shape.bpCode.length)
          shape.bpCode).toArray[index]?) :
    forall event,
      event ∈ (bpCodeWordReadTraceResult shape index).trace ->
        event.matchesReadStore store := by
  intro event hmem
  simp [bpCodeWordReadTraceResult, bpCodeReadWordTraceEvent,
    WordRAM.TraceEvent.matchesReadStore] at hmem ⊢
  subst event
  simpa using hread

theorem bpCodeWordReadTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (index : Nat) :
    forall event,
      event ∈ (bpCodeWordReadTraceResult shape index).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  intro event hmem
  simp [bpCodeWordReadTraceResult, bpCodeReadWordTraceEvent,
    WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive] at hmem ⊢
  subst event
  simp

/--
Trace-preserving read of the four BP payload words that cover a local BP block.

Missing boundary words contribute no payload word to the value but still count
as one attempted payload read in the trace.
-/
def localBPBlockWordsTraceResult
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : WordRAM.TraceResult (List (List Bool)) :=
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  let firstWord :=
    blockStartOf blockSize (blockOfClose blockSize close) / wordSize
  WordRAM.TraceResult.bind (bpCodeWordReadTraceResult shape firstWord)
    fun w0 =>
      WordRAM.TraceResult.bind
        (bpCodeWordReadTraceResult shape (firstWord + 1))
        fun w1 =>
          WordRAM.TraceResult.bind
            (bpCodeWordReadTraceResult shape (firstWord + 2))
            fun w2 =>
              WordRAM.TraceResult.map
                (fun w3 => w0 ++ w1 ++ w2 ++ w3)
                (bpCodeWordReadTraceResult shape (firstWord + 3))

theorem flatten_localBPBlockWordsTraceResult_value
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    SuccinctSpace.flattenPayloadWords
        (localBPBlockWordsTraceResult shape blockSize close).value =
      SuccinctSpace.flattenPayloadWords
        (localBPBlockWordsRead shape blockSize close) := by
  unfold localBPBlockWordsTraceResult localBPBlockWordsRead
    bpCodeWordReadTraceResult bpCodeWordReadsAt payloadWordReadOfGet?
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure, SuccinctSpace.flattenPayloadWords_append]

theorem localBPBlockWordsTraceResult_cost
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    (localBPBlockWordsTraceResult shape blockSize close).trace.length = 4 := by
  unfold localBPBlockWordsTraceResult bpCodeWordReadTraceResult
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure]

theorem localBPBlockWordsTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat)
    (store : WordRAM.ReadStore)
    (hread :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?) :
    forall event,
      event ∈ (localBPBlockWordsTraceResult shape blockSize close).trace ->
        event.matchesReadStore store := by
  intro event hmem
  unfold localBPBlockWordsTraceResult bpCodeWordReadTraceResult
    bpCodeReadWordTraceEvent at hmem
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure, WordRAM.TraceEvent.matchesReadStore] at hmem ⊢
  rcases hmem with hmem | hmem | hmem | hmem
  · subst event
    simpa using
      hread
        (blockStartOf blockSize (blockOfClose blockSize close) /
          SuccinctRank.machineWordBits shape.bpCode.length)
  · subst event
    simpa using
      hread
        (blockStartOf blockSize (blockOfClose blockSize close) /
          SuccinctRank.machineWordBits shape.bpCode.length + 1)
  · subst event
    simpa using
      hread
        (blockStartOf blockSize (blockOfClose blockSize close) /
          SuccinctRank.machineWordBits shape.bpCode.length + 2)
  · subst event
    simpa using
      hread
        (blockStartOf blockSize (blockOfClose blockSize close) /
          SuccinctRank.machineWordBits shape.bpCode.length + 3)

theorem localBPBlockWordsTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    forall event,
      event ∈ (localBPBlockWordsTraceResult shape blockSize close).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold localBPBlockWordsTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpCodeWordReadTraceResult_no_syntheticCostOnlyPrimitive shape
        (blockStartOf blockSize (blockOfClose blockSize close) /
          SuccinctRank.machineWordBits shape.bpCode.length)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        bpCodeWordReadTraceResult_no_syntheticCostOnlyPrimitive shape
          (blockStartOf blockSize (blockOfClose blockSize close) /
            SuccinctRank.machineWordBits shape.bpCode.length + 1)
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          bpCodeWordReadTraceResult_no_syntheticCostOnlyPrimitive shape
            (blockStartOf blockSize (blockOfClose blockSize close) /
              SuccinctRank.machineWordBits shape.bpCode.length + 2)
      · apply WordRAM.TraceResult.map_trace_forall
        exact
          bpCodeWordReadTraceResult_no_syntheticCostOnlyPrimitive shape
            (blockStartOf blockSize (blockOfClose blockSize close) /
              SuccinctRank.machineWordBits shape.bpCode.length + 3)

/-- Trace-preserving local BP window bits, derived from four payload reads. -/
def localBPWindowBitsTraceResult
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : WordRAM.TraceResult (List Bool) :=
  WordRAM.TraceResult.map SuccinctSpace.flattenPayloadWords
    (localBPBlockWordsTraceResult shape blockSize close)

theorem localBPWindowBitsTraceResult_value
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    (localBPWindowBitsTraceResult shape blockSize close).value =
      localBPWindowBits shape blockSize close := by
  unfold localBPWindowBitsTraceResult
  rw [WordRAM.TraceResult.map_value]
  rw [flatten_localBPBlockWordsTraceResult_value]
  exact (localBPWindowBits_eq_flatten_localBPBlockWordsRead
    shape blockSize close).symm

theorem localBPWindowBitsTraceResult_cost
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    (localBPWindowBitsTraceResult shape blockSize close).trace.length = 4 := by
  unfold localBPWindowBitsTraceResult
  simp [localBPBlockWordsTraceResult_cost]

theorem localBPWindowBitsTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat)
    (store : WordRAM.ReadStore)
    (hread :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?) :
    forall event,
      event ∈ (localBPWindowBitsTraceResult shape blockSize close).trace ->
        event.matchesReadStore store := by
  unfold localBPWindowBitsTraceResult
  exact WordRAM.TraceResult.map_trace_forall
    (fun event => event.matchesReadStore store)
    SuccinctSpace.flattenPayloadWords
    (localBPBlockWordsTraceResult shape blockSize close)
    (localBPBlockWordsTraceResult_matchesReadStore
      shape blockSize close store hread)

theorem localBPWindowBitsTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    forall event,
      event ∈ (localBPWindowBitsTraceResult shape blockSize close).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold localBPWindowBitsTraceResult
  exact WordRAM.TraceResult.map_trace_forall
    (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
    _ _
    (localBPBlockWordsTraceResult_no_syntheticCostOnlyPrimitive
      shape blockSize close)

/-- Structural trace for the seeded left endpoint-fringe decoder. -/
def localBPLeftFringeCandidateSeededTraceResult
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose seed : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let base := localBPWindowBase shape blockSize leftClose
  let count :=
    blockStartOf blockSize (blockOfClose blockSize leftClose) +
      blockSize - leftClose
  WordRAM.TraceResult.map
    (fun window =>
      some
        (localBPSeededPrefixRangeMinExcess window seed base
          (leftClose + 1) count,
          localBPSeededPrefixRangeArgMinPrefixPos window seed base
            (leftClose + 1) count))
    (localBPWindowBitsTraceResult shape blockSize leftClose)

theorem localBPLeftFringeCandidateSeededTraceResult_refines
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose seed : Nat) :
    (localBPLeftFringeCandidateSeededTraceResult
      shape blockSize leftClose seed).toCosted =
      localBPLeftFringeCandidateSeededCosted
        shape blockSize leftClose seed := by
  apply Costed.ext
  · unfold localBPLeftFringeCandidateSeededTraceResult
      localBPLeftFringeCandidateSeededCosted
    simp [WordRAM.TraceResult.map_toCosted, Costed.map,
      localBPWindowBitsTraceResult_value]
  · unfold localBPLeftFringeCandidateSeededTraceResult
      localBPLeftFringeCandidateSeededCosted
    simp [WordRAM.TraceResult.map_toCosted, Costed.map,
      localBPWindowBitsTraceResult_cost]

/-- Structural trace for the seeded right endpoint-fringe decoder. -/
def localBPRightFringeCandidateSeededTraceResult
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose seed : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let base := localBPWindowBase shape blockSize rightClose
  let start := blockStartOf blockSize (blockOfClose blockSize rightClose)
  let count := rightClose - start + 2
  WordRAM.TraceResult.map
    (fun window =>
      some
        (localBPSeededPrefixRangeMinExcess window seed base start count,
          localBPSeededPrefixRangeArgMinPrefixPos window seed base start count))
    (localBPWindowBitsTraceResult shape blockSize rightClose)

theorem localBPRightFringeCandidateSeededTraceResult_refines
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose seed : Nat) :
    (localBPRightFringeCandidateSeededTraceResult
      shape blockSize rightClose seed).toCosted =
      localBPRightFringeCandidateSeededCosted
        shape blockSize rightClose seed := by
  apply Costed.ext
  · unfold localBPRightFringeCandidateSeededTraceResult
      localBPRightFringeCandidateSeededCosted
    simp [WordRAM.TraceResult.map_toCosted, Costed.map,
      localBPWindowBitsTraceResult_value]
  · unfold localBPRightFringeCandidateSeededTraceResult
      localBPRightFringeCandidateSeededCosted
    simp [WordRAM.TraceResult.map_toCosted, Costed.map,
      localBPWindowBitsTraceResult_cost]

/-- Structural trace for the seeded same-block local BP decoder. -/
def localBPSameBlockCloseSeededTraceResult
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose seed : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  let base := localBPWindowBase shape blockSize leftClose
  let start := leftClose + 1
  let count := rightClose - leftClose + 1
  WordRAM.TraceResult.map
    (fun window =>
      bpCandidateClose?
        (some
          (localBPSeededPrefixRangeMinExcess window seed base start count,
            localBPSeededPrefixRangeArgMinPrefixPos window seed base
              start count)))
    (localBPWindowBitsTraceResult shape blockSize leftClose)

theorem localBPSameBlockCloseSeededTraceResult_refines
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose seed : Nat) :
    (localBPSameBlockCloseSeededTraceResult
      shape blockSize leftClose rightClose seed).toCosted =
      localBPSameBlockCloseSeededCosted
        shape blockSize leftClose rightClose seed := by
  apply Costed.ext
  · unfold localBPSameBlockCloseSeededTraceResult
      localBPSameBlockCloseSeededCosted
    simp [WordRAM.TraceResult.map_toCosted, Costed.map,
      localBPWindowBitsTraceResult_value,
      localBPWindowBits_eq_flatten_localBPBlockWordsRead]
  · unfold localBPSameBlockCloseSeededTraceResult
      localBPSameBlockCloseSeededCosted
    simp [WordRAM.TraceResult.map_toCosted, Costed.map,
      localBPWindowBitsTraceResult_cost]

/--
Large-regime concrete replay of the relative-rmM interior range-minimum query.

The abstract interior-directory record is intentionally too weak to support
this theorem, because it can be inhabited by proof-only oracles.  This function
therefore targets the canonical built directory and mirrors its two-level
payload-table construction directly.
-/
def concreteBPRelativeRmmInteriorRangeMinTraceResultOfReady
    (shape : Cartesian.CartesianShape)
    (_hready : concreteBPRelativeRmmInteriorReady shape)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  let summary := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := concreteBPRelativeRmmInteriorGlobalTable shape
  bpTwoLevelInteriorCandidateTraceResult localTable globalTable summary
    startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultOfReady_refines
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (startBlock count : Nat) :
    (concreteBPRelativeRmmInteriorRangeMinTraceResultOfReady
      shape hready startBlock count).toCosted =
      (concreteBPRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultOfReady
  unfold concreteBPRelativeRmmInteriorDirectory
  simp [hready, bpTwoLevelInteriorCandidateTraceResult_refines]

def concreteBPRelativeRmmInteriorRangeMinTraceResultOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  concreteBPRelativeRmmInteriorRangeMinTraceResultOfReady shape
    (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
    startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultOfSizeGe_refines
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (startBlock count : Nat) :
    (concreteBPRelativeRmmInteriorRangeMinTraceResultOfSizeGe
      shape hsize startBlock count).toCosted =
      (concreteBPRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count := by
  exact
    concreteBPRelativeRmmInteriorRangeMinTraceResultOfReady_refines
      shape (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
      startBlock count

/--
Large-regime relative-rmM interior trace with explicit global segment bases for
each payload table used by the two-level navigator.
-/
def concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
    (shape : Cartesian.CartesianShape)
    (_hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  let summary := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := concreteBPRelativeRmmInteriorGlobalTable shape
  bpTwoLevelInteriorCandidateTraceResultAtSegments localTable globalTable
    summary segments startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady_refines
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
      shape hready segments startBlock count).toCosted =
      (concreteBPRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
  unfold concreteBPRelativeRmmInteriorDirectory
  simp [hready, bpTwoLevelInteriorCandidateTraceResultAtSegments_refines]

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady_trace_forall
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hsummary :
      forall block event,
        List.Mem event
          ((concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minCandidateTraceResultAtSegments
              segments.summary block).trace -> P event)
    (hlocal :
      forall macroIdx localStart level event,
        List.Mem event
          ((concreteBPRelativeRmmInteriorLocalTable
            shape).readOffsetTraceResultAtSegment
              segments.localOffset segments.deadSegment macroIdx localStart
              level).trace -> P event)
    (hglobal :
      forall macroStart level event,
        List.Mem event
          ((concreteBPRelativeRmmInteriorGlobalTable
            shape).readBlockTraceResultAtSegment
              segments.globalBlock segments.deadSegment macroStart level).trace ->
            P event) :
    forall event,
      List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
            shape hready segments startBlock count).trace -> P event := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
  exact
    bpTwoLevelInteriorCandidateTraceResultAtSegments_trace_forall
      (concreteBPRelativeRmmInteriorLocalTable shape)
      (concreteBPRelativeRmmInteriorGlobalTable shape)
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      segments startBlock count P
      (fun macroIdx localStart count =>
        PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResultAtSegments_trace_forall
          (concreteBPRelativeRmmInteriorLocalTable shape)
          (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
          segments macroIdx localStart count P hlocal hsummary)
      (fun macroStart macroSpanCount =>
        PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResultAtSegments_trace_forall
          (concreteBPRelativeRmmInteriorGlobalTable shape)
          (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
          segments macroStart macroSpanCount P hglobal hsummary)

def concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady shape
    (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
    segments startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe_refines
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe
      shape hsize segments startBlock count).toCosted =
      (concreteBPRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count := by
  exact
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady_refines
      shape (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
      segments startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment
              segment) index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).argOffsetTable.wordRAMStore.readWord? segment index)
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorLocalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorGlobalTable
            shape).table.wordRAMStore.readWord? segment index)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
            shape hready segments startBlock count).trace ->
        event.matchesReadStore store := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
  exact
    bpTwoLevelInteriorCandidateTraceResultAtSegments_matchesReadStore
      (concreteBPRelativeRmmInteriorLocalTable shape)
      (concreteBPRelativeRmmInteriorGlobalTable shape)
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      segments store
      (fun macroIdx localStart count =>
        (concreteBPRelativeRmmInteriorLocalTable
          shape).twoSpanCandidateTraceResultAtSegments_matchesReadStore
            (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
            segments store hlocal hbaseline hminRel hmaxRel hargOffset
            macroIdx localStart count)
      (fun macroStart macroSpanCount =>
        (concreteBPRelativeRmmInteriorGlobalTable
          shape).twoSpanCandidateTraceResultAtSegments_matchesReadStore
            (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
            segments store hglobal hbaseline hminRel hmaxRel hargOffset
            macroStart macroSpanCount)
      startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment
              segment) index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).argOffsetTable.wordRAMStore.readWord? segment index)
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorLocalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorGlobalTable
            shape).table.wordRAMStore.readWord? segment index)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe
            shape hsize segments startBlock count).trace ->
        event.matchesReadStore store := by
  exact
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady_matchesReadStore
      shape (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
      segments store hbaseline hminRel hmaxRel hargOffset hlocal hglobal
      startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
            shape hready segments startBlock count).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
  exact
    bpTwoLevelInteriorCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
      (concreteBPRelativeRmmInteriorLocalTable shape)
      (concreteBPRelativeRmmInteriorGlobalTable shape)
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      segments
      (fun macroIdx localStart count =>
        (concreteBPRelativeRmmInteriorLocalTable
          shape).twoSpanCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
            (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
            segments macroIdx localStart count)
      (fun macroStart macroSpanCount =>
        (concreteBPRelativeRmmInteriorGlobalTable
          shape).twoSpanCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
            (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
            segments macroStart macroSpanCount)
      startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe
            shape hsize segments startBlock count).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  exact
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady_no_syntheticCostOnlyPrimitive
      shape (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
      segments startBlock count

def summaryRangeScanFromTraceResultAtSegments
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments) :
    Nat -> Nat -> Option (Nat × Nat) ->
      WordRAM.TraceResult (Option (Nat × Nat))
  | _block, 0, best? => WordRAM.TraceResult.pure best?
  | block, steps + 1, best? =>
      WordRAM.TraceResult.bind
        (table.minCandidateTraceResultAtSegments segments block)
        fun candidate? =>
          summaryRangeScanFromTraceResultAtSegments table segments
            (block + 1) steps (bpCandidateMerge? best? candidate?)

def summaryRangeScanTraceResultAtSegments
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  match count with
  | 0 => WordRAM.TraceResult.pure none
  | steps + 1 =>
      WordRAM.TraceResult.bind
        (table.minCandidateTraceResultAtSegments segments startBlock)
        fun first? =>
          summaryRangeScanFromTraceResultAtSegments table segments
            (startBlock + 1) steps first?

def boundedSummaryRangeScanTraceResultAtSegments
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  if startBlock + count <= blockCount then
    summaryRangeScanTraceResultAtSegments table segments startBlock count
  else
    WordRAM.TraceResult.pure none

theorem summaryRangeScanFromTraceResultAtSegments_refines
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block steps : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (best? : Option (Nat × Nat)) :
    (summaryRangeScanFromTraceResultAtSegments table segments
      block steps best?).toCosted =
      table.rangeScanFromCosted block steps best? := by
  induction steps generalizing block best? with
  | zero =>
      simp [summaryRangeScanFromTraceResultAtSegments,
        PayloadLiveBPRelativeMinMaxArgSummaryTable.rangeScanFromCosted,
        WordRAM.TraceResult.pure_toCosted]
  | succ steps ih =>
      simp [summaryRangeScanFromTraceResultAtSegments,
        PayloadLiveBPRelativeMinMaxArgSummaryTable.rangeScanFromCosted,
        WordRAM.TraceResult.bind_toCosted,
        PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResultAtSegments_refines_minCandidateCosted,
        Costed.bind, ih]

theorem summaryRangeScanTraceResultAtSegments_refines
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments) :
    (summaryRangeScanTraceResultAtSegments table segments
      startBlock count).toCosted =
      table.rangeScanCosted startBlock count := by
  unfold summaryRangeScanTraceResultAtSegments
  cases count with
  | zero =>
      simp [PayloadLiveBPRelativeMinMaxArgSummaryTable.rangeScanCosted,
        WordRAM.TraceResult.pure_toCosted]
  | succ steps =>
      simp [PayloadLiveBPRelativeMinMaxArgSummaryTable.rangeScanCosted,
        WordRAM.TraceResult.bind_toCosted,
        PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResultAtSegments_refines_minCandidateCosted,
        summaryRangeScanFromTraceResultAtSegments_refines, Costed.bind]

theorem boundedSummaryRangeScanTraceResultAtSegments_refines
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments) :
    (boundedSummaryRangeScanTraceResultAtSegments table segments
      startBlock count).toCosted =
      table.boundedRangeScanCosted startBlock count := by
  unfold boundedSummaryRangeScanTraceResultAtSegments
  unfold PayloadLiveBPRelativeMinMaxArgSummaryTable.boundedRangeScanCosted
  by_cases hbound : startBlock + count <= blockCount
  · simp [hbound, summaryRangeScanTraceResultAtSegments_refines]
  · simp [hbound, WordRAM.TraceResult.pure_toCosted, Costed.pure]

theorem summaryRangeScanFromTraceResultAtSegments_trace_forall
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block steps : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (best? : Option (Nat × Nat))
    (P : WordRAM.TraceEvent -> Prop)
    (hsummary :
      forall block event,
        List.Mem event
          (table.minCandidateTraceResultAtSegments segments block).trace ->
        P event) :
    forall event,
      List.Mem event
          (summaryRangeScanFromTraceResultAtSegments table segments
            block steps best?).trace -> P event := by
  induction steps generalizing block best? with
  | zero =>
      simp [summaryRangeScanFromTraceResultAtSegments]
      exact WordRAM.TraceResult.pure_trace_forall P best?
  | succ steps ih =>
      unfold summaryRangeScanFromTraceResultAtSegments
      apply WordRAM.TraceResult.bind_trace_forall
      · exact hsummary block
      · exact ih (block := block + 1)
          (best? :=
            bpCandidateMerge? best?
              (table.minCandidateTraceResultAtSegments segments block).value)

theorem summaryRangeScanTraceResultAtSegments_trace_forall
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (P : WordRAM.TraceEvent -> Prop)
    (hsummary :
      forall block event,
        List.Mem event
          (table.minCandidateTraceResultAtSegments segments block).trace ->
        P event) :
    forall event,
      List.Mem event
          (summaryRangeScanTraceResultAtSegments table segments
            startBlock count).trace -> P event := by
  unfold summaryRangeScanTraceResultAtSegments
  cases count with
  | zero =>
      simp
      exact WordRAM.TraceResult.pure_trace_forall P
        (none : Option (Nat × Nat))
  | succ steps =>
      apply WordRAM.TraceResult.bind_trace_forall
      · exact hsummary startBlock
      · exact
          summaryRangeScanFromTraceResultAtSegments_trace_forall
            table segments
            (table.minCandidateTraceResultAtSegments
              segments startBlock).value P hsummary

theorem boundedSummaryRangeScanTraceResultAtSegments_trace_forall
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (P : WordRAM.TraceEvent -> Prop)
    (hsummary :
      forall block event,
        List.Mem event
          (table.minCandidateTraceResultAtSegments segments block).trace ->
        P event) :
    forall event,
      List.Mem event
          (boundedSummaryRangeScanTraceResultAtSegments table segments
            startBlock count).trace -> P event := by
  unfold boundedSummaryRangeScanTraceResultAtSegments
  by_cases hbound : startBlock + count <= blockCount
  · simp [hbound]
    exact
      summaryRangeScanTraceResultAtSegments_trace_forall
        table segments P hsummary
  · simp [hbound]
    exact WordRAM.TraceResult.pure_trace_forall P
      (none : Option (Nat × Nat))

theorem boundedSummaryRangeScanTraceResultAtSegments_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment)
            index =
          table.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment)
            index =
          table.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment)
            index =
          table.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment)
            index =
          table.argOffsetTable.wordRAMStore.readWord? segment index) :
    forall event,
      List.Mem event
          (boundedSummaryRangeScanTraceResultAtSegments table segments
            startBlock count).trace ->
        event.matchesReadStore store := by
  exact
    boundedSummaryRangeScanTraceResultAtSegments_trace_forall
      table segments (fun event => event.matchesReadStore store)
      (fun block event hmem =>
        table.minCandidateTraceResultAtSegments_matchesReadStore
          segments store hbaseline hminRel hmaxRel hargOffset block event
          hmem)

theorem boundedSummaryRangeScanTraceResultAtSegments_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments) :
    forall event,
      List.Mem event
          (boundedSummaryRangeScanTraceResultAtSegments table segments
            startBlock count).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  exact
    boundedSummaryRangeScanTraceResultAtSegments_trace_forall
      table segments (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
      (fun block event hmem =>
        table.minCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
          segments block event hmem)

/--
Legacy diagnostic replay for the retired all-pairs relative-rmM interior
witness table, read through its min and arg payload tables. The public all-size
interior trace does not dispatch here; see
`concreteBPRelativeRmmInteriorAllSizeStructuralRoute_total`.
-/
def concreteBPFiniteSmallInteriorRangeMinTraceResultAtSegments
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  let table := concreteBPFiniteSmallInteriorRangeMinTable shape
  let slot :=
    finiteSmallInteriorRangeSlot
      (canonicalBPRelativeSummaryBlockCount shape) startBlock count
  WordRAM.TraceResult.bind
    (table.minTable.readTraceResultAtSegment
      segments.finiteSmallMin segments.deadSegment slot)
    fun min? =>
      WordRAM.TraceResult.map
        (fun arg? =>
          match min?, arg? with
          | some minExcess, some prefixPos => some (minExcess, prefixPos)
          | _, _ => none)
        (table.argTable.readTraceResultAtSegment
          segments.finiteSmallArg segments.deadSegment slot)

theorem concreteBPFiniteSmallInteriorRangeMinTraceResultAtSegments_refines
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    (concreteBPFiniteSmallInteriorRangeMinTraceResultAtSegments
      shape segments startBlock count).toCosted =
      (concreteBPFiniteSmallInteriorRangeMinTable shape).rangeWitnessCosted
        (finiteSmallInteriorRangeSlot
          (canonicalBPRelativeSummaryBlockCount shape) startBlock count) := by
  apply Costed.ext
  · simp [concreteBPFiniteSmallInteriorRangeMinTraceResultAtSegments,
      PayloadLiveBPRangeArgMinWitnessTable.rangeWitnessCosted,
      FixedWidthNatTable.readTraceResultAtSegment_refines_readCosted,
      WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
      Costed.bind, Costed.map]
    cases
      ((concreteBPFiniteSmallInteriorRangeMinTable shape).minTable.readCosted
        (finiteSmallInteriorRangeSlot
          (canonicalBPRelativeSummaryBlockCount shape) startBlock count)).value
    <;> cases
      ((concreteBPFiniteSmallInteriorRangeMinTable shape).argTable.readCosted
        (finiteSmallInteriorRangeSlot
          (canonicalBPRelativeSummaryBlockCount shape) startBlock count)).value
    <;> rfl
  · simp [concreteBPFiniteSmallInteriorRangeMinTraceResultAtSegments,
      PayloadLiveBPRangeArgMinWitnessTable.rangeWitnessCosted,
      FixedWidthNatTable.readTraceResultAtSegment_refines_readCosted,
      WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
      Costed.bind, Costed.map]

theorem concreteBPFiniteSmallInteriorRangeMinTraceResultAtSegments_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (hmin :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.finiteSmallMin segments.deadSegment segment) index =
          (concreteBPFiniteSmallInteriorRangeMinTable
            shape).minTable.wordRAMStore.readWord? segment index)
    (harg :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.finiteSmallArg segments.deadSegment segment) index =
          (concreteBPFiniteSmallInteriorRangeMinTable
            shape).argTable.wordRAMStore.readWord? segment index)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (concreteBPFiniteSmallInteriorRangeMinTraceResultAtSegments
            shape segments startBlock count).trace ->
        event.matchesReadStore store := by
  unfold concreteBPFiniteSmallInteriorRangeMinTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      fixedWidthNatTable_readTraceResultAtSegment_matchesReadStore
        (concreteBPFiniteSmallInteriorRangeMinTable shape).minTable
        segments.finiteSmallMin segments.deadSegment
        (finiteSmallInteriorRangeSlot
          (canonicalBPRelativeSummaryBlockCount shape) startBlock count)
        store hmin
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      fixedWidthNatTable_readTraceResultAtSegment_matchesReadStore
        (concreteBPFiniteSmallInteriorRangeMinTable shape).argTable
        segments.finiteSmallArg segments.deadSegment
        (finiteSmallInteriorRangeSlot
          (canonicalBPRelativeSummaryBlockCount shape) startBlock count)
        store harg

theorem concreteBPFiniteSmallInteriorRangeMinTraceResultAtSegments_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (concreteBPFiniteSmallInteriorRangeMinTraceResultAtSegments
            shape segments startBlock count).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPFiniteSmallInteriorRangeMinTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      (concreteBPFiniteSmallInteriorRangeMinTable
        shape).minTable.readTraceResultAtSegment_no_syntheticCostOnlyPrimitive
        segments.finiteSmallMin segments.deadSegment
        (finiteSmallInteriorRangeSlot
          (canonicalBPRelativeSummaryBlockCount shape) startBlock count)
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      (concreteBPFiniteSmallInteriorRangeMinTable
        shape).argTable.readTraceResultAtSegment_no_syntheticCostOnlyPrimitive
        segments.finiteSmallArg segments.deadSegment
        (finiteSmallInteriorRangeSlot
          (canonicalBPRelativeSummaryBlockCount shape) startBlock count)
/-- Canonical all-size interior execution as one physical component segment. -/
def canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment
    (shape : Cartesian.CartesianShape) (componentSegment : Nat)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Prod Nat Nat)) :=
  flatStoreExecutionTraceResultAtSegment componentSegment
    (canonicalRelativeRmmInteriorRangeMinExecutionWithStore shape
      (canonicalRelativeRmmInteriorComponentStore shape).store.words
      startBlock count)

theorem canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment_refines
    (shape : Cartesian.CartesianShape) (componentSegment : Nat)
    (startBlock count : Nat) :
    (canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment
      shape componentSegment startBlock count).toCosted =
      (canonicalRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count := by
  simp [canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment,
    canonicalRelativeRmmInteriorDirectory,
    canonicalRelativeRmmInteriorRangeMinCostedWithStore,
    canonicalRelativeRmmInteriorRangeMinCostedWithRead,
    canonicalRelativeRmmInteriorRangeMinExecutionWithStore,
    canonicalRelativeRmmInteriorRangeMinExecutionWithRead]

theorem canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment_matchesReadStore
    (shape : Cartesian.CartesianShape) (componentSegment : Nat)
    (store : WordRAM.ReadStore)
    (hcomponent :
      forall address,
        store.readWord? componentSegment address =
          (canonicalRelativeRmmInteriorComponentStore
            shape).store.words[address]?)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
        (canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment
          shape componentSegment startBlock count).trace ->
        event.matchesReadStore store := by
  intro event hmem
  unfold canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment at hmem
  unfold flatStoreExecutionTraceResultAtSegment at hmem
  cases List.mem_map.mp hmem with
  | intro read hrest =>
      cases hrest with
      | intro hread hevent =>
          subst event
          have hstored :=
            (canonicalRelativeRmmInteriorRangeMinComputation
              shape startBlock count).reads_match_store
              (FlatWordStore.ofArray
                (canonicalRelativeRmmInteriorComponentStore
                  shape).store.words)
              read.1 read.2 hread
          simp [WordRAM.TraceEvent.matchesReadStore]
          rw [hcomponent]
          exact hstored

theorem canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (componentSegment : Nat)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
        (canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment
          shape componentSegment startBlock count).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  exact
    flatStoreExecutionTraceResultAtSegment_no_syntheticCostOnlyPrimitive
      componentSegment
      (canonicalRelativeRmmInteriorRangeMinExecutionWithStore shape
        (canonicalRelativeRmmInteriorComponentStore shape).store.words
        startBlock count)


/--
All-size structural replay for the canonical relative-rmM interior query.
Every shape uses the same positive canonical layout and one component store.
-/
def concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment
    shape segments.canonicalComponent startBlock count

/-- Compatibility replay for the former Ready/Active/inactive route. -/
def concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralLegacy
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    WordRAM.TraceResult (Option (Prod Nat Nat)) :=
  if hready : concreteBPRelativeRmmInteriorReady shape then
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
      shape hready segments startBlock count
  else if canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    boundedSummaryRangeScanTraceResultAtSegments
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      segments.summary startBlock count
  else
    WordRAM.TraceResult.pure none

/--
Public route theorem for the all-size structural interior replay.

`Ready` remains the fast two-level regime predicate, not a total predicate.
The public all-size trace is total because every shape follows one of three
concrete structural routes: Ready uses the two-level replay, active non-Ready
uses the bounded summary scan, and inactive uses a pure `none` trace.
-/
theorem concreteBPRelativeRmmInteriorAllSizeStructuralRoute_total_legacy
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    (∃ hready : concreteBPRelativeRmmInteriorReady shape,
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralLegacy
          shape segments startBlock count =
        concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
          shape hready segments startBlock count) ∨
      (¬ concreteBPRelativeRmmInteriorReady shape ∧
        canonicalBPRelativeMinMaxArgSummaryTableActive shape ∧
        concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralLegacy
            shape segments startBlock count =
          boundedSummaryRangeScanTraceResultAtSegments
            (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
            segments.summary startBlock count) ∨
      (¬ concreteBPRelativeRmmInteriorReady shape ∧
        ¬ canonicalBPRelativeMinMaxArgSummaryTableActive shape ∧
        concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralLegacy
            shape segments startBlock count =
          WordRAM.TraceResult.pure none) := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralLegacy
  by_cases hready : concreteBPRelativeRmmInteriorReady shape
  · left
    exact ⟨hready, by simp [hready]⟩
  · right
    by_cases hactive :
        canonicalBPRelativeMinMaxArgSummaryTableActive shape
    · left
      exact ⟨hready, hactive, by simp [hready, hactive]⟩
    · right
      exact ⟨hready, hactive, by simp [hready, hactive]⟩

/-- Every shape uses the one canonical component-store route. -/
theorem concreteBPRelativeRmmInteriorAllSizeStructuralRoute_total
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
        shape segments startBlock count =
      canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment
        shape segments.canonicalComponent startBlock count := by
  rfl

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural_refines_legacy
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralLegacy
      shape segments startBlock count).toCosted =
      (concreteBPRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralLegacy
  by_cases hready : concreteBPRelativeRmmInteriorReady shape
  · simp [hready,
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady_refines]
  · by_cases hactive :
        canonicalBPRelativeMinMaxArgSummaryTableActive shape
    · unfold concreteBPRelativeRmmInteriorDirectory
      simp [hready, hactive,
        boundedSummaryRangeScanTraceResultAtSegments_refines]
    · unfold concreteBPRelativeRmmInteriorDirectory
      simp [hready, hactive, WordRAM.TraceResult.pure_toCosted,
        Costed.pure]

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural_matchesReadStore_legacy
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment
              segment) index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).argOffsetTable.wordRAMStore.readWord? segment index)
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorLocalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorGlobalTable
            shape).table.wordRAMStore.readWord? segment index)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralLegacy
            shape segments startBlock count).trace ->
        event.matchesReadStore store := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralLegacy
  by_cases hready : concreteBPRelativeRmmInteriorReady shape
  · simp [hready]
    exact
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady_matchesReadStore
        shape hready segments store hbaseline hminRel hmaxRel hargOffset
        hlocal hglobal startBlock count
  · by_cases hactive :
        canonicalBPRelativeMinMaxArgSummaryTableActive shape
    · simp [hready, hactive]
      exact
        boundedSummaryRangeScanTraceResultAtSegments_matchesReadStore
          (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
          segments.summary store hbaseline hminRel hmaxRel hargOffset
    · simp [hready, hactive]
      exact WordRAM.TraceResult.pure_trace_forall
        (fun event => event.matchesReadStore store)
        (none : Option (Nat × Nat))

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural_no_syntheticCostOnlyPrimitive_legacy
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralLegacy
            shape segments startBlock count).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralLegacy
  by_cases hready : concreteBPRelativeRmmInteriorReady shape
  · simp [hready]
    exact
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady_no_syntheticCostOnlyPrimitive
        shape hready segments startBlock count
  · by_cases hactive :
        canonicalBPRelativeMinMaxArgSummaryTableActive shape
    · simp [hready, hactive]
      exact
        boundedSummaryRangeScanTraceResultAtSegments_no_syntheticCostOnlyPrimitive
          (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
          segments.summary
    · simp [hready, hactive]
      exact WordRAM.TraceResult.pure_trace_forall
        (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
        (none : Option (Nat × Nat))

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural_refines
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
      shape segments startBlock count).toCosted =
      (canonicalRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count := by
  exact
    canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment_refines
      shape segments.canonicalComponent startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (hcomponent :
      forall address,
        store.readWord? segments.canonicalComponent address =
          (canonicalRelativeRmmInteriorComponentStore
            shape).store.words[address]?)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape segments startBlock count).trace ->
        event.matchesReadStore store := by
  exact
    canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment_matchesReadStore
      shape segments.canonicalComponent store hcomponent startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape segments startBlock count).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  exact
    canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment_no_syntheticCostOnlyPrimitive
      shape segments.canonicalComponent startBlock count

/-- Interpreted false-rank callback for the BP close seed. -/
def interpretedRankCloseCosted
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) : Costed Nat :=
  (((rankData.rankProgramClamped false pos).eval
    (rankData.rankWordRAMStore false)).toCosted)

theorem interpretedRankCloseCosted_refines_rankCostedClamped
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    interpretedRankCloseCosted rankData pos =
      rankData.rankCostedClamped false pos := by
  exact rankData.rankProgramClamped_refines_rankCostedClamped false pos

theorem interpretedRankCloseCosted_cost_le_three
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (interpretedRankCloseCosted rankData pos).cost <= 3 := by
  rw [interpretedRankCloseCosted_refines_rankCostedClamped
    (rankData := rankData) (pos := pos)]
  exact rankData.rankCostedClamped_cost_le_three false pos

theorem interpretedRankCloseCosted_exact
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (interpretedRankCloseCosted rankData pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  rw [interpretedRankCloseCosted_refines_rankCostedClamped
    (rankData := rankData) (pos := pos)]
  exact rankData.rankCostedClamped_exact false pos

/--
Register-interpreted false-rank callback for the BP close seed.

Unlike `interpretedRankCloseCosted`, the queried position is read from a
natural register before the sample and bit-word addresses are computed.
-/
def registerRankCloseCosted
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) : Costed Nat :=
  (((rankData.rankRegProgram false (NatExpr.reg 0)).eval
    (rankData.rankWordRAMStore false)
    (RegFile.withNat1 pos)).toCosted)

theorem registerRankCloseCosted_refines_interpretedRankCloseCosted
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    registerRankCloseCosted rankData pos =
      interpretedRankCloseCosted rankData pos := by
  unfold registerRankCloseCosted interpretedRankCloseCosted
  exact
    rankData.rankRegProgram_refines_rankProgramClamped false
      (NatExpr.reg 0) (RegFile.withNat1 pos)

theorem registerRankCloseCosted_cost_le_three
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (registerRankCloseCosted rankData pos).cost <= 3 := by
  rw [registerRankCloseCosted_refines_interpretedRankCloseCosted
    (rankData := rankData) (pos := pos)]
  exact interpretedRankCloseCosted_cost_le_three
    (rankData := rankData) (pos := pos)

theorem registerRankCloseCosted_exact
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (registerRankCloseCosted rankData pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  rw [registerRankCloseCosted_refines_interpretedRankCloseCosted
    (rankData := rankData) (pos := pos)]
  exact interpretedRankCloseCosted_exact
    (rankData := rankData) (pos := pos)

/-- Register-program trace for the false-rank callback used by close seeds. -/
def registerRankCloseTraceResult
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.ofResult
    (((rankData.rankRegProgram false (NatExpr.reg 0)).eval
      (rankData.rankWordRAMStore false)
      (RegFile.withNat1 pos)))

theorem registerRankCloseTraceResult_refines_registerRankCloseCosted
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (registerRankCloseTraceResult rankData pos).toCosted =
      registerRankCloseCosted rankData pos := by
  rfl

/-- Trace-preserving version of `localBPSeedFromRankCloseCosted`. -/
def localBPSeedFromRankCloseTraceResult
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (blockSize close : Nat) : WordRAM.TraceResult Nat :=
  let base := localBPWindowBase shape blockSize close
  WordRAM.TraceResult.map
    (fun rankFalse => localBPSeedFromRankFalse base rankFalse)
    (rankCloseTrace base)

theorem localBPSeedFromRankCloseTraceResult_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize close : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize close).toCosted =
      localBPSeedFromRankCloseCosted
        shape rankCloseCosted blockSize close := by
  simp [localBPSeedFromRankCloseTraceResult,
    localBPSeedFromRankCloseCosted, hrank]

/--
Trace-preserving same-block close decoder.

The rank seed and bounded local BP decoder are both replayed as structural
traces over payload reads.
-/
def localBPSameBlockCloseDecodedTraceResultWithRankSeed
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (blockSize leftClose rightClose : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun seed =>
      localBPSameBlockCloseSeededTraceResult
        shape blockSize leftClose rightClose seed

theorem localBPSameBlockCloseDecodedTraceResultWithRankSeed_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (localBPSameBlockCloseDecodedTraceResultWithRankSeed
      shape rankCloseTrace blockSize leftClose rightClose).toCosted =
      localBPSameBlockCloseDecodedCostedWithRankSeed
        shape rankCloseCosted blockSize leftClose rightClose := by
  simp [localBPSameBlockCloseDecodedTraceResultWithRankSeed,
    localBPSameBlockCloseDecodedCostedWithRankSeed,
    localBPSeedFromRankCloseTraceResult_refines,
    localBPSameBlockCloseSeededTraceResult_refines, hrank]

theorem localBPSeedFromRankCloseTraceResult_trace_forall
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (blockSize close : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace -> P event) :
    forall event,
      List.Mem event
          (localBPSeedFromRankCloseTraceResult
            shape rankCloseTrace blockSize close).trace ->
        P event := by
  unfold localBPSeedFromRankCloseTraceResult
  exact WordRAM.TraceResult.map_trace_forall P
    (fun rankFalse =>
      localBPSeedFromRankFalse
        (localBPWindowBase shape blockSize close) rankFalse)
    (rankCloseTrace (localBPWindowBase shape blockSize close))
    (hrank (localBPWindowBase shape blockSize close))

theorem localBPLeftFringeCandidateSeededTraceResult_trace_forall
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose seed : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hbp :
      forall event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize leftClose).trace ->
          P event) :
    forall event,
      List.Mem event
          (localBPLeftFringeCandidateSeededTraceResult
            shape blockSize leftClose seed).trace ->
        P event := by
  unfold localBPLeftFringeCandidateSeededTraceResult
  exact WordRAM.TraceResult.map_trace_forall P
    (fun window =>
      some
        (localBPSeededPrefixRangeMinExcess window seed
          (localBPWindowBase shape blockSize leftClose)
          (leftClose + 1)
          (blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
          localBPSeededPrefixRangeArgMinPrefixPos window seed
            (localBPWindowBase shape blockSize leftClose)
            (leftClose + 1)
            (blockStartOf blockSize (blockOfClose blockSize leftClose) +
              blockSize - leftClose)))
    (localBPWindowBitsTraceResult shape blockSize leftClose) hbp

theorem localBPRightFringeCandidateSeededTraceResult_trace_forall
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose seed : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hbp :
      forall event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize rightClose).trace ->
          P event) :
    forall event,
      List.Mem event
          (localBPRightFringeCandidateSeededTraceResult
            shape blockSize rightClose seed).trace ->
        P event := by
  unfold localBPRightFringeCandidateSeededTraceResult
  exact WordRAM.TraceResult.map_trace_forall P
    (fun window =>
      some
        (localBPSeededPrefixRangeMinExcess window seed
          (localBPWindowBase shape blockSize rightClose)
          (blockStartOf blockSize (blockOfClose blockSize rightClose))
          (rightClose -
            blockStartOf blockSize (blockOfClose blockSize rightClose) + 2),
          localBPSeededPrefixRangeArgMinPrefixPos window seed
            (localBPWindowBase shape blockSize rightClose)
            (blockStartOf blockSize (blockOfClose blockSize rightClose))
            (rightClose -
              blockStartOf blockSize (blockOfClose blockSize rightClose) + 2)))
    (localBPWindowBitsTraceResult shape blockSize rightClose) hbp

theorem localBPSameBlockCloseSeededTraceResult_trace_forall
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose seed : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hbp :
      forall event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize leftClose).trace ->
          P event) :
    forall event,
      List.Mem event
          (localBPSameBlockCloseSeededTraceResult
            shape blockSize leftClose rightClose seed).trace ->
        P event := by
  unfold localBPSameBlockCloseSeededTraceResult
  exact WordRAM.TraceResult.map_trace_forall P
    (fun window =>
      bpCandidateClose?
        (some
          (localBPSeededPrefixRangeMinExcess window seed
            (localBPWindowBase shape blockSize leftClose)
            (leftClose + 1) (rightClose - leftClose + 1),
            localBPSeededPrefixRangeArgMinPrefixPos window seed
              (localBPWindowBase shape blockSize leftClose)
              (leftClose + 1) (rightClose - leftClose + 1))))
    (localBPWindowBitsTraceResult shape blockSize leftClose) hbp

theorem localBPSameBlockCloseDecodedTraceResultWithRankSeed_trace_forall
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (blockSize leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace -> P event)
    (hbp :
      forall event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize leftClose).trace ->
          P event) :
    forall event,
      List.Mem event
          (localBPSameBlockCloseDecodedTraceResultWithRankSeed
            shape rankCloseTrace blockSize leftClose rightClose).trace ->
        P event := by
  unfold localBPSameBlockCloseDecodedTraceResultWithRankSeed
  exact WordRAM.TraceResult.bind_trace_forall P
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    (fun seed =>
      localBPSameBlockCloseSeededTraceResult
        shape blockSize leftClose rightClose seed)
    (localBPSeedFromRankCloseTraceResult_trace_forall
      shape rankCloseTrace blockSize leftClose P hrank)
    (localBPSameBlockCloseSeededTraceResult_trace_forall
      shape blockSize leftClose rightClose
      (localBPSeedFromRankCloseTraceResult
        shape rankCloseTrace blockSize leftClose).value P hbp)

/--
Trace-preserving cross-block close decoder.

The two endpoint seed rank reads and endpoint-fringe decoders are structural
traces.  The interior relative-rmM query remains the existing charged decoder
leaf.
-/
def crossBlockCloseTraceResultWithRankSeed
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun leftSeed =>
      WordRAM.TraceResult.bind
        (localBPLeftFringeCandidateSeededTraceResult
          shape blockSize leftClose leftSeed)
        fun left? =>
          WordRAM.TraceResult.bind
            (if leftBlock + 1 < rightBlock then
              WordRAM.TraceResult.ofCosted
                (directory.interior.rangeMinCosted (leftBlock + 1)
                  (rightBlock - leftBlock - 1))
            else
              WordRAM.TraceResult.pure none)
            fun middle? =>
              WordRAM.TraceResult.bind
                (localBPSeedFromRankCloseTraceResult
                  shape rankCloseTrace blockSize rightClose)
                fun rightSeed =>
                  WordRAM.TraceResult.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (localBPRightFringeCandidateSeededTraceResult
                      shape blockSize rightClose rightSeed)

theorem crossBlockCloseTraceResultWithRankSeed_refines
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (directory.crossBlockCloseTraceResultWithRankSeed
      rankCloseTrace leftClose rightClose).toCosted =
      directory.crossBlockCloseCostedWithRankSeed
        rankCloseCosted leftClose rightClose := by
  unfold crossBlockCloseTraceResultWithRankSeed
  unfold crossBlockCloseCostedWithRankSeed
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  case pos =>
    simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      blockSize, hmiddle]
  case neg =>
    simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      blockSize, hmiddle]

theorem crossBlockCloseTraceResultWithRankSeed_trace_forall
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace -> P event)
    (hbp :
      forall blockSize close event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize close).trace ->
          P event)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (WordRAM.TraceResult.ofCosted
            (directory.interior.rangeMinCosted startBlock count)).trace ->
          P event) :
    forall event,
      List.Mem event
          (directory.crossBlockCloseTraceResultWithRankSeed
            rankCloseTrace leftClose rightClose).trace ->
        P event := by
  unfold crossBlockCloseTraceResultWithRankSeed
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  intro event hmem
  by_cases hmiddle :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose + 1 <
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose
  · simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, hmiddle] at hmem
    rcases List.mem_append.mp hmem with hmem | htail
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize leftClose P hrank event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | htail
    · exact localBPLeftFringeCandidateSeededTraceResult_trace_forall
        shape blockSize leftClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize leftClose).value P
        (hbp blockSize leftClose) event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | htail
    · exact hinterior
        (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
          leftClose + 1)
        (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
          rightClose -
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
          leftClose - 1)
        event hmem
    rcases List.mem_append.mp htail with hmem | hmem
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize rightClose P hrank event
        (by simpa [blockSize] using hmem)
    · exact localBPRightFringeCandidateSeededTraceResult_trace_forall
        shape blockSize rightClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize rightClose).value P
        (hbp blockSize rightClose) event
        (by simpa [blockSize] using hmem)
  · simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, hmiddle] at hmem
    rcases List.mem_append.mp hmem with hmem | htail
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize leftClose P hrank event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | htail
    · exact localBPLeftFringeCandidateSeededTraceResult_trace_forall
        shape blockSize leftClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize leftClose).value P
        (hbp blockSize leftClose) event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | hmem
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize rightClose P hrank event
        (by simpa [blockSize] using hmem)
    · exact localBPRightFringeCandidateSeededTraceResult_trace_forall
        shape blockSize rightClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize rightClose).value P
        (hbp blockSize rightClose) event
        (by simpa [blockSize] using hmem)

theorem crossBlockCloseTraceResultWithRankSeed_matchesReadStore
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (leftClose rightClose : Nat)
    (store : WordRAM.ReadStore)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          event.matchesReadStore store)
    (hbp :
      forall blockSize close event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize close).trace ->
          event.matchesReadStore store) :
    forall event,
      List.Mem event
          (directory.crossBlockCloseTraceResultWithRankSeed
            rankCloseTrace leftClose rightClose).trace ->
        event.matchesReadStore store := by
  exact
    crossBlockCloseTraceResultWithRankSeed_trace_forall
      directory rankCloseTrace leftClose rightClose
      (fun event => event.matchesReadStore store)
      hrank hbp
      (fun startBlock count =>
        WordRAM.TraceResult.ofCosted_matchesReadStore
          (directory.interior.rangeMinCosted startBlock count) store)

/--
Concrete large-regime cross-block close decoder with a structural interior
relative-rmM trace.
-/
def crossBlockCloseTraceResultWithRankSeedOfReady
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun leftSeed =>
      WordRAM.TraceResult.bind
        (localBPLeftFringeCandidateSeededTraceResult
          shape blockSize leftClose leftSeed)
        fun left? =>
          WordRAM.TraceResult.bind
            (if leftBlock + 1 < rightBlock then
              concreteBPRelativeRmmInteriorRangeMinTraceResultOfReady
                shape hready (leftBlock + 1)
                (rightBlock - leftBlock - 1)
            else
              WordRAM.TraceResult.pure none)
            fun middle? =>
              WordRAM.TraceResult.bind
                (localBPSeedFromRankCloseTraceResult
                  shape rankCloseTrace blockSize rightClose)
                fun rightSeed =>
                  WordRAM.TraceResult.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (localBPRightFringeCandidateSeededTraceResult
                      shape blockSize rightClose rightSeed)

/- theorem crossBlockCloseTraceResultWithRankSeedOfSizeGe_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (crossBlockCloseTraceResultWithRankSeedOfSizeGe
      shape rankCloseTrace hsize leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  unfold crossBlockCloseTraceResultWithRankSeedOfSizeGe
  unfold ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  Â· simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      concreteBPRelativeRmmInteriorRangeMinTraceResultOfSizeGe_refines,
      blockSize, hmiddle]
  Â· simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      blockSize, hmiddle]
-/

theorem crossBlockCloseTraceResultWithRankSeedOfReady_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (crossBlockCloseTraceResultWithRankSeedOfReady
      shape rankCloseTrace hready leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  unfold crossBlockCloseTraceResultWithRankSeedOfReady
  unfold ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  case pos =>
    simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      concreteBPRelativeRmmInteriorRangeMinTraceResultOfReady_refines,
      concreteCompactBPCloseLCADirectory, blockSize, hmiddle]
  case neg =>
    simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      blockSize, hmiddle]

def crossBlockCloseTraceResultWithRankSeedOfSizeGe
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  crossBlockCloseTraceResultWithRankSeedOfReady shape rankCloseTrace
    (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
    leftClose rightClose

theorem crossBlockCloseTraceResultWithRankSeedOfSizeGe_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (crossBlockCloseTraceResultWithRankSeedOfSizeGe
      shape rankCloseTrace hsize leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  exact
    crossBlockCloseTraceResultWithRankSeedOfReady_refines
      shape rankCloseTrace rankCloseCosted
      (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
      leftClose rightClose hrank

/--
Large-regime cross-block close decoder whose interior table reads are relabeled
into caller-supplied global segments.

The rank-seed callback is assumed to have already been relabeled by the caller,
and local BP-code reads remain at segment 0.
-/
def crossBlockCloseTraceResultWithRankSeedAtSegmentsOfReady
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun leftSeed =>
      WordRAM.TraceResult.bind
        (localBPLeftFringeCandidateSeededTraceResult
          shape blockSize leftClose leftSeed)
        fun left? =>
          WordRAM.TraceResult.bind
            (if leftBlock + 1 < rightBlock then
              concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
                shape hready segments (leftBlock + 1)
                (rightBlock - leftBlock - 1)
            else
              WordRAM.TraceResult.pure none)
            fun middle? =>
              WordRAM.TraceResult.bind
                (localBPSeedFromRankCloseTraceResult
                  shape rankCloseTrace blockSize rightClose)
                fun rightSeed =>
                  WordRAM.TraceResult.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (localBPRightFringeCandidateSeededTraceResult
                      shape blockSize rightClose rightSeed)

theorem crossBlockCloseTraceResultWithRankSeedAtSegmentsOfReady_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (crossBlockCloseTraceResultWithRankSeedAtSegmentsOfReady
      shape rankCloseTrace hready segments leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  unfold crossBlockCloseTraceResultWithRankSeedAtSegmentsOfReady
  unfold ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  case pos =>
    simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady_refines,
      concreteCompactBPCloseLCADirectory, blockSize, hmiddle]
  case neg =>
    simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      blockSize, hmiddle]

def crossBlockCloseTraceResultWithRankSeedAtSegmentsOfSizeGe
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  crossBlockCloseTraceResultWithRankSeedAtSegmentsOfReady shape
    rankCloseTrace (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
    segments leftClose rightClose

theorem crossBlockCloseTraceResultWithRankSeedAtSegmentsOfSizeGe_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (crossBlockCloseTraceResultWithRankSeedAtSegmentsOfSizeGe
      shape rankCloseTrace hsize segments leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  exact
    crossBlockCloseTraceResultWithRankSeedAtSegmentsOfReady_refines
      shape rankCloseTrace rankCloseCosted
      (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
      segments leftClose rightClose hrank

theorem crossBlockCloseTraceResultWithRankSeedAtSegmentsOfReady_trace_forall
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace -> P event)
    (hbp :
      forall blockSize close event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize close).trace ->
          P event)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
            shape hready segments startBlock count).trace ->
          P event) :
    forall event,
      List.Mem event
          (crossBlockCloseTraceResultWithRankSeedAtSegmentsOfReady
            shape rankCloseTrace hready segments leftClose rightClose).trace ->
        P event := by
  unfold crossBlockCloseTraceResultWithRankSeedAtSegmentsOfReady
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  intro event hmem
  by_cases hmiddle :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose + 1 <
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose
  · simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, hmiddle] at hmem
    rcases List.mem_append.mp hmem with hmem | htail
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize leftClose P hrank event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | htail
    · exact localBPLeftFringeCandidateSeededTraceResult_trace_forall
        shape blockSize leftClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize leftClose).value P
        (hbp blockSize leftClose) event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | htail
    · exact hinterior
        (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
          leftClose + 1)
        (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
          rightClose -
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
          leftClose - 1)
        event hmem
    rcases List.mem_append.mp htail with hmem | hmem
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize rightClose P hrank event
        (by simpa [blockSize] using hmem)
    · exact localBPRightFringeCandidateSeededTraceResult_trace_forall
        shape blockSize rightClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize rightClose).value P
        (hbp blockSize rightClose) event
        (by simpa [blockSize] using hmem)
  · simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, hmiddle] at hmem
    rcases List.mem_append.mp hmem with hmem | htail
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize leftClose P hrank event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | htail
    · exact localBPLeftFringeCandidateSeededTraceResult_trace_forall
        shape blockSize leftClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize leftClose).value P
        (hbp blockSize leftClose) event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | hmem
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize rightClose P hrank event
        (by simpa [blockSize] using hmem)
    · exact localBPRightFringeCandidateSeededTraceResult_trace_forall
        shape blockSize rightClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize rightClose).value P
        (hbp blockSize rightClose) event
        (by simpa [blockSize] using hmem)

theorem crossBlockCloseTraceResultWithRankSeedAtSegmentsOfSizeGe_trace_forall
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace -> P event)
    (hbp :
      forall blockSize close event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize close).trace ->
          P event)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe
            shape hsize segments startBlock count).trace ->
          P event) :
    forall event,
      List.Mem event
          (crossBlockCloseTraceResultWithRankSeedAtSegmentsOfSizeGe
            shape rankCloseTrace hsize segments leftClose rightClose).trace ->
        P event := by
  exact
    crossBlockCloseTraceResultWithRankSeedAtSegmentsOfReady_trace_forall
      shape rankCloseTrace
      (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
      segments leftClose rightClose P hrank hbp
      (by
        intro startBlock count event hmem
        exact hinterior startBlock count event hmem)

/-- Raw canonical block indices are bounded by the total canonical block count. -/
theorem canonicalBPRelativeSummary_blockOfClose_le_blockCountRaw
    {shape : Cartesian.CartesianShape} {close : Nat}
    (hclose : close < shape.bpCode.length) :
    blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) close <=
      canonicalBPRelativeSummaryBlockCountRaw shape := by
  have hblockSizePos := canonicalBPRelativeSummaryBlockSizeRaw_pos shape
  have hupper := canonicalBPRelativeSummaryBlockCountRaw_upper_cover shape
  have hdiv :
      close / canonicalBPRelativeSummaryBlockSizeRaw shape <
        canonicalBPRelativeSummaryBlockCountRaw shape + 1 := by
    apply (Nat.div_lt_iff_lt_mul hblockSizePos).2
    exact Nat.lt_trans hclose hupper
  simpa [blockOfClose] using Nat.le_of_lt_succ hdiv

/-- The total canonical block width fits in two modeled machine words. -/
theorem canonicalBPRelativeSummaryBlockSizeRaw_le_two_machine_of_size_pos
    {shape : Cartesian.CartesianShape}
    (hsize : 0 < shape.size) :
    canonicalBPRelativeSummaryBlockSizeRaw shape <=
      2 * SuccinctRank.machineWordBits shape.bpCode.length := by
  have hbase :=
    canonicalBPRelativeSummaryBase_le_superWidth_of_size_pos
      (shape := shape) hsize
  simpa [canonicalBPRelativeSummaryBlockSizeRaw,
    canonicalBPRelativeSummarySuperWidth] using
      Nat.mul_le_mul_left 2 hbase

/-- Honest transitional cap for the canonical close/LCA route. -/
def canonicalCompactBPCloseQueryCostWithRankSeed
    (rankCost : Nat) : Nat :=
  8 + 2 * rankCost + canonicalRelativeRmmInteriorQueryCost

/-- Four physical BP-code reads form each accepted endpoint fringe. -/
def canonicalEndpointFringeChargedTraceCost : Nat := 4

/--
Operation-aligned U3 algebra for the accepted close/LCA execution: two rank
seeds, two endpoint fringes, and one bounded physical interior replay.
-/
def canonicalPrincipledBPCloseChargedTraceCostWithRankSeed
    (rankCost : Nat) : Nat :=
  2 * rankCost + 2 * canonicalEndpointFringeChargedTraceCost +
    canonicalRelativeRmmPrincipledInteriorChargedTraceCost

/-- Canonical cross-block costed consumer of the uniform interior directory. -/
def canonicalCrossBlockCloseCostedWithRankSeed
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  Costed.bind
    (localBPSeedFromRankCloseCosted
      shape rankCloseCosted blockSize leftClose)
    fun leftSeed =>
      Costed.bind
        (localBPLeftFringeCandidateSeededCosted
          shape blockSize leftClose leftSeed)
        fun left? =>
          Costed.bind
            (if leftBlock + 1 < rightBlock then
              (canonicalRelativeRmmInteriorDirectory shape).rangeMinCosted
                (leftBlock + 1) (rightBlock - leftBlock - 1)
            else
              Costed.pure none)
            fun middle? =>
              Costed.bind
                (localBPSeedFromRankCloseCosted
                  shape rankCloseCosted blockSize rightClose)
                fun rightSeed =>
                  Costed.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (localBPRightFringeCandidateSeededCosted
                      shape blockSize rightClose rightSeed)

/--
All-size structural cross-block close decoder. The endpoint rank seeds and
fringe decoders use the canonical positive layout, and the middle range uses
the one canonical component-store replay.
-/
def crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun leftSeed =>
      WordRAM.TraceResult.bind
        (localBPLeftFringeCandidateSeededTraceResult
          shape blockSize leftClose leftSeed)
        fun left? =>
          WordRAM.TraceResult.bind
            (if leftBlock + 1 < rightBlock then
              concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
                shape segments (leftBlock + 1)
                (rightBlock - leftBlock - 1)
            else
              WordRAM.TraceResult.pure none)
            fun middle? =>
              WordRAM.TraceResult.bind
                (localBPSeedFromRankCloseTraceResult
                  shape rankCloseTrace blockSize rightClose)
                fun rightSeed =>
                  WordRAM.TraceResult.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (localBPRightFringeCandidateSeededTraceResult
                      shape blockSize rightClose rightSeed)

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
      shape rankCloseTrace segments leftClose rightClose).toCosted =
      canonicalCrossBlockCloseCostedWithRankSeed
        shape
        rankCloseCosted leftClose rightClose := by
  unfold crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
  unfold canonicalCrossBlockCloseCostedWithRankSeed
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  case pos =>
    simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural_refines,
      blockSize, hmiddle]
  case neg =>
    simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      blockSize, hmiddle]

/-- Canonical cross-block cost is the two rank seeds, two fringes, and one interior query. -/
theorem canonicalCrossBlockCloseCostedWithRankSeed_cost_le
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose rankCost : Nat)
    (hrankCost : forall pos, (rankCloseCosted pos).cost <= rankCost) :
    (canonicalCrossBlockCloseCostedWithRankSeed
      shape rankCloseCosted leftClose rightClose).cost <=
        canonicalCompactBPCloseQueryCostWithRankSeed rankCost := by
  unfold canonicalCrossBlockCloseCostedWithRankSeed
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  have hleftSeed :=
    localBPSeedFromRankCloseCosted_cost_le shape rankCloseCosted
      blockSize leftClose rankCost hrankCost
  have hleft :=
    localBPLeftFringeCandidateSeededCosted_cost_le shape blockSize leftClose
      (localBPSeedFromRankCloseCosted shape rankCloseCosted
        blockSize leftClose).value
  have hmiddle :
      (if leftBlock + 1 < rightBlock then
          (canonicalRelativeRmmInteriorDirectory shape).rangeMinCosted
            (leftBlock + 1) (rightBlock - leftBlock - 1)
        else
          Costed.pure none).cost <= canonicalRelativeRmmInteriorQueryCost := by
    by_cases hgap : leftBlock + 1 < rightBlock
    case pos =>
      rw [if_pos hgap]
      exact
        (canonicalRelativeRmmInteriorDirectory shape).rangeMin_cost_le
          (leftBlock + 1) (rightBlock - leftBlock - 1)
    case neg =>
      rw [if_neg hgap]
      simp [Costed.pure]
  have hrightSeed :=
    localBPSeedFromRankCloseCosted_cost_le shape rankCloseCosted
      blockSize rightClose rankCost hrankCost
  have hright :=
    localBPRightFringeCandidateSeededCosted_cost_le shape blockSize rightClose
      (localBPSeedFromRankCloseCosted shape rankCloseCosted
        blockSize rightClose).value
  dsimp [blockSize, leftBlock, rightBlock] at hleftSeed hleft hmiddle hrightSeed hright
  simp [Costed.bind, Costed.map, Costed.pure]
  simp [Costed.pure] at hmiddle
  unfold canonicalCompactBPCloseQueryCostWithRankSeed
  omega

/--
The cross-block U2 execution obeys the U3 operation-aligned cap whenever both
selected closes are genuine BP positions.  No work is added to realize it.
-/
theorem canonicalCrossBlockCloseCostedWithRankSeed_cost_le_principled
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose rankCost : Nat)
    (_hleftCloseBound : leftClose < shape.bpCode.length)
    (hrightCloseBound : rightClose < shape.bpCode.length)
    (hrankCost : forall pos, (rankCloseCosted pos).cost <= rankCost) :
    (canonicalCrossBlockCloseCostedWithRankSeed
      shape rankCloseCosted leftClose rightClose).cost <=
        canonicalPrincipledBPCloseChargedTraceCostWithRankSeed rankCost := by
  unfold canonicalCrossBlockCloseCostedWithRankSeed
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  have hleftSeed :=
    localBPSeedFromRankCloseCosted_cost_le shape rankCloseCosted
      blockSize leftClose rankCost hrankCost
  have hleft :=
    localBPLeftFringeCandidateSeededCosted_cost_le shape blockSize leftClose
      (localBPSeedFromRankCloseCosted shape rankCloseCosted
        blockSize leftClose).value
  have hmiddle :
      (if leftBlock + 1 < rightBlock then
          (canonicalRelativeRmmInteriorDirectory shape).rangeMinCosted
            (leftBlock + 1) (rightBlock - leftBlock - 1)
        else
          Costed.pure none).cost <=
        canonicalRelativeRmmPrincipledInteriorChargedTraceCost := by
    by_cases hgap : leftBlock + 1 < rightBlock
    case pos =>
      rw [if_pos hgap]
      have hrightBlockLe :
          rightBlock <= canonicalBPRelativeSummaryBlockCountRaw shape := by
        exact canonicalBPRelativeSummary_blockOfClose_le_blockCountRaw
          (shape := shape) hrightCloseBound
      have hbound :
          (leftBlock + 1) + (rightBlock - leftBlock - 1) <=
            (RelativeRmm.canonicalLayout shape).blockCount := by
        simpa [RelativeRmm.canonicalLayout] using (show
          (leftBlock + 1) + (rightBlock - leftBlock - 1) <=
            canonicalBPRelativeSummaryBlockCountRaw shape by omega)
      let base := canonicalBPRelativeSummaryBase shape
      have hbasePos : 0 < base := by
        simp [base, canonicalBPRelativeSummaryBase]
      have htwoBlocks :
          2 <= canonicalBPRelativeSummaryBlockCountRaw shape := by omega
      have htwoDiv : 2 <= shape.size / base := by
        simpa [canonicalBPRelativeSummaryBlockCountRaw, base] using htwoBlocks
      have hmul : 2 * base <= shape.size :=
        (Nat.le_div_iff_mul_le hbasePos).mp htwoDiv
      have hsizeTwo : 2 <= shape.size := by omega
      have hlog : 1 <= Nat.log2 shape.size :=
        natLog2_ge_of_pow_le (by simpa using hsizeTwo)
      have hbaseTwo : 2 <= base := by
        simp only [base, canonicalBPRelativeSummaryBase]
        omega
      have hsize : 4 <= shape.size := by omega
      simpa [canonicalRelativeRmmInteriorDirectory] using
        canonicalRelativeRmmInteriorRangeMinCostedWithStore_cost_le_thirty_of_size_ge_four_of_bounded
          shape hsize (leftBlock + 1) (rightBlock - leftBlock - 1) hbound
    case neg =>
      rw [if_neg hgap]
      simp [Costed.pure]
  have hrightSeed :=
    localBPSeedFromRankCloseCosted_cost_le shape rankCloseCosted
      blockSize rightClose rankCost hrankCost
  have hright :=
    localBPRightFringeCandidateSeededCosted_cost_le shape blockSize rightClose
      (localBPSeedFromRankCloseCosted shape rankCloseCosted
        blockSize rightClose).value
  dsimp [blockSize, leftBlock, rightBlock] at hleftSeed hleft hmiddle hrightSeed hright
  simp [Costed.bind, Costed.map, Costed.pure]
  simp [Costed.pure] at hmiddle
  unfold canonicalPrincipledBPCloseChargedTraceCostWithRankSeed
  unfold canonicalEndpointFringeChargedTraceCost
  omega

/-- Exact canonical cross-block close semantics for one valid RMQ query. -/
theorem canonicalCrossBlockCloseCostedWithRankSeed_exact_of_query
    {shape : Cartesian.CartesianShape}
    (rankCloseCosted : Nat -> Costed Nat)
    {left len leftClose rightClose answerClose : Nat}
    (hrankExact :
      forall pos,
        (rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hcross :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose <
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose) :
    (canonicalCrossBlockCloseCostedWithRankSeed
      shape rankCloseCosted leftClose rightClose).erase =
        some answerClose := by
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hrightBlockLe :
      rightBlock <= canonicalBPRelativeSummaryBlockCountRaw shape := by
    exact
      canonicalBPRelativeSummary_blockOfClose_le_blockCountRaw
        (shape := shape) hrightCloseBound
  have hsizePos : 0 < shape.size := by omega
  have hblockSizeLeTwo :
      blockSize <=
        2 * SuccinctRank.machineWordBits shape.bpCode.length := by
    simpa [blockSize] using
      canonicalBPRelativeSummaryBlockSizeRaw_le_two_machine_of_size_pos
        (shape := shape) hsizePos
  have hblockSizeLeThree :
      blockSize <=
        3 * SuccinctRank.machineWordBits shape.bpCode.length := by
    omega
  have hblockCountLen :
      canonicalBPRelativeSummaryBlockCountRaw shape * blockSize <=
        shape.bpCode.length := by
    simpa [blockSize] using
      canonicalBPRelativeSummaryBlockCountRaw_mul_blockSizeRaw_le_bpCode_length
        shape
  have hleftBaseBlock :
      localBPWindowBase shape blockSize leftClose <=
        blockStartOf blockSize leftBlock := by
    simpa [leftBlock] using
      localBPWindowBase_le_blockStart shape blockSize leftClose
  have hleftBaseClose :
      localBPWindowBase shape blockSize leftClose <= leftClose := by
    exact Nat.le_trans hleftBaseBlock blockStartOf_blockOfClose_le
  have hleftBaseLen :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length := by
    omega
  have hleftStartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1 := by
    omega
  have hleftInside :
      leftClose < blockStartOf blockSize leftBlock + blockSize := by
    simpa [leftBlock] using
      close_lt_blockStartOf_blockOfClose_add
        (blockSize := blockSize) (close := leftClose)
        (canonicalBPRelativeSummaryBlockSizeRaw_pos shape)
  have hleftEndWidth :
      blockStartOf blockSize leftBlock + blockSize <=
        localBPWindowBase shape blockSize leftClose +
          4 * SuccinctRank.machineWordBits shape.bpCode.length := by
    simpa [leftBlock] using
      localBPWindow_block_end_le_four_words shape blockSize leftClose
        hblockSizeLeThree
  have hleftSuccLeRight : leftBlock + 1 <= rightBlock := by
    simpa [blockSize, leftBlock, rightBlock] using
      Nat.succ_le_of_lt hcross
  have hleftSuccLeCount :
      leftBlock + 1 <= canonicalBPRelativeSummaryBlockCountRaw shape := by
    exact Nat.le_trans hleftSuccLeRight hrightBlockLe
  have hleftEndLen :
      blockStartOf blockSize leftBlock + blockSize <=
        shape.bpCode.length := by
    have hmul := Nat.mul_le_mul_right blockSize hleftSuccLeCount
    have hmulLen :
        (leftBlock + 1) * blockSize <= shape.bpCode.length :=
      Nat.le_trans hmul hblockCountLen
    simpa [blockStartOf, Nat.add_mul, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hmulLen
  have hleftEndCovered :
      blockStartOf blockSize leftBlock + blockSize <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length := by
    exact localBPWindowBits_covers_of_le_width
      (shape := shape) (blockSize := blockSize) (close := leftClose)
      (pos := blockStartOf blockSize leftBlock + blockSize)
      (by omega) hleftEndLen hleftEndWidth
  have hleftSeed :
      (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
          leftClose).value =
        localBPSeedExcess shape blockSize leftClose := by
    simpa [Costed.erase] using
      localBPSeedFromRankCloseCosted_eq_localBPSeedExcess
        shape rankCloseCosted blockSize leftClose hrankExact hleftBaseLen
  have hleftFringe :
      (localBPLeftFringeCandidateSeededCosted shape blockSize leftClose
          (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
            leftClose).value).value =
        (localBPLeftFringeCandidateCosted shape blockSize leftClose).value := by
    rw [hleftSeed]
    simpa [Costed.erase] using
      localBPLeftFringeCandidateSeededCosted_eq_semantic
        (shape := shape) (blockSize := blockSize) (leftClose := leftClose)
        hleftBaseLen hleftStartBase hleftEndCovered hleftInside
  have hrightBaseBlock :
      localBPWindowBase shape blockSize rightClose <=
        blockStartOf blockSize rightBlock := by
    simpa [rightBlock] using
      localBPWindowBase_le_blockStart shape blockSize rightClose
  have hrightInside :
      blockStartOf blockSize rightBlock <= rightClose := by
    simpa [rightBlock] using
      (blockStartOf_blockOfClose_le
        (blockSize := blockSize) (close := rightClose))
  have hrightBaseLen :
      localBPWindowBase shape blockSize rightClose <= shape.bpCode.length := by
    omega
  have hrightEndLen : rightClose + 1 <= shape.bpCode.length := by
    omega
  have hrightBlockEndWidth :
      blockStartOf blockSize rightBlock + blockSize <=
        localBPWindowBase shape blockSize rightClose +
          4 * SuccinctRank.machineWordBits shape.bpCode.length := by
    simpa [rightBlock] using
      localBPWindow_block_end_le_four_words shape blockSize rightClose
        hblockSizeLeThree
  have hrightEndWidth :
      rightClose + 1 <=
        localBPWindowBase shape blockSize rightClose +
          4 * SuccinctRank.machineWordBits shape.bpCode.length := by
    have hrightInsideStrict :
        rightClose < blockStartOf blockSize rightBlock + blockSize := by
      simpa [rightBlock] using
        close_lt_blockStartOf_blockOfClose_add
          (blockSize := blockSize) (close := rightClose)
          (canonicalBPRelativeSummaryBlockSizeRaw_pos shape)
    omega
  have hrightEndCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize rightClose +
          (localBPWindowBits shape blockSize rightClose).length := by
    exact localBPWindowBits_covers_of_le_width
      (shape := shape) (blockSize := blockSize) (close := rightClose)
      (pos := rightClose + 1)
      (by omega) hrightEndLen hrightEndWidth
  have hrightSeed :
      (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
          rightClose).value =
        localBPSeedExcess shape blockSize rightClose := by
    simpa [Costed.erase] using
      localBPSeedFromRankCloseCosted_eq_localBPSeedExcess
        shape rankCloseCosted blockSize rightClose hrankExact hrightBaseLen
  have hrightFringe :
      (localBPRightFringeCandidateSeededCosted shape blockSize rightClose
          (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
            rightClose).value).value =
        (localBPRightFringeCandidateCosted shape blockSize rightClose).value := by
    rw [hrightSeed]
    simpa [Costed.erase] using
      localBPRightFringeCandidateSeededCosted_eq_semantic
        (shape := shape) (blockSize := blockSize) (rightClose := rightClose)
        hrightBaseLen hrightBaseBlock hrightInside hrightEndCovered
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_query
      (shape := shape) (start := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer
  have hmerge :=
    bpRelativeRmmCandidateMerge_exact_of_query_semantics_no_block_bounds
      (shape := shape) (blockSize := blockSize)
      (left := left) (len := len) (leftClose := leftClose)
      (rightClose := rightClose) (answerClose := answerClose)
      hlen hleft hright hanswer
      (canonicalBPRelativeSummaryBlockSizeRaw_pos shape)
      (by simpa [blockSize] using hcross) hsemantic.1 hsemantic.2
  unfold canonicalCrossBlockCloseCostedWithRankSeed
  by_cases hgap : leftBlock + 1 < rightBlock
  case pos =>
    have hcount : 0 < rightBlock - leftBlock - 1 := by omega
    have hmiddle :
        ((canonicalRelativeRmmInteriorDirectory shape).rangeMinCosted
          (leftBlock + 1) (rightBlock - leftBlock - 1)).value =
            some
              (bpRangeMinExcess shape blockSize (leftBlock + 1)
                (rightBlock - leftBlock - 1),
              bpRangeArgMinPrefixPos shape blockSize (leftBlock + 1)
                (rightBlock - leftBlock - 1)) := by
      have hmiddleBound :
          leftBlock + 1 + (rightBlock - leftBlock - 1) <=
            (RelativeRmm.canonicalLayout shape).blockCount := by
        have heq :
            leftBlock + 1 + (rightBlock - leftBlock - 1) = rightBlock := by omega
        simpa [RelativeRmm.canonicalLayout, heq] using hrightBlockLe
      simpa [Costed.erase, RelativeRmm.canonicalLayout, blockSize] using
        canonicalRelativeRmmInteriorDirectory_rangeMinCosted_erase_exact
          (shape := shape) hcount hmiddleBound
    have hmerge' :
        bpCandidateMerge3?
            (localBPLeftFringeCandidateCosted shape blockSize leftClose).value
            (some
              (bpRangeMinExcess shape blockSize (leftBlock + 1)
                (rightBlock - leftBlock - 1),
               bpRangeArgMinPrefixPos shape blockSize (leftBlock + 1)
                (rightBlock - leftBlock - 1)))
            (localBPRightFringeCandidateCosted shape blockSize rightClose).value =
          some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
      simpa [localBPLeftFringeCandidateCosted,
        localBPRightFringeCandidateCosted, blockSize, leftBlock, rightBlock,
        hgap] using hmerge
    simp [Costed.bind, Costed.map, Costed.erase,
      localBPLeftFringeCandidateCosted,
      localBPRightFringeCandidateCosted, hleftFringe, hrightFringe,
      hgap, hmiddle, blockSize, leftBlock, rightBlock]
    change
      bpCandidateClose?
          (bpCandidateMerge3?
            (localBPLeftFringeCandidateCosted shape blockSize leftClose).value
            (some
              (bpRangeMinExcess shape blockSize (leftBlock + 1) (rightBlock - leftBlock - 1),
               bpRangeArgMinPrefixPos shape blockSize (leftBlock + 1) (rightBlock - leftBlock - 1)))
            (localBPRightFringeCandidateCosted shape blockSize rightClose).value) =
        some answerClose
    rw [hmerge']
    simp [bpCandidateClose?]
  case neg =>
    have hmerge' :
        bpCandidateMerge3?
            (localBPLeftFringeCandidateCosted shape blockSize leftClose).value
            none
            (localBPRightFringeCandidateCosted shape blockSize rightClose).value =
          some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
      simpa [localBPLeftFringeCandidateCosted,
        localBPRightFringeCandidateCosted, blockSize, leftBlock, rightBlock,
        hgap] using hmerge
    simp [Costed.bind, Costed.map, Costed.erase, Costed.pure,
      localBPLeftFringeCandidateCosted,
      localBPRightFringeCandidateCosted, hleftFringe, hrightFringe,
      hgap, blockSize, leftBlock, rightBlock]
    change
      bpCandidateClose?
          (bpCandidateMerge3?
            (localBPLeftFringeCandidateCosted shape blockSize leftClose).value
            none
            (localBPRightFringeCandidateCosted shape blockSize rightClose).value) =
        some answerClose
    rw [hmerge']
    simp [bpCandidateClose?]

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments_trace_forall
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace -> P event)
    (hbp :
      forall blockSize close event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize close).trace ->
          P event)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape segments startBlock count).trace ->
          P event) :
    forall event,
      List.Mem event
          (crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
            shape rankCloseTrace segments leftClose rightClose).trace ->
        P event := by
  unfold crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  intro event hmem
  by_cases hmiddle :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose + 1 <
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose
  · simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, hmiddle] at hmem
    rcases List.mem_append.mp hmem with hmem | htail
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize leftClose P hrank event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | htail
    · exact localBPLeftFringeCandidateSeededTraceResult_trace_forall
        shape blockSize leftClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize leftClose).value P
        (hbp blockSize leftClose) event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | htail
    · exact hinterior
        (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          leftClose + 1)
        (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose -
          blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          leftClose - 1)
        event hmem
    rcases List.mem_append.mp htail with hmem | hmem
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize rightClose P hrank event
        (by simpa [blockSize] using hmem)
    · exact localBPRightFringeCandidateSeededTraceResult_trace_forall
        shape blockSize rightClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize rightClose).value P
        (hbp blockSize rightClose) event
        (by simpa [blockSize] using hmem)
  · simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, hmiddle] at hmem
    rcases List.mem_append.mp hmem with hmem | htail
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize leftClose P hrank event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | htail
    · exact localBPLeftFringeCandidateSeededTraceResult_trace_forall
        shape blockSize leftClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize leftClose).value P
        (hbp blockSize leftClose) event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | hmem
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize rightClose P hrank event
        (by simpa [blockSize] using hmem)
    · exact localBPRightFringeCandidateSeededTraceResult_trace_forall
        shape blockSize rightClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize rightClose).value P
        (hbp blockSize rightClose) event
        (by simpa [blockSize] using hmem)

/-- One payload read from the finite-small same-block close table. -/
def finiteSmallSameBlockCloseReadTraceResultAtSegment
    (shape : Cartesian.CartesianShape)
    (segmentBase deadSegment leftClose rightClose : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map (fun entry? => entry?.join)
    ((concreteBPFiniteSmallSameBlockCloseTable shape).readTraceResultAtSegment
      segmentBase deadSegment
      (finiteSmallSameBlockCloseSlot shape leftClose rightClose))

theorem finiteSmallSameBlockCloseReadTraceResultAtSegment_refines
    (shape : Cartesian.CartesianShape)
    (segmentBase deadSegment leftClose rightClose : Nat) :
    (finiteSmallSameBlockCloseReadTraceResultAtSegment
      shape segmentBase deadSegment leftClose rightClose).toCosted =
      finiteSmallSameBlockCloseReadCosted shape leftClose rightClose := by
  simp [finiteSmallSameBlockCloseReadTraceResultAtSegment,
    finiteSmallSameBlockCloseReadCosted,
    FixedWidthOptionNatTable.readTraceResultAtSegment_refines_readCosted,
    WordRAM.TraceResult.map_toCosted, Costed.map]

/--
Compatibility replay for the finite-small same-block table.  The public
all-size close/LCA path below uses the structural BP-code zero-block scan
instead of this table branch.
-/
def finiteSmallSameBlockCloseTraceResultAtSegment
    (shape : Cartesian.CartesianShape)
    (segmentBase deadSegment leftClose rightClose : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  finiteSmallSameBlockCloseReadTraceResultAtSegment
    shape segmentBase deadSegment leftClose rightClose

theorem finiteSmallSameBlockCloseTraceResultAtSegment_refines
    (shape : Cartesian.CartesianShape)
    (segmentBase deadSegment leftClose rightClose : Nat) :
    (finiteSmallSameBlockCloseTraceResultAtSegment
      shape segmentBase deadSegment leftClose rightClose).toCosted =
      finiteSmallSameBlockCloseCosted shape leftClose rightClose := by
  apply Costed.ext
  · change
      (finiteSmallSameBlockCloseTraceResultAtSegment
        shape segmentBase deadSegment leftClose rightClose).toCosted.erase =
        (finiteSmallSameBlockCloseCosted
          shape leftClose rightClose).erase
    simp [finiteSmallSameBlockCloseTraceResultAtSegment,
      finiteSmallSameBlockCloseCosted,
      finiteSmallSameBlockCloseReadTraceResultAtSegment_refines]
  · simp [finiteSmallSameBlockCloseTraceResultAtSegment,
      finiteSmallSameBlockCloseCosted,
      finiteSmallSameBlockCloseReadTraceResultAtSegment_refines]

theorem finiteSmallSameBlockCloseTraceResultAtSegment_refines_local
    (shape : Cartesian.CartesianShape)
    (segmentBase deadSegment leftClose rightClose : Nat) :
    (finiteSmallSameBlockCloseTraceResultAtSegment
      shape segmentBase deadSegment leftClose rightClose).toCosted.erase =
      (localBPSameBlockCloseCosted shape leftClose rightClose).erase := by
  rw [finiteSmallSameBlockCloseTraceResultAtSegment_refines,
    finiteSmallSameBlockCloseCosted_refines_local]

theorem finiteSmallSameBlockCloseReadTraceResultAtSegment_trace_forall
    (shape : Cartesian.CartesianShape)
    (segmentBase deadSegment leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hread :
      forall event,
        List.Mem event
          ((concreteBPFiniteSmallSameBlockCloseTable shape).readTraceResultAtSegment
            segmentBase deadSegment
            (finiteSmallSameBlockCloseSlot shape leftClose rightClose)).trace ->
          P event) :
    forall event,
      List.Mem event
          (finiteSmallSameBlockCloseReadTraceResultAtSegment
            shape segmentBase deadSegment leftClose rightClose).trace ->
        P event := by
  unfold finiteSmallSameBlockCloseReadTraceResultAtSegment
  exact WordRAM.TraceResult.map_trace_forall _ _ _ hread

theorem finiteSmallSameBlockCloseTraceResultAtSegment_trace_forall
    (shape : Cartesian.CartesianShape)
    (segmentBase deadSegment leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hread :
      forall event,
        List.Mem event
          (finiteSmallSameBlockCloseReadTraceResultAtSegment
            shape segmentBase deadSegment leftClose rightClose).trace ->
        P event) :
    forall event,
      List.Mem event
          (finiteSmallSameBlockCloseTraceResultAtSegment
            shape segmentBase deadSegment leftClose rightClose).trace ->
        P event := by
  unfold finiteSmallSameBlockCloseTraceResultAtSegment
  exact hread

theorem finiteSmallSameBlockCloseTraceResultAtSegment_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (segmentBase deadSegment leftClose rightClose : Nat)
    (store : WordRAM.ReadStore)
    (hsegment :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index =
          (concreteBPFiniteSmallSameBlockCloseTable
            shape).wordRAMStore.readWord? segment index) :
    forall event,
      List.Mem event
          (finiteSmallSameBlockCloseTraceResultAtSegment
            shape segmentBase deadSegment leftClose rightClose).trace ->
        event.matchesReadStore store := by
  apply finiteSmallSameBlockCloseTraceResultAtSegment_trace_forall
  intro event hmem
  exact
    finiteSmallSameBlockCloseReadTraceResultAtSegment_trace_forall
      shape segmentBase deadSegment leftClose rightClose
      (fun event => event.matchesReadStore store)
      (fixedWidthOptionNatTable_readTraceResultAtSegment_matchesReadStore
        (concreteBPFiniteSmallSameBlockCloseTable shape)
        segmentBase deadSegment
        (finiteSmallSameBlockCloseSlot shape leftClose rightClose)
        store hsegment) event hmem

theorem finiteSmallSameBlockCloseTraceResultAtSegment_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (segmentBase deadSegment leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (finiteSmallSameBlockCloseTraceResultAtSegment
            shape segmentBase deadSegment leftClose rightClose).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  apply finiteSmallSameBlockCloseTraceResultAtSegment_trace_forall
  intro event hmem
  exact
    finiteSmallSameBlockCloseReadTraceResultAtSegment_trace_forall
      shape segmentBase deadSegment leftClose rightClose
      (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
      ((concreteBPFiniteSmallSameBlockCloseTable
        shape).readTraceResultAtSegment_no_syntheticCostOnlyPrimitive
        segmentBase deadSegment
        (finiteSmallSameBlockCloseSlot shape leftClose rightClose))
      event hmem

/-- Read every BP-code payload chunk used by the zero-block same-block replay. -/
def zeroBlockSameBlockCloseWordsTraceResult
    (shape : Cartesian.CartesianShape) :
    WordRAM.TraceResult (List (List Bool)) where
  value := zeroBlockSameBlockCloseStructuralWords shape
  trace :=
    (List.range (zeroBlockSameBlockCloseStructuralWords shape).length).map
      (fun index => bpCodeReadWordTraceEvent shape index)

theorem zeroBlockSameBlockCloseWordsTraceResult_value
    (shape : Cartesian.CartesianShape) :
    (zeroBlockSameBlockCloseWordsTraceResult shape).value =
      zeroBlockSameBlockCloseStructuralWords shape := by
  rfl

theorem zeroBlockSameBlockCloseWordsTraceResult_trace_length
    (shape : Cartesian.CartesianShape) :
    (zeroBlockSameBlockCloseWordsTraceResult shape).trace.length =
      (zeroBlockSameBlockCloseStructuralWords shape).length := by
  simp [zeroBlockSameBlockCloseWordsTraceResult]

private theorem list_range_flatMap_getElem?_singleton
    (words : List (List Bool)) :
    (List.range words.length).flatMap
        (fun index =>
          match words[index]? with
          | some word => [word]
          | none => []) =
      words := by
  induction words with
  | nil =>
      simp
  | cons word words ih =>
      change
        (List.range (words.length + 1)).flatMap
            (fun index =>
              match (word :: words)[index]? with
              | some word => [word]
              | none => []) =
          word :: words
      rw [List.range_succ_eq_map]
      simp [List.flatMap_map, List.getElem?_cons_succ, ih]

def readStorePayloadWordValue
    (store : WordRAM.ReadStore) (segment index : Nat) :
    List (List Bool) :=
  match store.readWord? segment index with
  | some word => [word]
  | none => []

/--
Store-parameterized read of every BP-code payload chunk used by the zero-block
same-block replay.  Unlike `zeroBlockSameBlockCloseWordsTraceResult`, both the
returned words and read events are produced from the supplied read store.
-/
def zeroBlockSameBlockCloseWordsTraceResultWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore) :
    WordRAM.TraceResult (List (List Bool)) where
  value :=
    (List.range (zeroBlockSameBlockCloseStructuralWords shape).length).flatMap
      (fun index => readStorePayloadWordValue store 0 index)
  trace :=
    (List.range (zeroBlockSameBlockCloseStructuralWords shape).length).map
      (fun index =>
        WordRAM.TraceEvent.readWord 0 index (store.readWord? 0 index))

theorem zeroBlockSameBlockCloseWordsTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore) :
    forall event,
      List.Mem event
          (zeroBlockSameBlockCloseWordsTraceResultWithStore
            shape store).trace ->
        event.matchesReadStore store := by
  intro event hmem
  rcases List.mem_map.mp hmem with ⟨index, _hindex, rfl⟩
  simp [WordRAM.TraceEvent.matchesReadStore]

theorem zeroBlockSameBlockCloseWordsTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore) :
    forall event,
      List.Mem event
          (zeroBlockSameBlockCloseWordsTraceResultWithStore
            shape store).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  intro event hmem
  rcases List.mem_map.mp hmem with ⟨index, _hindex, rfl⟩
  simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

theorem zeroBlockSameBlockCloseWordsTraceResultWithStore_value_eq_of_store_agreement
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?) :
    (zeroBlockSameBlockCloseWordsTraceResultWithStore
      shape store).value =
      (zeroBlockSameBlockCloseWordsTraceResult shape).value := by
  simpa [zeroBlockSameBlockCloseWordsTraceResultWithStore,
    zeroBlockSameBlockCloseWordsTraceResult,
    zeroBlockSameBlockCloseStructuralWords,
    readStorePayloadWordValue, hbpCode] using
    list_range_flatMap_getElem?_singleton
      (SuccinctSpace.chunkPayloadWords
        (SuccinctRank.machineWordBits shape.bpCode.length)
        shape.bpCode)

theorem zeroBlockSameBlockCloseWordsTraceResultWithStore_trace_eq_of_store_agreement
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?) :
    (zeroBlockSameBlockCloseWordsTraceResultWithStore
      shape store).trace =
      (zeroBlockSameBlockCloseWordsTraceResult shape).trace := by
  simp [zeroBlockSameBlockCloseWordsTraceResultWithStore,
    zeroBlockSameBlockCloseWordsTraceResult,
    bpCodeReadWordTraceEvent, hbpCode]

/--
Store-parameterized zero-block same-block evaluator.

The trace and answer are evaluated from `store.readWord?` at the BP-code segment,
then decoded by the bits-derived zero-block value function.
-/
def zeroBlockSameBlockCloseStructuralTraceResultWithStore
    (shape : Cartesian.CartesianShape)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map
    (fun words =>
      zeroBlockSameBlockCloseStructuralValueFromWords
        shape words leftClose rightClose)
    (zeroBlockSameBlockCloseWordsTraceResultWithStore shape store)

theorem zeroBlockSameBlockCloseStructuralTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (zeroBlockSameBlockCloseStructuralTraceResultWithStore
            shape store leftClose rightClose).trace ->
        event.matchesReadStore store := by
  exact
    WordRAM.TraceResult.map_trace_forall
      (fun event => event.matchesReadStore store)
      (fun words =>
        zeroBlockSameBlockCloseStructuralValueFromWords
          shape words leftClose rightClose)
      (zeroBlockSameBlockCloseWordsTraceResultWithStore shape store)
      (zeroBlockSameBlockCloseWordsTraceResultWithStore_matchesReadStore
        shape store)

theorem zeroBlockSameBlockCloseStructuralTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (zeroBlockSameBlockCloseStructuralTraceResultWithStore
            shape store leftClose rightClose).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  exact
    WordRAM.TraceResult.map_trace_forall
      (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
      (fun words =>
        zeroBlockSameBlockCloseStructuralValueFromWords
          shape words leftClose rightClose)
      (zeroBlockSameBlockCloseWordsTraceResultWithStore shape store)
      (zeroBlockSameBlockCloseWordsTraceResultWithStore_no_syntheticCostOnlyPrimitive
        shape store)

theorem zeroBlockSameBlockCloseStructuralTraceResult_store_parametric
    (shape : Cartesian.CartesianShape)
    (storeA storeB : WordRAM.ReadStore)
    (leftClose rightClose : Nat)
    (hread :
      forall index, storeA.readWord? 0 index = storeB.readWord? 0 index) :
    (zeroBlockSameBlockCloseStructuralTraceResultWithStore
      shape storeA leftClose rightClose).value =
        (zeroBlockSameBlockCloseStructuralTraceResultWithStore
          shape storeB leftClose rightClose).value /\
      (zeroBlockSameBlockCloseStructuralTraceResultWithStore
        shape storeA leftClose rightClose).trace =
        (zeroBlockSameBlockCloseStructuralTraceResultWithStore
          shape storeB leftClose rightClose).trace := by
  constructor <;>
    simp [zeroBlockSameBlockCloseStructuralTraceResultWithStore,
      zeroBlockSameBlockCloseWordsTraceResultWithStore,
      readStorePayloadWordValue, hread]

theorem zeroBlockSameBlockCloseWordsTraceResult_trace_forall
    (shape : Cartesian.CartesianShape)
    (P : WordRAM.TraceEvent -> Prop)
    (hbpCode :
      forall index, P (bpCodeReadWordTraceEvent shape index)) :
    forall event,
      List.Mem event (zeroBlockSameBlockCloseWordsTraceResult shape).trace ->
        P event := by
  intro event hmem
  rcases List.mem_map.mp hmem with ⟨index, _hindex, rfl⟩
  exact hbpCode index

theorem zeroBlockSameBlockCloseWordsTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (store : WordRAM.ReadStore)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?) :
    forall event,
      List.Mem event (zeroBlockSameBlockCloseWordsTraceResult shape).trace ->
        event.matchesReadStore store := by
  exact
    zeroBlockSameBlockCloseWordsTraceResult_trace_forall shape
      (fun event => event.matchesReadStore store)
      (fun index => by
        simp [bpCodeReadWordTraceEvent, WordRAM.TraceEvent.matchesReadStore,
          hbpCode index])

theorem zeroBlockSameBlockCloseWordsTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) :
    forall event,
      List.Mem event (zeroBlockSameBlockCloseWordsTraceResult shape).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  exact
    zeroBlockSameBlockCloseWordsTraceResult_trace_forall shape
      (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
      (fun index => by
        simp [bpCodeReadWordTraceEvent,
          WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive])

/--
Structural zero-block same-block fallback.

When the canonical block size is zero, the close replay scans the counted
chunked BP-code payload directly and computes the same prefix-min answer as the
costed local BP specification.
-/
def zeroBlockSameBlockCloseStructuralTraceResult
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map
    (fun words =>
      zeroBlockSameBlockCloseStructuralValueFromWords
        shape words leftClose rightClose)
    (zeroBlockSameBlockCloseWordsTraceResult shape)

theorem zeroBlockSameBlockCloseStructuralTraceResult_evalWithStore
    (shape : Cartesian.CartesianShape)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?) :
    (zeroBlockSameBlockCloseStructuralTraceResultWithStore
      shape store leftClose rightClose).value =
        (zeroBlockSameBlockCloseStructuralTraceResult
          shape leftClose rightClose).value /\
      (zeroBlockSameBlockCloseStructuralTraceResultWithStore
        shape store leftClose rightClose).trace =
        (zeroBlockSameBlockCloseStructuralTraceResult
          shape leftClose rightClose).trace := by
  constructor
  · simp [zeroBlockSameBlockCloseStructuralTraceResultWithStore,
      zeroBlockSameBlockCloseStructuralTraceResult,
      zeroBlockSameBlockCloseWordsTraceResultWithStore_value_eq_of_store_agreement
        shape store hbpCode]
  · simp [zeroBlockSameBlockCloseStructuralTraceResultWithStore,
      zeroBlockSameBlockCloseStructuralTraceResult,
      zeroBlockSameBlockCloseWordsTraceResultWithStore_trace_eq_of_store_agreement
        shape store hbpCode]

theorem zeroBlockSameBlockCloseStructuralTraceResult_refines
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (zeroBlockSameBlockCloseStructuralTraceResult
      shape leftClose rightClose).toCosted =
      zeroBlockSameBlockCloseCosted shape leftClose rightClose := by
  apply Costed.ext
  · simp [zeroBlockSameBlockCloseStructuralTraceResult,
      zeroBlockSameBlockCloseWordsTraceResult,
      zeroBlockSameBlockCloseCosted,
      zeroBlockSameBlockCloseStructuralValue]
  · simp [zeroBlockSameBlockCloseStructuralTraceResult,
      zeroBlockSameBlockCloseWordsTraceResult_trace_length,
      zeroBlockSameBlockCloseCosted]

theorem zeroBlockSameBlockCloseStructuralTraceResult_exact
    {shape : Cartesian.CartesianShape}
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (zeroBlockSameBlockCloseStructuralTraceResult
      shape leftClose rightClose).value =
      some answerClose := by
  simpa [zeroBlockSameBlockCloseStructuralTraceResult,
    zeroBlockSameBlockCloseWordsTraceResult,
    zeroBlockSameBlockCloseStructuralValue] using
    zeroBlockSameBlockCloseStructuralValue_exact
      hlen hbound hleft hright hanswer

theorem zeroBlockSameBlockCloseStructuralTraceResult_trace_forall
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hbpCode :
      forall index, P (bpCodeReadWordTraceEvent shape index)) :
    forall event,
      List.Mem event
          (zeroBlockSameBlockCloseStructuralTraceResult
            shape leftClose rightClose).trace ->
        P event := by
  exact
    WordRAM.TraceResult.map_trace_forall P
      (fun words =>
        zeroBlockSameBlockCloseStructuralValueFromWords
          shape words leftClose rightClose)
      (zeroBlockSameBlockCloseWordsTraceResult shape)
      (zeroBlockSameBlockCloseWordsTraceResult_trace_forall
        shape P hbpCode)

theorem zeroBlockSameBlockCloseStructuralTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat)
    (store : WordRAM.ReadStore)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?) :
    forall event,
      List.Mem event
          (zeroBlockSameBlockCloseStructuralTraceResult
            shape leftClose rightClose).trace ->
        event.matchesReadStore store := by
  exact
    zeroBlockSameBlockCloseStructuralTraceResult_trace_forall
      shape leftClose rightClose
      (fun event => event.matchesReadStore store)
      (fun index => by
        simp [bpCodeReadWordTraceEvent, WordRAM.TraceEvent.matchesReadStore,
          hbpCode index])

theorem zeroBlockSameBlockCloseStructuralTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (zeroBlockSameBlockCloseStructuralTraceResult
            shape leftClose rightClose).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  exact
    zeroBlockSameBlockCloseStructuralTraceResult_trace_forall
      shape leftClose rightClose
      (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
      (fun index => by
        simp [bpCodeReadWordTraceEvent,
          WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive])

/--
Trace-preserving compact close/LCA query.

The rank-seed reads and bounded local BP endpoint decoders are structural
Word-RAM traces. The zero-block branch scans counted BP-code chunks; the
relative-rmM interior query remains an older charged decoder leaf on this
compatibility trace.
-/
def lcaCloseTraceResultWithRankSeed
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  if blockSize = 0 then
    zeroBlockSameBlockCloseStructuralTraceResult shape leftClose rightClose
  else if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    localBPSameBlockCloseDecodedTraceResultWithRankSeed
      shape rankCloseTrace blockSize leftClose rightClose
  else
    directory.crossBlockCloseTraceResultWithRankSeed
      rankCloseTrace leftClose rightClose

theorem lcaCloseTraceResultWithRankSeed_refines
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (directory.lcaCloseTraceResultWithRankSeed
      rankCloseTrace leftClose rightClose).toCosted =
      directory.lcaCloseCostedWithRankSeed
        rankCloseCosted leftClose rightClose := by
  by_cases hzero : canonicalBPRelativeSummaryBlockSize shape = 0
  · simp [lcaCloseTraceResultWithRankSeed, lcaCloseCostedWithRankSeed,
      hzero, zeroBlockSameBlockCloseStructuralTraceResult_refines]
  · by_cases hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose
    · simp [lcaCloseTraceResultWithRankSeed, lcaCloseCostedWithRankSeed,
        hzero, hsame,
        localBPSameBlockCloseDecodedTraceResultWithRankSeed_refines,
        hrank]
    · simp [lcaCloseTraceResultWithRankSeed, lcaCloseCostedWithRankSeed,
        hzero, hsame, crossBlockCloseTraceResultWithRankSeed_refines,
        hrank]

theorem lcaCloseTraceResultWithRankSeed_matchesReadStore
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (leftClose rightClose : Nat)
    (store : WordRAM.ReadStore)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          event.matchesReadStore store)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hbp :
      forall blockSize close event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize close).trace ->
          event.matchesReadStore store) :
    forall event,
      List.Mem event
          (directory.lcaCloseTraceResultWithRankSeed
            rankCloseTrace leftClose rightClose).trace ->
        event.matchesReadStore store := by
  by_cases hzero : canonicalBPRelativeSummaryBlockSize shape = 0
  · simp [lcaCloseTraceResultWithRankSeed, hzero]
    exact
      zeroBlockSameBlockCloseStructuralTraceResult_matchesReadStore
        shape leftClose rightClose store hbpCode
  · by_cases hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose
    · simp [lcaCloseTraceResultWithRankSeed, hzero, hsame]
      exact
        localBPSameBlockCloseDecodedTraceResultWithRankSeed_trace_forall
          shape rankCloseTrace
          (canonicalBPRelativeSummaryBlockSize shape)
          leftClose rightClose
          (fun event => event.matchesReadStore store)
          hrank
          (hbp (canonicalBPRelativeSummaryBlockSize shape) leftClose)
    · simp [lcaCloseTraceResultWithRankSeed, hzero, hsame]
      exact
        crossBlockCloseTraceResultWithRankSeed_matchesReadStore
          directory rankCloseTrace leftClose rightClose store hrank hbp

/--
Legacy all-size close/LCA trace decomposition: every event in the old total
trace comes from structural rank/BP leaves, the structural BP-code zero-block
same-block scan, or the remaining `TraceResult.ofCosted` boundary for the
cross-block interior relative-rmM query.
-/
theorem lcaCloseTraceResultWithRankSeed_legacy_ofCosted_boundary_trace_forall
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace -> P event)
    (hbp :
      forall blockSize close event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize close).trace ->
          P event)
    (hsameZero :
      forall event,
        List.Mem event
          (zeroBlockSameBlockCloseStructuralTraceResult
            shape leftClose rightClose).trace ->
          P event)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (WordRAM.TraceResult.ofCosted
            (directory.interior.rangeMinCosted startBlock count)).trace ->
          P event) :
    forall event,
      List.Mem event
          (directory.lcaCloseTraceResultWithRankSeed
            rankCloseTrace leftClose rightClose).trace ->
        P event := by
  by_cases hzero : canonicalBPRelativeSummaryBlockSize shape = 0
  · simp [lcaCloseTraceResultWithRankSeed, hzero]
    exact hsameZero
  · by_cases hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose
    · simp [lcaCloseTraceResultWithRankSeed, hzero, hsame]
      exact
        localBPSameBlockCloseDecodedTraceResultWithRankSeed_trace_forall
          shape rankCloseTrace
          (canonicalBPRelativeSummaryBlockSize shape)
          leftClose rightClose P hrank
          (hbp (canonicalBPRelativeSummaryBlockSize shape) leftClose)
    · simp [lcaCloseTraceResultWithRankSeed, hzero, hsame]
      exact
        crossBlockCloseTraceResultWithRankSeed_trace_forall
          directory rankCloseTrace leftClose rightClose P hrank hbp
          hinterior

/--
Concrete large-regime compact close/LCA query trace.

The large-regime hypothesis routes through the positive dispatch, so the
zero-block structural scan is not part of this replay.  The cross-block case
uses the concrete interior relative-rmM trace.
-/
def lcaCloseTraceResultWithRankSeedOfReady
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    localBPSameBlockCloseDecodedTraceResultWithRankSeed
      shape rankCloseTrace blockSize leftClose rightClose
  else
    crossBlockCloseTraceResultWithRankSeedOfReady
      shape rankCloseTrace hready leftClose rightClose

/- theorem lcaCloseTraceResultWithRankSeedOfSizeGe_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (lcaCloseTraceResultWithRankSeedOfSizeGe
      shape rankCloseTrace hsize leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  have hdispatch :=
    ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed_eq_positive_dispatch_of_size_ge
      (concreteCompactBPCloseLCADirectory shape)
      rankCloseCosted leftClose rightClose hsize
  rw [hdispatch]
  by_cases hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose
  Â· simp [lcaCloseTraceResultWithRankSeedOfSizeGe, hsame,
      localBPSameBlockCloseDecodedTraceResultWithRankSeed_refines,
      hrank]
  Â· simp [lcaCloseTraceResultWithRankSeedOfSizeGe, hsame,
      crossBlockCloseTraceResultWithRankSeedOfSizeGe_refines,
      hrank]
-/

theorem lcaCloseTraceResultWithRankSeedOfReady_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (lcaCloseTraceResultWithRankSeedOfReady
      shape rankCloseTrace hready leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  have hdispatch :=
    ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed_eq_positive_dispatch_of_ready
      (concreteCompactBPCloseLCADirectory shape)
      rankCloseCosted leftClose rightClose hready
  rw [hdispatch]
  by_cases hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose
  case pos =>
    simp [lcaCloseTraceResultWithRankSeedOfReady, hsame,
      localBPSameBlockCloseDecodedTraceResultWithRankSeed_refines,
      hrank]
  case neg =>
    simp [lcaCloseTraceResultWithRankSeedOfReady, hsame,
      crossBlockCloseTraceResultWithRankSeedOfReady_refines,
      concreteCompactBPCloseLCADirectory, hrank]

def lcaCloseTraceResultWithRankSeedOfSizeGe
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  lcaCloseTraceResultWithRankSeedOfReady shape rankCloseTrace
    (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
    leftClose rightClose

theorem lcaCloseTraceResultWithRankSeedOfSizeGe_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (lcaCloseTraceResultWithRankSeedOfSizeGe
      shape rankCloseTrace hsize leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  exact
    lcaCloseTraceResultWithRankSeedOfReady_refines
      shape rankCloseTrace rankCloseCosted
      (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
      leftClose rightClose hrank

/--
Large-regime compact close/LCA trace with caller-controlled interior table
segment bases.

The caller supplies an already-relabeled rank-seed trace callback.  Local BP
window reads stay at the shared BP-code segment 0; only the interior navigator
tables are routed through `segments`.
-/
def lcaCloseTraceResultWithRankSeedAtSegmentsOfReady
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    localBPSameBlockCloseDecodedTraceResultWithRankSeed
      shape rankCloseTrace blockSize leftClose rightClose
  else
    crossBlockCloseTraceResultWithRankSeedAtSegmentsOfReady
      shape rankCloseTrace hready segments leftClose rightClose

theorem lcaCloseTraceResultWithRankSeedAtSegmentsOfReady_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (lcaCloseTraceResultWithRankSeedAtSegmentsOfReady
      shape rankCloseTrace hready segments leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  have hdispatch :=
    ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed_eq_positive_dispatch_of_ready
      (concreteCompactBPCloseLCADirectory shape)
      rankCloseCosted leftClose rightClose hready
  rw [hdispatch]
  by_cases hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose
  case pos =>
    simp [lcaCloseTraceResultWithRankSeedAtSegmentsOfReady, hsame,
      localBPSameBlockCloseDecodedTraceResultWithRankSeed_refines,
      hrank]
  case neg =>
    simp [lcaCloseTraceResultWithRankSeedAtSegmentsOfReady, hsame,
      crossBlockCloseTraceResultWithRankSeedAtSegmentsOfReady_refines,
      concreteCompactBPCloseLCADirectory, hrank]

def lcaCloseTraceResultWithRankSeedAtSegmentsOfSizeGe
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  lcaCloseTraceResultWithRankSeedAtSegmentsOfReady shape rankCloseTrace
    (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
    segments leftClose rightClose

theorem lcaCloseTraceResultWithRankSeedAtSegmentsOfSizeGe_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (lcaCloseTraceResultWithRankSeedAtSegmentsOfSizeGe
      shape rankCloseTrace hsize segments leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  exact
    lcaCloseTraceResultWithRankSeedAtSegmentsOfReady_refines
      shape rankCloseTrace rankCloseCosted
      (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
      segments leftClose rightClose hrank

theorem lcaCloseTraceResultWithRankSeedAtSegmentsOfReady_trace_forall
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace -> P event)
    (hbp :
      forall blockSize close event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize close).trace ->
          P event)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
            shape hready segments startBlock count).trace ->
          P event) :
    forall event,
      List.Mem event
          (lcaCloseTraceResultWithRankSeedAtSegmentsOfReady
            shape rankCloseTrace hready segments leftClose rightClose).trace ->
        P event := by
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  · simpa [lcaCloseTraceResultWithRankSeedAtSegmentsOfReady, blockSize,
      hsame] using
      localBPSameBlockCloseDecodedTraceResultWithRankSeed_trace_forall
        shape rankCloseTrace blockSize leftClose rightClose P hrank
        (hbp blockSize leftClose)
  · simpa [lcaCloseTraceResultWithRankSeedAtSegmentsOfReady, blockSize,
      hsame] using
      crossBlockCloseTraceResultWithRankSeedAtSegmentsOfReady_trace_forall
        shape rankCloseTrace hready segments leftClose rightClose P
        hrank hbp hinterior

theorem lcaCloseTraceResultWithRankSeedAtSegmentsOfSizeGe_trace_forall
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace -> P event)
    (hbp :
      forall blockSize close event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize close).trace ->
          P event)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe
            shape hsize segments startBlock count).trace ->
          P event) :
    forall event,
      List.Mem event
          (lcaCloseTraceResultWithRankSeedAtSegmentsOfSizeGe
            shape rankCloseTrace hsize segments leftClose rightClose).trace ->
        P event := by
  exact
    lcaCloseTraceResultWithRankSeedAtSegmentsOfReady_trace_forall
      shape rankCloseTrace
      (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
      segments leftClose rightClose P hrank hbp
      (by
        intro startBlock count event hmem
        exact hinterior startBlock count event hmem)

theorem lcaCloseTraceResultWithRankSeedAtSegmentsOfReady_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat)
    (store : WordRAM.ReadStore)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          event.matchesReadStore store)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
            shape hready segments startBlock count).trace ->
          event.matchesReadStore store) :
    forall event,
      List.Mem event
          (lcaCloseTraceResultWithRankSeedAtSegmentsOfReady
            shape rankCloseTrace hready segments leftClose rightClose).trace ->
        event.matchesReadStore store := by
  exact
    lcaCloseTraceResultWithRankSeedAtSegmentsOfReady_trace_forall
      shape rankCloseTrace hready segments leftClose rightClose
      (fun event => event.matchesReadStore store)
      hrank
      (fun blockSize close =>
        localBPWindowBitsTraceResult_matchesReadStore
          shape blockSize close store hbpCode)
      hinterior

theorem lcaCloseTraceResultWithRankSeedAtSegmentsOfSizeGe_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat)
    (store : WordRAM.ReadStore)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          event.matchesReadStore store)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe
            shape hsize segments startBlock count).trace ->
          event.matchesReadStore store) :
    forall event,
      List.Mem event
          (lcaCloseTraceResultWithRankSeedAtSegmentsOfSizeGe
            shape rankCloseTrace hsize segments leftClose rightClose).trace ->
        event.matchesReadStore store := by
  exact
    lcaCloseTraceResultWithRankSeedAtSegmentsOfReady_matchesReadStore
      shape rankCloseTrace
      (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)
      segments leftClose rightClose store hrank hbpCode
      (by
        intro startBlock count event hmem
        exact hinterior startBlock count event hmem)

/-- Compact close/LCA query using the interpreted false-rank seed callback. -/
def lcaCloseCostedWithInterpretedRankSeed
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  directory.lcaCloseCostedWithRankSeed
    (fun pos => interpretedRankCloseCosted rankData pos)
    leftClose rightClose

theorem lcaCloseCostedWithInterpretedRankSeed_refines_lcaCloseCostedWithRankSeed
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (leftClose rightClose : Nat) :
    directory.lcaCloseCostedWithInterpretedRankSeed rankData leftClose
        rightClose =
      directory.lcaCloseCostedWithRankSeed
        (fun pos => rankData.rankCostedClamped false pos)
        leftClose rightClose := by
  have hfun :
      (fun pos => interpretedRankCloseCosted rankData pos) =
        (fun pos => rankData.rankCostedClamped false pos) := by
    funext pos
    exact interpretedRankCloseCosted_refines_rankCostedClamped
      (rankData := rankData) (pos := pos)
  simp [lcaCloseCostedWithInterpretedRankSeed, hfun]

theorem lcaCloseCostedWithInterpretedRankSeed_cost_le
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCostedWithInterpretedRankSeed rankData leftClose
        rightClose).cost <=
      concreteCompactBPCloseQueryCostWithRankSeed 3 := by
  unfold lcaCloseCostedWithInterpretedRankSeed
  exact
    directory.lcaCloseCostedWithRankSeed_cost_le
      (fun pos => interpretedRankCloseCosted rankData pos)
      leftClose rightClose 3
      (by
        intro pos
        exact interpretedRankCloseCosted_cost_le_three
          (rankData := rankData) (pos := pos))

theorem lcaCloseCostedWithInterpretedRankSeed_exact_of_query
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (directory.lcaCloseCostedWithInterpretedRankSeed rankData leftClose
        rightClose).erase =
      some answerClose := by
  unfold lcaCloseCostedWithInterpretedRankSeed
  exact
    directory.lcaCloseCostedWithRankSeed_exact_of_query
      (fun pos => interpretedRankCloseCosted rankData pos)
      (by
        intro pos
        exact interpretedRankCloseCosted_exact
          (rankData := rankData) (pos := pos))
      hlen hbound hleft hright hanswer

theorem lcaCloseCostedWithInterpretedRankSeed_profile
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead) :
    (forall leftClose rightClose,
      (directory.lcaCloseCostedWithInterpretedRankSeed rankData leftClose
        rightClose).cost <=
          concreteCompactBPCloseQueryCostWithRankSeed 3) /\
      (forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCostedWithInterpretedRankSeed rankData
                    leftClose rightClose).erase =
                    some answerClose) := by
  constructor
  next =>
    intro leftClose rightClose
    exact directory.lcaCloseCostedWithInterpretedRankSeed_cost_le
      rankData leftClose rightClose
  next =>
    intro left len leftClose rightClose answerClose hlen hbound hleft hright
      hanswer
    exact directory.lcaCloseCostedWithInterpretedRankSeed_exact_of_query
      rankData hlen hbound hleft hright hanswer

end ConcreteCompactBPCloseLCADirectory

end SuccinctClose
end RMQ
