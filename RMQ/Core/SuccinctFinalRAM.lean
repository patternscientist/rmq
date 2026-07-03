import RMQ.Core.SuccinctFinal
import RMQ.Core.GenericSelect.RAM
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAM
import RMQ.Core.WordRAM.Register

/-!
# Word-RAM bridge for the final BP-native succinct RMQ query

This module is an additive refinement layer over `SuccinctFinal`.  The existing
final capstone remains the reference theorem; the definitions below replay the
same final query shape with interpreted close-select, rank-seed, and answer-rank
leaves, then prove that the interpreted query refines the existing `Costed`
query.
-/

namespace RMQ
namespace SuccinctFinal

/-- Interpreted close-select leg for the built generic sparse-exception source. -/
def concreteBPNativeSelectCloseInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : Costed (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    |>.selectInterpretedCosted idx

/-- Interpreted false-rank leg for the built BP-close rank component. -/
def concreteBPNativeRankCloseInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (pos : Nat) : Costed Nat :=
  (builtRelativeSplitBPCloseRankData shape)
    |>.rankRegisterInterpretedCosted false pos

/-- Structural `WordRAM.TraceEvent` replay for the close-select leg. -/
def concreteBPNativeSelectCloseWordTraceResult
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    |>.selectTraceResult idx

theorem concreteBPNativeSelectCloseWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseWordTraceResult shape idx).toCosted =
      concreteBPNativeSelectCloseInterpretedCosted shape idx := by
  simp [concreteBPNativeSelectCloseWordTraceResult,
    concreteBPNativeSelectCloseInterpretedCosted,
    GenericSelect.SparseExceptionSelectData.selectTraceResult_refines_interpretedCosted]

/--
Concrete global segment layout for the generic sparse-exception close-select
trace. Segment `0` is reserved for the shared BP-code word store; auxiliary
tables start at segment `1`.
-/
def concreteBPNativeDeadTraceSegment : Nat := 26

def concreteBPNativeSelectCloseTraceSegmentLayout :
    GenericSelect.SparseExceptionSelectTraceSegmentLayout where
  superTable :=
    { baseOccurrence := 1
      baseWordIndex := 2
      rankBefore := 3
      firstOffset := 4
      deadSegment := concreteBPNativeDeadTraceSegment }
  localTable :=
    { baseOccurrence := 5
      baseWordIndex := 6
      rankBefore := 7
      firstOffset := 8
      deadSegment := concreteBPNativeDeadTraceSegment }
  longFlagRankBase := 9
  longRelativeBase := 12
  sparseDirectory :=
    { rankBase := 13
      relativeBase := 16
      deadSegment := concreteBPNativeDeadTraceSegment }
  bitWordBase := 0
  deadSegment := concreteBPNativeDeadTraceSegment

/-- Segment base for the final false-rank callback used by answer recovery. -/
def concreteBPNativeRankCloseTraceSegmentBase : Nat := 17

/-- Segment bases for the compact close/LCA interior navigator. -/
def concreteBPNativeInteriorTraceSegments :
    SuccinctClose.BPRelativeRmmInteriorTraceSegments where
  summary :=
    { baseline := 20
      minRel := 21
      maxRel := 22
      argOffset := 23
      deadSegment := concreteBPNativeDeadTraceSegment }
  localOffset := 24
  globalBlock := 25
  deadSegment := concreteBPNativeDeadTraceSegment

/--
The concrete read-only payload store for the globally segmented final RMQ
trace.

Segments are assigned as follows:
* `0`: packed BP-code words shared by select, rank, and local-BP decoders.
* `1..16`: close-select auxiliary tables.
* `17..19`: final false-rank samples and packed BP-code words.
* `20..25`: compact close/LCA relative-rmM interior tables.

Word-primitive events such as in-word rank/select are not payload reads and
therefore do not consult this store.
-/
def concreteBPNativeSuccinctRMQGlobalReadStore
    (shape : Cartesian.CartesianShape) : WordRAM.ReadStore where
  readWord? segment index :=
    let selectData :=
      GenericSelect.sparseExceptionSelectData shape.bpCode false
    let rankStore :=
      (builtRelativeSplitBPCloseRankData shape).rankRegisterWordRAMStore false
    let summary :=
      SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    let localTable :=
      SuccinctClose.concreteBPRelativeRmmInteriorLocalTable shape
    let globalTable :=
      SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable shape
    if segment = 0 then
      selectData.bitWords.store.wordRAMStore.readWord? 0 index
    else if segment = 1 then
      selectData.superTable.baseOccurrenceTable.wordRAMStore.readWord? 0 index
    else if segment = 2 then
      selectData.superTable.baseWordIndexTable.wordRAMStore.readWord? 0 index
    else if segment = 3 then
      selectData.superTable.rankBeforeTable.wordRAMStore.readWord? 0 index
    else if segment = 4 then
      selectData.superTable.firstOffsetTable.wordRAMStore.readWord? 0 index
    else if segment = 5 then
      selectData.localTable.baseOccurrenceTable.wordRAMStore.readWord? 0 index
    else if segment = 6 then
      selectData.localTable.baseWordIndexTable.wordRAMStore.readWord? 0 index
    else if segment = 7 then
      selectData.localTable.rankBeforeTable.wordRAMStore.readWord? 0 index
    else if segment = 8 then
      selectData.localTable.firstOffsetTable.wordRAMStore.readWord? 0 index
    else if segment = 9 then
      (selectData.longFlagRankData.rankRegisterWordRAMStore true).readWord? 0 index
    else if segment = 10 then
      (selectData.longFlagRankData.rankRegisterWordRAMStore true).readWord? 1 index
    else if segment = 11 then
      (selectData.longFlagRankData.rankRegisterWordRAMStore true).readWord? 2 index
    else if segment = 12 then
      selectData.longSuperRelativeTable.wordRAMStore.readWord? 0 index
    else if segment = 13 then
      (selectData.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord? 0 index
    else if segment = 14 then
      (selectData.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord? 1 index
    else if segment = 15 then
      (selectData.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord? 2 index
    else if segment = 16 then
      selectData.sparseDirectory.relativeTable.wordRAMStore.readWord? 0 index
    else if segment = 17 then
      rankStore.readWord? 0 index
    else if segment = 18 then
      rankStore.readWord? 1 index
    else if segment = 19 then
      rankStore.readWord? 2 index
    else if segment = 20 then
      summary.baselineTable.wordRAMStore.readWord? 0 index
    else if segment = 21 then
      summary.minRelTable.wordRAMStore.readWord? 0 index
    else if segment = 22 then
      summary.maxRelTable.wordRAMStore.readWord? 0 index
    else if segment = 23 then
      summary.argOffsetTable.wordRAMStore.readWord? 0 index
    else if segment = 24 then
      localTable.table.wordRAMStore.readWord? 0 index
    else if segment = 25 then
      globalTable.table.wordRAMStore.readWord? 0 index
    else
      none

theorem concreteBPNativeSuccinctRMQGlobalReadStore_bpCode
    (shape : Cartesian.CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 index =
      (SuccinctSpace.chunkPayloadWords
        (SuccinctRank.machineWordBits shape.bpCode.length)
        shape.bpCode).toArray[index]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    GenericSelect.sparseExceptionSelectData,
    GenericSelect.wordBits,
    SuccinctSpace.BoundedPayloadWordStore.ofChunks,
    SuccinctSpace.PayloadWordStore.wordRAMStore,
    WordRAM.Store.readWord?]

/--
Close-select trace with payload-read segments shifted into the final global
layout.  The packed BP-code reads remain at segment `0` so the final query can
share one BP-code payload segment instead of copying the code per component.
-/
def concreteBPNativeSelectCloseGlobalWordTraceResult
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    |>.selectTraceResultRelabeled
      concreteBPNativeSelectCloseTraceSegmentLayout idx

theorem concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).toCosted =
      concreteBPNativeSelectCloseInterpretedCosted shape idx := by
  simp [concreteBPNativeSelectCloseGlobalWordTraceResult,
    concreteBPNativeSelectCloseInterpretedCosted,
    GenericSelect.SparseExceptionSelectData.selectTraceResultRelabeled_refines_interpretedCosted]

theorem concreteBPNativeSelectCloseGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  let data := GenericSelect.sparseExceptionSelectData shape.bpCode false
  change forall event,
      event ∈
          (data.selectTraceResultRelabeled
            concreteBPNativeSelectCloseTraceSegmentLayout idx).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
  apply
    GenericSelect.SparseExceptionSelectData.selectTraceResultRelabeled_trace_forall
      data concreteBPNativeSelectCloseTraceSegmentLayout idx
      (fun event =>
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape))
  · intro slot event hmem
    exact
      data.superTable.readTraceResultRelabeled_matchesReadStore
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        slot event hmem
  · intro slot event hmem
    exact
      WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
        (data.longFlagRankData.rankTraceResult true slot)
        (WordRAM.ReadStore.ofStore
          (data.longFlagRankData.rankRegisterWordRAMStore true))
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (WordRAM.tripleSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment)
        (by
          intro segment index
          cases segment with
          | zero =>
              simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                concreteBPNativeSelectCloseTraceSegmentLayout,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap,
                WordRAM.ReadStore.ofStore]
          | succ segment =>
              cases segment with
              | zero =>
                  simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                    concreteBPNativeSelectCloseTraceSegmentLayout,
                    WordRAM.tripleSegmentMap,
                    WordRAM.TraceEvent.tripleSegmentMap,
                    WordRAM.ReadStore.ofStore]
              | succ segment =>
                  cases segment with
                  | zero =>
                      simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                        concreteBPNativeSelectCloseTraceSegmentLayout,
                        WordRAM.tripleSegmentMap,
                        WordRAM.TraceEvent.tripleSegmentMap,
                        WordRAM.ReadStore.ofStore]
                  | succ segment =>
                      simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                        concreteBPNativeSelectCloseTraceSegmentLayout,
                        concreteBPNativeDeadTraceSegment,
                        WordRAM.tripleSegmentMap,
                        WordRAM.TraceEvent.tripleSegmentMap,
                        WordRAM.ReadStore.ofStore,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                        WordRAM.Store.readWord?])
        (data.longFlagRankData.rankTraceResult_matchesReadStore true slot)
        event hmem
  · intro base slot event hmem
    exact
      GenericSelect.relativeOffsetReadTraceResultRelabeled_matchesReadStore
        concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
        concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        data.longSuperRelativeTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        base slot event hmem
  · intro slot event hmem
    exact
      data.localTable.readTraceResultRelabeled_matchesReadStore
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        slot event hmem
  · intro base localSlot localOccurrence event hmem
    exact
      data.sparseDirectory.readTraceResultRelabeled_matchesReadStore
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (by
          intro segment index
          cases segment with
          | zero =>
              simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                concreteBPNativeSelectCloseTraceSegmentLayout,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap]
          | succ segment =>
              cases segment with
              | zero =>
                  simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                    concreteBPNativeSelectCloseTraceSegmentLayout,
                    WordRAM.tripleSegmentMap,
                    WordRAM.TraceEvent.tripleSegmentMap]
              | succ segment =>
                  cases segment with
                  | zero =>
                      simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                        concreteBPNativeSelectCloseTraceSegmentLayout,
                        WordRAM.tripleSegmentMap,
                        WordRAM.TraceEvent.tripleSegmentMap]
                  | succ segment =>
                      simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                        concreteBPNativeSelectCloseTraceSegmentLayout,
                        concreteBPNativeDeadTraceSegment,
                        WordRAM.tripleSegmentMap,
                        WordRAM.TraceEvent.tripleSegmentMap,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                        WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        base localSlot localOccurrence event hmem
  · intro basePosition baseOccurrence q event hmem
    exact
      GenericSelect.denseTwoWordSelectTraceResultRelabeled_matchesReadStore
        concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
        concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        false data.bitWords
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        basePosition baseOccurrence q event hmem

/-- Real register-program trace for the final false-rank leg. -/
def concreteBPNativeRankCloseWordTraceResult
    (shape : Cartesian.CartesianShape)
    (pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.ofResult
    (((builtRelativeSplitBPCloseRankData shape)
      |>.rankRegisterProgram false (WordRAM.Register.NatExpr.reg 0)).eval
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterWordRAMStore false)
        (WordRAM.Register.RegFile.withNat1 pos))

theorem concreteBPNativeRankCloseWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeRankCloseWordTraceResult shape pos).toCosted =
      concreteBPNativeRankCloseInterpretedCosted shape pos := by
  rfl

/--
Final false-rank trace relabeled into a caller-supplied global segment range.

The value and modeled cost are unchanged; only payload-read segment identifiers
are shifted for later assembly into one global store.
-/
def concreteBPNativeRankCloseWordTraceResultAtSegment
    (shape : Cartesian.CartesianShape)
    (rankSegmentBase pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    (WordRAM.tripleSegmentMap rankSegmentBase
      concreteBPNativeDeadTraceSegment)
    (concreteBPNativeRankCloseWordTraceResult shape pos)

theorem concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted
    (shape : Cartesian.CartesianShape)
    (rankSegmentBase pos : Nat) :
    (concreteBPNativeRankCloseWordTraceResultAtSegment
      shape rankSegmentBase pos).toCosted =
      concreteBPNativeRankCloseInterpretedCosted shape pos := by
  simp [concreteBPNativeRankCloseWordTraceResultAtSegment,
    concreteBPNativeRankCloseWordTraceResult_refines_interpretedCosted]

theorem concreteBPNativeRankCloseGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      event ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegment
            shape concreteBPNativeRankCloseTraceSegmentBase pos).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  apply
    WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
      (concreteBPNativeRankCloseWordTraceResult shape pos)
      (WordRAM.ReadStore.ofStore
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterWordRAMStore false))
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (WordRAM.tripleSegmentMap concreteBPNativeRankCloseTraceSegmentBase
        concreteBPNativeDeadTraceSegment)
  · intro segment index
    cases segment with
    | zero =>
        simp [concreteBPNativeSuccinctRMQGlobalReadStore,
          concreteBPNativeRankCloseTraceSegmentBase,
          WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
          WordRAM.ReadStore.ofStore]
    | succ segment =>
        cases segment with
        | zero =>
            simp [concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeRankCloseTraceSegmentBase,
              WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
              WordRAM.ReadStore.ofStore]
        | succ segment =>
            cases segment with
            | zero =>
                simp [concreteBPNativeSuccinctRMQGlobalReadStore,
                  concreteBPNativeRankCloseTraceSegmentBase,
                  WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
                  WordRAM.ReadStore.ofStore]
            | succ segment =>
                simp [concreteBPNativeSuccinctRMQGlobalReadStore,
                  concreteBPNativeDeadTraceSegment,
                  WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
                  WordRAM.ReadStore.ofStore,
                  SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                  WordRAM.Store.readWord?]
  · intro event hmem
    simpa [concreteBPNativeRankCloseWordTraceResult,
      WordRAM.TraceResult.ofResult_trace,
      WordRAM.TraceEvent.matchesReadStore_ofStore] using
      WordRAM.Register.NatProgram.eval_reads_subset_payload
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterProgram false (WordRAM.Register.NatExpr.reg 0))
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterWordRAMStore false)
        (WordRAM.Register.RegFile.withNat1 pos)
        event hmem

/--
Interpreted compact LCA-close leg.

The compact close directory is unchanged; the rank seed callback it consumes is
now the interpreted false-rank query above.
-/
def concreteBPNativeLCACloseInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  (concreteBPNativeCloseDirectory shape).lcaCloseCostedWithRankSeed
    (concreteBPNativeRankCloseInterpretedCosted shape)
    leftClose rightClose

/--
Trace-preserving replay for the compact close/LCA leg.

The rank seed reads inside this leg are structural register-program traces. The
bounded local BP decoders, endpoint-fringe decoders, and relative-rmM interior
query are still charged decoder leaves, so this is a partially structural
close/LCA replay rather than the final fully payload-read-derived navigator.
-/
def concreteBPNativeLCACloseWordTraceResult
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  (concreteBPNativeCloseDirectory shape).lcaCloseTraceResultWithRankSeed
    (concreteBPNativeRankCloseWordTraceResult shape) leftClose rightClose

theorem concreteBPNativeLCACloseWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (concreteBPNativeLCACloseWordTraceResult
      shape leftClose rightClose).toCosted =
      concreteBPNativeLCACloseInterpretedCosted shape leftClose rightClose := by
  simp [concreteBPNativeLCACloseWordTraceResult,
    concreteBPNativeLCACloseInterpretedCosted,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeed_refines,
    concreteBPNativeRankCloseWordTraceResult_refines_interpretedCosted]

/--
Large-regime structural replay for the compact LCA-close leg.

The size hypothesis lets the close directory dispatch through the positive
summary-block path, so the zero-block semantic fallback is absent and the
cross-block interior relative-rmM leg uses its concrete trace replay.
-/
def concreteBPNativeLCACloseWordTraceResultOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedOfSizeGe
    shape (concreteBPNativeRankCloseWordTraceResult shape)
    hsize leftClose rightClose

theorem concreteBPNativeLCACloseWordTraceResultOfSizeGe_refines_interpretedCosted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat) :
    (concreteBPNativeLCACloseWordTraceResultOfSizeGe
      shape hsize leftClose rightClose).toCosted =
      concreteBPNativeLCACloseInterpretedCosted shape leftClose rightClose := by
  simp [concreteBPNativeLCACloseWordTraceResultOfSizeGe,
    concreteBPNativeLCACloseInterpretedCosted,
    concreteBPNativeCloseDirectory,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedOfSizeGe_refines,
    concreteBPNativeRankCloseWordTraceResult_refines_interpretedCosted]

/--
Large-regime LCA-close trace with caller-controlled global segment bases.

The rank-seed callback is shifted by `rankSegmentBase`; local BP-code reads
stay at segment 0; and relative-rmM interior tables use `interiorSegments`.
-/
def concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (rankSegmentBase : Nat)
    (interiorSegments : SuccinctClose.BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAtSegmentsOfSizeGe
    shape
    (concreteBPNativeRankCloseWordTraceResultAtSegment shape rankSegmentBase)
    hsize interiorSegments leftClose rightClose

theorem concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe_refines_interpretedCosted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (rankSegmentBase : Nat)
    (interiorSegments : SuccinctClose.BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat) :
    (concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe
      shape hsize rankSegmentBase interiorSegments leftClose rightClose).toCosted =
      concreteBPNativeLCACloseInterpretedCosted shape leftClose rightClose := by
  simp [concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe,
    concreteBPNativeLCACloseInterpretedCosted,
    concreteBPNativeCloseDirectory,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAtSegmentsOfSizeGe_refines,
    concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted]

/--
All-size compact LCA-close trace with the rank-seed callback relabeled into the
final global rank segments. Local BP-code reads stay at segment `0`; tiny or
inactive fallback work contributes synthetic word-primitive events rather than
payload reads.
-/
def concreteBPNativeLCACloseGlobalWordTraceResult
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  (concreteBPNativeCloseDirectory shape).lcaCloseTraceResultWithRankSeed
    (concreteBPNativeRankCloseWordTraceResultAtSegment
      shape concreteBPNativeRankCloseTraceSegmentBase)
    leftClose rightClose

theorem concreteBPNativeLCACloseGlobalWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (concreteBPNativeLCACloseGlobalWordTraceResult
      shape leftClose rightClose).toCosted =
      concreteBPNativeLCACloseInterpretedCosted shape leftClose rightClose := by
  simp [concreteBPNativeLCACloseGlobalWordTraceResult,
    concreteBPNativeLCACloseInterpretedCosted,
    concreteBPNativeCloseDirectory,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeed_refines,
    concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted]

theorem concreteBPNativeLCACloseGlobalWordTraceResult_matchesReadStore_total
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeLCACloseGlobalWordTraceResult
            shape leftClose rightClose).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeed_matchesReadStore
      (concreteBPNativeCloseDirectory shape)
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      leftClose rightClose
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (fun pos =>
        concreteBPNativeRankCloseGlobalWordTraceResult_matchesReadStore
          shape pos)
      (fun blockSize close =>
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult_matchesReadStore
          shape blockSize close
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (concreteBPNativeSuccinctRMQGlobalReadStore_bpCode shape))

theorem concreteBPNativeInteriorGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe
            shape hsize concreteBPNativeInteriorTraceSegments
            startBlock count).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe_matchesReadStore
      shape hsize concreteBPNativeInteriorTraceSegments
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (by
        intro segment index
        cases segment <;>
          simp [concreteBPNativeSuccinctRMQGlobalReadStore,
            concreteBPNativeInteriorTraceSegments,
            concreteBPNativeDeadTraceSegment,
            WordRAM.singletonSegmentMap,
            WordRAM.TraceEvent.singletonSegmentMap,
            SuccinctSpace.FixedWidthNatTable.wordRAMStore,
            SuccinctSpace.PayloadWordStore.wordRAMStore,
            WordRAM.Store.readWord?])
      (by
        intro segment index
        cases segment <;>
          simp [concreteBPNativeSuccinctRMQGlobalReadStore,
            concreteBPNativeInteriorTraceSegments,
            concreteBPNativeDeadTraceSegment,
            WordRAM.singletonSegmentMap,
            WordRAM.TraceEvent.singletonSegmentMap,
            SuccinctSpace.FixedWidthNatTable.wordRAMStore,
            SuccinctSpace.PayloadWordStore.wordRAMStore,
            WordRAM.Store.readWord?])
      (by
        intro segment index
        cases segment <;>
          simp [concreteBPNativeSuccinctRMQGlobalReadStore,
            concreteBPNativeInteriorTraceSegments,
            concreteBPNativeDeadTraceSegment,
            WordRAM.singletonSegmentMap,
            WordRAM.TraceEvent.singletonSegmentMap,
            SuccinctSpace.FixedWidthNatTable.wordRAMStore,
            SuccinctSpace.PayloadWordStore.wordRAMStore,
            WordRAM.Store.readWord?])
      (by
        intro segment index
        cases segment <;>
          simp [concreteBPNativeSuccinctRMQGlobalReadStore,
            concreteBPNativeInteriorTraceSegments,
            concreteBPNativeDeadTraceSegment,
            WordRAM.singletonSegmentMap,
            WordRAM.TraceEvent.singletonSegmentMap,
            SuccinctSpace.FixedWidthNatTable.wordRAMStore,
            SuccinctSpace.PayloadWordStore.wordRAMStore,
            WordRAM.Store.readWord?])
      (by
        intro segment index
        cases segment <;>
          simp [concreteBPNativeSuccinctRMQGlobalReadStore,
            concreteBPNativeInteriorTraceSegments,
            concreteBPNativeDeadTraceSegment,
            WordRAM.singletonSegmentMap,
            WordRAM.TraceEvent.singletonSegmentMap,
            SuccinctSpace.FixedWidthNatTable.wordRAMStore,
            SuccinctSpace.PayloadWordStore.wordRAMStore,
            WordRAM.Store.readWord?])
      (by
        intro segment index
        cases segment <;>
          simp [concreteBPNativeSuccinctRMQGlobalReadStore,
            concreteBPNativeInteriorTraceSegments,
            concreteBPNativeDeadTraceSegment,
            WordRAM.singletonSegmentMap,
            WordRAM.TraceEvent.singletonSegmentMap,
            SuccinctSpace.FixedWidthNatTable.wordRAMStore,
            SuccinctSpace.PayloadWordStore.wordRAMStore,
            WordRAM.Store.readWord?])
      startBlock count

theorem concreteBPNativeLCACloseGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe
            shape hsize concreteBPNativeRankCloseTraceSegmentBase
            concreteBPNativeInteriorTraceSegments
            leftClose rightClose).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAtSegmentsOfSizeGe_matchesReadStore
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      hsize concreteBPNativeInteriorTraceSegments leftClose rightClose
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (fun pos =>
        concreteBPNativeRankCloseGlobalWordTraceResult_matchesReadStore
          shape pos)
      (concreteBPNativeSuccinctRMQGlobalReadStore_bpCode shape)
      (fun startBlock count =>
        concreteBPNativeInteriorGlobalWordTraceResult_matchesReadStore
          shape hsize startBlock count)

/--
Final BP-native RMQ query with interpreted close-select, compact close/LCA, and
answer-rank leaves.
-/
def concreteBPNativeSuccinctRMQQueryInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.bind (concreteBPNativeSelectCloseInterpretedCosted shape left)
    fun leftClose? =>
      Costed.bind
        (concreteBPNativeSelectCloseInterpretedCosted shape (right - 1))
        fun rightClose? =>
          match leftClose?, rightClose? with
          | some leftClose, some rightClose =>
              Costed.bind
                (concreteBPNativeLCACloseInterpretedCosted shape
                  leftClose rightClose)
                fun answerClose? =>
                  match answerClose? with
                  | some answerClose =>
                      Costed.map (fun closeRank => some (closeRank - 1))
                        (concreteBPNativeRankCloseInterpretedCosted
                          shape (answerClose + 1))
                  | none => Costed.pure none
          | _, _ => Costed.pure none

/-- Optional-natural registers used by the final whole-query control program. -/
inductive WholeQueryOptReg where
  | leftClose
  | rightClose
  | answerClose
  | output
deriving Repr, DecidableEq

/-- Natural registers used by the final whole-query control program. -/
inductive WholeQueryNatReg where
  | closeRank
deriving Repr, DecidableEq

/-- Concrete register state for the final BP-native RMQ query program. -/
structure WholeQueryState where
  leftClose? : Option Nat := none
  rightClose? : Option Nat := none
  answerClose? : Option Nat := none
  closeRank : Nat := 0
  output? : Option Nat := none
deriving Repr

namespace WholeQueryState

/-- Empty initial register state. -/
def empty : WholeQueryState where

/-- Read an optional-natural register. -/
def opt (state : WholeQueryState) : WholeQueryOptReg -> Option Nat
  | .leftClose => state.leftClose?
  | .rightClose => state.rightClose?
  | .answerClose => state.answerClose?
  | .output => state.output?

/-- Read a natural register. -/
def nat (state : WholeQueryState) : WholeQueryNatReg -> Nat
  | .closeRank => state.closeRank

/-- Write an optional-natural register. -/
def setOpt (state : WholeQueryState) (reg : WholeQueryOptReg)
    (value : Option Nat) : WholeQueryState :=
  match reg with
  | .leftClose => { state with leftClose? := value }
  | .rightClose => { state with rightClose? := value }
  | .answerClose => { state with answerClose? := value }
  | .output => { state with output? := value }

/-- Write a natural register. -/
def setNat (state : WholeQueryState) (reg : WholeQueryNatReg)
    (value : Nat) : WholeQueryState :=
  match reg with
  | .closeRank => { state with closeRank := value }

end WholeQueryState

/--
First-order natural expressions for the final query-control program.

These expressions may inspect the two public query inputs and the program's own
registers. They do not contain Lean callbacks.
-/
inductive WholeQueryNatExpr where
  | const (value : Nat)
  | inputLeft
  | inputRight
  | optNatD (reg : WholeQueryOptReg) (fallback : Nat)
  | natReg (reg : WholeQueryNatReg)
  | add (left right : WholeQueryNatExpr)
  | sub (left right : WholeQueryNatExpr)
deriving Repr, DecidableEq

namespace WholeQueryNatExpr

/-- Evaluate a first-order query expression. -/
def eval (left right : Nat) (state : WholeQueryState) :
    WholeQueryNatExpr -> Nat
  | .const value => value
  | .inputLeft => left
  | .inputRight => right
  | .optNatD reg fallback => (state.opt reg).getD fallback
  | .natReg reg => state.nat reg
  | .add a b => a.eval left right state + b.eval left right state
  | .sub a b => a.eval left right state - b.eval left right state

end WholeQueryNatExpr

/--
Closed instruction set for the final BP-native RMQ query.

This is first-order control over already-interpreted component leaves: it has
fixed instruction constructors, register operands, and arithmetic expressions,
not higher-order continuations or arbitrary callbacks.
-/
inductive WholeQueryInstr where
  | selectClose (dst : WholeQueryOptReg) (idx : WholeQueryNatExpr)
  | lcaClose (dst leftReg rightReg : WholeQueryOptReg)
  | rankCloseIfSome
      (dst : WholeQueryNatReg) (guard : WholeQueryOptReg)
      (pos : WholeQueryNatExpr)
  | outputPredIfSome
      (dst guard : WholeQueryOptReg) (src : WholeQueryNatReg)
deriving Repr

namespace WholeQueryInstr

/-- Execute one whole-query instruction. -/
def eval (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    Costed WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      Costed.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseInterpretedCosted shape
          (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          Costed.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseInterpretedCosted shape
              leftClose rightClose)
      | _, _ => Costed.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          Costed.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseInterpretedCosted shape
              (pos.eval left right state))
      | none => Costed.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ => Costed.pure (state.setOpt dst (some (state.nat src - 1)))
      | none => Costed.pure (state.setOpt dst none)

end WholeQueryInstr

/-- First-order whole-query control programs for the final RMQ path. -/
abbrev WholeQueryProgram := List WholeQueryInstr

namespace WholeQueryProgram

/-- Execute a whole-query control program. -/
def eval (shape : Cartesian.CartesianShape) (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> Costed WholeQueryState
  | [], state => Costed.pure state
  | instr :: rest, state =>
      Costed.bind (instr.eval shape left right state) fun state' =>
        eval shape left right rest state'

end WholeQueryProgram

/--
Trace events for the first flattened whole-query layer.

This trace records the closed controller's domain leaves and their modeled
costs.  It is intentionally not yet a single payload-store `WordRAM.TraceEvent`
list: the select-close and compact close/LCA leaves still expose interpreted
`Costed` queries.  The point of this layer is to stop collapsing the whole
query directly to `Costed`, so later passes can replace these leaf summaries by
lower-level payload traces one component at a time.
-/
inductive WholeQueryLeafTraceEvent where
  | selectClose (idx : Nat) (result : Option Nat) (cost : Nat)
  | lcaClose (leftClose rightClose : Nat) (result : Option Nat) (cost : Nat)
  | rankClose (pos result cost : Nat)
deriving Repr, DecidableEq

namespace WholeQueryLeafTraceEvent

/-- Modeled cost contributed by one whole-query leaf event. -/
def cost : WholeQueryLeafTraceEvent -> Nat
  | selectClose _ _ cost => cost
  | lcaClose _ _ _ cost => cost
  | rankClose _ _ cost => cost

end WholeQueryLeafTraceEvent

/-- Sum of modeled costs recorded in a whole-query leaf trace. -/
def wholeQueryLeafTraceCost : List WholeQueryLeafTraceEvent -> Nat
  | [] => 0
  | event :: rest => event.cost + wholeQueryLeafTraceCost rest

@[simp] theorem wholeQueryLeafTraceCost_nil :
    wholeQueryLeafTraceCost [] = 0 := by
  rfl

@[simp] theorem wholeQueryLeafTraceCost_cons
    (event : WholeQueryLeafTraceEvent)
    (rest : List WholeQueryLeafTraceEvent) :
    wholeQueryLeafTraceCost (event :: rest) =
      event.cost + wholeQueryLeafTraceCost rest := by
  rfl

theorem wholeQueryLeafTraceCost_append
    (leftTrace rightTrace : List WholeQueryLeafTraceEvent) :
    wholeQueryLeafTraceCost (leftTrace ++ rightTrace) =
      wholeQueryLeafTraceCost leftTrace +
        wholeQueryLeafTraceCost rightTrace := by
  induction leftTrace with
  | nil =>
      simp [wholeQueryLeafTraceCost]
  | cons event rest ih =>
      simp [wholeQueryLeafTraceCost, ih, Nat.add_assoc]

/-- Result of evaluating whole-query control while preserving leaf trace data. -/
structure WholeQueryLeafTraceResult where
  state : WholeQueryState
  trace : List WholeQueryLeafTraceEvent
deriving Repr

namespace WholeQueryLeafTraceResult

/-- Project a leaf-trace result back to the theorem-facing `Costed` carrier. -/
def toCosted (result : WholeQueryLeafTraceResult) : Costed WholeQueryState where
  value := result.state
  cost := wholeQueryLeafTraceCost result.trace

@[simp] theorem toCosted_value (result : WholeQueryLeafTraceResult) :
    result.toCosted.value = result.state := by
  rfl

@[simp] theorem toCosted_cost (result : WholeQueryLeafTraceResult) :
    result.toCosted.cost = wholeQueryLeafTraceCost result.trace := by
  rfl

end WholeQueryLeafTraceResult

namespace WholeQueryInstr

/-- Execute one instruction while preserving a domain-leaf trace. -/
def evalLeafTrace (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    WholeQueryLeafTraceResult :=
  match instr with
  | .selectClose dst idx =>
      let query :=
        concreteBPNativeSelectCloseInterpretedCosted shape
          (idx.eval left right state)
      { state := state.setOpt dst query.value
        trace :=
          [WholeQueryLeafTraceEvent.selectClose
            (idx.eval left right state) query.value query.cost] }
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          let query :=
            concreteBPNativeLCACloseInterpretedCosted shape
              leftClose rightClose
          { state := state.setOpt dst query.value
            trace :=
              [WholeQueryLeafTraceEvent.lcaClose
                leftClose rightClose query.value query.cost] }
      | _, _ =>
          { state := state.setOpt dst none, trace := [] }
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          let query :=
            concreteBPNativeRankCloseInterpretedCosted shape
              (pos.eval left right state)
          { state := state.setNat dst query.value
            trace :=
              [WholeQueryLeafTraceEvent.rankClose
                (pos.eval left right state) query.value query.cost] }
      | none => { state := state, trace := [] }
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ =>
          { state := state.setOpt dst (some (state.nat src - 1))
            trace := [] }
      | none =>
          { state := state.setOpt dst none, trace := [] }

theorem evalLeafTrace_refines_eval
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    (instr.evalLeafTrace shape left right state).toCosted =
      instr.eval shape left right state := by
  cases instr with
  | selectClose dst idx =>
      apply Costed.ext <;>
        simp [evalLeafTrace, eval, WholeQueryLeafTraceResult.toCosted,
          wholeQueryLeafTraceCost, WholeQueryLeafTraceEvent.cost,
          Costed.map, Costed.bind, Costed.pure]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          apply Costed.ext <;>
            simp [evalLeafTrace, eval, hleft, hright,
              WholeQueryLeafTraceResult.toCosted, wholeQueryLeafTraceCost,
              WholeQueryLeafTraceEvent.cost, Costed.map, Costed.bind,
              Costed.pure]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard <;>
        apply Costed.ext <;>
          simp [evalLeafTrace, eval, hguard,
            WholeQueryLeafTraceResult.toCosted, wholeQueryLeafTraceCost,
            WholeQueryLeafTraceEvent.cost, Costed.map, Costed.bind,
            Costed.pure]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        apply Costed.ext <;>
          simp [evalLeafTrace, eval, hguard,
            WholeQueryLeafTraceResult.toCosted, Costed.pure]

end WholeQueryInstr

namespace WholeQueryProgram

/-- Execute a whole-query control program while preserving leaf trace data. -/
def evalLeafTrace (shape : Cartesian.CartesianShape) (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> WholeQueryLeafTraceResult
  | [], state => { state := state, trace := [] }
  | instr :: rest, state =>
      let first := instr.evalLeafTrace shape left right state
      let tail := evalLeafTrace shape left right rest first.state
      { state := tail.state, trace := first.trace ++ tail.trace }

theorem evalLeafTrace_refines_eval
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    (evalLeafTrace shape left right program state).toCosted =
      eval shape left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalLeafTrace, eval, WholeQueryLeafTraceResult.toCosted,
        Costed.pure]
  | cons instr rest ih =>
      unfold evalLeafTrace eval
      let first := instr.evalLeafTrace shape left right state
      let tail := evalLeafTrace shape left right rest first.state
      have hfirst :
          first.toCosted = instr.eval shape left right state := by
        simpa [first] using
          WholeQueryInstr.evalLeafTrace_refines_eval shape left right instr
            state
      have htail :
          tail.toCosted = eval shape left right rest first.state := by
        simpa [tail] using ih first.state
      apply Costed.ext
      · rw [← hfirst]
        simpa [WholeQueryLeafTraceResult.toCosted, Costed.bind] using
          congrArg Costed.value htail
      · rw [← hfirst]
        change
          wholeQueryLeafTraceCost (first.trace ++ tail.trace) =
            first.toCosted.cost +
              (eval shape left right rest first.state).cost
        rw [wholeQueryLeafTraceCost_append]
        have htailCost :
            wholeQueryLeafTraceCost tail.trace =
              (eval shape left right rest first.state).cost := by
          simpa [WholeQueryLeafTraceResult.toCosted] using
            congrArg Costed.cost htail
        simp [WholeQueryLeafTraceResult.toCosted, htailCost]

end WholeQueryProgram

namespace WholeQueryInstr

/-- Execute one instruction while preserving a unified `WordRAM.TraceEvent` stream. -/
def evalWordTrace (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    WordRAM.TraceResult WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      WordRAM.TraceResult.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseWordTraceResult shape
          (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          WordRAM.TraceResult.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseWordTraceResult shape
              leftClose rightClose)
      | _, _ => WordRAM.TraceResult.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseWordTraceResult shape
              (pos.eval left right state))
      | none => WordRAM.TraceResult.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.pure
            (state.setOpt dst (some (state.nat src - 1)))
      | none =>
          WordRAM.TraceResult.pure (state.setOpt dst none)

theorem evalWordTrace_refines_eval
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    (instr.evalWordTrace shape left right state).toCosted =
      instr.eval shape left right state := by
  cases instr with
  | selectClose dst idx =>
      simp [evalWordTrace, eval,
        concreteBPNativeSelectCloseWordTraceResult_refines_interpretedCosted,
        WordRAM.TraceResult.map_toCosted, Costed.map]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          simp [evalWordTrace, eval, hleft, hright,
            concreteBPNativeLCACloseWordTraceResult_refines_interpretedCosted,
            WordRAM.TraceResult.map_toCosted,
            WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard <;>
        simp [evalWordTrace, eval, hguard,
          concreteBPNativeRankCloseWordTraceResult_refines_interpretedCosted,
          WordRAM.TraceResult.map_toCosted,
          WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalWordTrace, eval, hguard,
          WordRAM.TraceResult.pure_toCosted, Costed.pure]

/--
Execute one instruction in the all-size global-segment replay.

This uses the same global segment convention as the large-regime replay, but
the compact close/LCA instruction follows the total all-size close trace. Tiny
or inactive close-navigation fallback work is represented by synthetic
word-primitive events rather than payload reads.
-/
def evalGlobalWordTrace (shape : Cartesian.CartesianShape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) : WordRAM.TraceResult WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      WordRAM.TraceResult.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          WordRAM.TraceResult.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseGlobalWordTraceResult
              shape leftClose rightClose)
      | _, _ => WordRAM.TraceResult.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseWordTraceResultAtSegment
              shape concreteBPNativeRankCloseTraceSegmentBase
              (pos.eval left right state))
      | none => WordRAM.TraceResult.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.pure
            (state.setOpt dst (some (state.nat src - 1)))
      | none =>
          WordRAM.TraceResult.pure (state.setOpt dst none)

theorem evalGlobalWordTrace_refines_eval
    (shape : Cartesian.CartesianShape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    (instr.evalGlobalWordTrace shape left right state).toCosted =
      instr.eval shape left right state := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTrace, eval,
        concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted,
        WordRAM.TraceResult.map_toCosted, Costed.map]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          simp [evalGlobalWordTrace, eval, hleft, hright,
            concreteBPNativeLCACloseGlobalWordTraceResult_refines_interpretedCosted,
            WordRAM.TraceResult.map_toCosted,
            WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTrace, eval, hguard,
          concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted,
          WordRAM.TraceResult.map_toCosted,
          WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTrace, eval, hguard,
          WordRAM.TraceResult.pure_toCosted, Costed.pure]

theorem evalGlobalWordTrace_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      List.Mem event
          (instr.evalGlobalWordTrace shape left right state).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTrace]
      exact
        concreteBPNativeSelectCloseGlobalWordTraceResult_matchesReadStore
          shape (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [evalGlobalWordTrace, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [evalGlobalWordTrace, hleft, hright]
              intro event hmem
              cases hmem
          | some rightClose =>
              simp [evalGlobalWordTrace, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResult_matchesReadStore_total
                  shape leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTrace, hguard]
          intro event hmem
          cases hmem
      | some _ =>
        simp [evalGlobalWordTrace, hguard]
        exact
          concreteBPNativeRankCloseGlobalWordTraceResult_matchesReadStore
            shape (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTrace, hguard] <;>
        intro event hmem <;> cases hmem

/--
Execute one instruction in the large-regime replay.

Only the compact close/LCA instruction differs from `evalWordTrace`: it uses the
large-regime LCA-close trace, which expands the positive-block interior path
instead of retaining the all-size semantic fallback.
-/
def evalWordTraceOfSizeGe (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    WordRAM.TraceResult WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      WordRAM.TraceResult.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseWordTraceResult shape
          (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          WordRAM.TraceResult.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseWordTraceResultOfSizeGe shape hsize
              leftClose rightClose)
      | _, _ => WordRAM.TraceResult.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseWordTraceResult shape
              (pos.eval left right state))
      | none => WordRAM.TraceResult.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.pure
            (state.setOpt dst (some (state.nat src - 1)))
      | none =>
          WordRAM.TraceResult.pure (state.setOpt dst none)

theorem evalWordTraceOfSizeGe_refines_eval
    (shape : Cartesian.CartesianShape) (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) (instr : WholeQueryInstr) (state : WholeQueryState) :
    (instr.evalWordTraceOfSizeGe shape hsize left right state).toCosted =
      instr.eval shape left right state := by
  cases instr with
  | selectClose dst idx =>
      simp [evalWordTraceOfSizeGe, eval,
        concreteBPNativeSelectCloseWordTraceResult_refines_interpretedCosted,
        WordRAM.TraceResult.map_toCosted, Costed.map]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          simp [evalWordTraceOfSizeGe, eval, hleft, hright,
            concreteBPNativeLCACloseWordTraceResultOfSizeGe_refines_interpretedCosted,
            WordRAM.TraceResult.map_toCosted,
            WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard <;>
        simp [evalWordTraceOfSizeGe, eval, hguard,
          concreteBPNativeRankCloseWordTraceResult_refines_interpretedCosted,
          WordRAM.TraceResult.map_toCosted,
          WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalWordTraceOfSizeGe, eval, hguard,
          WordRAM.TraceResult.pure_toCosted, Costed.pure]

/--
Execute one instruction in the large-regime global-segment replay.

This is the first whole-query evaluator whose structural leaves agree on a
single segment layout: shared BP code at segment `0`, close-select auxiliary
segments `1` through `16`, rank segments `17` through `19`, and compact
close/LCA interior segments `20` through `25`.
-/
def evalGlobalWordTraceOfSizeGe (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    WordRAM.TraceResult WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      WordRAM.TraceResult.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          WordRAM.TraceResult.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe
              shape hsize concreteBPNativeRankCloseTraceSegmentBase
              concreteBPNativeInteriorTraceSegments leftClose rightClose)
      | _, _ => WordRAM.TraceResult.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseWordTraceResultAtSegment
              shape concreteBPNativeRankCloseTraceSegmentBase
              (pos.eval left right state))
      | none => WordRAM.TraceResult.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.pure
            (state.setOpt dst (some (state.nat src - 1)))
      | none =>
          WordRAM.TraceResult.pure (state.setOpt dst none)

theorem evalGlobalWordTraceOfSizeGe_refines_eval
    (shape : Cartesian.CartesianShape) (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) (instr : WholeQueryInstr) (state : WholeQueryState) :
    (instr.evalGlobalWordTraceOfSizeGe shape hsize left right state).toCosted =
      instr.eval shape left right state := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTraceOfSizeGe, eval,
        concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted,
        WordRAM.TraceResult.map_toCosted, Costed.map]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          simp [evalGlobalWordTraceOfSizeGe, eval, hleft, hright,
            concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe_refines_interpretedCosted,
            WordRAM.TraceResult.map_toCosted,
            WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceOfSizeGe, eval, hguard,
          concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted,
          WordRAM.TraceResult.map_toCosted,
          WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceOfSizeGe, eval, hguard,
          WordRAM.TraceResult.pure_toCosted, Costed.pure]

theorem evalGlobalWordTraceOfSizeGe_matchesReadStore
    (shape : Cartesian.CartesianShape) (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      List.Mem event
          (instr.evalGlobalWordTraceOfSizeGe
            shape hsize left right state).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTraceOfSizeGe]
      exact
        concreteBPNativeSelectCloseGlobalWordTraceResult_matchesReadStore
          shape (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [evalGlobalWordTraceOfSizeGe, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [evalGlobalWordTraceOfSizeGe, hleft, hright]
              intro event hmem
              cases hmem
          | some rightClose =>
              simp [evalGlobalWordTraceOfSizeGe, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResult_matchesReadStore
                  shape hsize leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTraceOfSizeGe, hguard]
          intro event hmem
          cases hmem
      | some _ =>
        simp [evalGlobalWordTraceOfSizeGe, hguard]
        exact
          concreteBPNativeRankCloseGlobalWordTraceResult_matchesReadStore
            shape (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceOfSizeGe, hguard] <;>
        intro event hmem <;> cases hmem

end WholeQueryInstr

namespace WholeQueryProgram

/-- Execute a whole-query program while preserving one `WordRAM.TraceEvent` list. -/
def evalWordTrace (shape : Cartesian.CartesianShape) (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> WordRAM.TraceResult WholeQueryState
  | [], state => WordRAM.TraceResult.pure state
  | instr :: rest, state =>
      WordRAM.TraceResult.bind
        (instr.evalWordTrace shape left right state) fun state' =>
          evalWordTrace shape left right rest state'

theorem evalWordTrace_refines_eval
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    (evalWordTrace shape left right program state).toCosted =
      eval shape left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalWordTrace, eval, WordRAM.TraceResult.pure_toCosted,
        Costed.pure]
  | cons instr rest ih =>
      simp [evalWordTrace, eval, WordRAM.TraceResult.bind_toCosted,
        WholeQueryInstr.evalWordTrace_refines_eval, ih, Costed.bind]

/--
Execute a whole-query program in the all-size global-segment replay.

This preserves one `WordRAM.TraceEvent` stream under the final query's shared
payload-store layout. The close/LCA instruction uses the total all-size trace,
so tiny/inactive fallback work is kept as synthetic word primitives while real
payload reads retain global segment addresses.
-/
def evalGlobalWordTrace (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> WordRAM.TraceResult WholeQueryState
  | [], state => WordRAM.TraceResult.pure state
  | instr :: rest, state =>
      WordRAM.TraceResult.bind
        (instr.evalGlobalWordTrace shape left right state)
        fun state' =>
          evalGlobalWordTrace shape left right rest state'

theorem evalGlobalWordTrace_refines_eval
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    (evalGlobalWordTrace shape left right program state).toCosted =
      eval shape left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTrace, eval,
        WordRAM.TraceResult.pure_toCosted, Costed.pure]
  | cons instr rest ih =>
      simp [evalGlobalWordTrace, eval,
        WordRAM.TraceResult.bind_toCosted,
        WholeQueryInstr.evalGlobalWordTrace_refines_eval, ih,
        Costed.bind]

theorem evalGlobalWordTrace_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      List.Mem event
          (evalGlobalWordTrace
            shape left right program state).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTrace]
      exact WordRAM.TraceResult.pure_trace_forall _ state
  | cons instr rest ih =>
      unfold evalGlobalWordTrace
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTrace_matchesReadStore
            shape left right instr state
      · exact ih
          (instr.evalGlobalWordTrace shape left right state).value

/--
Execute a whole-query program in the large-regime replay.

This preserves one `WordRAM.TraceEvent` stream while using the size-indexed
compact close/LCA replay for the LCA instruction.
-/
def evalWordTraceOfSizeGe (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> WordRAM.TraceResult WholeQueryState
  | [], state => WordRAM.TraceResult.pure state
  | instr :: rest, state =>
      WordRAM.TraceResult.bind
        (instr.evalWordTraceOfSizeGe shape hsize left right state)
        fun state' =>
          evalWordTraceOfSizeGe shape hsize left right rest state'

theorem evalWordTraceOfSizeGe_refines_eval
    (shape : Cartesian.CartesianShape) (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    (evalWordTraceOfSizeGe shape hsize left right program state).toCosted =
      eval shape left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalWordTraceOfSizeGe, eval, WordRAM.TraceResult.pure_toCosted,
        Costed.pure]
  | cons instr rest ih =>
      simp [evalWordTraceOfSizeGe, eval, WordRAM.TraceResult.bind_toCosted,
        WholeQueryInstr.evalWordTraceOfSizeGe_refines_eval, ih, Costed.bind]

/--
Execute a whole-query program in the large-regime global-segment replay.

The trace is still a `WordRAM.TraceEvent` stream, but payload reads from the
select, rank, and compact close/LCA leaves are now assembled under one shared
segment convention instead of each leaf using local segment numbers.
-/
def evalGlobalWordTraceOfSizeGe (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> WordRAM.TraceResult WholeQueryState
  | [], state => WordRAM.TraceResult.pure state
  | instr :: rest, state =>
      WordRAM.TraceResult.bind
        (instr.evalGlobalWordTraceOfSizeGe shape hsize left right state)
        fun state' =>
          evalGlobalWordTraceOfSizeGe shape hsize left right rest state'

theorem evalGlobalWordTraceOfSizeGe_refines_eval
    (shape : Cartesian.CartesianShape) (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    (evalGlobalWordTraceOfSizeGe shape hsize left right program state).toCosted =
      eval shape left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTraceOfSizeGe, eval,
        WordRAM.TraceResult.pure_toCosted, Costed.pure]
  | cons instr rest ih =>
      simp [evalGlobalWordTraceOfSizeGe, eval,
        WordRAM.TraceResult.bind_toCosted,
        WholeQueryInstr.evalGlobalWordTraceOfSizeGe_refines_eval, ih,
        Costed.bind]

theorem evalGlobalWordTraceOfSizeGe_matchesReadStore
    (shape : Cartesian.CartesianShape) (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      List.Mem event
          (evalGlobalWordTraceOfSizeGe
            shape hsize left right program state).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTraceOfSizeGe]
      exact WordRAM.TraceResult.pure_trace_forall _ state
  | cons instr rest ih =>
      unfold evalGlobalWordTraceOfSizeGe
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTraceOfSizeGe_matchesReadStore
            shape hsize left right instr state
      · exact ih
          (instr.evalGlobalWordTraceOfSizeGe
            shape hsize left right state).value

end WholeQueryProgram

/-- The closed whole-query control program for the final BP-native RMQ query. -/
def concreteBPNativeSuccinctRMQWholeQueryProgram : WholeQueryProgram :=
  [ WholeQueryInstr.selectClose .leftClose .inputLeft
  , WholeQueryInstr.selectClose .rightClose
      (.sub .inputRight (.const 1))
  , WholeQueryInstr.lcaClose .answerClose .leftClose .rightClose
  , WholeQueryInstr.rankCloseIfSome .closeRank .answerClose
      (.add (.optNatD .answerClose 0) (.const 1))
  , WholeQueryInstr.outputPredIfSome .output .answerClose .closeRank
  ]

/--
Final BP-native RMQ query as one closed whole-query control program.

The component leaves remain the existing interpreted select-close, compact
close/LCA, and two-level register-backed rank leaves; the surrounding query
control is now a first-order instruction list rather than open Lean-side
continuations.
-/
def concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.map WholeQueryState.output?
    (WholeQueryProgram.eval shape left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty)

/--
Final BP-native RMQ query with a preserved controller-level leaf trace.

Projecting this result to `Costed` refines the existing closed whole-query
interpreter.  The trace is deliberately a domain-leaf trace, not yet one shared
payload-store `WordRAM.TraceEvent` list.
-/
def concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.map WholeQueryState.output?
    ((WholeQueryProgram.evalLeafTrace shape left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty).toCosted)

/--
Final BP-native RMQ query with one unified `WordRAM.TraceEvent` stream.

This is a real `TraceEvent` stream for the closed query controller. Its
select-close, answer-rank, and compact-close rank-seed reads are structural
payload/register traces. The bounded local BP decoders, endpoint-fringe
decoders, and relative-rmM interior query remain explicit charged decoder
leaves, which are the remaining payload-read replay target.
-/
def concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.map WholeQueryState.output?
    ((WholeQueryProgram.evalWordTrace shape left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty).toCosted)

/--
All-size final BP-native RMQ query as one globally segmented
`WordRAM.TraceEvent` result.

Unlike `concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted`, the component
payload reads already use the final shared segment layout. Unlike the
large-regime result below, tiny/inactive close-navigation fallback work is
retained as synthetic word-primitive events rather than structurally replaying
the positive close navigator.
-/
def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map WholeQueryState.output?
    (WholeQueryProgram.evalGlobalWordTrace shape left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty)

/-- `Costed` projection of the all-size globally segmented trace. -/
def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
    shape left right).toCosted

/--
Large-regime final BP-native RMQ query with one unified `WordRAM.TraceEvent`
stream.

Compared with `concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted`, the
compact close/LCA instruction now uses the large-regime structural replay, so
the positive-block local/fringe/interior path is represented by trace events
instead of the all-size semantic fallback.
-/
def concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.map WholeQueryState.output?
    ((WholeQueryProgram.evalWordTraceOfSizeGe shape hsize left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty).toCosted)

/--
Large-regime final BP-native RMQ query as a trace result, before projection to
`Costed`.

The trace is one list of `WordRAM.TraceEvent`s. Its component traces still use
local segment numbering, so this is not yet a proof that all reads target one
globally laid-out payload store.
-/
def concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map WholeQueryState.output?
    (WholeQueryProgram.evalWordTraceOfSizeGe shape hsize left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty)

/--
Large-regime final BP-native RMQ query as one globally segmented
`WordRAM.TraceEvent` result.

Unlike `concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe`, this
uses the relabeled select/rank/close leaves, so payload-read segment numbers
are globally meaningful across the whole query: BP code at segment `0`, select
auxiliary tables at `1..16`, rank tables at `17..19`, and close-interior tables
at `20..25`.
-/
def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map WholeQueryState.output?
    (WholeQueryProgram.evalGlobalWordTraceOfSizeGe shape hsize left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty)

/-- `Costed` projection of the globally segmented large-regime trace. -/
def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) : Costed (Option Nat) :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
    shape hsize left right).toCosted

/--
Component-local provenance for large-regime final RMQ trace events.

This predicate is intentionally weaker than a global-store theorem: it records
that each event in the assembled stream comes from one of the concrete
close-select, compact close/LCA, or answer-rank component traces. A future
global-store theorem should add segment relabeling and prove the same reads
agree with one combined payload layout.
-/
def concreteBPNativeLargeRegimeTraceEventAdmissible
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat)
    (event : WordRAM.TraceEvent) : Prop :=
  List.Mem event
      (concreteBPNativeSelectCloseWordTraceResult shape left).trace \/
    List.Mem event
      (concreteBPNativeSelectCloseWordTraceResult shape (right - 1)).trace \/
    (exists leftClose rightClose,
      List.Mem event
        (concreteBPNativeLCACloseWordTraceResultOfSizeGe
          shape hsize leftClose rightClose).trace) \/
    (exists answerClose,
      List.Mem event
        (concreteBPNativeRankCloseWordTraceResult
          shape (answerClose + 1)).trace) \/
    Not event.isReadWord

/--
Small numeric envelope for the natural data carried by one `WordRAM` trace
event.  It is intentionally syntactic: payload reads contribute their segment
and index; word-local primitives contribute the natural operands and result
positions they expose in the trace.
-/
def concreteBPNativeTraceEventNatEnvelope :
    WordRAM.TraceEvent -> Nat
  | WordRAM.TraceEvent.readWord segment index _ => Nat.max segment index
  | WordRAM.TraceEvent.wordRank _ limit result => Nat.max limit result
  | WordRAM.TraceEvent.wordSelect _ occurrence none => occurrence
  | WordRAM.TraceEvent.wordSelect _ occurrence (some result) =>
      Nat.max occurrence result

/-- Maximum natural envelope over a trace. -/
def concreteBPNativeTraceNatEnvelope :
    List WordRAM.TraceEvent -> Nat
  | [] => 0
  | event :: rest =>
      Nat.max (concreteBPNativeTraceEventNatEnvelope event)
        (concreteBPNativeTraceNatEnvelope rest)

/--
Declared bit width large enough for every natural datum exposed by this trace.
This is a trace-local bound, not an asymptotic machine-word theorem.
-/
def concreteBPNativeTraceEventBitWidth
    (trace : List WordRAM.TraceEvent) : Nat :=
  Nat.log2 (concreteBPNativeTraceNatEnvelope trace) + 1

/-- Read addresses exposed by an event fit in the declared bit width. -/
def concreteBPNativeTraceEventReadAddressFitsInBits
    (bits : Nat) : WordRAM.TraceEvent -> Prop
  | WordRAM.TraceEvent.readWord segment index _ =>
      WordRAM.Register.AddressFitsInBits bits segment index
  | WordRAM.TraceEvent.wordRank _ _ _ => True
  | WordRAM.TraceEvent.wordSelect _ _ _ => True

/-- Word-primitive natural operands/results exposed by an event fit in bits. -/
def concreteBPNativeTraceEventPrimitiveOperandsFitInBits
    (bits : Nat) : WordRAM.TraceEvent -> Prop
  | WordRAM.TraceEvent.readWord _ _ _ => True
  | WordRAM.TraceEvent.wordRank _ limit result =>
      WordRAM.Register.FitsInBits bits limit /\
        WordRAM.Register.FitsInBits bits result
  | WordRAM.TraceEvent.wordSelect _ occurrence result =>
      WordRAM.Register.FitsInBits bits occurrence /\
        forall value, result = some value ->
          WordRAM.Register.FitsInBits bits value

theorem concreteBPNativeTraceEventNatEnvelope_le_traceNatEnvelope_of_mem
    {trace : List WordRAM.TraceEvent} {event : WordRAM.TraceEvent}
    (hmem : List.Mem event trace) :
    concreteBPNativeTraceEventNatEnvelope event <=
      concreteBPNativeTraceNatEnvelope trace := by
  induction trace with
  | nil =>
      cases hmem
  | cons head tail ih =>
      cases hmem with
      | head =>
          exact Nat.le_max_left _ _
      | tail _ htail =>
          exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

theorem concreteBPNativeTraceEventNatEnvelope_lt_two_pow_bitWidth_of_mem
    {trace : List WordRAM.TraceEvent} {event : WordRAM.TraceEvent}
    (hmem : List.Mem event trace) :
    concreteBPNativeTraceEventNatEnvelope event <
      2 ^ concreteBPNativeTraceEventBitWidth trace := by
  have hle :=
    concreteBPNativeTraceEventNatEnvelope_le_traceNatEnvelope_of_mem
      (trace := trace) (event := event) hmem
  have hlt :
      concreteBPNativeTraceNatEnvelope trace <
        2 ^ concreteBPNativeTraceEventBitWidth trace := by
    unfold concreteBPNativeTraceEventBitWidth
    exact Nat.lt_log2_self
  exact Nat.lt_of_le_of_lt hle hlt

theorem concreteBPNativeTraceEventReadAddressFitsInBits_of_mem
    {trace : List WordRAM.TraceEvent} {event : WordRAM.TraceEvent}
    (hmem : List.Mem event trace) :
    concreteBPNativeTraceEventReadAddressFitsInBits
      (concreteBPNativeTraceEventBitWidth trace) event := by
  have hlt :=
    concreteBPNativeTraceEventNatEnvelope_lt_two_pow_bitWidth_of_mem
      (trace := trace) (event := event) hmem
  cases event with
  | readWord segment index word? =>
      have hmax :
          Nat.max segment index <
            2 ^ concreteBPNativeTraceEventBitWidth trace := by
        simpa [concreteBPNativeTraceEventNatEnvelope] using hlt
      constructor
      · exact Nat.lt_of_le_of_lt (Nat.le_max_left segment index) hmax
      · exact Nat.lt_of_le_of_lt (Nat.le_max_right segment index) hmax
  | wordRank target limit result =>
      trivial
  | wordSelect target occurrence result =>
      trivial

theorem concreteBPNativeTraceEventPrimitiveOperandsFitInBits_of_mem
    {trace : List WordRAM.TraceEvent} {event : WordRAM.TraceEvent}
    (hmem : List.Mem event trace) :
    concreteBPNativeTraceEventPrimitiveOperandsFitInBits
      (concreteBPNativeTraceEventBitWidth trace) event := by
  have hlt :=
    concreteBPNativeTraceEventNatEnvelope_lt_two_pow_bitWidth_of_mem
      (trace := trace) (event := event) hmem
  cases event with
  | readWord segment index word? =>
      trivial
  | wordRank target limit result =>
      have hmax :
          Nat.max limit result <
            2 ^ concreteBPNativeTraceEventBitWidth trace := by
        simpa [concreteBPNativeTraceEventNatEnvelope] using hlt
      constructor
      · exact Nat.lt_of_le_of_lt (Nat.le_max_left limit result) hmax
      · exact Nat.lt_of_le_of_lt (Nat.le_max_right limit result) hmax
  | wordSelect target occurrence result =>
      cases result with
      | none =>
          constructor
          · simpa [WordRAM.Register.FitsInBits,
              concreteBPNativeTraceEventNatEnvelope] using hlt
          · intro value hvalue
            cases hvalue
      | some result =>
          have hmax :
              Nat.max occurrence result <
                2 ^ concreteBPNativeTraceEventBitWidth trace := by
            simpa [concreteBPNativeTraceEventNatEnvelope] using hlt
          constructor
          · exact Nat.lt_of_le_of_lt
              (Nat.le_max_left occurrence result) hmax
          · intro value hvalue
            cases hvalue
            exact Nat.lt_of_le_of_lt
              (Nat.le_max_right occurrence result) hmax

/--
Trace-local bit width for the final all-size global payload-store trace.  It is
the finite bound consumed by the bounded execution-story theorem below.
-/
def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Nat :=
  concreteBPNativeTraceEventBitWidth
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
      shape left right).trace

/-- Large-regime companion trace-local bit width. -/
def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBitsOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) : Nat :=
  concreteBPNativeTraceEventBitWidth
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
      shape hsize left right).trace

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_eq_traceResult_toCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted := by
  rfl

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_wholeQueryInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
  rw [WordRAM.TraceResult.map_toCosted]
  rw [
    WholeQueryProgram.evalGlobalWordTrace_refines_eval
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_read_or_primitive
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive := by
  intro event _hmem
  exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WholeQueryProgram.evalGlobalWordTrace_matchesReadStore
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty

/--
Store-extensional variant of the all-size global trace store theorem. If a
candidate read store agrees with the concrete global store at every read event
that the final query trace actually emits, then the same trace is validated by
that candidate store too.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore_of_trace_read_agreement
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (store : WordRAM.ReadStore)
    (hagree :
      forall segment index word?,
        List.Mem (WordRAM.TraceEvent.readWord segment index word?)
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          store.readWord? segment index =
            (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              segment index) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.matchesReadStore store := by
  intro event hmem
  cases event with
  | readWord segment index word? =>
      have hconcrete :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore
          shape left right
          (WordRAM.TraceEvent.readWord segment index word?) hmem
      have hagree' := hagree segment index word? hmem
      have hconcrete' :
          (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            segment index = word? := by
        simpa [WordRAM.TraceEvent.matchesReadStore] using hconcrete
      exact Eq.trans hagree' hconcrete'
  | wordRank target limit result =>
      simp [WordRAM.TraceEvent.matchesReadStore]
  | wordSelect target occurrence result =>
      simp [WordRAM.TraceEvent.matchesReadStore]

/--
Public all-size execution-story packet for the globally segmented final RMQ
trace. It removes the large-regime premise from the store-backed story: every
actual payload read in the final query agrees with the concrete global read
store, and any tiny/inactive fallback events are explicit word primitives.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted /\
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)) := by
  constructor
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_eq_traceResult_toCosted
        shape left right
  constructor
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_wholeQueryInterpretedCosted
        shape left right
  constructor
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_read_or_primitive
        shape left right
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore
        shape left right

/--
Store-extensional all-size execution-story packet. Besides the ordinary
global-store theorem shape, this version may be instantiated with any read store
that agrees with the concrete global store on the payload-read events present in
the emitted final-query trace.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_store_extensional_execution_story
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (store : WordRAM.ReadStore)
    (hagree :
      forall segment index word?,
        List.Mem (WordRAM.TraceEvent.readWord segment index word?)
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          store.readWord? segment index =
            (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              segment index) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted /\
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.matchesReadStore store) := by
  constructor
  case left =>
    exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_eq_traceResult_toCosted
        shape left right
  case right =>
    constructor
    case left =>
      exact
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_wholeQueryInterpretedCosted
          shape left right
    case right =>
      constructor
      case left =>
        exact
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_read_or_primitive
            shape left right
      case right =>
        exact
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore_of_trace_read_agreement
            shape left right store hagree

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_bounds
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeTraceEventReadAddressFitsInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
            shape left right) event /\
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
            shape left right) event := by
  intro event hmem
  constructor
  · exact
      concreteBPNativeTraceEventReadAddressFitsInBits_of_mem
        (trace :=
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace)
        (event := event) hmem
  · exact
      concreteBPNativeTraceEventPrimitiveOperandsFitInBits_of_mem
        (trace :=
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace)
        (event := event) hmem

/--
Bounded all-size execution-story packet for the globally segmented final RMQ
trace.  It extends the store-backed execution story with a concrete finite
event width: every payload-read address and every word-primitive natural
operand/result appearing in the final trace fits that width.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted /\
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeTraceEventReadAddressFitsInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
            shape left right) event) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
            shape left right) event) := by
  rcases
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story
      shape left right with
    ⟨hcost, hrefine, hclass, hstore⟩
  exact
    ⟨hcost, hrefine, hclass, hstore,
      (fun event hmem =>
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_bounds
          shape left right event hmem).1),
      (fun event hmem =>
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_bounds
          shape left right event hmem).2)⟩

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_eq_traceResult_toCosted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
      shape hsize left right =
      (concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe
        shape hsize left right).toCosted := by
  simp [concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe,
    concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe,
    Costed.map]

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_eq_traceResult_toCosted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
        shape hsize left right).toCosted := by
  rfl

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_refines_wholeQueryInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
  rw [WordRAM.TraceResult.map_toCosted]
  rw [
    WholeQueryProgram.evalGlobalWordTraceOfSizeGe_refines_eval
      shape hsize left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_event_read_or_primitive
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        event.isReadWord \/ event.isWordPrimitive := by
  intro event _hmem
  exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WholeQueryProgram.evalGlobalWordTraceOfSizeGe_matchesReadStore
      shape hsize left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty

/--
Public execution-story packet for the globally segmented final RMQ trace.
It states that the globally segmented trace is the public query after `Costed`
projection, refines the existing whole-query interpreter, contains only
payload-read or word-primitive events, and every event agrees with the single
concrete global read store assembled from the final RMQ payload components.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_execution_story
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
        shape hsize left right).toCosted /\
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)) := by
  exact
    ⟨concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_eq_traceResult_toCosted
        shape hsize left right,
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_refines_wholeQueryInterpretedCosted
        shape hsize left right,
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_event_read_or_primitive
        shape hsize left right,
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_matchesReadStore
        shape hsize left right⟩

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_event_bounds
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        concreteBPNativeTraceEventReadAddressFitsInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBitsOfSizeGe
            shape hsize left right) event /\
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBitsOfSizeGe
            shape hsize left right) event := by
  intro event hmem
  constructor
  · exact
      concreteBPNativeTraceEventReadAddressFitsInBits_of_mem
        (trace :=
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
            shape hsize left right).trace)
        (event := event) hmem
  · exact
      concreteBPNativeTraceEventPrimitiveOperandsFitInBits_of_mem
        (trace :=
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
            shape hsize left right).trace)
        (event := event) hmem

/--
Bounded large-regime companion to the all-size global execution story.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_bounded_execution_story
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
        shape hsize left right).toCosted /\
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        concreteBPNativeTraceEventReadAddressFitsInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBitsOfSizeGe
            shape hsize left right) event) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBitsOfSizeGe
            shape hsize left right) event) := by
  rcases
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_execution_story
      shape hsize left right with
    ⟨hcost, hrefine, hclass, hstore⟩
  exact
    ⟨hcost, hrefine, hclass, hstore,
      (fun event hmem =>
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_event_bounds
          shape hsize left right event hmem).1),
      (fun event hmem =>
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_event_bounds
          shape hsize left right event hmem).2)⟩

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe_event_admissible
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        concreteBPNativeLargeRegimeTraceEventAdmissible
          shape hsize left right event := by
  intro event hmem
  unfold concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe at hmem
  unfold concreteBPNativeLargeRegimeTraceEventAdmissible
  simp [concreteBPNativeSuccinctRMQWholeQueryProgram,
    WholeQueryProgram.evalWordTraceOfSizeGe,
    WholeQueryInstr.evalWordTraceOfSizeGe,
    WholeQueryNatExpr.eval, WholeQueryState.empty, WholeQueryState.opt,
    WholeQueryState.setOpt, WordRAM.TraceResult.bind,
    WordRAM.TraceResult.map, WordRAM.TraceResult.pure] at hmem ⊢
  rcases List.mem_append.mp hmem with hleftMem | hmem
  · exact Or.inl hleftMem
  rcases List.mem_append.mp hmem with hrightMem | hmem
  · exact Or.inr (Or.inl hrightMem)
  cases hleftVal :
      (concreteBPNativeSelectCloseWordTraceResult shape left).value with
  | none =>
      simp [hleftVal] at hmem
  | some leftClose =>
      cases hrightVal :
          (concreteBPNativeSelectCloseWordTraceResult shape (right - 1)).value with
      | none =>
          simp [hleftVal, hrightVal] at hmem
      | some rightClose =>
          simp [hleftVal, hrightVal, List.mem_append] at hmem
          rcases hmem with hlcaMem | hmem
          · exact Or.inr (Or.inr (Or.inl
              (Exists.intro leftClose
                (Exists.intro rightClose hlcaMem))))
          cases hanswerVal :
              (concreteBPNativeLCACloseWordTraceResultOfSizeGe
                shape hsize leftClose rightClose).value with
          | none =>
              simp [hanswerVal] at hmem
          | some answerClose =>
              simp [hanswerVal, WholeQueryState.setNat] at hmem
              exact Or.inr (Or.inr (Or.inr (Or.inl
                (Exists.intro answerClose hmem))))

/--
Large-regime trace-event accounting for the current final RMQ word trace.

This is still component-local provenance: every event in the unified stream is
traced to one of the concrete component traces or is a non-read primitive, and
every event is classified as either a payload read or a word primitive.  The
stronger global-store theorem further relabels component-local payload-read
segments into one shared payload layout.
-/
def concreteBPNativeLargeRegimeTraceEventSourceAccounted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat)
    (event : WordRAM.TraceEvent) : Prop :=
  concreteBPNativeLargeRegimeTraceEventAdmissible
    shape hsize left right event /\
    (event.isReadWord \/ event.isWordPrimitive)

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe_event_source_accounted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        concreteBPNativeLargeRegimeTraceEventSourceAccounted
          shape hsize left right event := by
  intro event hmem
  constructor
  · exact
      concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe_event_admissible
        shape hsize left right event hmem
  · exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event

/--
Single public execution-story packet for the current large-regime final RMQ
word trace.

The packet ties together the trace result, its `Costed` projection, and the
component-local provenance/classification theorem.  It is intentionally named
`source_accounted`: the remaining strengthening is the global-store version
that relabels local component segments into one concrete shared payload store.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceOfSizeGe_source_accounted_execution_story
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
      shape hsize left right =
      (concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe
        shape hsize left right).toCosted /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        concreteBPNativeLargeRegimeTraceEventSourceAccounted
          shape hsize left right event) := by
  constructor
  · exact
      concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_eq_traceResult_toCosted
        shape hsize left right
  · exact
      concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe_event_source_accounted
        shape hsize left right

theorem concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_refines_wholeQueryInterpretedCosted
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted shape left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
  rw [
    WholeQueryProgram.evalLeafTrace_refines_eval
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_refines_wholeQueryInterpretedCosted
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted shape left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
  rw [
    WholeQueryProgram.evalWordTrace_refines_eval
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_refines_wholeQueryInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
      shape hsize left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
  rw [
    WholeQueryProgram.evalWordTraceOfSizeGe_refines_eval
      shape hsize left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

theorem concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_refines_queryInterpretedCosted
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right =
      concreteBPNativeSuccinctRMQQueryInterpretedCosted shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
    concreteBPNativeSuccinctRMQWholeQueryProgram
    WholeQueryProgram.eval WholeQueryInstr.eval
    concreteBPNativeSuccinctRMQQueryInterpretedCosted
  apply Costed.ext
  · cases hleft :
        (concreteBPNativeSelectCloseInterpretedCosted shape left).value with
    | none =>
        simp [hleft, WholeQueryProgram.eval, WholeQueryInstr.eval,
          WholeQueryNatExpr.eval, WholeQueryState.empty,
          WholeQueryState.opt, WholeQueryState.setOpt, Costed.bind,
          Costed.map, Costed.pure]
    | some leftClose =>
        cases hright :
            (concreteBPNativeSelectCloseInterpretedCosted
              shape (right - 1)).value with
        | none =>
            simp [hleft, hright, WholeQueryProgram.eval,
              WholeQueryInstr.eval, WholeQueryNatExpr.eval,
              WholeQueryState.empty, WholeQueryState.opt,
              WholeQueryState.setOpt, Costed.bind, Costed.map, Costed.pure]
        | some rightClose =>
            cases hanswer :
                (concreteBPNativeLCACloseInterpretedCosted
                  shape leftClose rightClose).value with
            | none =>
                simp [hleft, hright, hanswer, WholeQueryProgram.eval,
                  WholeQueryInstr.eval, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.setOpt, Costed.bind, Costed.map,
                  Costed.pure]
            | some answerClose =>
                simp [hleft, hright, hanswer, WholeQueryProgram.eval,
                  WholeQueryInstr.eval, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.nat, WholeQueryState.setOpt,
                  WholeQueryState.setNat, Costed.bind, Costed.map,
                  Costed.pure]
  · cases hleft :
        (concreteBPNativeSelectCloseInterpretedCosted shape left).value with
    | none =>
        simp [hleft, WholeQueryProgram.eval, WholeQueryInstr.eval,
          WholeQueryNatExpr.eval, WholeQueryState.empty,
          WholeQueryState.opt, WholeQueryState.setOpt, Costed.bind,
          Costed.map, Costed.pure]
    | some leftClose =>
        cases hright :
            (concreteBPNativeSelectCloseInterpretedCosted
              shape (right - 1)).value with
        | none =>
            simp [hleft, hright, WholeQueryProgram.eval,
              WholeQueryInstr.eval, WholeQueryNatExpr.eval,
              WholeQueryState.empty, WholeQueryState.opt,
              WholeQueryState.setOpt, Costed.bind, Costed.map, Costed.pure]
        | some rightClose =>
            cases hanswer :
                (concreteBPNativeLCACloseInterpretedCosted
                  shape leftClose rightClose).value with
            | none =>
                simp [hleft, hright, hanswer, WholeQueryProgram.eval,
                  WholeQueryInstr.eval, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.setOpt, Costed.bind, Costed.map,
                  Costed.pure]
            | some answerClose =>
                simp [hleft, hright, hanswer, WholeQueryProgram.eval,
                  WholeQueryInstr.eval, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.nat, WholeQueryState.setOpt,
                  WholeQueryState.setNat, Costed.bind, Costed.map,
                  Costed.pure]

theorem concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    concreteBPNativeSelectCloseInterpretedCosted shape idx =
      concreteBPNativeSelectCloseCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily shape idx := by
  unfold concreteBPNativeSelectCloseInterpretedCosted
    concreteBPNativeSelectCloseCosted
    builtGenericSparseExceptionSelectBPCloseAccessFamily
    builtGenericSparseExceptionSelectBPCloseAccessDirectory
  simpa [GenericSelect.sparseExceptionSelectSource,
    GenericSelect.SparseExceptionSelectData.toChargedSelectPositionSource]
    using
      (GenericSelect.SparseExceptionSelectData.selectInterpretedCosted_refines_selectCosted
        (GenericSelect.sparseExceptionSelectData shape.bpCode false) idx)

theorem concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    concreteBPNativeRankCloseInterpretedCosted shape pos =
      concreteBPNativeRankCloseCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily shape pos := by
  unfold concreteBPNativeRankCloseInterpretedCosted
    concreteBPNativeRankCloseCosted
    builtGenericSparseExceptionSelectBPCloseAccessFamily
    builtGenericSparseExceptionSelectBPCloseAccessDirectory
  rw [
    (builtRelativeSplitBPCloseRankData shape)
      |>.rankRegisterInterpretedCosted_refines_rankInterpretedCosted false pos]
  exact
    (builtRelativeSplitBPCloseRankData shape)
      |>.rankInterpretedCosted_refines_rankCosted false pos

theorem concreteBPNativeLCACloseInterpretedCosted_refines_lcaCloseCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    concreteBPNativeLCACloseInterpretedCosted shape leftClose rightClose =
      concreteBPNativeLCACloseCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily
        shape leftClose rightClose := by
  unfold concreteBPNativeLCACloseInterpretedCosted
    concreteBPNativeLCACloseCosted
  have hfun :
      concreteBPNativeRankCloseInterpretedCosted shape =
        concreteBPNativeRankCloseCosted
          builtGenericSparseExceptionSelectBPCloseAccessFamily shape := by
    funext pos
    exact concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted
      shape pos
  simp [hfun]

theorem concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQQueryInterpretedCosted shape left right =
      concreteBPNativeSuccinctRMQQueryCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily
        shape left right := by
  unfold concreteBPNativeSuccinctRMQQueryInterpretedCosted
    concreteBPNativeSuccinctRMQQueryCosted
  simp only [
    concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted,
    concreteBPNativeLCACloseInterpretedCosted_refines_lcaCloseCosted,
    concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted]
  rfl

theorem concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted]
  exact
    concreteBPNativeSuccinctRMQQueryCosted_cost_le
      builtGenericSparseExceptionSelectBPCloseAccessFamily shape left right

theorem concreteBPNativeSuccinctRMQQueryInterpretedCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQQueryInterpretedCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted]
  exact
    concreteBPNativeSuccinctRMQQueryCosted_exact
      builtGenericSparseExceptionSelectBPCloseAccessFamily
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_refines_queryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_refines_queryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQQueryInterpretedCosted_exact
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_cost_le
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
      shape hsize left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (hsize : 2 ^ 128 <= shape.size)
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
      shape hsize left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_cost_le
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (hsize : 2 ^ 128 <= shape.size)
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
      hshape hlen hbound

/--
Interpreter-backed two-sided public capstone for the built generic-select
BP-native succinct RMQ path.

This theorem has the same lower-bound, payload, cost, and exactness shape as the
current public generic sparse-exception capstone, but its query clause is the
interpreted query defined in this module.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_interpreted_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQQueryInterpretedCosted
            shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost
                SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQQueryInterpretedCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile
  dsimp only at h
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, hcost, hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape left right
          exact
            concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le
              shape left right),
        (by
          intro shape hshape left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQQueryInterpretedCosted_exact
              hshape hlen hbound)⟩

/--
Whole-query-interpreted two-sided public capstone for the built generic-select
BP-native succinct RMQ path.

This strengthens the interpreted capstone by routing the query-level control
itself through the closed `WholeQueryProgram`; the component leaves are still
the interpreted select-close, compact close/LCA, and register-backed rank
queries.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
            shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost
                SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_interpreted_profile
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, _hcost, _hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape left right
          exact
            concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
              shape left right),
        (by
          intro shape hshape left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
              hshape hlen hbound)⟩

/--
Leaf-trace-preserving two-sided capstone for the built generic-select
BP-native succinct RMQ path.

This is the next flattening checkpoint after the closed whole-query controller:
the same fixed instruction list now evaluates to a domain-leaf trace before it
is projected back to `Costed`.  The trace still records interpreted leaf
queries, not one unified payload-store trace.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_leaf_trace_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted
            shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost
                SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, _hcost, _hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape left right
          exact
            concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_cost_le
              shape left right),
        (by
          intro shape hshape left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_exact
              hshape hlen hbound)⟩

/--
Unified-`WordRAM.TraceEvent` two-sided capstone for the built generic-select
BP-native succinct RMQ path.

This keeps the same payload and exactness theorem surface, but the public query
is now evaluated through `WholeQueryProgram.evalWordTrace`. Select-close,
answer-rank, and compact-close rank-seed reads contribute structural
payload/register traces; bounded local/fringe/interior close-navigation leaves
remain explicit charged decoder leaves.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted
            shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost
                SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, _hcost, _hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape left right
          exact
            concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_cost_le
              shape left right),
        (by
          intro shape hshape left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_exact
              hshape hlen hbound)⟩

/--
Large-regime unified-`WordRAM.TraceEvent` two-sided capstone for the built
generic-select BP-native succinct RMQ path.

This is the structural close-navigation strengthening of
`..._whole_query_word_trace_profile`: in the query clauses, the size hypothesis
routes the compact close/LCA leg through the positive-block local/fringe and
relative-rmM interior trace replay rather than through the all-size fallback.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_large_regime_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall (shape : Cartesian.CartesianShape),
          (hsize : 2 ^ 128 <= shape.size) ->
            forall left right,
              (concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
                shape hsize left right).cost <=
                  concreteBPNativeSuccinctRMQQueryCost
                    SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (hsize : 2 ^ 128 <= shape.size) ->
              forall {left len : Nat},
                0 < len ->
                  left + len <= n ->
                    (concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
                      shape hsize left (left + len)).erase =
                      some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, _hcost, _hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape hsize left right
          exact
            concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_cost_le
              shape hsize left right),
        (by
          intro shape hshape hsize left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_exact
              hshape hsize hlen hbound)⟩

/--
Globally segmented large-regime word-trace capstone for the built
generic-select BP-native succinct RMQ path.

This keeps the same two-sided `2*n + o(n)`, constant-query, exactness surface as
the large-regime word-trace capstone, but the query clauses use the relabeled
global-segment trace result.  Payload-read segment IDs are now consistent
across the final query.  The remaining execution-story hardening is the
`matchesReadStore` proof for the concrete global payload store.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_global_word_trace_large_regime_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall (shape : Cartesian.CartesianShape),
          (hsize : 2 ^ 128 <= shape.size) ->
            forall left right,
              (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
                shape hsize left right).cost <=
                  concreteBPNativeSuccinctRMQQueryCost
                    SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (hsize : 2 ^ 128 <= shape.size) ->
              forall {left len : Nat},
                0 < len ->
                  left + len <= n ->
                    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
                      shape hsize left (left + len)).erase =
                      some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, _hcost, _hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape hsize left right
          exact
            concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_cost_le
              shape hsize left right),
        (by
          intro shape hshape hsize left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_exact
              hshape hsize hlen hbound)⟩

end SuccinctFinal
end RMQ
