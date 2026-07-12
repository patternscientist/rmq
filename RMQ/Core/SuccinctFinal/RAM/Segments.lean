import RMQ.Core.SuccinctFinal
import RMQ.Core.GenericSelect.RAM
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAM
import RMQ.Core.WordRAM.Register

/-!
# Global segment layout for the final BP-native succinct RMQ RAM bridge

This module contains the concrete segment numbering and read-store map shared by
`RMQ.Core.SuccinctFinalRAM` and the flat-payload backing layer.
-/

namespace RMQ
namespace SuccinctFinal

/--
Concrete global segment layout for the generic sparse-exception close-select
trace. Segment `0` is reserved for the shared BP-code word store; auxiliary
tables start at segment `1`.
-/
def concreteBPNativeDeadTraceSegment : Nat := 29

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
  canonicalComponent := 20
  summary :=
    { baseline := 20
      minRel := 21
      maxRel := 22
      argOffset := 23
      deadSegment := concreteBPNativeDeadTraceSegment }
  localOffset := 24
  globalBlock := 25
  finiteSmallMin := 26
  finiteSmallArg := 27
  deadSegment := concreteBPNativeDeadTraceSegment

/-- Retired compatibility segment for the finite-small same-block close table. -/
def concreteBPNativeFiniteSmallSameBlockCloseTraceSegment : Nat := 28

/--
The concrete read-only payload store for the globally segmented final RMQ
trace.

Segments are assigned as follows:
* `0`: packed BP-code words shared by select, rank, and local-BP decoders.
* `1..16`: close-select auxiliary tables.
* `17..19`: final false-rank samples and packed BP-code words.
* `20..25`: compact close/LCA relative-rmM interior tables.
* `26..27`: retired finite-small interior witness slots; they resolve to no
  words in the public stores.
* `28`: retired finite-small same-block compatibility slot; the public
  all-size trace does not read it and the flat layout does not count it.

Word-primitive events such as in-word rank/select are not payload reads and
therefore do not consult this store.
-/
def concreteBPNativeSuccinctRMQGlobalReadStoreLegacy
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

/--
Reviewer-facing global store. Segment 20 is replaced by the canonical
concatenated interior component; every other segment is the compatibility
global store.
-/
def concreteBPNativeSuccinctRMQGlobalReadStore
    (shape : Cartesian.CartesianShape) : WordRAM.ReadStore where
  readWord? segment index :=
    let selectData :=
      GenericSelect.sparseExceptionSelectData shape.bpCode false
    let rankStore :=
      (builtRelativeSplitBPCloseRankData shape).rankRegisterWordRAMStore false
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
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words[index]?
    else
      none
/-- Segment 20 is exactly the canonical concatenated interior component store. -/
theorem concreteBPNativeSuccinctRMQGlobalReadStore_canonicalComponent
    (shape : Cartesian.CartesianShape) (index : Nat) :

    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        concreteBPNativeInteriorTraceSegments.canonicalComponent index =
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words[index]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore,
    concreteBPNativeInteriorTraceSegments]

theorem concreteBPNativeSuccinctRMQGlobalReadStoreLegacy_bpCode
    (shape : Cartesian.CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape).readWord? 0 index =

      (SuccinctSpace.chunkPayloadWords
        (SuccinctRank.machineWordBits shape.bpCode.length)
        shape.bpCode).toArray[index]? := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStoreLegacy,
    GenericSelect.sparseExceptionSelectData,
    GenericSelect.wordBits,
    SuccinctSpace.BoundedPayloadWordStore.ofChunks,
    SuccinctSpace.PayloadWordStore.wordRAMStore,
    WordRAM.Store.readWord?]
theorem concreteBPNativeSuccinctRMQGlobalReadStore_bpCode
    (shape : Cartesian.CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        0 index =
      (SuccinctSpace.chunkPayloadWords
        (SuccinctRank.machineWordBits shape.bpCode.length)
        shape.bpCode).toArray[index]? := by
  change (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape).readWord?
    0 index = _
  exact concreteBPNativeSuccinctRMQGlobalReadStoreLegacy_bpCode shape index


theorem concreteBPNativeSuccinctRMQGlobalReadStore_retiredFiniteSmallInterior_none
    (shape : Cartesian.CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 26 index =
        none /\
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 27 index =
        none := by
  simp [concreteBPNativeSuccinctRMQGlobalReadStore]

end SuccinctFinal
end RMQ
