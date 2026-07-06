import RMQ.Core.SuccinctFinalRAM
import RMQ.Core.WordRAM.ReadStoreEval
import RMQ.Core.GenericSelect.RAMStoreParam
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAMStoreParam

/-!
# Store-parametric leaves for the final RMQ whole-query trace

The globally segmented final-query trace (`SuccinctFinalRAM`) evaluates each
leaf against its component-local store and relabels the trace into the global
segment layout.  The store-extensional theorem there is therefore weak: value
and cost do not depend on the supplied store.

This file starts the genuine store-parameterized replay.  Each leaf gets a
`WithStore` evaluator whose reads and value are produced from a supplied
`WordRAM.ReadStore` pulled back along the leaf's segment map, together with:

* `_matchesReadStore` — for **every** store, the emitted read events report
  exactly that store's words (the by-construction anti-oracle clause);
* an agreement theorem — with the concrete global read store the evaluator is
  literally the canonical leaf trace, so exactness and cost transfer; and
* `_store_parametric` — two stores agreeing on the leaf's mapped segments
  produce the same value and trace.
-/

namespace RMQ

namespace SuccinctFinal

/-- Segment map placing the final false-rank component's three local segments
at a supplied base. -/
def concreteBPNativeRankCloseSegmentMap (rankSegmentBase : Nat) :
    Nat -> Nat :=
  WordRAM.tripleSegmentMap rankSegmentBase concreteBPNativeDeadTraceSegment

/--
The concrete global read store, pulled back along the final false-rank segment
map, is exactly the rank component's local store.
-/
theorem concreteBPNativeRankClose_pullback_globalReadStore
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (concreteBPNativeRankCloseSegmentMap
          concreteBPNativeRankCloseTraceSegmentBase) =
      WordRAM.ReadStore.ofStore
        ((builtRelativeSplitBPCloseRankData shape).rankRegisterWordRAMStore
          false) := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | _ | _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeRankCloseSegmentMap,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeRankCloseTraceSegmentBase,
      concreteBPNativeDeadTraceSegment,
      WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
      WordRAM.Store.readWord?]

/--
Store-parameterized final false-rank leaf: the two-level register rank program
is evaluated against the supplied read store pulled back along the rank segment
map, and the emitted trace is relabeled into the global layout.
-/
def concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (rankSegmentBase pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    (concreteBPNativeRankCloseSegmentMap rankSegmentBase)
    (WordRAM.TraceResult.ofResult
      (((builtRelativeSplitBPCloseRankData shape).rankRegisterProgram
          false (WordRAM.Register.NatExpr.reg 0)).evalR
        (store.pullback
          (concreteBPNativeRankCloseSegmentMap rankSegmentBase))
        (WordRAM.Register.RegFile.withNat1 pos)))

/-- For every supplied store, the store-parameterized rank leaf's read events
report exactly that store's words. -/
theorem concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (rankSegmentBase pos : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
            shape store rankSegmentBase pos).trace ->
        event.matchesReadStore store := by
  intro event hmem
  simp only [concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore,
    WordRAM.TraceResult.relabelReadSegmentsWith,
    WordRAM.TraceResult.ofResult] at hmem
  rcases List.mem_map.mp hmem with ⟨inner, hinner, rfl⟩
  exact
    WordRAM.TraceEvent.relabelReadSegmentWith_matchesReadStore_of_pullback
      (concreteBPNativeRankCloseSegmentMap rankSegmentBase) store
      (WordRAM.Register.NatProgram.evalR_matchesReadStore
        ((builtRelativeSplitBPCloseRankData shape).rankRegisterProgram
          false (WordRAM.Register.NatExpr.reg 0))
        (store.pullback
          (concreteBPNativeRankCloseSegmentMap rankSegmentBase))
        (WordRAM.Register.RegFile.withNat1 pos)
        inner hinner)

/--
With the concrete global read store, the store-parameterized rank leaf is
literally the canonical globally segmented rank leaf.
-/
theorem concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_globalReadStore
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        concreteBPNativeRankCloseTraceSegmentBase pos =
      concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase pos := by
  unfold concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
    concreteBPNativeRankCloseWordTraceResultAtSegment
    concreteBPNativeRankCloseWordTraceResult
  rw [concreteBPNativeRankClose_pullback_globalReadStore,
    WordRAM.Register.NatProgram.evalR_ofStore]
  rfl

/--
Whole-leaf parametricity: two read stores agreeing on the rank leaf's mapped
segments produce the same value and the same trace.
-/
theorem concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (rankSegmentBase pos : Nat)
    (hread :
      forall segment index,
        storeA.readWord?
            (concreteBPNativeRankCloseSegmentMap rankSegmentBase segment)
            index =
          storeB.readWord?
            (concreteBPNativeRankCloseSegmentMap rankSegmentBase segment)
            index) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape storeA rankSegmentBase pos =
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape storeB rankSegmentBase pos := by
  unfold concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  rw [WordRAM.ReadStore.pullback_eq_of_agree_on_map
    (concreteBPNativeRankCloseSegmentMap rankSegmentBase) hread]

/--
Store-parameterized positive same-block local-BP close leaf with the concrete
final false-rank seed.  Both the rank seed and the BP-code local window read
from the supplied global read store.
-/
def localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose : Nat) :
  WordRAM.TraceResult (Option Nat) :=
  SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape store concreteBPNativeRankCloseTraceSegmentBase)
      store blockSize leftClose rightClose

theorem localBPSameBlockCloseDecodedTraceResultWithFinalRankSeed_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose : Nat) :
    forall event,
      event ∈
          (localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
            shape store blockSize leftClose rightClose).trace ->
        event.matchesReadStore store := by
  unfold localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_matchesReadStore
        shape
        (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shape store concreteBPNativeRankCloseTraceSegmentBase)
        store blockSize leftClose rightClose
        (fun pos event hmem =>
          concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_matchesReadStore
            shape store concreteBPNativeRankCloseTraceSegmentBase pos
            event hmem)

theorem localBPSameBlockCloseDecodedTraceResultWithFinalRankSeed_evalWithStore
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose : Nat) :
    localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        blockSize leftClose rightClose =
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseDecodedTraceResultWithRankSeed
          shape
          (concreteBPNativeRankCloseWordTraceResultAtSegment
            shape concreteBPNativeRankCloseTraceSegmentBase)
          blockSize leftClose rightClose := by
  unfold localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
  have hrank :
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        concreteBPNativeRankCloseTraceSegmentBase) =
        concreteBPNativeRankCloseWordTraceResultAtSegment
          shape concreteBPNativeRankCloseTraceSegmentBase := by
    funext pos
    exact
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_globalReadStore
        shape pos
  rw [hrank]
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_eq_of_agree
        (concreteBPNativeRankCloseWordTraceResultAtSegment
          shape concreteBPNativeRankCloseTraceSegmentBase)
        (concreteBPNativeSuccinctRMQGlobalReadStore_bpCode shape)
        blockSize leftClose rightClose

theorem localBPSameBlockCloseDecodedTraceResultWithFinalRankSeed_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hbp :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (hrank :
      forall segment index,
        storeA.readWord?
            (concreteBPNativeRankCloseSegmentMap
              concreteBPNativeRankCloseTraceSegmentBase segment)
            index =
          storeB.readWord?
            (concreteBPNativeRankCloseSegmentMap
              concreteBPNativeRankCloseTraceSegmentBase segment)
            index)
    (blockSize leftClose rightClose : Nat) :
    localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
        shape storeA blockSize leftClose rightClose =
      localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
        shape storeB blockSize leftClose rightClose := by
  unfold localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
  have hrankTrace :
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape storeA concreteBPNativeRankCloseTraceSegmentBase) =
        concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shape storeB concreteBPNativeRankCloseTraceSegmentBase := by
    funext pos
    exact
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_store_parametric
        shape concreteBPNativeRankCloseTraceSegmentBase pos hrank
  rw [hrankTrace]
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_store_parametric
        shape
        (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shape storeB concreteBPNativeRankCloseTraceSegmentBase)
        hbp blockSize leftClose rightClose

/--
Store-parameterized close-select leaf: the sparse-exception select tower
evaluated against a supplied read store under the final global segment layout.
-/
def concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    |>.selectTraceResultRelabeledWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout store idx

/-- For every supplied store, the store-parameterized close-select leaf's read
events report exactly that store's words. -/
theorem concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (idx : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
            shape store idx).trace ->
        event.matchesReadStore store := by
  exact
    (GenericSelect.sparseExceptionSelectData shape.bpCode false)
      |>.selectTraceResultRelabeledWithStore_matchesReadStore
        concreteBPNativeSelectCloseTraceSegmentLayout store idx

section SelectClosePullbacks

variable (shape : Cartesian.CartesianShape)

private theorem selectClosePullback_superBaseOccurrence :
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

private theorem selectClosePullback_superBaseWordIndex :
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

private theorem selectClosePullback_superRankBefore :
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

private theorem selectClosePullback_superFirstOffset :
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

private theorem selectClosePullback_localBaseOccurrence :
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

private theorem selectClosePullback_localBaseWordIndex :
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

private theorem selectClosePullback_localRankBefore :
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

private theorem selectClosePullback_localFirstOffset :
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

private theorem selectClosePullback_longFlagRank :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.tripleSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment) =
      WordRAM.ReadStore.ofStore
        ((GenericSelect.sparseExceptionSelectData shape.bpCode
          false).longFlagRankData.rankRegisterWordRAMStore true) := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | _ | _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_longRelative :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).longSuperRelativeTable.wordRAMStore := by
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

private theorem selectClosePullback_sparseRank :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.tripleSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment) =
      WordRAM.ReadStore.ofStore
        ((GenericSelect.sparseExceptionSelectData shape.bpCode
          false).sparseDirectory.rankData.rankRegisterWordRAMStore true) := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | _ | _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_sparseRelative :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.relativeBase
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).sparseDirectory.relativeTable.wordRAMStore := by
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

private theorem selectClosePullback_bitWords :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).bitWords.store.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

end SelectClosePullbacks

/--
With the concrete global read store, the store-parameterized close-select leaf
is literally the canonical globally segmented close-select leaf.
-/
theorem concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_globalReadStore
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape) idx =
      concreteBPNativeSelectCloseGlobalWordTraceResult shape idx := by
  unfold concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
    concreteBPNativeSelectCloseGlobalWordTraceResult
  exact
    (GenericSelect.sparseExceptionSelectData shape.bpCode false)
      |>.selectTraceResultRelabeledWithStore_eq_of_pullback
        (selectClosePullback_superBaseOccurrence shape)
        (selectClosePullback_superBaseWordIndex shape)
        (selectClosePullback_superRankBefore shape)
        (selectClosePullback_superFirstOffset shape)
        (selectClosePullback_longFlagRank shape)
        (selectClosePullback_longRelative shape)
        (selectClosePullback_localBaseOccurrence shape)
        (selectClosePullback_localBaseWordIndex shape)
        (selectClosePullback_localRankBefore shape)
        (selectClosePullback_localFirstOffset shape)
        (selectClosePullback_sparseRank shape)
        (selectClosePullback_sparseRelative shape)
        (selectClosePullback_bitWords shape)
        idx

/-- Precise store agreement for the whole final RMQ supplied-store replay.
The fields enumerate the final global segment layout: BP code, select-close
auxiliary tables, final false-rank tables, and compact close/LCA interior
tables. -/
structure concreteBPNativeSuccinctRMQWholeQueryReadAgreement
    (_shape : Cartesian.CartesianShape)
    (storeA storeB : WordRAM.ReadStore) : Prop where
  bpCode :
    forall index,
      storeA.readWord? 0 index = storeB.readWord? 0 index
  selectSuperBaseOccurrence :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseOccurrence
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseOccurrence
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index
  selectSuperBaseWordIndex :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseWordIndex
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseWordIndex
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index
  selectSuperRankBefore :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.rankBefore
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.rankBefore
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index
  selectSuperFirstOffset :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.firstOffset
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.firstOffset
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index
  selectLongFlagRank :
    forall segment index,
      storeA.readWord?
          (WordRAM.tripleSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
            concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.tripleSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
            concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
            segment) index
  selectLongRelative :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
            concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
            concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
            segment) index
  selectLocalBaseOccurrence :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseOccurrence
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseOccurrence
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index
  selectLocalBaseWordIndex :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseWordIndex
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseWordIndex
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index
  selectLocalRankBefore :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.rankBefore
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.rankBefore
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index
  selectLocalFirstOffset :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.firstOffset
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.firstOffset
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index
  selectSparseRank :
    forall segment index,
      storeA.readWord?
          (WordRAM.tripleSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.tripleSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
            segment) index
  selectSparseRelative :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.relativeBase
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.relativeBase
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
            segment) index
  selectBitWords :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
            concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
            concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
            segment) index
  rankClose :
    forall segment index,
      storeA.readWord?
          (concreteBPNativeRankCloseSegmentMap
            concreteBPNativeRankCloseTraceSegmentBase segment) index =
        storeB.readWord?
          (concreteBPNativeRankCloseSegmentMap
            concreteBPNativeRankCloseTraceSegmentBase segment) index
  interiorLocal :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeInteriorTraceSegments.localOffset
            concreteBPNativeInteriorTraceSegments.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeInteriorTraceSegments.localOffset
            concreteBPNativeInteriorTraceSegments.deadSegment
            segment) index
  interiorGlobal :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeInteriorTraceSegments.globalBlock
            concreteBPNativeInteriorTraceSegments.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeInteriorTraceSegments.globalBlock
            concreteBPNativeInteriorTraceSegments.deadSegment
            segment) index
  summaryBaseline :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeInteriorTraceSegments.summary.baseline
            concreteBPNativeInteriorTraceSegments.summary.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeInteriorTraceSegments.summary.baseline
            concreteBPNativeInteriorTraceSegments.summary.deadSegment
            segment) index
  summaryMinRel :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeInteriorTraceSegments.summary.minRel
            concreteBPNativeInteriorTraceSegments.summary.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeInteriorTraceSegments.summary.minRel
            concreteBPNativeInteriorTraceSegments.summary.deadSegment
            segment) index
  summaryMaxRel :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeInteriorTraceSegments.summary.maxRel
            concreteBPNativeInteriorTraceSegments.summary.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeInteriorTraceSegments.summary.maxRel
            concreteBPNativeInteriorTraceSegments.summary.deadSegment
            segment) index
  summaryArgOffset :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeInteriorTraceSegments.summary.argOffset
            concreteBPNativeInteriorTraceSegments.summary.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeInteriorTraceSegments.summary.argOffset
            concreteBPNativeInteriorTraceSegments.summary.deadSegment
            segment) index

namespace concreteBPNativeSuccinctRMQWholeQueryReadAgreement

theorem refl (shape : Cartesian.CartesianShape)
    (store : WordRAM.ReadStore) :
    concreteBPNativeSuccinctRMQWholeQueryReadAgreement
      shape store store := by
  constructor <;> intros <;> rfl

theorem of_all_segments
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall segment index,
        storeA.readWord? segment index = storeB.readWord? segment index) :
    concreteBPNativeSuccinctRMQWholeQueryReadAgreement
      shape storeA storeB := by
  constructor <;> intros <;> exact hread _ _

end concreteBPNativeSuccinctRMQWholeQueryReadAgreement

theorem concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (rankSegmentBase pos : Nat) :
    forall event,
      event ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
            shape store rankSegmentBase pos).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
      (concreteBPNativeRankCloseSegmentMap rankSegmentBase)
      (WordRAM.TraceResult.ofResult
        (((builtRelativeSplitBPCloseRankData shape).rankRegisterProgram
            false (WordRAM.Register.NatExpr.reg 0)).evalR
          (store.pullback
            (concreteBPNativeRankCloseSegmentMap rankSegmentBase))
          (WordRAM.Register.RegFile.withNat1 pos)))
      (by
        intro event hmem
        simpa only [WordRAM.TraceResult.ofResult_trace] using
          WordRAM.Register.NatProgram.evalR_no_syntheticCostOnlyPrimitive
            ((builtRelativeSplitBPCloseRankData shape).rankRegisterProgram
              false (WordRAM.Register.NatExpr.reg 0))
            (store.pullback
              (concreteBPNativeRankCloseSegmentMap rankSegmentBase))
            (WordRAM.Register.RegFile.withNat1 pos)
            event hmem)

theorem concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hagree :
      concreteBPNativeSuccinctRMQWholeQueryReadAgreement
        shape storeA storeB)
    (idx : Nat) :
    concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape storeA idx =
      concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape storeB idx := by
  unfold concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
  exact
    (GenericSelect.sparseExceptionSelectData shape.bpCode false)
      |>.selectTraceResultRelabeledWithStore_store_parametric
        (layout := concreteBPNativeSelectCloseTraceSegmentLayout)
        hagree.selectSuperBaseOccurrence
        hagree.selectSuperBaseWordIndex
        hagree.selectSuperRankBefore
        hagree.selectSuperFirstOffset
        hagree.selectLongFlagRank
        hagree.selectLongRelative
        hagree.selectLocalBaseOccurrence
        hagree.selectLocalBaseWordIndex
        hagree.selectLocalRankBefore
        hagree.selectLocalFirstOffset
        hagree.selectSparseRank
        hagree.selectSparseRelative
        hagree.selectBitWords
        idx

theorem concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (idx : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
            shape store idx).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
  exact
    (GenericSelect.sparseExceptionSelectData shape.bpCode false)
      |>.selectTraceResultRelabeledWithStore_no_syntheticCostOnlyPrimitive
        concreteBPNativeSelectCloseTraceSegmentLayout store idx

def concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
    shape
    (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
      shape store concreteBPNativeRankCloseTraceSegmentBase)
    concreteBPNativeInteriorTraceSegments
    store concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
    leftClose rightClose

theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) :
    forall event,
      event ∈
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
            shape store leftClose rightClose).trace ->
        event.matchesReadStore store := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_matchesReadStore
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape store concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments store
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      (fun pos event hmem =>
        concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_matchesReadStore
          shape store concreteBPNativeRankCloseTraceSegmentBase pos
          event hmem)

theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) :
    forall event,
      event ∈
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
            shape store leftClose rightClose).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_no_syntheticCostOnlyPrimitive
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape store concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments store
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      (fun pos event hmem =>
        concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
          shape store concreteBPNativeRankCloseTraceSegmentBase pos
          event hmem)

theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_globalReadStore
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        leftClose rightClose =
      concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        shape leftClose rightClose := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
  have hrank :
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        concreteBPNativeRankCloseTraceSegmentBase) =
        concreteBPNativeRankCloseWordTraceResultAtSegment
          shape concreteBPNativeRankCloseTraceSegmentBase := by
    funext pos
    exact
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_globalReadStore
        shape pos
  rw [hrank]
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_eq_of_agree
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      (concreteBPNativeSuccinctRMQGlobalReadStore_bpCode shape)
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

theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hagree :
      concreteBPNativeSuccinctRMQWholeQueryReadAgreement
        shape storeA storeB)
    (leftClose rightClose : Nat) :
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shape storeA leftClose rightClose =
      concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shape storeB leftClose rightClose := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  have hrank :
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape storeA concreteBPNativeRankCloseTraceSegmentBase) =
        concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shape storeB concreteBPNativeRankCloseTraceSegmentBase := by
    funext pos
    exact
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_store_parametric
        shape concreteBPNativeRankCloseTraceSegmentBase pos
        hagree.rankClose
  rw [hrank]
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_store_parametric
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape storeB concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      hagree.bpCode
      hagree.interiorLocal
      hagree.interiorGlobal
      hagree.summaryBaseline
      hagree.summaryMinRel
      hagree.summaryMaxRel
      hagree.summaryArgOffset

namespace WholeQueryInstr

def evalGlobalWordTraceWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) : WordRAM.TraceResult WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      WordRAM.TraceResult.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
          shape store (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          WordRAM.TraceResult.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
              shape store leftClose rightClose)
      | _, _ => WordRAM.TraceResult.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
              shape store concreteBPNativeRankCloseTraceSegmentBase
              (pos.eval left right state))
      | none => WordRAM.TraceResult.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.pure
            (state.setOpt dst (some (state.nat src - 1)))
      | none =>
          WordRAM.TraceResult.pure (state.setOpt dst none)

theorem evalGlobalWordTraceWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      event ∈
          (instr.evalGlobalWordTraceWithStore
            shape store left right state).trace ->
        event.matchesReadStore store := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTraceWithStore]
      exact
        concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_matchesReadStore
          shape store (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [evalGlobalWordTraceWithStore, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [evalGlobalWordTraceWithStore, hleft, hright]
          | some rightClose =>
              simp [evalGlobalWordTraceWithStore, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_matchesReadStore
                  shape store leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTraceWithStore, hguard]
      | some _ =>
        simp [evalGlobalWordTraceWithStore, hguard]
        exact
          concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_matchesReadStore
            shape store concreteBPNativeRankCloseTraceSegmentBase
            (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceWithStore, hguard] <;>
        intro event hmem <;> cases hmem

theorem evalGlobalWordTraceWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      event ∈
          (instr.evalGlobalWordTraceWithStore
            shape store left right state).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTraceWithStore]
      exact
        concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_no_syntheticCostOnlyPrimitive
          shape store (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [evalGlobalWordTraceWithStore, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [evalGlobalWordTraceWithStore, hleft, hright]
          | some rightClose =>
              simp [evalGlobalWordTraceWithStore, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_no_syntheticCostOnlyPrimitive
                  shape store leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTraceWithStore, hguard]
      | some _ =>
        simp [evalGlobalWordTraceWithStore, hguard]
        exact
          concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
            shape store concreteBPNativeRankCloseTraceSegmentBase
            (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceWithStore, hguard] <;>
        intro event hmem <;> cases hmem

theorem evalGlobalWordTraceWithStore_globalReadStore
    (shape : Cartesian.CartesianShape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    instr.evalGlobalWordTraceWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        left right state =
      instr.evalGlobalWordTrace shape left right state := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTraceWithStore, evalGlobalWordTrace,
        concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_globalReadStore]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          simp [evalGlobalWordTraceWithStore, evalGlobalWordTrace,
            hleft, hright,
            concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_globalReadStore]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceWithStore, evalGlobalWordTrace,
          hguard,
          concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_globalReadStore]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceWithStore, evalGlobalWordTrace, hguard]

theorem evalGlobalWordTraceWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hagree :
      concreteBPNativeSuccinctRMQWholeQueryReadAgreement
        shape storeA storeB)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    instr.evalGlobalWordTraceWithStore shape storeA left right state =
      instr.evalGlobalWordTraceWithStore shape storeB left right state := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTraceWithStore,
        concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_store_parametric
          shape hagree (idx.eval left right state)]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          simp [evalGlobalWordTraceWithStore, hleft, hright,
            concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_store_parametric
              shape hagree]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTraceWithStore, hguard]
      | some _ =>
          simp [evalGlobalWordTraceWithStore, hguard,
            concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_store_parametric
              shape concreteBPNativeRankCloseTraceSegmentBase
              (pos.eval left right state) hagree.rankClose]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceWithStore, hguard]

end WholeQueryInstr

namespace WholeQueryProgram

def evalGlobalWordTraceWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> WordRAM.TraceResult WholeQueryState
  | [], state => WordRAM.TraceResult.pure state
  | instr :: rest, state =>
      WordRAM.TraceResult.bind
        (instr.evalGlobalWordTraceWithStore shape store left right state)
        fun state' =>
          evalGlobalWordTraceWithStore shape store left right rest state'

theorem evalGlobalWordTraceWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      event ∈
          (evalGlobalWordTraceWithStore
            shape store left right program state).trace ->
        event.matchesReadStore store := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTraceWithStore]
  | cons instr rest ih =>
      unfold evalGlobalWordTraceWithStore
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTraceWithStore_matchesReadStore
            shape store left right instr state
      · exact ih
          (instr.evalGlobalWordTraceWithStore
            shape store left right state).value

theorem evalGlobalWordTraceWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      event ∈
          (evalGlobalWordTraceWithStore
            shape store left right program state).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTraceWithStore]
  | cons instr rest ih =>
      unfold evalGlobalWordTraceWithStore
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTraceWithStore_no_syntheticCostOnlyPrimitive
            shape store left right instr state
      · exact ih
          (instr.evalGlobalWordTraceWithStore
            shape store left right state).value

theorem evalGlobalWordTraceWithStore_globalReadStore
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    evalGlobalWordTraceWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        left right program state =
      evalGlobalWordTrace shape left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTraceWithStore, evalGlobalWordTrace]
  | cons instr rest ih =>
      unfold evalGlobalWordTraceWithStore evalGlobalWordTrace
      rw [
        WholeQueryInstr.evalGlobalWordTraceWithStore_globalReadStore
          shape left right instr state]
      cases hfirst : instr.evalGlobalWordTrace shape left right state
      simp [WordRAM.TraceResult.bind, ih]

theorem evalGlobalWordTraceWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hagree :
      concreteBPNativeSuccinctRMQWholeQueryReadAgreement
        shape storeA storeB)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    evalGlobalWordTraceWithStore shape storeA left right program state =
      evalGlobalWordTraceWithStore shape storeB left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTraceWithStore]
  | cons instr rest ih =>
      unfold evalGlobalWordTraceWithStore
      rw [
        WholeQueryInstr.evalGlobalWordTraceWithStore_store_parametric
          shape hagree left right instr state]
      cases hfirst :
          instr.evalGlobalWordTraceWithStore
            shape storeB left right state
      simp [WordRAM.TraceResult.bind, ih]

end WholeQueryProgram

def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map WholeQueryState.output?
    (WholeQueryProgram.evalGlobalWordTraceWithStore shape store left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty)

def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) : Costed (Option Nat) :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    shape store left right).toCosted

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right).trace ->
        event.matchesReadStore store := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WholeQueryProgram.evalGlobalWordTraceWithStore_matchesReadStore
      shape store left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WholeQueryProgram.evalGlobalWordTraceWithStore_no_syntheticCostOnlyPrimitive
      shape store left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
  rw [
    WholeQueryProgram.evalGlobalWordTraceWithStore_globalReadStore
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hagree :
      concreteBPNativeSuccinctRMQWholeQueryReadAgreement
        shape storeA storeB)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape storeA left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape storeB left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  rw [
    WholeQueryProgram.evalGlobalWordTraceWithStore_store_parametric
      shape hagree left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_refines_wholeQueryInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
      shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      left right).toCosted =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
        shape left right := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_wholeQueryInterpretedCosted
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_exact
      hshape hlen hbound

end SuccinctFinal

end RMQ
