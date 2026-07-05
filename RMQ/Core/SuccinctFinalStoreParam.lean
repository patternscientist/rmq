import RMQ.Core.SuccinctFinalRAM
import RMQ.Core.WordRAM.ReadStoreEval
import RMQ.Core.GenericSelect.RAMStoreParam

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

end SuccinctFinal

end RMQ
