import RMQ.Core.SuccinctRMQClassic
import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL, part 3.  Closing the scoping hole I found in the defender's
evidence: `L3_leaf_size_only` fixes ONE store shared by both shapes, so it says
nothing about the primary public route, whose leaf
`concreteBPNativeRankCloseWordTraceResultAtSegment` supplies a SHAPE-DERIVED
store `concreteBPNativeChunkedRankCloseSeedReadStore shape base`.

Goal: show the residual shape-dependence on that route is EXACTLY the store,
i.e. exactly memory contents reached by counted `readWord` events.
-/

namespace AdvF2Bridge

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian

/-- The non-store leaf is literally the store-parametric leaf applied to the
shape's own seed store. -/
theorem nonstore_is_withstore_at_seed
    (s : CartesianShape) (base pos : Nat) :
    concreteBPNativeRankCloseWordTraceResultAtSegment s base pos
      = concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s
          (concreteBPNativeChunkedRankCloseSeedReadStore s base) base pos :=
  rfl

/-- Restatement of the defender's decisive lemma, proved here independently so
this file does not depend on their file. -/
theorem L3_withstore_size_only
    (a b : CartesianShape) (hsize : a.size = b.size)
    (store : WordRAM.ReadStore) (base pos : Nat) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore a store base pos
      = concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore b store base pos := by
  have hlen : a.bpCode.length = b.bpCode.length := by
    rw [CartesianShape.bpCode_length, CartesianShape.bpCode_length, hsize]
  unfold concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  rw [hlen]
  unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  simp only [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordOffset,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos,
    show (builtRelativeSplitBPCloseRankData a).wordSize
        = (builtRelativeSplitBPCloseRankData b).wordSize from by
      show SuccinctRank.machineWordBits a.bpCode.length
          = SuccinctRank.machineWordBits b.bpCode.length
      rw [hlen],
    show (builtRelativeSplitBPCloseRankData a).blocksPerSuper
        = (builtRelativeSplitBPCloseRankData b).blocksPerSuper from by
      show SuccinctRank.machineWordBits a.bpCode.length
          = SuccinctRank.machineWordBits b.bpCode.length
      rw [hlen],
    hlen]

/--
**GAP-CLOSING THEOREM.**  On the PRIMARY PUBLIC ROUTE's non-store leaf, the
whole shape-dependence factors through (i) `shape.size` and (ii) the supplied
memory image.  Concretely: for same-size shapes `a b`, running the non-store
leaf of `a` is the same as running `b`'s leaf against `a`'s memory.

So `builtRelativeSplitBPCloseRankData` contributes nothing to the executed
address/branch structure beyond `size`; everything else it contributes is the
CONTENT of the store, which the leaf can only see via `readWord` events.
-/
theorem nonstore_leaf_shape_dependence_is_store_only
    (a b : CartesianShape) (hsize : a.size = b.size) (base pos : Nat) :
    concreteBPNativeRankCloseWordTraceResultAtSegment a base pos
      = concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore b
          (concreteBPNativeChunkedRankCloseSeedReadStore a base) base pos := by
  rw [nonstore_is_withstore_at_seed]
  exact L3_withstore_size_only a b hsize _ base pos

/-- Corollary: if the two shapes' seed stores agree pointwise (i.e. same memory
image), the non-store leaves are literally equal.  This isolates the store as
the ONLY residual channel. -/
theorem nonstore_leaf_eq_of_store_agree
    (a b : CartesianShape) (hsize : a.size = b.size) (base pos : Nat)
    (hstore :
      concreteBPNativeChunkedRankCloseSeedReadStore a base
        = concreteBPNativeChunkedRankCloseSeedReadStore b base) :
    concreteBPNativeRankCloseWordTraceResultAtSegment a base pos
      = concreteBPNativeRankCloseWordTraceResultAtSegment b base pos := by
  rw [nonstore_leaf_shape_dependence_is_store_only a b hsize base pos,
    hstore, nonstore_is_withstore_at_seed]

/-! ## Anti-oracle: every event of the non-store leaf matches its own store. -/
theorem nonstore_leaf_matchesReadStore
    (s : CartesianShape) (base pos : Nat) :
    forall event,
      List.Mem event (concreteBPNativeRankCloseWordTraceResultAtSegment s base pos).trace ->
        event.matchesReadStore (concreteBPNativeChunkedRankCloseSeedReadStore s base) := by
  rw [nonstore_is_withstore_at_seed]
  exact
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_matchesReadStore
      s (concreteBPNativeChunkedRankCloseSeedReadStore s base) base pos

end AdvF2Bridge

#print axioms AdvF2Bridge.nonstore_is_withstore_at_seed
#print axioms AdvF2Bridge.L3_withstore_size_only
#print axioms AdvF2Bridge.nonstore_leaf_shape_dependence_is_store_only
#print axioms AdvF2Bridge.nonstore_leaf_eq_of_store_agree
#print axioms AdvF2Bridge.nonstore_leaf_matchesReadStore
