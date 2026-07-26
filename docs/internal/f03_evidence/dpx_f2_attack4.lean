import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Independent re-derivation of the decisive statement, WITHOUT reusing the
audited file, plus an axiom audit, plus the two extra universality
strengthenings the audit did not state:

  (A) equal size <-> equal leaf, in BOTH directions of interest;
  (B) the leaf as a function of `n` alone: there is a single function of
      (n, store, base, pos) that computes it for every shape of size n.
-/

namespace DPXF2D

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian

/-- Re-proved from scratch here (not imported from the audited scratch file). -/
theorem leaf_size_only
    (a b : CartesianShape) (hsize : a.size = b.size)
    (store : WordRAM.ReadStore) (rankSegmentBase pos : Nat) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        a store rankSegmentBase pos
      = concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        b store rankSegmentBase pos := by
  have hlen : a.bpCode.length = b.bpCode.length := by
    rw [CartesianShape.bpCode_length, CartesianShape.bpCode_length, hsize]
  unfold concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  rw [hlen]
  unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  simp only [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordOffset,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos,
    hlen,
    show (builtRelativeSplitBPCloseRankData a).wordSize
        = (builtRelativeSplitBPCloseRankData b).wordSize from by
      show SuccinctRank.machineWordBits a.bpCode.length
        = SuccinctRank.machineWordBits b.bpCode.length
      rw [hlen],
    show (builtRelativeSplitBPCloseRankData a).blocksPerSuper
        = (builtRelativeSplitBPCloseRankData b).blocksPerSuper from by
      show SuccinctRank.machineWordBits a.bpCode.length
        = SuccinctRank.machineWordBits b.bpCode.length
      rw [hlen]]

/-- (B) A shape-FREE function of `n` that computes the leaf.  Uses the
canonical left spine of `n` nodes as the witness shape; the point is that the
controller could obtain the leaf from `n` alone. -/
def spineL : Nat -> CartesianShape
  | 0 => .empty
  | k + 1 => .node (spineL k) .empty

theorem spineL_size (k : Nat) : (spineL k).size = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [spineL, CartesianShape.size, ih]

/-- The leaf factors through `n` on the nose: a function of `(n, store, base,
pos)` with no shape argument reproduces it for EVERY shape. -/
def leafOfN (n : Nat) (store : WordRAM.ReadStore) (base pos : Nat) :
    WordRAM.TraceResult Nat :=
  concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
    (spineL n) store base pos

theorem leaf_factors_through_n
    (s : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        s store base pos
      = leafOfN s.size store base pos :=
  leaf_size_only s (spineL s.size) (by rw [spineL_size]) store base pos

#print axioms leaf_size_only
#print axioms leaf_factors_through_n

end DPXF2D
