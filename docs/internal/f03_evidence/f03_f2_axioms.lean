import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 / F2 classification experiment.

Target: `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData`, the two-level
rank data structure over `shape.bpCode`, and specifically the GEOMETRY of that
structure that the CONTROLLER consumes at leaf L3
(`concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore`).

Part A: each geometry field of the built structure, by `rfl`, as a function of
`shape.bpCode.length` alone.

Part B: the decisive statement -- the whole L3 leaf (value AND trace) depends on
`shape` only through `shape.size`, for EVERY shape pair, EVERY store, EVERY
segment base, EVERY position.
-/

namespace F03F2

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian

/-! ## Part A: geometry fields, definitionally -/

theorem wordSize_eq (s : CartesianShape) :
    (builtRelativeSplitBPCloseRankData s).wordSize
      = SuccinctRank.machineWordBits s.bpCode.length := rfl

theorem blocksPerSuper_eq (s : CartesianShape) :
    (builtRelativeSplitBPCloseRankData s).blocksPerSuper
      = SuccinctRank.machineWordBits s.bpCode.length := rfl

theorem superWidth_eq (s : CartesianShape) :
    (builtRelativeSplitBPCloseRankData s).superWidth
      = SuccinctRank.machineWordBits s.bpCode.length := rfl

theorem blockWidth_eq (s : CartesianShape) :
    (builtRelativeSplitBPCloseRankData s).blockWidth
      = SuccinctRank.machineWordBits
          (SuccinctRank.machineWordBits s.bpCode.length *
            SuccinctRank.machineWordBits s.bpCode.length) := rfl

/-- All four geometry fields are functions of `2 * shape.size`, i.e. of `n`. -/
theorem wordSize_size_only (s : CartesianShape) :
    (builtRelativeSplitBPCloseRankData s).wordSize
      = SuccinctRank.machineWordBits (2 * s.size) := by
  rw [wordSize_eq, CartesianShape.bpCode_length]

theorem blocksPerSuper_size_only (s : CartesianShape) :
    (builtRelativeSplitBPCloseRankData s).blocksPerSuper
      = SuccinctRank.machineWordBits (2 * s.size) := by
  rw [blocksPerSuper_eq, CartesianShape.bpCode_length]

theorem superWidth_size_only (s : CartesianShape) :
    (builtRelativeSplitBPCloseRankData s).superWidth
      = SuccinctRank.machineWordBits (2 * s.size) := by
  rw [superWidth_eq, CartesianShape.bpCode_length]

theorem blockWidth_size_only (s : CartesianShape) :
    (builtRelativeSplitBPCloseRankData s).blockWidth
      = SuccinctRank.machineWordBits
          (SuccinctRank.machineWordBits (2 * s.size) *
            SuccinctRank.machineWordBits (2 * s.size)) := by
  rw [blockWidth_eq, CartesianShape.bpCode_length]

/-! ## Part A': the three addresses / one limit the L3 leaf actually forms -/

theorem superIndex_size_only (s : CartesianShape) (pos : Nat) :
    (builtRelativeSplitBPCloseRankData s).superIndex pos
      = Nat.min pos (2 * s.size)
          / SuccinctRank.machineWordBits (2 * s.size)
          / SuccinctRank.machineWordBits (2 * s.size) := by
  show (Nat.min pos s.bpCode.length
      / (builtRelativeSplitBPCloseRankData s).wordSize)
      / (builtRelativeSplitBPCloseRankData s).blocksPerSuper = _
  rw [wordSize_eq, blocksPerSuper_eq, CartesianShape.bpCode_length]

theorem wordIndex_size_only (s : CartesianShape) (pos : Nat) :
    (builtRelativeSplitBPCloseRankData s).wordIndex pos
      = Nat.min pos (2 * s.size)
          / SuccinctRank.machineWordBits (2 * s.size) := by
  show Nat.min pos s.bpCode.length
      / (builtRelativeSplitBPCloseRankData s).wordSize = _
  rw [wordSize_eq, CartesianShape.bpCode_length]

theorem wordOffset_size_only (s : CartesianShape) (pos : Nat) :
    (builtRelativeSplitBPCloseRankData s).wordOffset pos
      = Nat.min pos (2 * s.size)
          - (Nat.min pos (2 * s.size)
              / SuccinctRank.machineWordBits (2 * s.size))
            * SuccinctRank.machineWordBits (2 * s.size) := by
  show Nat.min pos s.bpCode.length
      - (Nat.min pos s.bpCode.length
          / (builtRelativeSplitBPCloseRankData s).wordSize)
        * (builtRelativeSplitBPCloseRankData s).wordSize = _
  rw [wordSize_eq, CartesianShape.bpCode_length]

/-! ## Part B: the L3 leaf is size-only, quantified over everything -/

/-- Generic: the chunked rank leaf reads a rank structure only through
`bits.length`, `wordSize`, and `blocksPerSuper`. -/
theorem chunkedRankLeaf_factors
    {bitsA bitsB : List Bool} {sa ba qa sb bb qb : Nat}
    (dataA : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData bitsA sa ba qa)
    (dataB : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData bitsB sb bb qb)
    (hlen : bitsA.length = bitsB.length)
    (hw : dataA.wordSize = dataB.wordSize)
    (hb : dataA.blocksPerSuper = dataB.blocksPerSuper)
    (store : WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment c : Nat)
    (target : Bool) (pos : Nat) :
    dataA.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment c target pos
      = dataB.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment c target pos := by
  unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  simp only [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordOffset,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos,
    hlen, hw, hb]

/--
**DECISIVE.** The store-parametric rank leaf L3 of the closed controller is
identical -- same returned value, same event-by-event trace -- for any two
Cartesian shapes of the same size, against the same supplied read store, at
every segment base and every position.

Hence the ONLY thing the controller learns from `builtRelativeSplitBPCloseRankData`
without a probe is `shape.size`, i.e. `n`.
-/
theorem L3_leaf_size_only
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
  exact chunkedRankLeaf_factors
    (builtRelativeSplitBPCloseRankData a)
    (builtRelativeSplitBPCloseRankData b)
    hlen
    (by rw [wordSize_eq, wordSize_eq, hlen])
    (by rw [blocksPerSuper_eq, blocksPerSuper_eq, hlen])
    store rankSegmentBase (rankSegmentBase + 1) (rankSegmentBase + 2)
    (rankSegmentBase + 4)
    (SuccinctClose.bpFringeChunkBits b.bpCode.length) false pos

end F03F2

namespace F03F2Axioms
#print axioms F03F2.L3_leaf_size_only
#print axioms F03F2.chunkedRankLeaf_factors
#print axioms F03F2.wordSize_eq
#print axioms F03F2.blocksPerSuper_eq
#print axioms F03F2.superWidth_eq
#print axioms F03F2.blockWidth_eq
#print axioms F03F2.superIndex_size_only
#print axioms F03F2.wordIndex_size_only
#print axioms F03F2.wordOffset_size_only
end F03F2Axioms
