import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 / F1 CHECKED classification theorem.

Claim: `concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore` (controller
leaf L3) depends on the `CartesianShape` argument ONLY through `shape.size`.
Hence, for every store, every segment base and every position, the leaf's VALUE
and its full read TRACE are functions of (n, base, pos, store replies) alone.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctRank

namespace F03F1Thm

/-- Step 0: the built rank data's two geometry knobs are size-only. -/
theorem builtData_wordSize (shape : CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).wordSize
      = SuccinctRank.machineWordBits shape.bpCode.length := rfl

theorem builtData_blocksPerSuper (shape : CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).blocksPerSuper
      = SuccinctRank.machineWordBits shape.bpCode.length := rfl

/-- Step 1: `bpChunkedRankTraceResultWithStore` consumes its `data` argument
(and therefore the type index `bits`) only through `bits.length`, `wordSize`
and `blocksPerSuper`.  Everything else in `data` — the sample tables, the packed
bit words, i.e. the actual tree CONTENTS — is inert for both value and trace. -/
theorem bpChunkedRank_congr
    {bits1 bits2 : List Bool} {so1 bo1 qc1 so2 bo2 qc2 : Nat}
    (d1 : TwoLevelPayloadLiveStoredWordRankData bits1 so1 bo1 qc1)
    (d2 : TwoLevelPayloadLiveStoredWordRankData bits2 so2 bo2 qc2)
    (hlen : bits1.length = bits2.length)
    (hws : d1.wordSize = d2.wordSize)
    (hbps : d1.blocksPerSuper = d2.blocksPerSuper)
    (store : WordRAM.ReadStore) (ss bs ws cs c1 c2 : Nat) (hc : c1 = c2)
    (target : Bool) (pos : Nat) :
    d1.bpChunkedRankTraceResultWithStore store ss bs ws cs c1 target pos
      = d2.bpChunkedRankTraceResultWithStore store ss bs ws cs c2 target pos := by
  have hq : d1.queryPos pos = d2.queryPos pos := by
    simp [TwoLevelPayloadLiveStoredWordRankData.queryPos, hlen]
  have hwi : d1.wordIndex pos = d2.wordIndex pos := by
    simp [TwoLevelPayloadLiveStoredWordRankData.wordIndex, hq, hws]
  have hsi : d1.superIndex pos = d2.superIndex pos := by
    simp [TwoLevelPayloadLiveStoredWordRankData.superIndex, hwi, hbps]
  have hwo : d1.wordOffset pos = d2.wordOffset pos := by
    simp [TwoLevelPayloadLiveStoredWordRankData.wordOffset, hq, hwi, hws]
  unfold TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  rw [hsi, hwi, hwo, hc]

/-- Step 2 (MAIN): F1 is size-only.  Two shapes of the same size give the SAME
`TraceResult` — same value and same trace — against EVERY store, at every
segment base and every position. -/
theorem F1_size_only (s1 s2 : CartesianShape) (hsize : s1.size = s2.size)
    (store : WordRAM.ReadStore) (base pos : Nat) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s1 store base pos
      = concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s2 store base pos := by
  have hlen : s1.bpCode.length = s2.bpCode.length := by
    rw [CartesianShape.bpCode_length, CartesianShape.bpCode_length, hsize]
  unfold concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  exact
    bpChunkedRank_congr
      (builtRelativeSplitBPCloseRankData s1)
      (builtRelativeSplitBPCloseRankData s2)
      hlen
      (by rw [builtData_wordSize, builtData_wordSize, hlen])
      (by rw [builtData_blocksPerSuper, builtData_blocksPerSuper, hlen])
      store base (base + 1) (base + 2) (base + 4) _ _ (by rw [hlen]) false pos

/-- Step 3: consequently the ordered probe list of F1 is size-only too. -/
theorem F1_reads_size_only (s1 s2 : CartesianShape) (hsize : s1.size = s2.size)
    (store : WordRAM.ReadStore) (base pos : Nat) :
    (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        s1 store base pos).trace
      = (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        s2 store base pos).trace := by
  rw [F1_size_only s1 s2 hsize store base pos]

#print axioms F1_size_only
#print axioms F1_reads_size_only

end F03F1Thm
