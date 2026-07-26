import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
DP-F03 (b) part 6: the two divisor slots the backward slice flagged
X-CANDIDATE, namely

  TwoLevelPayloadLiveStoredWordRankData.wordIndex  = data.queryPos pos / data.wordSize
  TwoLevelPayloadLiveStoredWordRankData.superIndex = data.wordIndex pos / data.blocksPerSuper

instantiated at the controller's rank directory
`builtRelativeSplitBPCloseRankData shape`.  The slice tags the whole record as
content-derived; here we pin the three FIELDS that actually reach the divisor.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctRank

namespace DPF03RankFields

theorem wordSize_eq (shape : CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).wordSize =
      machineWordBits (2 * shape.size) := by
  show builtRelativeSplitBPCloseRankWordSize shape = _
  unfold builtRelativeSplitBPCloseRankWordSize
  rw [CartesianShape.bpCode_length]

theorem blocksPerSuper_eq (shape : CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).blocksPerSuper =
      machineWordBits (2 * shape.size) := by
  show builtRelativeSplitBPCloseRankBlocksPerSuper shape = _
  unfold builtRelativeSplitBPCloseRankBlocksPerSuper
    builtRelativeSplitBPCloseRankWordSize
  rw [CartesianShape.bpCode_length]

theorem queryPos_eq (shape : CartesianShape) (pos : Nat) :
    (builtRelativeSplitBPCloseRankData shape).queryPos pos =
      Nat.min pos (2 * shape.size) := by
  unfold TwoLevelPayloadLiveStoredWordRankData.queryPos
  rw [CartesianShape.bpCode_length]

/-- Hence both flagged divisor slots are size-only. -/
theorem wordIndex_eq (shape : CartesianShape) (pos : Nat) :
    (builtRelativeSplitBPCloseRankData shape).wordIndex pos =
      Nat.min pos (2 * shape.size) / machineWordBits (2 * shape.size) := by
  unfold TwoLevelPayloadLiveStoredWordRankData.wordIndex
  rw [queryPos_eq, wordSize_eq]

theorem superIndex_eq (shape : CartesianShape) (pos : Nat) :
    (builtRelativeSplitBPCloseRankData shape).superIndex pos =
      Nat.min pos (2 * shape.size) / machineWordBits (2 * shape.size) /
        machineWordBits (2 * shape.size) := by
  unfold TwoLevelPayloadLiveStoredWordRankData.superIndex
  rw [wordIndex_eq, blocksPerSuper_eq]

/-- Same-size shapes give the same word index and super index. -/
theorem wordIndex_congr {a b : CartesianShape} (h : a.size = b.size) (pos : Nat) :
    (builtRelativeSplitBPCloseRankData a).wordIndex pos =
      (builtRelativeSplitBPCloseRankData b).wordIndex pos := by
  rw [wordIndex_eq, wordIndex_eq, h]

theorem superIndex_congr {a b : CartesianShape} (h : a.size = b.size) (pos : Nat) :
    (builtRelativeSplitBPCloseRankData a).superIndex pos =
      (builtRelativeSplitBPCloseRankData b).superIndex pos := by
  rw [superIndex_eq, superIndex_eq, h]

end DPF03RankFields
