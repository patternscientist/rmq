import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL verification of the other agent's S-verdict theorems: restate them
here independently and print axioms.  A "CHECKED by rfl" claim that silently
rests on `sorryAx`, or whose statement is about a DIFFERENT constant than the
controller uses, would collapse the S verdict.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.SuccinctRank

namespace AdvSZAx

def baseN (n : Nat) : Nat := Nat.log2 n + 1
def blockCountRawN (n : Nat) : Nat := n / baseN n

theorem base_eq (s : CartesianShape) :
    canonicalBPRelativeSummaryBase s = baseN s.size := rfl

theorem blockCountRaw_eq (s : CartesianShape) :
    canonicalBPRelativeSummaryBlockCountRaw s = blockCountRawN s.size := rfl

/-- The decisive size-only step everywhere else leans on. -/
theorem code_len (s : CartesianShape) : s.bpCode.length = 2 * s.size :=
  CartesianShape.bpCode_length s

theorem superWidth_eq (s : CartesianShape) :
    canonicalBPRelativeSummarySuperWidth s = machineWordBits (2 * s.size) := by
  unfold canonicalBPRelativeSummarySuperWidth
  rw [code_len]

theorem rankWordSize_eq (s : CartesianShape) :
    builtRelativeSplitBPCloseRankWordSize s = machineWordBits (2 * s.size) := by
  unfold builtRelativeSplitBPCloseRankWordSize
  rw [code_len]

theorem dataWordSize_eq (s : CartesianShape) :
    (builtRelativeSplitBPCloseRankData s).wordSize = machineWordBits (2 * s.size) := by
  show builtRelativeSplitBPCloseRankWordSize s = _
  exact rankWordSize_eq s

theorem queryPos_eq (s : CartesianShape) (pos : Nat) :
    (builtRelativeSplitBPCloseRankData s).queryPos pos =
      Nat.min pos (2 * s.size) := by
  unfold TwoLevelPayloadLiveStoredWordRankData.queryPos
  rw [code_len]

/-- Size-congruence, the form the F03 rubric actually needs. -/
theorem base_congr {a b : CartesianShape} (h : a.size = b.size) :
    canonicalBPRelativeSummaryBase a = canonicalBPRelativeSummaryBase b := by
  rw [base_eq, base_eq, h]

theorem wordIndex_congr {a b : CartesianShape} (h : a.size = b.size) (pos : Nat) :
    (builtRelativeSplitBPCloseRankData a).wordIndex pos =
      (builtRelativeSplitBPCloseRankData b).wordIndex pos := by
  unfold TwoLevelPayloadLiveStoredWordRankData.wordIndex
  rw [queryPos_eq, queryPos_eq, dataWordSize_eq, dataWordSize_eq, h]

theorem active_congr {a b : CartesianShape} (h : a.size = b.size) :
    canonicalBPRelativeMinMaxArgSummaryTableActive a <->
      canonicalBPRelativeMinMaxArgSummaryTableActive b := by
  unfold canonicalBPRelativeMinMaxArgSummaryTableActive
  unfold canonicalBPRelativeSummaryBlockSizeRaw
    canonicalBPRelativeSummaryBlocksPerSuperRaw
    canonicalBPRelativeSummaryBlockCountRaw
    canonicalBPRelativeSummarySuperCountRaw
    canonicalBPRelativeSummarySuperWidth
    canonicalBPRelativeSummaryRelativeWidthRaw
    canonicalBPRelativeSummaryBase
  rw [code_len, code_len, h]

#print axioms base_eq
#print axioms blockCountRaw_eq
#print axioms code_len
#print axioms superWidth_eq
#print axioms rankWordSize_eq
#print axioms dataWordSize_eq
#print axioms queryPos_eq
#print axioms base_congr
#print axioms wordIndex_congr
#print axioms active_congr
#print axioms CartesianShape.bpCode_length

end AdvSZAx
