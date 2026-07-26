import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL stage 8: the divisor slots the other agent named but only
*tagged* ("stride", "localStride", "superStride", "macroCount", "macroSize",
"wordSize") -- pin each one to a Nat-only mirror of `shape.size` by a CHECKED
theorem, so the S verdict on them does not rest on a syntactic slice.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.SuccinctSelect
open RMQ.SuccinctRank

namespace AdvSZStrides

/-! Nat-only mirrors: no `CartesianShape` occurs anywhere below. -/
def wordBitsN (n : Nat) : Nat := machineWordBits (2 * n)
def ellN (n : Nat) : Nat := Nat.log2 (wordBitsN n) + 1
def superStrideN (n : Nat) : Nat := wordBitsN n * wordBitsN n
def localStrideN (n : Nat) : Nat := max 1 (wordBitsN n / (ellN n * ellN n))
def superLongSpanN (n : Nat) : Nat := superStrideN n * wordBitsN n * ellN n

theorem wordBits_eq (s : CartesianShape) :
    sparseDenseFalseSelectWordBits s = wordBitsN s.size := by
  unfold sparseDenseFalseSelectWordBits wordBitsN
  rw [CartesianShape.bpCode_length]

theorem ell_eq (s : CartesianShape) :
    sparseDenseFalseSelectEll s = ellN s.size := by
  unfold sparseDenseFalseSelectEll ellN
  rw [wordBits_eq]

theorem superStride_eq (s : CartesianShape) :
    sparseDenseFalseSelectSuperStride s = superStrideN s.size := by
  unfold sparseDenseFalseSelectSuperStride superStrideN
  rw [wordBits_eq]

theorem localStride_eq (s : CartesianShape) :
    sparseDenseFalseSelectLocalStride s = localStrideN s.size := by
  unfold sparseDenseFalseSelectLocalStride localStrideN
  rw [wordBits_eq, ell_eq]

theorem superLongSpan_eq (s : CartesianShape) :
    sparseDenseFalseSelectSuperLongSpan s = superLongSpanN s.size := by
  unfold sparseDenseFalseSelectSuperLongSpan superLongSpanN
  rw [superStride_eq, wordBits_eq, ell_eq]

/-- Hence every one of them is constant on a size class. -/
theorem superStride_congr {a b : CartesianShape} (h : a.size = b.size) :
    sparseDenseFalseSelectSuperStride a = sparseDenseFalseSelectSuperStride b := by
  rw [superStride_eq, superStride_eq, h]

theorem localStride_congr {a b : CartesianShape} (h : a.size = b.size) :
    sparseDenseFalseSelectLocalStride a = sparseDenseFalseSelectLocalStride b := by
  rw [localStride_eq, localStride_eq, h]

theorem superLongSpan_congr {a b : CartesianShape} (h : a.size = b.size) :
    sparseDenseFalseSelectSuperLongSpan a =
      sparseDenseFalseSelectSuperLongSpan b := by
  rw [superLongSpan_eq, superLongSpan_eq, h]

/-! The interior macro divisors. -/

def baseN (n : Nat) : Nat := Nat.log2 n + 1
def macroSizeN (n : Nat) : Nat := baseN n * baseN n

theorem macroSize_eq (s : CartesianShape) :
    concreteBPRelativeRmmInteriorMacroSize s = macroSizeN s.size := rfl

theorem macroSize_congr {a b : CartesianShape} (h : a.size = b.size) :
    concreteBPRelativeRmmInteriorMacroSize a =
      concreteBPRelativeRmmInteriorMacroSize b := by
  rw [macroSize_eq, macroSize_eq, h]

/-- Nat-only mirror of the whole activity predicate. -/
def blockSizeRawN (n : Nat) : Nat := 2 * baseN n
def blocksPerSuperRawN (n : Nat) : Nat := baseN n
def blockCountRawN (n : Nat) : Nat := n / baseN n
def superCountRawN (n : Nat) : Nat := blockCountRawN n / blocksPerSuperRawN n + 1
def relativeWidthRawN (n : Nat) : Nat := 2 * (Nat.log2 (baseN n) + 1) + 3

def activeN (n : Nat) : Prop :=
  blockCountRawN n * blockSizeRawN n <= 2 * n /\
    2 * bpSuperblockSpan (blockSizeRawN n) (blocksPerSuperRawN n) <
        2 ^ relativeWidthRawN n /\
    blockSizeRawN n < 2 ^ relativeWidthRawN n /\
    superCountRawN n * machineWordBits (2 * n) <=
      SuccinctSpace.sampledDirectoryOverhead
        canonicalBPRelativeSummarySuperSlots n /\
    3 * (blockCountRawN n * relativeWidthRawN n) <=
      SuccinctSpace.logLogSampledDirectoryOverhead
        canonicalBPRelativeSummaryBlockSlots n /\
    relativeWidthRawN n <= machineWordBits (2 * n)

theorem active_iff (s : CartesianShape) :
    canonicalBPRelativeMinMaxArgSummaryTableActive s <-> activeN s.size := by
  unfold canonicalBPRelativeMinMaxArgSummaryTableActive activeN
  unfold canonicalBPRelativeSummaryBlockSizeRaw
    canonicalBPRelativeSummaryBlocksPerSuperRaw
    canonicalBPRelativeSummaryBlockCountRaw
    canonicalBPRelativeSummarySuperCountRaw
    canonicalBPRelativeSummarySuperWidth
    canonicalBPRelativeSummaryRelativeWidthRaw
    canonicalBPRelativeSummaryBase
  simp only [superCountRawN, blockSizeRawN, blocksPerSuperRawN, blockCountRawN,
    relativeWidthRawN, baseN]
  rw [CartesianShape.bpCode_length]
  exact Iff.rfl

theorem blockCount_congr {a b : CartesianShape} (h : a.size = b.size) :
    canonicalBPRelativeSummaryBlockCount a =
      canonicalBPRelativeSummaryBlockCount b := by
  unfold canonicalBPRelativeSummaryBlockCount
  by_cases hact : canonicalBPRelativeMinMaxArgSummaryTableActive a
  · have hb : canonicalBPRelativeMinMaxArgSummaryTableActive b := by
      rw [active_iff, ← h, ← active_iff]; exact hact
    rw [if_pos hact, if_pos hb]
    unfold canonicalBPRelativeSummaryBlockCountRaw canonicalBPRelativeSummaryBase
    rw [h]
  · have hb : ¬ canonicalBPRelativeMinMaxArgSummaryTableActive b := by
      intro hcon; exact hact (by rw [active_iff, h, ← active_iff]; exact hcon)
    rw [if_neg hact, if_neg hb]

theorem macroCount_congr {a b : CartesianShape} (h : a.size = b.size) :
    concreteBPRelativeRmmInteriorMacroCount a =
      concreteBPRelativeRmmInteriorMacroCount b := by
  unfold concreteBPRelativeRmmInteriorMacroCount
  rw [blockCount_congr h, macroSize_congr h]

#print axioms wordBits_eq
#print axioms ell_eq
#print axioms superStride_eq
#print axioms localStride_eq
#print axioms superLongSpan_eq
#print axioms superStride_congr
#print axioms localStride_congr
#print axioms superLongSpan_congr
#print axioms macroSize_congr
#print axioms active_iff
#print axioms blockCount_congr
#print axioms macroCount_congr

end AdvSZStrides
