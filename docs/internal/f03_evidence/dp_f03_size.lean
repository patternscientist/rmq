import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
DP-F03 (a): the two `CartesianShape.size` users, and the table-activity
predicate / blockSize branch that the roadmap flags.

Everything below is stated as a CHECKED theorem: each canonical geometry
quantity is shown EQUAL to a Nat-only mirror applied to `shape.size`, so it
factors through `n` and is verdict S.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctSpace

namespace DPF03Size

/-! ## Nat-only mirrors (no `CartesianShape` anywhere) -/

def baseN (n : Nat) : Nat := Nat.log2 n + 1
def blockSizeRawN (n : Nat) : Nat := 2 * baseN n
def blocksPerSuperRawN (n : Nat) : Nat := baseN n
def blockCountRawN (n : Nat) : Nat := n / baseN n
def superCountRawN (n : Nat) : Nat := blockCountRawN n / blocksPerSuperRawN n + 1
def superWidthN (n : Nat) : Nat := SuccinctRank.machineWordBits (2 * n)
def relativeWidthRawN (n : Nat) : Nat := 2 * (Nat.log2 (baseN n) + 1) + 3

def activeN (n : Nat) : Prop :=
  blockCountRawN n * blockSizeRawN n <= 2 * n /\
    2 * bpSuperblockSpan (blockSizeRawN n) (blocksPerSuperRawN n) <
        2 ^ relativeWidthRawN n /\
    blockSizeRawN n < 2 ^ relativeWidthRawN n /\
    superCountRawN n * superWidthN n <=
      sampledDirectoryOverhead canonicalBPRelativeSummarySuperSlots n /\
    3 * (blockCountRawN n * relativeWidthRawN n) <=
      logLogSampledDirectoryOverhead canonicalBPRelativeSummaryBlockSlots n /\
    relativeWidthRawN n <= SuccinctRank.machineWordBits (2 * n)

instance activeN_decidable (n : Nat) : Decidable (activeN n) := by
  unfold activeN
  infer_instance

/-! ## (a) the two `size` users are definitionally size-only -/

theorem base_eq (s : CartesianShape) :
    canonicalBPRelativeSummaryBase s = baseN s.size := rfl

theorem blockCountRaw_eq (s : CartesianShape) :
    canonicalBPRelativeSummaryBlockCountRaw s = blockCountRawN s.size := rfl

/-! ## the rest of the canonical geometry, for completeness -/

theorem blockSizeRaw_eq (s : CartesianShape) :
    canonicalBPRelativeSummaryBlockSizeRaw s = blockSizeRawN s.size := rfl

theorem blocksPerSuperRaw_eq (s : CartesianShape) :
    canonicalBPRelativeSummaryBlocksPerSuperRaw s = blocksPerSuperRawN s.size := rfl

theorem superCountRaw_eq (s : CartesianShape) :
    canonicalBPRelativeSummarySuperCountRaw s = superCountRawN s.size := rfl

theorem relativeWidthRaw_eq (s : CartesianShape) :
    canonicalBPRelativeSummaryRelativeWidthRaw s = relativeWidthRawN s.size := rfl

theorem superWidth_eq (s : CartesianShape) :
    canonicalBPRelativeSummarySuperWidth s = superWidthN s.size := by
  unfold canonicalBPRelativeSummarySuperWidth superWidthN
  rw [CartesianShape.bpCode_length]

/-! ## (b) the table-activity predicate factors through `size` -/

theorem active_iff (s : CartesianShape) :
    canonicalBPRelativeMinMaxArgSummaryTableActive s <-> activeN s.size := by
  unfold canonicalBPRelativeMinMaxArgSummaryTableActive activeN
  rw [blockSizeRaw_eq, blocksPerSuperRaw_eq, blockCountRaw_eq,
    superCountRaw_eq, superWidth_eq, relativeWidthRaw_eq,
    CartesianShape.bpCode_length]

/-! ## size-congruence: same `n` forces the same geometry and the same branch -/

theorem base_congr {a b : CartesianShape} (h : a.size = b.size) :
    canonicalBPRelativeSummaryBase a = canonicalBPRelativeSummaryBase b := by
  rw [base_eq, base_eq, h]

theorem blockCountRaw_congr {a b : CartesianShape} (h : a.size = b.size) :
    canonicalBPRelativeSummaryBlockCountRaw a =
      canonicalBPRelativeSummaryBlockCountRaw b := by
  rw [blockCountRaw_eq, blockCountRaw_eq, h]

theorem active_congr {a b : CartesianShape} (h : a.size = b.size) :
    canonicalBPRelativeMinMaxArgSummaryTableActive a <->
      canonicalBPRelativeMinMaxArgSummaryTableActive b := by
  rw [active_iff, active_iff, h]

/-! ### the five `ite`-guarded geometry functions, each equal to a Nat-only mirror -/

def blockSizeN (n : Nat) : Nat := if activeN n then blockSizeRawN n else 0
def blocksPerSuperN (n : Nat) : Nat := if activeN n then blocksPerSuperRawN n else 1
def blockCountN (n : Nat) : Nat := if activeN n then blockCountRawN n else 0
def superCountN (n : Nat) : Nat := if activeN n then superCountRawN n else 0
def relativeWidthN (n : Nat) : Nat := if activeN n then relativeWidthRawN n else 0

theorem blockSize_eq (s : CartesianShape) :
    canonicalBPRelativeSummaryBlockSize s = blockSizeN s.size := by
  unfold canonicalBPRelativeSummaryBlockSize blockSizeN
  by_cases hact : canonicalBPRelativeMinMaxArgSummaryTableActive s
  · rw [if_pos hact, if_pos ((active_iff s).mp hact), blockSizeRaw_eq]
  · rw [if_neg hact, if_neg (fun h => hact ((active_iff s).mpr h))]

theorem blocksPerSuper_eq (s : CartesianShape) :
    canonicalBPRelativeSummaryBlocksPerSuper s = blocksPerSuperN s.size := by
  unfold canonicalBPRelativeSummaryBlocksPerSuper blocksPerSuperN
  by_cases hact : canonicalBPRelativeMinMaxArgSummaryTableActive s
  · rw [if_pos hact, if_pos ((active_iff s).mp hact), blocksPerSuperRaw_eq]
  · rw [if_neg hact, if_neg (fun h => hact ((active_iff s).mpr h))]

theorem blockCount_eq (s : CartesianShape) :
    canonicalBPRelativeSummaryBlockCount s = blockCountN s.size := by
  unfold canonicalBPRelativeSummaryBlockCount blockCountN
  by_cases hact : canonicalBPRelativeMinMaxArgSummaryTableActive s
  · rw [if_pos hact, if_pos ((active_iff s).mp hact), blockCountRaw_eq]
  · rw [if_neg hact, if_neg (fun h => hact ((active_iff s).mpr h))]

theorem superCount_eq (s : CartesianShape) :
    canonicalBPRelativeSummarySuperCount s = superCountN s.size := by
  unfold canonicalBPRelativeSummarySuperCount superCountN
  by_cases hact : canonicalBPRelativeMinMaxArgSummaryTableActive s
  · rw [if_pos hact, if_pos ((active_iff s).mp hact), superCountRaw_eq]
  · rw [if_neg hact, if_neg (fun h => hact ((active_iff s).mpr h))]

theorem relativeWidth_eq (s : CartesianShape) :
    canonicalBPRelativeSummaryRelativeWidth s = relativeWidthN s.size := by
  unfold canonicalBPRelativeSummaryRelativeWidth relativeWidthN
  by_cases hact : canonicalBPRelativeMinMaxArgSummaryTableActive s
  · rw [if_pos hact, if_pos ((active_iff s).mp hact), relativeWidthRaw_eq]
  · rw [if_neg hact, if_neg (fun h => hact ((active_iff s).mpr h))]

theorem blockSize_congr {a b : CartesianShape} (h : a.size = b.size) :
    canonicalBPRelativeSummaryBlockSize a =
      canonicalBPRelativeSummaryBlockSize b := by
  rw [blockSize_eq, blockSize_eq, h]

/-! ### the sibling guard predicate used by the same cost/space branch -/

def macroSizeN (n : Nat) : Nat := baseN n * baseN n

def readyN (n : Nat) : Prop := activeN n /\ macroSizeN n <= blockCountN n

instance readyN_decidable (n : Nat) : Decidable (readyN n) := by
  unfold readyN; infer_instance

theorem macroSize_eq (s : CartesianShape) :
    concreteBPRelativeRmmInteriorMacroSize s = macroSizeN s.size := rfl

theorem ready_iff (s : CartesianShape) :
    concreteBPRelativeRmmInteriorReady s <-> readyN s.size := by
  unfold concreteBPRelativeRmmInteriorReady readyN
  rw [active_iff, macroSize_eq, blockCount_eq]

theorem ready_congr {a b : CartesianShape} (h : a.size = b.size) :
    concreteBPRelativeRmmInteriorReady a <->
      concreteBPRelativeRmmInteriorReady b := by
  rw [ready_iff, ready_iff, h]

/-! ## executed witness: the exact width function w(n) -/

#eval show IO Unit from do
  IO.println "n | base=log2 n+1 | blockSize | blocksPerSuper | blockCount | superCount | superWidth | relWidth | ACTIVE"
  for n in [0,1,2,3,4,5,6,7,8,15,16,17,31,32,63,64,100,127,128,255,256,1000,1024,4096,65536] do
    IO.println s!"{n} | {baseN n} | {blockSizeRawN n} | {blocksPerSuperRawN n} | {blockCountRawN n} | {superCountRawN n} | {superWidthN n} | {relativeWidthRawN n} | {decide (activeN n)}"

-- Where does the table-activity branch actually flip?
#eval show IO Unit from do
  let mut firstTrue : Option Nat := none
  let mut flips : Array Nat := #[]
  let mut prev : Bool := false
  for n in List.range 4097 do
    let a := decide (activeN n)
    if a && firstTrue.isNone then firstTrue := some n
    if n > 0 && a != prev then flips := flips.push n
    prev := a
  IO.println s!"ACTIVE first true at n = {firstTrue}"
  IO.println s!"ACTIVE flip points in [0,4096] = {flips.toList}"
  let mut falseAbove : Array Nat := #[]
  for n in List.range 4097 do
    if n >= 600 && !(decide (activeN n)) then falseAbove := falseAbove.push n
  IO.println s!"n in [600,4096] with ACTIVE=false: count={falseAbove.size} first={falseAbove.toList.take 20}"

end DPF03Size
