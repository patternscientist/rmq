import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
ADVERSARIAL QUANTIFIER PROBE ON F5 (bpExcessAt / verdict P).

Question: what regime does the executed cross-shape evidence actually quantify over?

The interior range-min dispatch (InteriorDirectory.lean:2444-2468) has FOUR arms.
Arms 3 and 4 are the ONLY callers of
`canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation`
(InteriorDirectory.lean:2423, :2437), which is the ONLY caller of
`canonicalRelativeRmmMachineGlobalSpanCandidateComputation` (:2393, :2396),
which is the ONLY query-side consumer of `bpGlobalSparseBlockEntries`
and of `canonicalRelativeRmmInteriorGlobalLevelTable`.

The real query supplies (startBlock, count) = (leftBlock+1, rightBlock-leftBlock-1)
with leftBlock = blockOfClose blockSize leftClose,
     rightBlock = blockOfClose blockSize rightClose
(ChargedFringeTrace.lean:1163-1166), and only when leftBlock + 1 < rightBlock.

So: enumerate ALL realizable (leftClose, rightClose) block pairs and see which
arms can ever fire, as a function of n.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctSpace

namespace AdvQF5

/-- Size-only replica of the canonical layout. -/
def layoutOfSize (n : Nat) : RelativeRmm.Layout where
  blockSize := 2 * (Nat.log2 n + 1)
  blocksPerSuper := Nat.log2 n + 1
  blockCount := n / (Nat.log2 n + 1)
  relativeWidth := 2 * (Nat.log2 (Nat.log2 n + 1) + 1) + 3

/-- CHECKED: the canonical layout really is a function of `shape.size` alone. -/
theorem layout_size_only (s : CartesianShape) :
    RelativeRmm.canonicalLayout s = layoutOfSize s.size := rfl

/-- Replica of the four-arm dispatch at InteriorDirectory.lean:2444-2468.
0 = count = 0 (pure none), 1 = LocalTwoSpan, 2 = AdjacentMacro,
3 = LeftMiddleMacro (GLOBAL), 4 = CrossMacro (GLOBAL). -/
def arm (L : RelativeRmm.Layout) (startBlock count : Nat) : Nat :=
  let macroSize := L.macroSize
  let localStart := startBlock % macroSize
  if count = 0 then 0
  else if count <= macroSize - localStart then 1
  else
    let leftCount := macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize
    if middleMacroCount = 0 then 2
    else if rightCount = 0 then 3
    else 4

/-- Highest BP block index a real close position can land in: bpCode has
`2 * n` positions, so close <= 2*n-1 and block <= (2*n-1)/blockSize. -/
def maxBlock (n : Nat) : Nat :=
  if n = 0 then 0 else (2 * n - 1) / (layoutOfSize n).blockSize

/-- All arms reachable by a REALIZABLE query at size n. -/
def armsAt (n : Nat) : List Nat := Id.run do
  let L := layoutOfSize n
  let mb := maxBlock n
  let mut seen : List Nat := []
  for lb in [0:mb+1] do
    for rb in [0:mb+1] do
      if lb + 1 < rb then
        let a := arm L (lb + 1) (rb - lb - 1)
        if !seen.contains a then seen := a :: seen
  return seen.mergeSort (fun a b => a <= b)

def row (n : Nat) : String :=
  let L := layoutOfSize n
  s!"n={n} base={Nat.log2 n + 1} blockSize={L.blockSize} blockCount={L.blockCount} " ++
  s!"macroSize={L.macroSize} macroSampleCount={L.macroSampleCount} " ++
  s!"levelCount={L.levelCount} globalLevelCount={L.globalLevelCount} " ++
  s!"maxBlock={maxBlock n} REALIZABLE_ARMS={armsAt n}"

def firstWith (p : Nat -> Bool) (lo hi : Nat) : Option Nat := Id.run do
  for k in [lo:hi] do
    if p k then return some k
  return none

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advQ_f5_regime_out.txt"

run_cmd do
  let mut acc : Array String := #[]
  acc := acc.push "== EVIDENCE-BASE SIZES (all sizes ever executed by the F5 constancy tests) =="
  for n in [2,3,4,5,6,7,8,12,16,24,32,48] do
    acc := acc.push (row n)
  acc := acc.push "== SIZES THE EVIDENCE NEVER REACHED =="
  for n in [64,100,128,256,512,1000,1024,1342,1343,2048,3455,3456,4096,8192] do
    acc := acc.push (row n)
  -- thresholds, using only the size-only layout arithmetic
  let hasArm (a : Nat) (n : Nat) : Bool := (armsAt n).contains a
  acc := acc.push "== THRESHOLDS (minimal n at which each arm is realizable) =="
  acc := acc.push s!"min n with macroSampleCount >= 2 : {firstWith (fun n => 2 <= (layoutOfSize n).macroSampleCount) 1 5000}"
  acc := acc.push s!"min n with blockCount > macroSize : {firstWith (fun n => (layoutOfSize n).macroSize < (layoutOfSize n).blockCount) 1 5000}"
  acc := acc.push s!"min n with arm 2 (AdjacentMacro) realizable : {firstWith (hasArm 2) 1 4000}"
  acc := acc.push s!"min n with arm 3 (LeftMiddleMacro, GLOBAL tables) realizable : {firstWith (hasArm 3) 1 4000}"
  acc := acc.push s!"min n with arm 4 (CrossMacro, GLOBAL tables) realizable : {firstWith (hasArm 4) 1 4000}"
  IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)
  for l in acc do Lean.logInfo m!"{l}"

end AdvQF5
