import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
ADVERSARIAL F5 PROBE, PART 2.

Part 1 (advQ_f5_regime2.lean) showed: at EVERY size the F5 constancy evidence
executed (n <= 48) the only realizable interior arm is arm 1 (LocalTwoSpan);
arms 3/4 -- the sole query-side readers of the GLOBAL sparse block table and
the global level table -- first become realizable at n = 3457.

Part 2 asks the refutation question directly:

  (A) Which component REGIONS did the F5 probes actually touch?
  (B) If we FORCE arms 2/3/4 with synthetic counts at small n, do footprints and
      values still agree across maximally divergent same-size shapes?

Region boundaries come from `canonicalRelativeRmmInteriorComponentOffsets`
(InteriorDirectory.lean:1614-1647).
-/

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctSpace

namespace AdvQG

def leftComb : Nat -> CartesianShape
  | 0 => .empty
  | n + 1 => .node (leftComb n) .empty

def rightComb : Nat -> CartesianShape
  | 0 => .empty
  | n + 1 => .node .empty (rightComb n)

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | n + 1 => .node (balanced (n / 2)) (balanced (n - n / 2))

partial def zig (flip : Bool) : Nat -> CartesianShape
  | 0 => .empty
  | n + 1 =>
      if flip then .node (zig (not flip) n) .empty
      else .node (balanced (n / 3)) (zig (not flip) (n - n / 3))

def family (n : Nat) : List CartesianShape :=
  [leftComb n, rightComb n, balanced n, zig true n, zig false n]

def fixedStore : FlatWordStore := fun a =>
  some ((List.range 8).map fun i => (a + i) % 3 == 0)

/-- Name the component region an address falls into. -/
def regionOf (s : CartesianShape) (a : Nat) : String :=
  let o := canonicalRelativeRmmInteriorComponentOffsets s
  if a >= o.deadAddress then "DEAD"
  else if a >= o.globalLevel then "globalLevel"
  else if a >= o.localLevel then "localLevel"
  else if a >= o.globalBlock then "GLOBALBLOCK"
  else if a >= o.localOffset then "localOffset"
  else if a >= o.argOffset then "argOffset"
  else if a >= o.maxRel then "maxRel"
  else if a >= o.minRel then "minRel"
  else "baseline"

def regions (s : CartesianShape) (fp : List Nat) : List String :=
  (fp.map (regionOf s)).eraseDups.mergeSort (fun a b => a <= b)

def allEq {a : Type} [BEq a] : List a -> Bool
  | [] => true
  | x :: xs => xs.all (fun y => y == x)

/-- Replica of the four-arm dispatch (InteriorDirectory.lean:2444-2468). -/
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
    if middleMacroCount = 0 then 2 else if rightCount = 0 then 3 else 4

def maxBlockOf (n : Nat) (L : RelativeRmm.Layout) : Nat :=
  if n = 0 then 0 else (2 * n - 1) / L.blockSize

/-- Run one (startBlock,count) probe across the whole same-size family. -/
def probeRow (n : Nat) (sb cnt : Nat) : String :=
  let ss := family n
  let s0 := ss.headD .empty
  let L := RelativeRmm.canonicalLayout s0
  let runs := ss.map fun s =>
    let e := (canonicalRelativeRmmInteriorRangeMinComputation s sb cnt).run fixedStore
    (e.footprint, e.value)
  let fps := runs.map Prod.fst
  let vals := runs.map Prod.snd
  s!"  n={n} arm={arm L sb cnt} (sb={sb},count={cnt}) reads={(fps.headD []).length} " ++
  s!"footprintConst={allEq fps} valueConst={allEq vals} " ++
  s!"regions={regions s0 (fps.headD [])}"

/-- Regions touched by the union of ALL realizable probes at size n. -/
def realizableRegions (n : Nat) : String :=
  let ss := family n
  let s0 := ss.headD .empty
  let L := RelativeRmm.canonicalLayout s0
  let mb := maxBlockOf n L
  let pairs := (List.range (mb + 1)).flatMap fun lb =>
    (List.range (mb + 1)).filterMap fun rb =>
      if lb + 1 < rb then some (lb + 1, rb - lb - 1) else none
  let fp := pairs.flatMap fun p =>
    ((canonicalRelativeRmmInteriorRangeMinComputation s0 p.1 p.2).run fixedStore).footprint
  let arms := (pairs.map fun p => arm L p.1 p.2).eraseDups.mergeSort (fun a b => a <= b)
  let allConst := pairs.all fun p =>
    let runs := ss.map fun s =>
      let e := (canonicalRelativeRmmInteriorRangeMinComputation s p.1 p.2).run fixedStore
      (e.footprint, e.value)
    allEq (runs.map Prod.fst) && allEq (runs.map Prod.snd)
  s!"  n={n} realizablePairs={pairs.length} armsSeen={arms} " ++
  s!"ALL_REALIZABLE_CONST={allConst} regionsTouched={regions s0 fp}"

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advQ_f5_global_out.txt"

run_cmd do
  let mut acc : Array String := #[]
  acc := acc.push "== (A) REGIONS TOUCHED BY ALL REALIZABLE QUERIES (exhaustive over block pairs) =="
  for n in [8, 12, 16, 24, 32, 48] do
    let l := realizableRegions n
    acc := acc.push l
    IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)
    Lean.logInfo m!"{l}"
  acc := acc.push "== (B) FORCED ARMS 2/3/4 VIA SYNTHETIC (NON-REALIZABLE) COUNTS =="
  for n in [16, 24, 32, 48] do
    let L := RelativeRmm.canonicalLayout ((family n).headD .empty)
    let m := L.macroSize
    -- arm 2: count just over one macro
    -- arm 3: leftCount + k*macroSize exactly  (rightCount = 0)
    -- arm 4: leftCount + k*macroSize + r      (rightCount = r > 0)
    let probes : List (Nat × Nat) :=
      [(0, m + 1), (0, 2 * m), (0, 2 * m + 3), (0, 3 * m), (0, 3 * m + 5),
       (1, m + 2 * m), (1, m - 1 + 2 * m + 4), (m / 2, 3 * m)]
    for p in probes do
      let l := probeRow n p.1 p.2
      acc := acc.push l
      IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)
      Lean.logInfo m!"{l}"
  IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)

end AdvQG
