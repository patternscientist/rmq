import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
ADVERSARIAL F5 PROBE, PART 2b (focused).

Force interior arms 2/3/4 with SYNTHETIC (non-realizable) counts at the
smallest sizes, and ask: do the never-executed arms touch the GLOBAL sparse
block region at all, and do footprints/values still agree across maximally
divergent same-size shapes?
-/

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctSpace

namespace AdvQF

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

def arm (L : RelativeRmm.Layout) (startBlock count : Nat) : Nat :=
  let macroSize := L.macroSize
  let localStart := startBlock % macroSize
  if count = 0 then 0
  else if count <= macroSize - localStart then 1
  else
    let leftCount := macroSize - localStart
    let remaining := count - leftCount
    if remaining / macroSize = 0 then 2
    else if remaining % macroSize = 0 then 3
    else 4

def probeRow (n : Nat) (sb cnt : Nat) : String :=
  let ss := family n
  let s0 := ss.headD .empty
  let L := RelativeRmm.canonicalLayout s0
  let runs := ss.map fun s =>
    let e := (canonicalRelativeRmmInteriorRangeMinComputation s sb cnt).run fixedStore
    (e.footprint, e.value)
  let fps := runs.map Prod.fst
  s!"  n={n} macroSize={L.macroSize} macroSampleCount={L.macroSampleCount} " ++
  s!"globalLevelCount={L.globalLevelCount} globalLevelDomain={bpSparseLevelDomain L.macroSampleCount} " ++
  s!"arm={arm L sb cnt} (sb={sb},count={cnt}) reads={(fps.headD []).length} " ++
  s!"footprintConst={allEq fps} valueConst={allEq (runs.map Prod.snd)} " ++
  s!"regions={regions s0 (fps.headD [])} fp={fps.headD []}"

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advQ_f5_forced_out.txt"

run_cmd do
  let mut acc : Array String := #[]
  for n in [12, 16] do
    let L := RelativeRmm.canonicalLayout ((family n).headD .empty)
    let m := L.macroSize
    -- arm 2, arm 3 (rightCount = 0), arm 4 (rightCount > 0)
    let probes : List (Nat × Nat) :=
      [(0, m + 1), (0, 2 * m), (0, 2 * m + 3), (0, 3 * m), (1, m - 1 + 2 * m + 4)]
    for p in probes do
      let l := probeRow n p.1 p.2
      acc := acc.push l
      IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)
      Lean.logInfo m!"{l}"
  IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)

end AdvQF
