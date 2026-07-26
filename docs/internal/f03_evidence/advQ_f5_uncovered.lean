import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
ADVERSARIAL F5 PROBE, PART 4.

Parts 1-2 showed that in EVERY interior range-min run ever executed
(realizable or forced), the only IN-RANGE reads land in the two sparse LEVEL
tables -- whose entries are `bpSparseLevelEntries domain`, content-free.  Reads
aimed at `bpLocalSparseOffsetEntries` (localOffset region) and
`bpGlobalSparseBlockEntries` (GLOBALBLOCK region) -- two of the six
bpExcessAt-derived content lists -- always returned the dead address.

So those two lists have never been exercised at an in-range index.  Test them
DIRECTLY, across maximally divergent same-size shapes.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctSpace

namespace AdvQU

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

/-- Directly exercise the LOCAL sparse offset table (bpLocalSparseOffsetEntries). -/
def localRow (n : Nat) (macroIdx localStart level : Nat) : String :=
  let ss := family n
  let s0 := ss.headD .empty
  let runs := ss.map fun s =>
    let e := (canonicalRelativeRmmMachineLocalSpanCandidateComputation
      s macroIdx localStart level).run fixedStore
    (e.footprint, e.value)
  let fps := runs.map Prod.fst
  s!"  LOCAL n={n} (macroIdx={macroIdx},localStart={localStart},level={level}) " ++
  s!"footprintConst={allEq fps} valueConst={allEq (runs.map Prod.snd)} " ++
  s!"regions={regions s0 (fps.headD [])}"

/-- Directly exercise the GLOBAL sparse block table (bpGlobalSparseBlockEntries). -/
def globalRow (n : Nat) (macroStart level : Nat) : String :=
  let ss := family n
  let s0 := ss.headD .empty
  let runs := ss.map fun s =>
    let e := (canonicalRelativeRmmMachineGlobalSpanCandidateComputation
      s macroStart level).run fixedStore
    (e.footprint, e.value)
  let fps := runs.map Prod.fst
  s!"  GLOBAL n={n} (macroStart={macroStart},level={level}) " ++
  s!"footprintConst={allEq fps} valueConst={allEq (runs.map Prod.snd)} " ++
  s!"regions={regions s0 (fps.headD [])}"

/-- ANTI-VACUITY: do the two lists actually differ between same-size shapes? -/
def contentRow (n : Nat) : String :=
  let ss := family n
  let L := RelativeRmm.canonicalLayout (ss.headD .empty)
  let locals := ss.map fun s =>
    bpLocalSparseOffsetEntries s L.blockSize L.blockCount L.macroSize
      L.macroSampleCount L.levelCount
  let globals := ss.map fun s =>
    bpGlobalSparseBlockEntries s L.blockSize L.blockCount L.macroSize
      L.macroSampleCount L.globalLevelCount
  s!"  CONTENT n={n} localLens={locals.map List.length} globalLens={globals.map List.length} " ++
  s!"distinctLocalEntryVectors={locals.eraseDups.length} " ++
  s!"distinctGlobalEntryVectors={globals.eraseDups.length} " ++
  s!"local0={(locals.headD []).take 12} local1={((locals.drop 1).headD []).take 12}"

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advQ_f5_uncovered_out.txt"

run_cmd do
  let mut acc : Array String := #[]
  for n in [12, 16, 24] do
    let l := contentRow n
    acc := acc.push l
    IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)
    Lean.logInfo m!"{l}"
    for p in [(0,0,0), (0,1,0), (0,0,1), (0,3,2), (0,5,1)] do
      let l := localRow n p.1 p.2.1 p.2.2
      acc := acc.push l
      IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)
      Lean.logInfo m!"{l}"
    for p in [(0,0), (0,1), (1,0)] do
      let l := globalRow n p.1 p.2
      acc := acc.push l
      IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)
      Lean.logInfo m!"{l}"
  IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)

end AdvQU
