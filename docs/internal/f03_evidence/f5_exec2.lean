import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctSpace

namespace F5Exec2

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | n + 1 =>
    (List.range (n + 1)).flatMap fun l =>
      (shapesOfSize l).flatMap fun L =>
        (shapesOfSize (n - l)).map fun R => CartesianShape.node L R

def fixedStore : FlatWordStore := fun a =>
  some ((List.range 8).map fun i => (a + i) % 3 == 0)

def offTuple (s : CartesianShape) : List Nat :=
  let o := canonicalRelativeRmmInteriorComponentOffsets s
  [o.baseline, o.minRel, o.maxRel, o.argOffset, o.localOffset,
   o.globalBlock, o.localLevel, o.globalLevel, o.deadAddress]

def entryLists (s : CartesianShape) : List (List Nat) :=
  let L := RelativeRmm.canonicalLayout s
  [ bpSuperblockBaselineEntries s L.blockSize L.blocksPerSuper L.superSampleCount
  , bpBlockRelativeMinExcessEntries s L.blockSize L.blocksPerSuper L.blockCount
  , bpBlockRelativeMaxExcessEntries s L.blockSize L.blocksPerSuper L.blockCount
  , bpBlockArgMinLocalOffsetEntries s L.blockSize L.blockCount
  , bpLocalSparseOffsetEntries s L.blockSize L.blockCount L.macroSize
      L.macroSampleCount L.levelCount
  , bpGlobalSparseBlockEntries s L.blockSize L.blockCount L.macroSize
      L.macroSampleCount L.globalLevelCount ]

def allEq {a : Type} [BEq a] : List a -> Bool
  | [] => true
  | x :: xs => xs.all (fun y => y == x)

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/f5_exec2_out.txt"

def line (n : Nat) : String := Id.run do
  let ss := shapesOfSize n
  let offs := ss.map offTuple
  let els := ss.map entryLists
  let lens := els.map (fun ls => ls.map List.length)
  let sum0 := ss.map (fun s =>
    let e := (canonicalRelativeRmmMachineSummaryComputation s 0).run fixedStore
    (e.footprint, e.value))
  let sum1 := ss.map (fun s =>
    let e := (canonicalRelativeRmmMachineSummaryComputation s 1).run fixedStore
    (e.footprint, e.value))
  let rm := ss.map (fun s =>
    let e := (canonicalRelativeRmmInteriorRangeMinComputation s 0 n).run fixedStore
    (e.footprint, e.value))
  let rm2 := ss.map (fun s =>
    let e := (canonicalRelativeRmmInteriorRangeMinComputation s 1 (n/2+1)).run fixedStore
    (e.footprint, e.value))
  return s!"n={n} shapes={ss.length} " ++
    s!"offsetsConst={allEq offs} entryLensConst={allEq lens} " ++
    s!"ENTRY_CONTENTS_ALL_EQUAL={allEq els} " ++
    s!"summaryFootprintConst={allEq (sum0.map Prod.fst) && allEq (sum1.map Prod.fst)} " ++
    s!"summaryValueConst={allEq (sum0.map Prod.snd) && allEq (sum1.map Prod.snd)} " ++
    s!"rangeMinFootprintConst={allEq (rm.map Prod.fst) && allEq (rm2.map Prod.fst)} " ++
    s!"rangeMinValueConst={allEq (rm.map Prod.snd) && allEq (rm2.map Prod.snd)} " ++
    s!"| sampleOffsets={(offs.head?).getD []} sampleLens={(lens.head?).getD []} " ++
    s!"sampleEntries0={((els.head?).getD []).head?} " ++
    s!"lastEntries0={((els.getLast?).getD []).head?}"

run_cmd do
  let mut acc : Array String := #[]
  for n in [2,3,4,5,6,7] do
    let l := line n
    acc := acc.push l
    IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)
    Lean.logInfo m!"{l}"

end F5Exec2
