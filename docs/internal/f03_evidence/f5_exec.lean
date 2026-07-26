import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F5 executed experiment.

For every CartesianShape of a given size n (exhaustive enumeration), with ONE
fixed shape-free store, compare:
  (1) `canonicalRelativeRmmInteriorComponentOffsets shape` (all 9 address fields)
  (2) the lengths of the four summary `entries` lists and the two sparse ones
  (3) the CONTENTS of those entries lists  (anti-vacuity: must differ)
  (4) the executed footprint (address list) and value of
      `canonicalRelativeRmmMachineSummaryComputation shape block`
      and `canonicalRelativeRmmInteriorRangeMinComputation`-adjacent leaves.

Claim under test: every address the controller executes factors through n,
while the values it obtains vary with the shape ONLY through the store.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctSpace

namespace F5Exec

/-- All Cartesian shapes with exactly `n` nodes. -/
partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | n + 1 =>
    (List.range (n + 1)).flatMap fun l =>
      (shapesOfSize l).flatMap fun L =>
        (shapesOfSize (n - l)).map fun R => CartesianShape.node L R

/-- A fixed store that mentions no shape at all. -/
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

/-- Executed footprint+value of the summary read for one block. -/
def summaryRun (s : CartesianShape) (block : Nat) :
    List Nat × Option (Nat × Nat × Nat × Nat) :=
  let e := (canonicalRelativeRmmMachineSummaryComputation s block).run fixedStore
  (e.footprint, e.value)

/-- Executed footprint+value of the top interior range-min computation. -/
def rangeMinRun (s : CartesianShape) (a b : Nat) :
    List Nat × Option (Nat × Nat) :=
  let e := (canonicalRelativeRmmInteriorRangeMinComputation s a b).run fixedStore
  (e.footprint, e.value)

structure Report where
  n : Nat
  shapes : Nat
  offsetsConst : Bool
  entryLensConst : Bool
  entryContentsAllEqual : Bool
  summaryFootprintConst : Bool
  summaryValueConst : Bool
  rangeMinFootprintConst : Bool
  rangeMinValueConst : Bool
  sampleOffsets : List Nat
  sampleEntryLens : List Nat
deriving Repr

def allEq {a : Type} [BEq a] : List a -> Bool
  | [] => true
  | x :: xs => xs.all (fun y => y == x)

def report (n : Nat) : Report :=
  let ss := shapesOfSize n
  let offs := ss.map offTuple
  let els := ss.map entryLists
  let lens := els.map (fun ls => ls.map List.length)
  let sums := ss.map (fun s => summaryRun s 0)
  let sums1 := ss.map (fun s => summaryRun s 1)
  let rms := ss.map (fun s => rangeMinRun s 0 n)
  { n := n
    shapes := ss.length
    offsetsConst := allEq offs
    entryLensConst := allEq lens
    entryContentsAllEqual := allEq els
    summaryFootprintConst :=
      allEq (sums.map Prod.fst) && allEq (sums1.map Prod.fst)
    summaryValueConst := allEq (sums.map Prod.snd) && allEq (sums1.map Prod.snd)
    rangeMinFootprintConst := allEq (rms.map Prod.fst)
    rangeMinValueConst := allEq (rms.map Prod.snd)
    sampleOffsets := (offs.head?).getD []
    sampleEntryLens := ((lens.head?).getD []) }

#eval report 3
#eval report 4
#eval report 5
#eval report 6
#eval report 7
#eval report 8

end F5Exec
