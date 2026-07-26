import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F5 large-n stress: shapes of the SAME size with maximally different BP excess
profiles (left comb / right comb / balanced / two zigzags).  If the executed
addresses were content-dependent these would diverge.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctSpace

namespace F5Big

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

/-- zig: alternate which side gets the big subtree. -/
partial def zig (flip : Bool) : Nat -> CartesianShape
  | 0 => .empty
  | n + 1 =>
      if flip then .node (zig (not flip) n) .empty
      else .node (balanced (n / 3)) (zig (not flip) (n - n / 3))

def family (n : Nat) : List CartesianShape :=
  [leftComb n, rightComb n, balanced n, zig true n, zig false n]

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

def line (n : Nat) : String := Id.run do
  let ss := family n
  let sizes := ss.map CartesianShape.size
  let offs := ss.map offTuple
  let els := ss.map entryLists
  let lens := els.map (fun ls => ls.map List.length)
  -- executed footprints and values over several (startBlock, count) pairs
  let L := RelativeRmm.canonicalLayout (ss.headD .empty)
  let probes := [(0, L.blockCount), (0, 1), (1, 2), (0, L.macroSize + 1),
                 (L.macroSize / 2, L.macroSize + 2)]
  let fps := probes.map fun p =>
    ss.map fun s =>
      let e := (canonicalRelativeRmmInteriorRangeMinComputation s p.1 p.2).run
        fixedStore
      (e.footprint, e.value)
  let sums := (List.range 4).map fun b =>
    ss.map fun s =>
      let e := (canonicalRelativeRmmMachineSummaryComputation s b).run fixedStore
      (e.footprint, e.value)
  return s!"n={n} sizes={sizes} bpLen={(ss.headD .empty).bpCode.length} " ++
    s!"blockSize={L.blockSize} blocksPerSuper={L.blocksPerSuper} blockCount={L.blockCount} macroSize={L.macroSize} | " ++
    s!"offsetsConst={allEq offs} entryLensConst={allEq lens} " ++
    s!"ENTRY_CONTENTS_ALL_EQUAL={allEq els} " ++
    s!"rangeMinFootprintConst={fps.all (fun r => allEq (r.map Prod.fst))} " ++
    s!"rangeMinValueConst={fps.all (fun r => allEq (r.map Prod.snd))} " ++
    s!"summaryFootprintConst={sums.all (fun r => allEq (r.map Prod.fst))} " ++
    s!"summaryValueConst={sums.all (fun r => allEq (r.map Prod.snd))} " ++
    s!"|| distinctBaselineEntries={(els.map (fun l => l.headD [])).eraseDups.length}" ++
    s!" distinctMinRelEntries={(els.map (fun l => (l.drop 1).headD [])).eraseDups.length}" ++
    s!" offsets={offs.headD []}"

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/f5_big_out.txt"

run_cmd do
  let mut acc : Array String := #[]
  for n in [8, 12, 16, 24, 32, 48, 64, 100] do
    let l := line n
    acc := acc.push l
    IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)
    Lean.logInfo m!"{l}"

end F5Big
