import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-! ANTI-VACUITY for advF5_live: do the comparand shapes at n = 10..20 actually
have DIFFERENT bpExcessAt-derived table contents?  If they did not, FPDIFF=0
would be trivial.  Also reports whether the store words of segment 20 differ. -/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctClose

namespace AdvF5LiveAV

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | n + 1 => .node (balanced (n / 2)) (balanced (n - n / 2))

def leftComb : Nat -> CartesianShape
  | 0 => .empty
  | n + 1 => .node (leftComb n) .empty

def rightComb : Nat -> CartesianShape
  | 0 => .empty
  | n + 1 => .node .empty (rightComb n)

partial def zig (flip : Bool) : Nat -> CartesianShape
  | 0 => .empty
  | n + 1 =>
      if flip then .node (zig (not flip) n) .empty
      else .node (balanced (n / 3)) (zig (not flip) (n - n / 3))

def nxt (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def randShape : Nat -> Nat -> Nat -> Nat × CartesianShape
  | 0, seed, _ => (seed, .empty)
  | _ + 1, seed, 0 => (seed, .empty)
  | fuel + 1, seed, m + 1 =>
    let s1 := nxt seed
    let k := s1 % (m + 1)
    let (s2, L) := randShape fuel s1 k
    let (s3, R) := randShape fuel s2 (m - k)
    (s3, .node L R)

def family (n : Nat) : List CartesianShape :=
  let rs := (List.range 6).map fun i => (randShape (n + 2) (i * 7919 + 11) n).2
  ([balanced n, leftComb n, rightComb n, zig true n, zig false n] ++ rs).filter
    (fun s => s.size == n)

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

def offTuple (s : CartesianShape) : List Nat :=
  let o := canonicalRelativeRmmInteriorComponentOffsets s
  [o.baseline, o.minRel, o.maxRel, o.argOffset, o.localOffset,
   o.globalBlock, o.localLevel, o.globalLevel, o.deadAddress]

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advF5_live_av_out.txt"

def row (n : Nat) : String := Id.run do
  let ss := family n
  let els := ss.map entryLists
  let offs := ss.map offTuple
  let lens := els.map (fun l => l.map List.length)
  let seg20 := ss.map fun s =>
    (canonicalRelativeRmmInteriorComponentStore s).store.words.toList
  let msg :=
    s!"n={n} shapes={ss.length} distinctShapes={ss.eraseDups.length} " ++
    s!"DISTINCT_ENTRY_VECTORS={els.eraseDups.length} " ++
    s!"DISTINCT_SEG20_WORDS={seg20.eraseDups.length} " ++
    s!"seg20WordCount={(seg20.map List.length).eraseDups} " ++
    s!"distinctOffsetTuples={offs.eraseDups.length} distinctEntryLenTuples={lens.eraseDups.length} " ++
    s!"offsets={offs.headD []} entryLens={lens.headD []}"
  return msg

run_cmd do
  let mut acc : Array String := #[]
  for n in [10, 12, 14, 16, 20] do
    let l := AdvF5LiveAV.row n
    acc := acc.push l
    IO.FS.writeFile AdvF5LiveAV.outPath (String.intercalate "\n" acc.toList)
    Lean.logInfo m!"{l}"

end AdvF5LiveAV
