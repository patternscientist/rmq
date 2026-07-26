import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
ADVERSARIAL F5 ATTACK #2: RANDOM same-size shape sample at large n.

The prior defence used FIVE hand-picked shapes (combs / balanced / two zigzags)
for n >= 8.  Hand-picked families can systematically miss a leak.  Here we draw
a deterministic pseudo-random sample of same-size shapes (100 per size) at
n = 16, 33, 64, 100, 129 and compare every address-relevant structural value:

  * the full 9-field component-offset record (every table base + deadAddress),
  * the machine word counts of each of the EIGHT component stores,
  * the six content-bearing entry-list LENGTHS,
  * the whole canonical layout record,
  * executed footprints AND values of the summary and interior range-min
    computations under one FIXED shape-free store, over probe arguments that
    themselves come from the layout.

Anti-vacuity is reported in the same row (distinct entry-content vectors).
-/

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctSpace

namespace AdvF5Rand

/-- xorshift-ish deterministic generator. -/
def nxt (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

/-- Random shape with exactly `n` internal nodes.  `fuel` bounds the recursion
    structurally so this is a total definition. -/
def randShape : Nat -> Nat -> Nat -> Nat × CartesianShape
  | 0, seed, _ => (seed, .empty)
  | _ + 1, seed, 0 => (seed, .empty)
  | fuel + 1, seed, m + 1 =>
    let s1 := nxt seed
    let k := s1 % (m + 1)
    let (s2, L) := randShape fuel s1 k
    let (s3, R) := randShape fuel s2 (m - k)
    (s3, .node L R)

def sample (seed n count : Nat) : List CartesianShape := Id.run do
  let mut s := seed
  let mut acc : List CartesianShape := []
  for _ in List.range count do
    let (s', sh) := randShape (n + 2) s n
    s := nxt s'
    acc := sh :: acc
  return acc

def offTuple (s : CartesianShape) : List Nat :=
  let o := canonicalRelativeRmmInteriorComponentOffsets s
  [o.baseline, o.minRel, o.maxRel, o.argOffset, o.localOffset,
   o.globalBlock, o.localLevel, o.globalLevel, o.deadAddress]

def wordCounts (s : CartesianShape) : List Nat :=
  let hword := SuccinctRank.machineWordBits_pos s.bpCode.length
  let sum := canonicalRelativeRmmSummaryTable s
  [ (sum.baselineTable.machineStore hword).store.words.size
  , (sum.minRelTable.machineStore hword).store.words.size
  , (sum.maxRelTable.machineStore hword).store.words.size
  , (sum.argOffsetTable.machineStore hword).store.words.size
  , (canonicalRelativeRmmLocalMachineStore s).store.words.size
  , (canonicalRelativeRmmGlobalMachineStore s).store.words.size
  , (canonicalRelativeRmmLocalLevelMachineStore s).store.words.size
  , (canonicalRelativeRmmInteriorComponentStore s).store.words.size ]

def layoutTuple (s : CartesianShape) : List Nat :=
  let L := RelativeRmm.canonicalLayout s
  [L.blockSize, L.blocksPerSuper, L.blockCount, L.relativeWidth,
   L.superSampleCount, L.superWidth s, L.macroSize, L.macroSampleCount,
   L.offsetWidth, L.levelCount, L.globalLevelCount, L.blockAddressWidth]

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

def fixedStore : FlatWordStore := fun a =>
  some ((List.range 8).map fun i => (a * 5 + i * 3 + 1) % 4 == 0)

def allEq {a : Type} [BEq a] : List a -> Bool
  | [] => true
  | x :: xs => xs.all (fun y => y == x)

/-- index of first element differing from the head, if any -/
def firstDiff {a : Type} [BEq a] (l : List a) : Option Nat :=
  match l with
  | [] => none
  | x :: xs => (xs.findIdx? (fun y => !(y == x))).map (· + 1)

def line (n cnt : Nat) : String := Id.run do
  let ss := sample (n * 7919 + 17) n cnt
  let sizes := (ss.map CartesianShape.size).eraseDups
  let offs := ss.map offTuple
  let wcs := ss.map wordCounts
  let lays := ss.map layoutTuple
  let els := ss.map entryLists
  let lens := els.map (fun ls => ls.map List.length)
  let L := RelativeRmm.canonicalLayout (ss.headD .empty)
  let probes := [(0, L.blockCount), (0, 1), (1, 2), (0, L.macroSize + 1),
                 (L.macroSize / 2, L.macroSize + 2), (L.blockCount / 2, 3)]
  let fps := probes.map fun p =>
    ss.map fun s =>
      let e := (canonicalRelativeRmmInteriorRangeMinComputation s p.1 p.2).run
        fixedStore
      (e.footprint, e.value)
  let sums := (List.range 6).map fun b =>
    ss.map fun s =>
      let e := (canonicalRelativeRmmMachineSummaryComputation s b).run fixedStore
      (e.footprint, e.value)
  let distinctEntryVectors := els.eraseDups.length
  return s!"n={n} sample={ss.length} sizesSeen={sizes} distinctShapes={ss.eraseDups.length} " ++
    s!"layoutConst={allEq lays} offsetsConst={allEq offs} wordCountsConst={allEq wcs} " ++
    s!"entryLensConst={allEq lens} " ++
    s!"rangeMinFpConst={fps.all (fun r => allEq (r.map Prod.fst))} " ++
    s!"rangeMinValConst={fps.all (fun r => allEq (r.map Prod.snd))} " ++
    s!"summaryFpConst={sums.all (fun r => allEq (r.map Prod.fst))} " ++
    s!"summaryValConst={sums.all (fun r => allEq (r.map Prod.snd))} " ++
    s!"|| ANTIVAC_distinctEntryVectors={distinctEntryVectors} " ++
    s!"firstDiffOffsets={firstDiff offs} firstDiffWordCounts={firstDiff wcs} " ++
    s!"layout={lays.headD []} offsets={offs.headD []} wordCounts={wcs.headD []}"

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advF5_rand_out.txt"

run_cmd do
  let mut acc : Array String := #[]
  for p in [(9, 30), (11, 30), (16, 25), (23, 15), (33, 12), (64, 8)] do
    let l := AdvF5Rand.line p.1 p.2
    acc := acc.push l
    IO.FS.writeFile AdvF5Rand.outPath (String.intercalate "\n\n" acc.toList)
    Lean.logInfo m!"{l}"

end AdvF5Rand
