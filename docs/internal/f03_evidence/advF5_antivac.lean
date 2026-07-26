import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
ANTI-VACUITY for the F5 adversarial cross-shape runs.

A "no divergence" result is worthless if the executions never reach the region
built from `bpExcessAt`.  This file reports, for the real store and for the two
synthetic shape-free stores:
  * the segment histogram of the top-level ordered read footprint,
  * whether SEGMENT 20 (canonicalRelativeRmmInteriorComponentStore -- the flat
    region whose contents are produced by bpExcessAt) is actually probed,
  * whether the top-level output is a genuine `some k` that varies with the
    endpoints (rather than a uniform `none` short-circuit).
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctClose

namespace AdvF5AV

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | n + 1 =>
    (List.range (n + 1)).flatMap fun l =>
      (shapesOfSize l).flatMap fun L =>
        (shapesOfSize (n - l)).map fun R => CartesianShape.node L R

def constStore : WordRAM.ReadStore where
  readWord? := fun _ _ => some ((List.range 8).map fun i => i % 2 == 0)

def prngStore : WordRAM.ReadStore where
  readWord? := fun s i =>
    some ((List.range 12).map fun k => (7 * s + 13 * i + 5 * k + 3) % 3 == 0)

def realStore (s : CartesianShape) : WordRAM.ReadStore :=
  BPNavigation.concreteBPCloseNavigationGlobalReadStore s

def fp (st : WordRAM.ReadStore) (sh : CartesianShape) (l r : Nat) :
    List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore sh st l r

def outv (st : WordRAM.ReadStore) (sh : CartesianShape) (l r : Nat) :
    Option Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    sh st l r).value

def segs (f : List (Nat × Nat)) : List (Nat × Nat) :=
  let ss := (f.map Prod.fst).eraseDups.mergeSort (· <= ·)
  ss.map fun s => (s, (f.filter (fun p => p.1 == s)).length)

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advF5_antivac_out.txt"

def touches20 (l : List (List (Nat × Nat))) : Nat :=
  (l.filter (fun h => (h.map Prod.fst).contains 20)).length

def report (n : Nat) : String := Id.run do
  let ss := shapesOfSize n
  let sh := ss.headD .empty
  let sh2 := ss.getLast?.getD .empty
  let pairs := (List.range (n + 1)).flatMap fun l =>
    (List.range (n + 1)).filterMap fun r => if l < r then some (l, r) else none
  let outsReal := pairs.map fun p => outv (realStore sh) sh p.1 p.2
  let outsReal2 := pairs.map fun p => outv (realStore sh2) sh2 p.1 p.2
  let outsConst := pairs.map fun p => outv constStore sh p.1 p.2
  let outsPrng := pairs.map fun p => outv prngStore sh p.1 p.2
  let segReal := pairs.map fun p => segs (fp (realStore sh) sh p.1 p.2)
  let segConst := pairs.map fun p => segs (fp constStore sh p.1 p.2)
  let segPrng := pairs.map fun p => segs (fp prngStore sh p.1 p.2)
  let msg :=
    s!"n={n} shapes={ss.length} pairs={pairs.length}\n" ++
    s!"  REAL   outs={outsReal} distinct={outsReal.eraseDups.length} noneCount={(outsReal.filter (· == none)).length} seg20Runs={touches20 segReal}\n" ++
    s!"  REAL2  outs={outsReal2} distinct={outsReal2.eraseDups.length}\n" ++
    s!"  CONST  outs={outsConst} distinct={outsConst.eraseDups.length} seg20Runs={touches20 segConst}\n" ++
    s!"  PRNG   outs={outsPrng} distinct={outsPrng.eraseDups.length} seg20Runs={touches20 segPrng}\n" ++
    s!"  segHistREAL[0]={segReal.headD []} segHistCONST[0]={segConst.headD []} segHistPRNG[0]={segPrng.headD []}\n" ++
    s!"  segHistREAL[last]={segReal.getLast?.getD []} segHistCONST[last]={segConst.getLast?.getD []}"
  return msg

run_cmd do
  let mut acc : Array String := #[]
  for n in [3, 5, 6] do
    let l := AdvF5AV.report n
    acc := acc.push l
    IO.FS.writeFile AdvF5AV.outPath (String.intercalate "\n\n" acc.toList)
    Lean.logInfo m!"{l}"

end AdvF5AV
