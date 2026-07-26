import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
DECISIVE F5 TEST: cross-shape determinism IN THE REGIME WHERE SEGMENT 20 IS LIVE.

advF5_seg20b_out.txt shows the top-level controller does NOT touch segment 20
(canonicalRelativeRmmInteriorComponentStore -- the region whose contents are
produced by bpExcessAt) for n <= 8, and DOES touch it (18 reads/query) from
n = 10 upward.  Every previously-run top-level cross-shape experiment was at
n <= 7, i.e. entirely outside the region under audit.

Here: fix ONE anchor shape A, build the REAL store from A, and run the public
controller on other shapes B of the SAME SIZE against A's store.  Under the
claimed closure over (n, left, right, prior probes) the transcripts and outputs
must be identical.  Divergence = the free `shape` argument is a live input.

Reported per row: number of (B, endpoints) runs, count of footprint divergences,
count of value divergences, the seg-20 read count (anti-vacuity), and the first
witness if any.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctClose

namespace AdvF5Live

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
  [leftComb n, rightComb n, zig true n, zig false n] ++ rs

def fpv (st : WordRAM.ReadStore) (sh : CartesianShape) (l r : Nat) :
    List (Nat × Nat) × Option Nat :=
  let res :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore sh st l r
  (res.trace.filterMap (fun e =>
     match e with
     | WordRAM.TraceEvent.readWord seg idx _ => some (seg, idx)
     | _ => none), res.value)

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advF5_live_out.txt"

def row (n : Nat) : String := Id.run do
  let a := balanced n
  let st := BPNavigation.concreteBPCloseNavigationGlobalReadStore a
  let bs := (family n).filter (fun s => s.size == n && s != a)
  let pairs := [(0, n), (1, n - 1), (n / 4, 3 * n / 4)]
  let mut runs := 0
  let mut fpDiff := 0
  let mut valDiff := 0
  let mut seg20 := 0
  let mut witness := ""
  let mut anchorVals : List (Option Nat) := []
  for p in pairs do
    let (f0, v0) := fpv st a p.1 p.2
    seg20 := seg20 + (f0.filter (fun q => q.1 == 20)).length
    anchorVals := anchorVals ++ [v0]
    for b in bs do
      runs := runs + 1
      let (f, v) := fpv st b p.1 p.2
      if f != f0 then
        fpDiff := fpDiff + 1
        if witness == "" then
          witness := s!"FPDIFF l={p.1} r={p.2} A={a.bpCode} B={b.bpCode} lenA={f0.length} lenB={f.length} firstIdx={(f0.zip f).findIdx? (fun q => q.1 != q.2)}"
      if v != v0 then
        valDiff := valDiff + 1
        if witness == "" then
          witness := s!"VALDIFF l={p.1} r={p.2} A={a.bpCode} B={b.bpCode} vA={v0} vB={v}"
  let distinctBs := bs.eraseDups.length
  let msg :=
    s!"n={n} anchorSeg20Reads={seg20} comparandShapes={bs.length} distinct={distinctBs} " ++
    s!"runs={runs} FPDIFF={fpDiff} VALDIFF={valDiff} anchorVals={anchorVals} " ++
    s!"witness=<{witness}>"
  return msg

run_cmd do
  let mut acc : Array String := #[]
  for n in [10, 12, 14, 16, 20] do
    let l := AdvF5Live.row n
    acc := acc.push l
    IO.FS.writeFile AdvF5Live.outPath (String.intercalate "\n" acc.toList)
    Lean.logInfo m!"{l}"

end AdvF5Live
