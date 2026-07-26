import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
ADVERSARIAL F5 ATTACK #3: cross-shape with a REAL (well-formed) store.

Attack #1 used a synthetic constant/prng store.  Objection: the controller may
bail out early on garbage words, so a null result there could be vacuous.

Here the store is the genuine `concreteBPCloseNavigationGlobalReadStore shapeA`
built from ONE shape A.  It is shape-free relative to any other shape B of the
same size.  We run the public controller on B against A's store and compare the
ordered read footprint (and output value) with the run on A itself.

Under the claimed closure over (n, left, right, prior probes), the two runs must
produce byte-identical transcripts.  Any divergence is a direct witness that the
free `shape` argument feeds an address/branch.

Anti-vacuity is measured in the same run: segment histogram of the footprint,
and in particular whether segment 20 (canonicalRelativeRmmInteriorComponentStore
-- the region built from bpExcessAt) is actually probed.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctClose

namespace AdvF5Real

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | n + 1 =>
    (List.range (n + 1)).flatMap fun l =>
      (shapesOfSize l).flatMap fun L =>
        (shapesOfSize (n - l)).map fun R => CartesianShape.node L R

def realStore (s : CartesianShape) : WordRAM.ReadStore :=
  BPNavigation.concreteBPCloseNavigationGlobalReadStore s

def fp (st : WordRAM.ReadStore) (sh : CartesianShape) (l r : Nat) :
    List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore sh st l r

def outv (st : WordRAM.ReadStore) (sh : CartesianShape) (l r : Nat) :
    Option Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    sh st l r).value

def segHist (f : List (Nat × Nat)) : List (Nat × Nat) :=
  let segs := (f.map Prod.fst).eraseDups.mergeSort (· <= ·)
  segs.map fun s => (s, (f.filter (fun p => p.1 == s)).length)

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advF5_realstore_out.txt"

/-- For each anchor shape A, compare all same-size B against A under A's store. -/
def scan (n : Nat) : String := Id.run do
  let ss := shapesOfSize n
  let mut fpDiff := 0
  let mut valDiff := 0
  let mut runs := 0
  let mut witness := ""
  let mut seg20Runs := 0
  let mut maxLen := 0
  let mut hist0 : List (Nat × Nat) := []
  for a in ss do
    let st := realStore a
    for l in List.range (n + 1) do
      for r in List.range (n + 1) do
        if l < r then
          let f0 := fp st a l r
          let v0 := outv st a l r
          if f0.length > maxLen then maxLen := f0.length
          if hist0 == [] then hist0 := segHist f0
          if (f0.map Prod.fst).contains 20 then seg20Runs := seg20Runs + 1
          for b in ss do
            runs := runs + 1
            let f := fp st b l r
            let v := outv st b l r
            if f != f0 then
              fpDiff := fpDiff + 1
              if witness == "" then
                witness := s!"FPDIFF l={l} r={r} A={a.bpCode} B={b.bpCode} lenA={f0.length} lenB={f.length} fpA={f0} fpB={f}"
            if v != v0 then
              valDiff := valDiff + 1
              if witness == "" then
                witness := s!"VALDIFF l={l} r={r} A={a.bpCode} B={b.bpCode} vA={v0} vB={v}"
  return s!"n={n} shapes={ss.length} runs={runs} FPDIFF={fpDiff} VALDIFF={valDiff} " ++
    s!"anchorRunsTouchingSeg20={seg20Runs} maxFootprintLen={maxLen} " ++
    s!"sampleSegHist={hist0} witness=<{witness}>"

run_cmd do
  let mut acc : Array String := #[]
  for n in [2, 3, 4, 5] do
    let l := AdvF5Real.scan n
    acc := acc.push l
    IO.FS.writeFile AdvF5Real.outPath (String.intercalate "\n\n" acc.toList)
    Lean.logInfo m!"{l}"

end AdvF5Real
