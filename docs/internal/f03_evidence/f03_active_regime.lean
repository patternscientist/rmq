import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 cross-shape determinism IN THE ACTIVE REGIME.

Regime map (from f03_regimes.lean, run at commit d09bed7):
  `canonicalBPRelativeMinMaxArgSummaryTableActive` is FALSE for every size up to
  384 and TRUE at 512; `canonicalBPRelativeSummaryBlockSize` is 0 below the
  threshold and 20 at n=512. So EVERY cross-shape query experiment run below the
  threshold exercises only the degenerate arm, and cannot speak for the summary /
  interior machinery at all.

This file therefore runs the cross-shape determinism test at sizes ABOVE the
threshold, which is where the evidence has to come from.

Hypothesis under test (the candidate F03 universal consumer):
  for all shapeA shapeB store left right,
    shapeA.size = shapeB.size ->
      wholeQueryTraceWithStore shapeA store left right
        = wholeQueryTraceWithStore shapeB store left right
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose

namespace F03Active

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty

def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (balanced (n / 2)) (balanced (n - n / 2))

partial def pseudo (seed : Nat) : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      .node (pseudo (seed + 7) k) (pseudo (seed + 13) (n - k))

def addrStore (salt : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 24).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def run (shape : CartesianShape) (store : WordRAM.ReadStore) (l r : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    shape store l r

def compareAt (n : Nat) (tag : String) (store : WordRAM.ReadStore)
    (l r : Nat) : IO (Nat × Nat) := do
  let named : List (String × CartesianShape) :=
    [ ("leftSpine", leftSpine n)
    , ("rightSpine", rightSpine n)
    , ("balanced", balanced n)
    , ("pseudo1", pseudo 1 n) ]
  let (bn, b) := named.head!
  let br := run b store l r
  let active : Bool := decide (canonicalBPRelativeMinMaxArgSummaryTableActive b)
  IO.println s!"  [n={n} {tag} l={l} r={r}] summaryTableActive={active} base={bn} traceLen={br.trace.length} value={br.value}"
  let mut c := 0
  let mut d := 0
  for (nm, s) in named.tail! do
    c := c + 1
    let x := run s store l r
    if x.trace != br.trace || x.value != br.value then
      d := d + 1
      IO.println s!"    *** DIVERGENCE vs {nm}: traceLen={x.trace.length} value={x.value}"
      let z := (br.trace.zip x.trace).findIdx? (fun p => p.1 != p.2)
      IO.println s!"        firstDifferingIndex={z}"
      match z with
      | some i =>
          IO.println s!"        base[{i}]={repr (br.trace[i]?)}"
          IO.println s!"        this[{i}]={repr (x.trace[i]?)}"
      | none => IO.println s!"        (agree on common prefix, lengths differ)"
    else
      IO.println s!"    ok {nm}: identical trace ({x.trace.length} events) and value"
  return (c, d)

#eval show IO Unit from do
  let mut c := 0
  let mut d := 0
  -- 384 is the last INACTIVE size, 512 and 640 are ACTIVE. Control + treatment.
  for n in [384, 512, 640] do
    for (tag, st) in [("addr5", addrStore 5), ("flat1", flatStore (List.replicate 24 true))] do
      for (l, r) in [(0, n), (n / 4, 3 * n / 4)] do
        let (c', d') <- compareAt n tag st l r
        c := c + c'
        d := d + d'
  IO.println s!"F03-ACTIVE-REGIME TOTAL comparisons={c} divergences={d}"

end F03Active
