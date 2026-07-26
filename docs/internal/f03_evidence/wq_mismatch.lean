import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 TIER C -- THE MISMATCHED REAL-STORE EXPERIMENT.

Tier A/B fix a SYNTHETIC shape-free store.  A sceptic can object that a
synthetic store might send the controller down a short-circuit path that never
exercises the content-reading machinery, making cross-shape agreement vacuous.
Tier C removes that objection by using the route's OWN store,
`BPNavigation.concreteBPCloseNavigationGlobalReadStore C`
(RMQ/Core/BPNavigationRAM.lean:816), built from a third shape C.

Two measurements, run together:

(1) ANTI-VACUITY / liveness.  `wq A (real A) l r` vs `wq B (real B) l r`.
    These SHOULD differ: they are genuinely different RMQ instances.  If they
    never differ, the whole experiment is vacuous and nothing may be concluded.

(2) THE CLOSURE TEST.  `wq A (real C) l r` vs `wq B (real C) l r`
    for A, B, C all of the same size.  H predicts identical traces and values:
    the semantic `shape` argument is dead weight once the store is fixed.

(1) and (2) together say: shape reaches the controller ONLY through probe
replies -- classification P, not X.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctClose

namespace WQMismatch

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

def zigzag : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => if n % 2 == 0 then .node (zigzag n) .empty else .node .empty (zigzag n)

def cliff (n k : Nat) : CartesianShape :=
  if n == 0 then .empty
  else .node (leftSpine (min k (n - 1))) (rightSpine (n - 1 - min k (n - 1)))

partial def pseudo (seed : Nat) : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      .node (pseudo (seed + 7) k) (pseudo (seed + 13) (n - k))

def fams (n : Nat) : List (String × CartesianShape) :=
  [ ("leftSpine", leftSpine n), ("rightSpine", rightSpine n)
  , ("balanced", balanced n), ("zigzag", zigzag n)
  , ("cliff/2", cliff n (n / 2)), ("pseudo1", pseudo 1 n)
  , ("pseudo7", pseudo 7 n) ]

def real (s : CartesianShape) : WordRAM.ReadStore :=
  BPNavigation.concreteBPCloseNavigationGlobalReadStore s

def wq (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r

def logPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/wq_mismatch_log.txt"

#eval show IO Unit from do
  let h <- IO.FS.Handle.mk logPath IO.FS.Mode.write
  let say (s : String) : IO Unit := do h.putStrLn s; h.flush; IO.println s
  say "=== TIER C: mismatched REAL store ==="
  -- (1) liveness: do matched real-store runs distinguish shapes at all?
  say "-- (1) LIVENESS: wq A (real A) vs wq B (real B), same size, same endpoints"
  let mut liveCmp := 0
  let mut liveDistinct := 0
  for n in [4, 5, 6, 7, 8, 12, 16, 24, 32, 48, 64] do
    let fs := fams n
    let (bn, b) := fs.head!
    for (l, r) in [(0, n - 1), (0, n), (1, n - 1), (n / 2, n - 1)] do
      let bt := wq b (real b) l r
      for (nm, s) in fs.tail! do
        liveCmp := liveCmp + 1
        let x := wq s (real s) l r
        if x.trace != bt.trace || x.value != bt.value then
          liveDistinct := liveDistinct + 1
    say s!"  n={n} l/r x6 done: liveCmp={liveCmp} distinct={liveDistinct}"
  say s!"LIVENESS TOTAL comparisons={liveCmp} DISTINCT={liveDistinct} (must be > 0, ideally most)"
  -- (2) closure: fix the store to real C, vary the queried shape
  say "-- (2) CLOSURE: wq A (real C) vs wq B (real C), A,B,C all size n"
  let mut cmps := 0
  let mut traceDiff := 0
  let mut valDiff := 0
  for n in [4, 5, 6, 7, 8, 12, 16, 24, 32, 48, 64] do
    let fs := fams n
    for (cn, c) in fs do
      let st := real c
      for (l, r) in [(0, n - 1), (0, n), (1, n - 1), (n / 2, n - 1)] do
        let (bn, b) := fs.head!
        let br := wq b st l r
        for (nm, s) in fs.tail! do
          cmps := cmps + 1
          let x := wq s st l r
          if x.trace != br.trace then
            traceDiff := traceDiff + 1
            say s!"  *** TRACE DIVERGENCE n={n} storeShape={cn} l={l} r={r} base={bn} other={nm}"
            say s!"      lens={br.trace.length} vs {x.trace.length}"
            let z := (br.trace.zip x.trace).findIdx? (fun p => p.1 != p.2)
            say s!"      firstDiffIdx={z}"
            say s!"      base@={repr (z.bind (br.trace[·]?))}"
            say s!"      othr@={repr (z.bind (x.trace[·]?))}"
            say s!"      base.bp={b.bpCode}"
            say s!"      othr.bp={s.bpCode}"
            say s!"      store.bp={c.bpCode}"
          if x.value != br.value then
            valDiff := valDiff + 1
            say s!"  *** VALUE DIVERGENCE n={n} storeShape={cn} l={l} r={r} base={bn}({br.value}) other={nm}({x.value})"
            say s!"      base.bp={b.bpCode}"
            say s!"      othr.bp={s.bpCode}"
            say s!"      store.bp={c.bpCode}"
    say s!"  n={n} done: cmps={cmps} traceDiff={traceDiff} valDiff={valDiff}"
  say s!"CLOSURE TOTAL comparisons={cmps} traceDisagreements={traceDiff} valueDisagreements={valDiff}"
  h.flush

end WQMismatch
