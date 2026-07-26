import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 decisive experiment, scaled.

Closure hypothesis: the whole-query transcript and value are functions of
`(n, left, right, probe replies)` alone. Under one FIXED store the replies are
identical across shapes, so the hypothesis predicts identical transcripts and
identical values for every shape of the same size. Any differing pair is a
witness that semantic shape is a live input beyond the allowed set.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace F03Cross2

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

/-- A shape-free but address-sensitive store: contents depend only on the
    segment and index, never on any shape. -/
def addrStore (salt : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 16).map fun b => ((seg * 31 + idx * 7 + salt) >>> b) % 2 == 1)

def emptyStore : WordRAM.ReadStore where
  readWord? := fun _ _ => none

def footprint (shape : CartesianShape) (store : WordRAM.ReadStore)
    (l r : Nat) : List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
    shape store l r

def fullTrace (shape : CartesianShape) (store : WordRAM.ReadStore)
    (l r : Nat) : List WordRAM.TraceEvent :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    shape store l r).trace

def outValue (shape : CartesianShape) (store : WordRAM.ReadStore)
    (l r : Nat) : Option Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    shape store l r).value

structure Disagreement where
  n : Nat
  storeTag : String
  l : Nat
  r : Nat
  aIdx : Nat
  bIdx : Nat
  kind : String
deriving Repr

/-- Compare every shape of size `n` against the first one, for one store and
    one endpoint pair. Reports transcript and value disagreements. -/
def sweepOne (n : Nat) (storeTag : String) (store : WordRAM.ReadStore)
    (l r : Nat) : IO (Nat × Nat × Nat) := do
  let shapes := shapesOfSize n
  match shapes with
  | [] => return (0, 0, 0)
  | base :: _ =>
    let baseTrace := fullTrace base store l r
    let baseVal := outValue base store l r
    let mut traceDiff := 0
    let mut valDiff := 0
    let mut i := 0
    for s in shapes do
      let t := fullTrace s store l r
      let v := outValue s store l r
      if t != baseTrace then
        traceDiff := traceDiff + 1
        if traceDiff <= 2 then
          IO.println s!"  !! TRACE DIFFER n={n} store={storeTag} l={l} r={r} idx={i}"
          IO.println s!"     base.bp={base.bpCode}"
          IO.println s!"     this.bp={s.bpCode}"
          IO.println s!"     baseLen={baseTrace.length} thisLen={t.length}"
      if v != baseVal then
        valDiff := valDiff + 1
        if valDiff <= 2 then
          IO.println s!"  !! VALUE DIFFER n={n} store={storeTag} l={l} r={r} idx={i} base={baseVal} this={v}"
          IO.println s!"     base.bp={base.bpCode}"
          IO.println s!"     this.bp={s.bpCode}"
      i := i + 1
    return (shapes.length, traceDiff, valDiff)

#eval show IO Unit from do
  let stores : List (String × WordRAM.ReadStore) :=
    [ ("flat0", flatStore (List.replicate 16 false))
    , ("flat1", flatStore (List.replicate 16 true))
    , ("alt",   flatStore ((List.range 16).map fun b => b % 2 == 0))
    , ("addr7", addrStore 7)
    , ("addr0", addrStore 0)
    , ("none",  emptyStore)
    ]
  let mut grandTrace := 0
  let mut grandVal := 0
  let mut grandCmp := 0
  for n in [1, 2, 3, 4, 5, 6] do
    for st in stores do
      for l in List.range (n + 1) do
        for r in List.range (n + 2) do
          let (cnt, td, vd) <- sweepOne n st.1 st.2 l r
          grandCmp := grandCmp + cnt
          grandTrace := grandTrace + td
          grandVal := grandVal + vd
    IO.println s!"== through n={n}: comparisons={grandCmp} traceDiff={grandTrace} valueDiff={grandVal}"
  IO.println s!"TOTAL comparisons={grandCmp} traceDisagreements={grandTrace} valueDisagreements={grandVal}"

end F03Cross2
