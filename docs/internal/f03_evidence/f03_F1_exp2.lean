import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! F03 / F1 executed cross-shape experiment (linear in #shapes). -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctRank

namespace F03F1Exp2

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def hashStore : WordRAM.ReadStore where
  readWord? := fun seg i =>
    some ((List.range 16).map (fun k => (seg * 7 + i * 13 + k * 5) % 3 == 0))

def word0 : List Bool := [true, false, true, false, true, false, true, false]

def F1 (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    WordRAM.TraceResult Nat :=
  concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape store base pos

def F1reads (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    List (Nat × Nat) :=
  (F1 shape store base pos).trace.filterMap fun e =>
    match e with
    | WordRAM.TraceEvent.readWord s i _ => some (s, i)
    | _ => none

def knobs (shape : CartesianShape) (pos : Nat) : Nat × Nat × Nat × Nat × Nat × Nat :=
  let d := builtRelativeSplitBPCloseRankData shape
  (d.wordSize, d.blocksPerSuper, d.queryPos pos, d.superIndex pos, d.wordIndex pos,
    d.wordOffset pos)

def posList : List Nat := [0, 1, 2, 3, 5, 7, 11, 100]

/-- Per-shape signature: value+trace at every (base,pos) tested. -/
def sig (s : CartesianShape) (store : WordRAM.ReadStore) :
    List (Nat × List WordRAM.TraceEvent) :=
  ([0, 6] : List Nat).flatMap fun base =>
    posList.map fun p => let r := F1 s store base p; (r.value, r.trace)

-- EXPERIMENT A: geometry knobs constant across same-size shapes
#eval show IO Unit from do
  for n in [1, 2, 3, 4, 5] do
    let shapes := shapesOfSize n
    let b := shapes.headD CartesianShape.empty
    let baseKs := posList.map (knobs b)
    let mut differ := 0
    for s in shapes do
      if posList.map (knobs s) != baseKs then differ := differ + 1
    IO.println s!"KNOBS n={n} shapes={shapes.length} bpLen={b.bpCode.length} differ={differ} sample={baseKs.take 3}"

-- EXPERIMENT B: F1's own value+trace constant across same-size shapes
#eval show IO Unit from do
  for st in [(0, flatStore word0), (1, flatStore []), (2, hashStore)] do
    let (sid, store) := st
    for n in [1, 2, 3, 4, 5] do
      let shapes := shapesOfSize n
      let b := shapes.headD CartesianShape.empty
      let bsig := sig b store
      let mut differ := 0
      for s in shapes do
        if sig s store != bsig then differ := differ + 1
      IO.println s!"CROSSSHAPE store={sid} n={n} shapes={shapes.length} shapesDifferingFromShape0={differ} sigLen={bsig.length}"

-- EXPERIMENT C: exhibit actual probe lists (distinct bpCodes, same size)
#eval show IO Unit from do
  let shapes := shapesOfSize 5
  let store := hashStore
  for s in shapes.take 4 do
    let r := F1 s store 6 7
    IO.println s!"bp={s.bpCode}"
    IO.println s!"   reads={F1reads s store 6 7} value={r.value} steps={r.trace.length}"

-- EXPERIMENT D (anti-vacuity): the probe list DOES move with n
#eval show IO Unit from do
  let store := hashStore
  for n in [1, 2, 3, 4, 5, 6, 9, 17, 40] do
    let s := (shapesOfSize n).headD CartesianShape.empty
    IO.println s!"SIZEDEP n={n} bpLen={s.bpCode.length} knobs={knobs s 7} reads={F1reads s store 6 7}"

end F03F1Exp2
