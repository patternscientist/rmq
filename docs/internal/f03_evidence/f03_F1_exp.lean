import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 / F1 decisive experiments for
  RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctRank

namespace F03F1Exp

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

/-- Fixed, shape-free store: constant word at every (segment, index). -/
def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

/-- Fixed, shape-free store whose word depends on (segment, index) only. -/
def hashStore : WordRAM.ReadStore where
  readWord? := fun seg i =>
    some ((List.range 16).map (fun k => (seg * 7 + i * 13 + k * 5) % 3 == 0))

def word0 : List Bool := [true, false, true, false, true, false, true, false]

/-- F1 itself. -/
def F1 (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    WordRAM.TraceResult Nat :=
  concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape store base pos

/-- The (segment, index) pairs F1 actually probes, in order. -/
def F1reads (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    List (Nat × Nat) :=
  (F1 shape store base pos).trace.filterMap fun e =>
    match e with
    | WordRAM.TraceEvent.readWord s i _ => some (s, i)
    | _ => none

/-- The geometry knobs F1 consumes from the built data. -/
def knobs (shape : CartesianShape) (pos : Nat) : Nat × Nat × Nat × Nat × Nat × Nat :=
  let d := builtRelativeSplitBPCloseRankData shape
  (d.wordSize, d.blocksPerSuper, d.queryPos pos, d.superIndex pos, d.wordIndex pos,
    d.wordOffset pos)

-- =====================================================================
-- EXPERIMENT 1: knobs are constant across same-size shapes
-- =====================================================================
#eval show IO Unit from do
  for n in [1, 2, 3, 4, 5] do
    let shapes := shapesOfSize n
    let mut ks : List (Nat × Nat × Nat × Nat × Nat × Nat) := []
    for s in shapes do
      for p in [0, 1, 2, 3, 5, 7, 11, 100] do
        ks := ks ++ [knobs s p]
    -- group by shape: compare each shape's knob vector against shape 0's
    let base := shapes.headD CartesianShape.empty
    let baseKs := ([0, 1, 2, 3, 5, 7, 11, 100] : List Nat).map (knobs base)
    let mut differ := 0
    for s in shapes do
      let sKs := ([0, 1, 2, 3, 5, 7, 11, 100] : List Nat).map (knobs s)
      if sKs != baseKs then differ := differ + 1
    IO.println s!"KNOBS n={n} shapes={shapes.length} bpLen={base.bpCode.length} \
knobsDifferFromShape0={differ} sample={baseKs.take 3}"

-- =====================================================================
-- EXPERIMENT 2: F1's own trace + value, fixed store, across same-size shapes
-- =====================================================================
#eval show IO Unit from do
  for st in [(0, flatStore word0), (1, flatStore []), (2, hashStore)] do
    let (sid, store) := st
    for n in [1, 2, 3, 4, 5] do
      let shapes := shapesOfSize n
      let mut differPairs := 0
      let mut total := 0
      let mut readsDiffer := 0
      for a in shapes do
        for b in shapes do
          for base in [0, 6] do
            for p in [0, 1, 2, 3, 5, 7, 11, 100] do
              total := total + 1
              if F1 a store base p != F1 b store base p then
                differPairs := differPairs + 1
              if F1reads a store base p != F1reads b store base p then
                readsDiffer := readsDiffer + 1
      IO.println s!"CROSSSHAPE store={sid} n={n} shapes={shapes.length} \
comparisons={total} traceResultDiffer={differPairs} readsDiffer={readsDiffer}"

-- =====================================================================
-- EXPERIMENT 3: exhibit the actual probe list for one case
-- =====================================================================
#eval show IO Unit from do
  let shapes := shapesOfSize 5
  let store := hashStore
  for s in shapes.take 4 do
    IO.println s!"shape bp={s.bpCode}"
    IO.println s!"  base=6 pos=7 reads={F1reads s store 6 7} value={(F1 s store 6 7).value} \
steps={(F1 s store 6 7).trace.length}"

-- =====================================================================
-- EXPERIMENT 4: dependence on size IS real (sanity / anti-vacuity)
-- =====================================================================
#eval show IO Unit from do
  let store := hashStore
  for n in [1, 2, 3, 4, 5, 6, 9, 17] do
    let s := (shapesOfSize n).headD CartesianShape.empty
    IO.println s!"SIZEDEP n={n} bpLen={s.bpCode.length} knobs={knobs s 7} \
reads={F1reads s store 6 7}"

end F03F1Exp
