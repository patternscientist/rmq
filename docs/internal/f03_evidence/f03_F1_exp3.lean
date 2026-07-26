import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! F03 / F1 executed cross-shape experiment (fixed: no Catalan blowup). -/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctRank

namespace F03F1Exp3

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

/-- Right spine of size n (cheap witness of a given size). -/
def spine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (spine n)

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

def sig (s : CartesianShape) (store : WordRAM.ReadStore) :
    List (Nat × List WordRAM.TraceEvent) :=
  ([0, 6] : List Nat).flatMap fun base =>
    posList.map fun p => let r := F1 s store base p; (r.value, r.trace)

-- A: geometry knobs constant across ALL same-size shapes
#eval show IO Unit from do
  for n in [1, 2, 3, 4, 5, 6] do
    let shapes := shapesOfSize n
    let b := shapes.headD CartesianShape.empty
    let baseKs := posList.map (knobs b)
    let mut differ := 0
    for s in shapes do
      if posList.map (knobs s) != baseKs then differ := differ + 1
    IO.println s!"KNOBS n={n} shapes={shapes.length} bpLen={b.bpCode.length} shapesWithDifferentKnobs={differ} sample={baseKs.take 3}"

-- B: F1's own value+trace constant across ALL same-size shapes, 3 stores
#eval show IO Unit from do
  for st in [(0, flatStore word0), (1, flatStore []), (2, hashStore)] do
    let (sid, store) := st
    for n in [1, 2, 3, 4, 5, 6] do
      let shapes := shapesOfSize n
      let b := shapes.headD CartesianShape.empty
      let bsig := sig b store
      let mut differ := 0
      for s in shapes do
        if sig s store != bsig then differ := differ + 1
      IO.println s!"CROSSSHAPE store={sid} n={n} shapes={shapes.length} shapesDifferingFromShape0={differ} sigLen={bsig.length}"

-- C: exhibit actual probe lists for distinct same-size shapes
#eval show IO Unit from do
  let shapes := shapesOfSize 5
  let store := hashStore
  for s in shapes.take 5 do
    let r := F1 s store 6 7
    IO.println s!"bp={s.bpCode}"
    IO.println s!"   reads={F1reads s store 6 7} value={r.value} steps={r.trace.length}"

-- D (anti-vacuity): probe list DOES move with n
#eval show IO Unit from do
  let store := hashStore
  for n in [1, 2, 3, 5, 9, 17, 40, 200] do
    let s := spine n
    IO.println s!"SIZEDEP n={n} bpLen={s.bpCode.length} knobs={knobs s 7} reads={F1reads s store 6 7}"

-- E (anti-vacuity for the store): F1's replies DO move with the store
#eval show IO Unit from do
  let s := spine 9
  IO.println s!"STOREDEP flat0={(F1 s (flatStore word0) 6 7).value} \
flatEmpty={(F1 s (flatStore []) 6 7).value} hash={(F1 s hashStore 6 7).value}"
  IO.println s!"STOREDEP readsFlat0={F1reads s (flatStore word0) 6 7}"
  IO.println s!"STOREDEP readsHash={F1reads s hashStore 6 7}"

end F03F1Exp3
