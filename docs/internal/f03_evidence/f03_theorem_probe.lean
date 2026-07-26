import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
The exact F03 universal consumer, probed before it is proved.

CANDIDATE THEOREM (this is what a proof worker would have to discharge):

  theorem f03_geometry_closure
      (shapeA shapeB : Cartesian.CartesianShape)
      (hsize : shapeA.size = shapeB.size)
      (store : WordRAM.ReadStore) (left right : Nat) :
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          shapeA store left right =
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          shapeB store left right

If it holds, the controller's transcript AND value depend on the semantic shape
only through `shape.size = n`, which is exactly geometry closure: the route
already factors through the allowed inputs, and the free semantic-shape argument
can be replaced by `n` without rewriting the route.

This file does not prove it. It attacks it with structurally extreme same-size
shapes, at sizes above the small-size regime, to find a counterexample if one
exists.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace F03Thm

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

/-- Left spine: every node's right child empty. -/
def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty

/-- Right spine: every node's left child empty. -/
def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)

/-- Perfectly balanced-ish: split remaining nodes evenly. -/
partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (balanced (n / 2)) (balanced (n - n / 2))

/-- Caterpillar: alternate which side the spine descends. -/
partial def caterpillar (flip : Bool) : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n =>
      if flip then .node (caterpillar false n) .empty
      else .node .empty (caterpillar true n)

/-- Deterministic pseudo-random shape of a given size. -/
partial def pseudo (seed : Nat) : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      .node (pseudo (seed + 7) k) (pseudo (seed + 13) (n - k))

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def addrStore (salt : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 24).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)

def noneStore : WordRAM.ReadStore where
  readWord? := fun _ _ => none

def run (shape : CartesianShape) (store : WordRAM.ReadStore) (l r : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    shape store l r

def shapesAt (n : Nat) : List (String × CartesianShape) :=
  [ ("leftSpine",   leftSpine n)
  , ("rightSpine",  rightSpine n)
  , ("balanced",    balanced n)
  , ("caterpillarT", caterpillar true n)
  , ("caterpillarF", caterpillar false n)
  , ("pseudo1",     pseudo 1 n)
  , ("pseudo2",     pseudo 2 n)
  , ("pseudo99",    pseudo 99 n)
  ]

def stores : List (String × WordRAM.ReadStore) :=
  [ ("flat0", flatStore (List.replicate 24 false))
  , ("flat1", flatStore (List.replicate 24 true))
  , ("addr5", addrStore 5)
  , ("none",  noneStore)
  ]

/-- Compare every named shape of size `n` against the first, over several
    stores and endpoint pairs. Reports the FIRST divergence in full. -/
def probe (n : Nat) (endpoints : List (Nat × Nat)) : IO (Nat × Nat) := do
  let ss := shapesAt n
  match ss with
  | [] => return (0, 0)
  | (baseName, base) :: rest =>
    -- sanity: every generated shape really has size n
    for (nm, s) in ss do
      if s.size != n then
        IO.println s!"  GENERATOR BUG: {nm} size={s.size} expected {n}"
    let mut cmps := 0
    let mut diffs := 0
    for (stName, st) in stores do
      for (l, r) in endpoints do
        let b := run base st l r
        for (nm, s) in rest do
          cmps := cmps + 1
          let x := run s st l r
          if x.trace != b.trace || x.value != b.value then
            diffs := diffs + 1
            if diffs <= 3 then
              IO.println s!"  *** DIVERGENCE n={n} store={stName} l={l} r={r}"
              IO.println s!"      {baseName} vs {nm}"
              IO.println s!"      baseTraceLen={b.trace.length} thisTraceLen={x.trace.length}"
              IO.println s!"      baseValue={b.value} thisValue={x.value}"
              let z := (b.trace.zip x.trace).findIdx? (fun p => p.1 != p.2)
              IO.println s!"      firstDifferingEventIndex={z}"
              match z with
              | some i =>
                IO.println s!"      base[{i}]={repr (b.trace[i]?)}"
                IO.println s!"      this[{i}]={repr (x.trace[i]?)}"
              | none => IO.println s!"      (traces agree on common prefix; lengths differ)"
    return (cmps, diffs)

#eval show IO Unit from do
  let mut totalC := 0
  let mut totalD := 0
  for n in [1, 2, 3, 5, 8, 13, 21, 34, 55] do
    let eps := [(0, n), (0, 1), (n / 2, n), (0, n / 2 + 1), (n - 1, n)]
    let (c, d) <- probe n eps
    totalC := totalC + c
    totalD := totalD + d
    IO.println s!"n={n}: comparisons={c} divergences={d}"
  IO.println s!"F03-THEOREM-PROBE TOTAL comparisons={totalC} divergences={totalD}"

end F03Thm
