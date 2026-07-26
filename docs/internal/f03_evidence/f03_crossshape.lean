import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 decisive experiment: cross-shape transcript determinism.

If the whole-query controller were closed over `(n, left, right, prior probe
replies)`, then fixing the store and the endpoints would fix the read
transcript for every shape of the same size. Any two same-size shapes whose
transcripts differ under one fixed store witness that the semantic `shape`
is a live dynamic input beyond the allowed set.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace F03Cross

/-- Every Cartesian shape of a given size. -/
partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

/-- A fixed store that does not mention any shape. -/
def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

/-- Ordered logical read footprint under a supplied store. -/
def footprint (shape : CartesianShape) (store : WordRAM.ReadStore)
    (l r : Nat) : List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
    shape store l r

/-- Output value under a supplied store. -/
def outValue (shape : CartesianShape) (store : WordRAM.ReadStore)
    (l r : Nat) : Option Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    shape store l r).value

def word0 : List Bool := [true, false, true, false, true, false, true, false]

#eval show IO Unit from do
  let n := 3
  let shapes := shapesOfSize n
  IO.println s!"n={n} shapeCount={shapes.length}"
  let store := flatStore word0
  let mut prints := 0
  for a in shapes, i in List.range shapes.length do
    let fa := footprint a store 0 n
    IO.println s!"  shape[{i}] size={a.size} bp={a.bpCode} footprintLen={fa.length} out={outValue a store 0 n}"
    IO.println s!"    fp={fa}"
    prints := prints + 1
  IO.println s!"printed={prints}"

#eval show IO Unit from do
  let n := 3
  let shapes := shapesOfSize n
  let store := flatStore word0
  let mut differPairs := 0
  let mut total := 0
  for a in shapes do
    for b in shapes do
      total := total + 1
      if footprint a store 0 n != footprint b store 0 n then
        differPairs := differPairs + 1
  IO.println s!"CROSS-SHAPE FIXED-STORE: n={n} pairs={total} transcriptDiffer={differPairs}"

end F03Cross
