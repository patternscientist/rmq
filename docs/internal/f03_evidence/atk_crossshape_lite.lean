import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Lighter cross-shape determinism probe: n=4 and n=5, one store, all endpoints. -/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal

namespace AtkXL

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def store0 : WordRAM.ReadStore :=
  flatStore [true, true, false, true, false, false, true, false]

def footprint (s : CartesianShape) (l r : Nat) : List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore s store0 l r

#eval show IO Unit from do
  for n in [4] do
    let shapes := shapesOfSize n
    IO.println s!"n={n} shapes={shapes.length}"
    for (l, r) in [(0, n), (0, 2), (1, 3)] do
      let fps := shapes.map (fun s => toString (footprint s l r))
      let d := fps.eraseDups.length
      IO.println s!"  endpoints=({l},{r}) distinctTranscripts={d}/{shapes.length} len0={(footprint shapes.head! l r).length}"

end AtkXL
