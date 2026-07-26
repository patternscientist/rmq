import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
The coordinator's cross-shape determinism experiment, re-run OUT of the n=3
degenerate regime and over ALL endpoint pairs, not just (0,n).

If the controller were closed over (n, endpoints, prior probe replies), then
fixing the store and endpoints must fix the read transcript across every shape
of the same size. Any differing pair witnesses `shape` as a live free input.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal

namespace AtkX

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def footprint (shape : CartesianShape) (store : WordRAM.ReadStore)
    (l r : Nat) : List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore shape store l r

def outValue (shape : CartesianShape) (store : WordRAM.ReadStore)
    (l r : Nat) : Option Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore shape store l r).value

/-- Several stores, so the result is not an artifact of one all-alternating word. -/
def stores : List (String × WordRAM.ReadStore) :=
  [ ("alt",   flatStore [true, false, true, false, true, false, true, false])
  , ("ones",  flatStore [true, true, true, true, true, true, true, true])
  , ("zeros", flatStore [false, false, false, false, false, false, false, false])
  , ("mix",   flatStore [true, true, false, true, false, false, true, false]) ]

#eval show IO Unit from do
  for n in [3, 4, 5, 6] do
    let shapes := shapesOfSize n
    for (snm, store) in stores do
      let mut fpDistinct := 0
      let mut outDistinct := 0
      let mut cases := 0
      for l in List.range n do
        for r in List.range (n + 1) do
          if l < r then
            cases := cases + 1
            let fps := shapes.map (fun s => toString (footprint s store l r))
            let outs := shapes.map (fun s => toString (outValue s store l r))
            if fps.eraseDups.length > 1 then fpDistinct := fpDistinct + 1
            if outs.eraseDups.length > 1 then outDistinct := outDistinct + 1
      IO.println s!"n={n} shapes={shapes.length} store={snm} endpointPairs={cases} :: pairsWithDifferingTranscript={fpDistinct} pairsWithDifferingOutput={outDistinct}"

end AtkX
