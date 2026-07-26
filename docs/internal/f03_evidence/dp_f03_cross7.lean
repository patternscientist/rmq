import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! DP-F03 cross-shape determinism, small sizes only (fast variant). -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace DPF03Cross7

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def addrStore (k : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 16).map fun j => ((seg * 7 + idx * 13 + j * 5 + k) % 3 == 0))

def footprint (shape : CartesianShape) (store : WordRAM.ReadStore)
    (l r : Nat) : List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore shape store l r

def outValue (shape : CartesianShape) (store : WordRAM.ReadStore)
    (l r : Nat) : Option Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    shape store l r).value

def word0 : List Bool := [true, false, true, false, true, false, true, false]

def report (label : String) (n : Nat) (store : WordRAM.ReadStore) (l r : Nat) :
    IO Unit := do
  let shapes := shapesOfSize n
  match shapes with
  | [] => IO.println s!"{label} n={n} EMPTY"
  | s0 :: _ =>
    let fp0 := footprint s0 store l r
    let ov0 := outValue s0 store l r
    let mut fpD := 0
    let mut ovD := 0
    for s in shapes do
      if footprint s store l r != fp0 then fpD := fpD + 1
      if outValue s store l r != ov0 then ovD := ovD + 1
    IO.println s!"{label} n={n} l={l} r={r} shapes={shapes.length} fpLen={fp0.length} out0={ov0} footprintDiffers={fpD} outputDiffers={ovD}"

#eval show IO Unit from do
  for n in [7] do
    report "FLAT" n (flatStore word0) 0 n
    report "ADDR" n (addrStore 1) 0 n

end DPF03Cross7
