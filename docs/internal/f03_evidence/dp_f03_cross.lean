import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
DP-F03 (b) part 4: cross-shape determinism of the EXECUTED controller, at
several sizes and with SEVERAL stores and endpoint pairs.

If any branch, divisor, offset or selector on the executed path reads BP
CONTENT that did not come from a probe, then two shapes of the same size,
queried with the SAME store and the SAME endpoints, can differ in their ordered
read footprint or in their output.  This is the executable form of F03.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace DPF03Cross

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

/-- Constant store: every address returns the same word. -/
def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

/-- Address-dependent store: the reply depends on (segment, index) only,
    so replies are legitimate "prior probe" data and never mention a shape. -/
def addrStore (k : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 16).map fun j => ((seg * 7 + idx * 13 + j * 5 + k) % 3 == 0))

def emptyStore : WordRAM.ReadStore where
  readWord? := fun _ _ => none

def footprint (shape : CartesianShape) (store : WordRAM.ReadStore)
    (l r : Nat) : List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore shape store l r

def outValue (shape : CartesianShape) (store : WordRAM.ReadStore)
    (l r : Nat) : Option Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    shape store l r).value

def word0 : List Bool := [true, false, true, false, true, false, true, false]

structure Report where
  n : Nat
  shapes : Nat
  fpDiffer : Nat
  outDiffer : Nat
  fpLen0 : Nat

def runOne (n : Nat) (store : WordRAM.ReadStore) (l r : Nat) : Report := Id.run do
  let shapes := shapesOfSize n
  match shapes with
  | [] => pure { n := n, shapes := 0, fpDiffer := 0, outDiffer := 0, fpLen0 := 0 }
  | s0 :: _ =>
    let fp0 := footprint s0 store l r
    let ov0 := outValue s0 store l r
    let mut fpD := 0
    let mut ovD := 0
    for s in shapes do
      if footprint s store l r != fp0 then fpD := fpD + 1
      if outValue s store l r != ov0 then ovD := ovD + 1
    pure { n := n, shapes := shapes.length, fpDiffer := fpD, outDiffer := ovD,
           fpLen0 := fp0.length }

#eval show IO Unit from do
  IO.println "== cross-shape determinism, FLAT store, endpoints (0,n) =="
  for n in [1,2,3,4,5,6,7,8] do
    let rep := runOne n (flatStore word0) 0 n
    IO.println s!"n={rep.n} shapes={rep.shapes} fpLen={rep.fpLen0} footprintDiffersFromShape0={rep.fpDiffer} outputDiffersFromShape0={rep.outDiffer}"

#eval show IO Unit from do
  IO.println "== cross-shape determinism, ADDRESS-DEPENDENT store, endpoints (0,n) =="
  for n in [1,2,3,4,5,6,7,8] do
    let rep := runOne n (addrStore 1) 0 n
    IO.println s!"n={rep.n} shapes={rep.shapes} fpLen={rep.fpLen0} footprintDiffers={rep.fpDiffer} outputDiffers={rep.outDiffer}"

#eval show IO Unit from do
  IO.println "== cross-shape determinism, EMPTY store (all probes fail), endpoints (0,n) =="
  for n in [1,2,3,4,5,6,7,8] do
    let rep := runOne n emptyStore 0 n
    IO.println s!"n={rep.n} shapes={rep.shapes} fpLen={rep.fpLen0} footprintDiffers={rep.fpDiffer} outputDiffers={rep.outDiffer}"

#eval show IO Unit from do
  IO.println "== cross-shape determinism, INTERIOR endpoints, flat store =="
  for n in [4,5,6,7,8] do
    for lr in [(0,1),(1,2),(0,2),(1,n-1),(2,n)] do
      let rep := runOne n (flatStore word0) lr.1 lr.2
      IO.println s!"n={n} l={lr.1} r={lr.2} shapes={rep.shapes} fpLen={rep.fpLen0} footprintDiffers={rep.fpDiffer} outputDiffers={rep.outDiffer}"

/-- Print the distinct footprints at one size, to see WHAT differs if anything. -/
#eval show IO Unit from do
  let n := 6
  let store := flatStore word0
  let shapes := shapesOfSize n
  let mut seen : List (List (Nat × Nat)) := []
  for s in shapes do
    let fp := footprint s store 0 n
    if !(seen.contains fp) then seen := fp :: seen
  IO.println s!"n={n} shapeCount={shapes.length} distinctFootprints={seen.length}"
  let mut outs : List (Option Nat) := []
  for s in shapes do
    let o := outValue s store 0 n
    if !(outs.contains o) then outs := o :: outs
  IO.println s!"n={n} distinctOutputs={outs.length} outs={outs}"

end DPF03Cross
