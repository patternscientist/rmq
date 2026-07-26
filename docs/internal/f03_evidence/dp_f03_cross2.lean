import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! DP-F03 cross-shape determinism, larger sizes, plus ANTI-VACUITY checks. -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace DPF03Cross2

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
  for n in [5,6] do
    report "FLAT" n (flatStore word0) 0 n
    report "ADDR" n (addrStore 1) 0 n

-- ANTI-VACUITY 1: does the footprint vary with the endpoints?
#eval show IO Unit from do
  let n := 6
  let s := ((shapesOfSize n).headD CartesianShape.empty)
  let store := flatStore word0
  let mut fps : List (List (Nat × Nat)) := []
  let mut outs : List (Option Nat) := []
  for l in List.range (n+1) do
    for r in List.range (n+1) do
      let fp := footprint s store l r
      let o := outValue s store l r
      if !(fps.contains fp) then fps := fp :: fps
      if !(outs.contains o) then outs := o :: outs
  IO.println s!"ANTIVAC endpoints: n={n} pairs={(n+1)*(n+1)} distinctFootprints={fps.length} distinctOutputs={outs.length}"

-- ANTI-VACUITY 2: does the footprint vary with the STORE contents?
#eval show IO Unit from do
  let n := 6
  let s := ((shapesOfSize n).headD CartesianShape.empty)
  let mut fps : List (List (Nat × Nat)) := []
  let mut outs : List (Option Nat) := []
  for k in List.range 12 do
    let store := addrStore k
    let fp := footprint s store 0 n
    let o := outValue s store 0 n
    if !(fps.contains fp) then fps := fp :: fps
    if !(outs.contains o) then outs := o :: outs
  for w in [[true],[false],[true,true,false],[false,false,false,false,false,false,false,false]] do
    let store := flatStore w
    let fp := footprint s store 0 n
    let o := outValue s store 0 n
    if !(fps.contains fp) then fps := fp :: fps
    if !(outs.contains o) then outs := o :: outs
  IO.println s!"ANTIVAC stores: n={n} stores=16 distinctFootprints={fps.length} distinctOutputs={outs.length}"

-- ANTI-VACUITY 3: does the footprint vary with n at all?
#eval show IO Unit from do
  let store := flatStore word0
  for n in [1,2,3,4,5,6] do
    let s := ((shapesOfSize n).headD CartesianShape.empty)
    let fp := footprint s store 0 n
    IO.println s!"ANTIVAC size: n={n} fpLen={fp.length} firstReads={fp.take 6} lastReads={(fp.drop (fp.length - 4))}"

end DPF03Cross2
