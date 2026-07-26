import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL attack, stage 6: EXHAUSTIVE controller differential at n = 8 and
n = 9 (1430 and 4862 shapes), one Catalan level beyond the other agent's
exhaustive coverage (they stopped at n = 7 / 429 shapes).
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvSZExh8

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

partial def shapesN : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesN k).flatMap fun l =>
          (shapesN (n - k)).map fun r => CartesianShape.node l r

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def addrStore (k : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 24).map fun j => ((seg * 7 + idx * 13 + j * 5 + k) % 3 == 0))

def word0 : List Bool := [true, false, true, false, true, false, true, false]

def footprint (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore s st l r

def outValue (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    s st l r).value

def report (label : String) (n : Nat) (st : WordRAM.ReadStore) (l r : Nat) :
    IO Unit := do
  let ss := shapesN n
  match ss with
  | [] => pure ()
  | s0 :: _ =>
    let fp0 := footprint s0 st l r
    let ov0 := outValue s0 st l r
    let mut fpD := 0
    let mut ovD := 0
    for s in ss do
      if footprint s st l r != fp0 then fpD := fpD + 1
      if outValue s st l r != ov0 then ovD := ovD + 1
    IO.println s!"{label} n={n} l={l} r={r} shapes={ss.length} fpLen={fp0.length} out0={ov0} footprintDiffers={fpD} outputDiffers={ovD}"

#eval show IO Unit from do
  report "EXH-FLAT" 8 (flatStore word0) 0 8
  report "EXH-ADDR" 8 (addrStore 3) 0 8
  report "EXH-MID"  8 (flatStore word0) 3 6
  report "EXH-FLAT" 9 (flatStore word0) 0 9
  report "EXH-ADDR" 9 (addrStore 3) 0 9

end AdvSZExh8
