import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL attack, stage 4: the CONTROLLER transcript, same-size, at sizes
the other agent never reached (they stopped at n = 7, entirely inside the
ACTIVE=false regime).  Same protocol: one FIXED shape-free store, fixed
endpoints, compare ordered read footprint and output value across shapes of
equal size.  Any divergence is a same-size counterexample and refutes the
benign reading directly at the controller.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvSZCtrl

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

partial def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (leftSpine n) CartesianShape.empty

partial def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (balanced (n / 2)) (balanced (n - n / 2))

partial def randShape (seed : Nat) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      let s := (seed * 1103515245 + 12345) % 2147483648
      let k := s % (n + 1)
      CartesianShape.node (randShape (s / 7 + 1) k) (randShape (s / 11 + 3) (n - k))

def familyOf (n : Nat) : List CartesianShape :=
  [leftSpine n, rightSpine n, balanced n, randShape 1 n, randShape 7 n,
   randShape 99 n, randShape 4242 n]

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
  let fam := familyOf n
  if (fam.map (fun s => s.size)).any (fun k => k != n) then
    IO.println s!"{label} n={n} *** SIZE MISMATCH ***"
  else
    match fam with
    | [] => pure ()
    | s0 :: _ =>
      let fp0 := footprint s0 st l r
      let ov0 := outValue s0 st l r
      let mut fpD := 0
      let mut ovD := 0
      for s in fam do
        if footprint s st l r != fp0 then fpD := fpD + 1
        if outValue s st l r != ov0 then ovD := ovD + 1
      IO.println s!"{label} n={n} l={l} r={r} shapes={fam.length} fpLen={fp0.length} out0={ov0} footprintDiffers={fpD} outputDiffers={ovD}"

#eval show IO Unit from do
  for n in [8,12,16,24,32,48,64] do
    report "FLAT" n (flatStore word0) 0 n
    report "ADDR" n (addrStore 3) 0 n
    report "FLAT-mid" n (flatStore word0) (n/3) (2*n/3)

end AdvSZCtrl
