import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL REFUTATION (reachability lens), attack #1.

The defended verdict rests behaviourally on a cross-shape determinism experiment
that only ever ran at n <= 7.  base(n) = Nat.log2 n + 1, so for n <= 7 we have
base in {1,2,3} and blockCountRaw = n / base in {0,1,2,3}: every block/superblock
loop is degenerate or empty, and the relative-summary activity predicate is OFF
for all n <= 511 (the defender measured this themselves).

Here I rerun the SAME behavioural test at NON-degenerate sizes with structurally
extreme shapes of equal size (left spine vs right spine vs balanced vs zigzag vs
pseudo-random), which have maximally different bpCode CONTENT but identical
bpCode LENGTH.  If any footprint or output differs, the controller is reading
shape content and F03 is a genuine CHECKED_OBSTRUCTION.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvRxBigN2

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

/-- alternating spine: left, right, left, right ... -/
partial def zigzag (goLeft : Bool) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      if goLeft then CartesianShape.node (zigzag false n) CartesianShape.empty
      else CartesianShape.node CartesianShape.empty (zigzag true n)

/-- deterministic pseudo-random split -/
partial def pseudo (seed : Nat) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      CartesianShape.node (pseudo (seed + 7) k) (pseudo (seed + 13) (n - k))

/-- comb: chunks of 3 hung off a right spine -/
partial def comb : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      if n >= 2 then
        CartesianShape.node
          (CartesianShape.node CartesianShape.empty CartesianShape.empty)
          (comb (n - 1))
      else CartesianShape.node CartesianShape.empty (comb n)

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

def family (n : Nat) : List (String × CartesianShape) :=
  [("leftSpine", leftSpine n),
   ("rightSpine", rightSpine n),
   ("balanced", balanced n),
   ("zigzagL", zigzag true n),
   ("comb", comb n),
   ("pseudo3", pseudo 3 n),
   ("pseudo11", pseudo 11 n)]

/-- sanity: the family really does have equal size and DIFFERENT bpCode content. -/
def shapeSanity (n : Nat) : IO Unit := do
  let fam := family n
  IO.println s!"-- shape family sanity n={n} --"
  let codes := fam.map fun (lbl, s) => (lbl, s.size, s.bpCode.length,
      (s.bpCode.map fun b => cond b 1 0).foldl (fun a b => (a * 2 + b) % 1000003) 0)
  for (lbl, sz, len, h) in codes do
    IO.println s!"   {lbl} size={sz} bpCodeLen={len} bpCodeHash={h}"
  let distinctCodes := ((fam.map fun (_, s) => s.bpCode).eraseDups).length
  IO.println s!"   DISTINCT_BPCODES={distinctCodes} of {fam.length}"

def report (label : String) (n : Nat) (store : WordRAM.ReadStore) (l r : Nat) :
    IO Unit := do
  let fam := family n
  match fam with
  | [] => IO.println s!"{label} n={n} EMPTY"
  | (lbl0, s0) :: _ =>
    let fp0 := footprint s0 store l r
    let ov0 := outValue s0 store l r
    let mut fpD := 0
    let mut ovD := 0
    let mut diffs : List String := []
    for (lbl, s) in fam do
      let fp := footprint s store l r
      let ov := outValue s store l r
      if fp != fp0 then
        fpD := fpD + 1
        diffs := (s!"FP_DIFF {lbl} vs {lbl0}: len {fp.length} vs {fp0.length}") :: diffs
      if ov != ov0 then
        ovD := ovD + 1
        diffs := (s!"OUT_DIFF {lbl}: {ov} vs {ov0} ({lbl0})") :: diffs
    IO.println s!"{label} n={n} l={l} r={r} shapes={fam.length} fpLen={fp0.length} out0={ov0} footprintDiffers={fpD} outputDiffers={ovD}"
    for d in diffs.reverse do IO.println s!"    {d}"

#eval show IO Unit from do
  for n in [128, 256, 512, 700, 1024] do
    shapeSanity n
    report "FLAT" n (flatStore word0) 0 n
    report "ADDR" n (addrStore 1) 0 n
    report "FLATmid" n (flatStore word0) (n / 3) (2 * n / 3)

end AdvRxBigN2
