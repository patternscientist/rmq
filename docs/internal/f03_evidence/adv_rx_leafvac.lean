import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL REFUTATION, attack #3 (THE reachability attack).

RMQ/Core/SuccinctFinalStoreParam.lean:2068-2075 -- the `lcaClose` instruction
only runs the L2 leaf when BOTH select registers are already `some`:

    | .lcaClose dst leftReg rightReg =>
        match state.opt leftReg, state.opt rightReg with
        | some leftClose, some rightClose => ... L2 ...
        | _, _ => WordRAM.TraceResult.pure (state.setOpt dst none)

The whole `bpExcessAt` (F5) cone hangs off L2 (defender's BFS path of length 14).
So if, under the arbitrary shape-free stores used in the cross-shape experiments,
`selectClose` returns `none`, then `lcaClose` short-circuits, L2 NEVER RUNS, and
the entire cross-shape determinism result is VACUOUS for the F5 cone -- it would
be measuring only the L1 select leaf.  The defender's anti-vacuity checks
(footprint varies with n / endpoints / store) are all satisfiable by L1 alone.

Part A: did lcaClose actually fire?
Part B: invoke each leaf L1/L2/L3 DIRECTLY, bypassing every short-circuit,
        and compare full traces + values across equal-size shapes.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvRxLeaf

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

partial def zigzag (goLeft : Bool) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      if goLeft then CartesianShape.node (zigzag false n) CartesianShape.empty
      else CartesianShape.node CartesianShape.empty (zigzag true n)

partial def pseudo (seed : Nat) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      CartesianShape.node (pseudo (seed + 7) k) (pseudo (seed + 13) (n - k))

def family (n : Nat) : List (String × CartesianShape) :=
  [("leftSpine", leftSpine n), ("rightSpine", rightSpine n),
   ("balanced", balanced n), ("zigzagL", zigzag true n),
   ("pseudo3", pseudo 3 n), ("pseudo11", pseudo 11 n)]

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def addrStore (k : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 16).map fun j => ((seg * 7 + idx * 13 + j * 5 + k) % 3 == 0))

/-- an "honest" store: serve the shape's own BP code back as every word.
    This is the store family most likely to drive the controller down live paths. -/
def bpStore (s : CartesianShape) : WordRAM.ReadStore where
  readWord? := fun _ _ => some s.bpCode

def allTrueStore (w : Nat) : WordRAM.ReadStore where
  readWord? := fun _ _ => some (List.replicate w true)

def word0 : List Bool := [true, false, true, false, true, false, true, false]

/-! ## Part A: does lcaClose fire? -/

def selVal (s : CartesianShape) (store : WordRAM.ReadStore) (idx : Nat) :
    Option Nat :=
  (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore s store idx).value

def partA (label : String) (n : Nat) (store : CartesianShape -> WordRAM.ReadStore)
    (l r : Nat) : IO Unit := do
  let fam := family n
  let mut fired := 0
  let mut details : List String := []
  for (lbl, s) in fam do
    let st := store s
    let lc := selVal s st l
    let rc := selVal s st (r - 1)
    let didFire := lc.isSome && rc.isSome
    if didFire then fired := fired + 1
    details := s!"{lbl}: leftClose={lc} rightClose={rc} lcaCloseFIRES={didFire}" :: details
  IO.println s!"  [A] {label} n={n} l={l} r={r} : lcaClose fired for {fired}/{fam.length} shapes"
  for d in details.reverse do IO.println s!"        {d}"

/-! ## Part B: direct leaf invocation, no short-circuit possible -/

def cmpFull {a : Type} [BEq a] (label : String) (n : Nat)
    (f : CartesianShape -> WordRAM.TraceResult a) : IO Unit := do
  let fam := family n
  match fam with
  | [] => pure ()
  | (lbl0, s0) :: _ =>
    let r0 := f s0
    let mut trD := 0
    let mut vD := 0
    let mut msgs : List String := []
    for (lbl, s) in fam do
      let r := f s
      if r.trace != r0.trace then
        trD := trD + 1
        let z := (r.trace.zip r0.trace).findIdx? (fun p => p.1 != p.2)
        msgs := s!"TRACE_DIFF {lbl} vs {lbl0} firstDiffIdx={z} len={r.trace.length}/{r0.trace.length}" :: msgs
      if !(r.value == r0.value) then
        vD := vD + 1
        msgs := s!"VALUE_DIFF {lbl} vs {lbl0}" :: msgs
    IO.println s!"  [B] {label} n={n} events={r0.trace.length} traceDiffers={trD} valueDiffers={vD}"
    for m in msgs.reverse do IO.println s!"        {m}"

def leafL1 (store : WordRAM.ReadStore) (idx : Nat) (s : CartesianShape) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSelectCloseGlobalWordTraceResultWithStore s store idx

def leafL2 (store : WordRAM.ReadStore) (lc rc : Nat) (s : CartesianShape) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore s store lc rc

def leafL3 (store : WordRAM.ReadStore) (base pos : Nat) (s : CartesianShape) :
    WordRAM.TraceResult Nat :=
  concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s store base pos

#eval show IO Unit from do
  IO.println "=== PART A: does the lcaClose instruction actually fire? ==="
  for n in [8, 16, 32] do
    partA "FLAT" n (fun _ => flatStore word0) 0 n
    partA "ADDR" n (fun _ => addrStore 1) 0 n
    partA "BPSELF" n bpStore 0 n
    partA "ALLTRUE" n (fun _ => allTrueStore 16) 0 n
  IO.println ""
  IO.println "=== PART B: DIRECT leaf invocation, short-circuit bypassed ==="
  for n in [8, 16, 32] do
    IO.println s!"  -- n={n} --"
    cmpFull "L1 select (FLAT, idx=3)" n (leafL1 (flatStore word0) 3)
    cmpFull "L1 select (ADDR, idx=3)" n (leafL1 (addrStore 1) 3)
    cmpFull "L2 LCA    (FLAT, 2,7)"   n (leafL2 (flatStore word0) 2 7)
    cmpFull "L2 LCA    (ADDR, 2,7)"   n (leafL2 (addrStore 1) 2 7)
    cmpFull "L2 LCA    (ADDR, 1,n)"   n (leafL2 (addrStore 3) 1 n)
    cmpFull "L2 LCA    (ALLTRUE,2,7)" n (leafL2 (allTrueStore 16) 2 7)
    cmpFull "L3 rank   (ADDR, base0,pos5)" n (leafL3 (addrStore 1) 0 5)

end AdvRxLeaf
