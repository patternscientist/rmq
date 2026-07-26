import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL REFUTATION, attack #5: broaden the quantification.

Every previous leaf test used a handful of hand-picked argument values.  Here I
sweep ALL leaf arguments in range, for each of the three controller leaves
L1/L2/L3, against structurally extreme equal-size shapes, comparing the FULL
trace (every event, all fields) and the value.  Anti-vacuity is measured in the
same run: how many DISTINCT traces the leaf produces as its own (non-shape)
arguments move.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvRxSweep

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

def family (n : Nat) : List CartesianShape :=
  [leftSpine n, rightSpine n, balanced n, zigzag true n, pseudo 3 n, pseudo 11 n]

def addrStore (k : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 16).map fun j => ((seg * 7 + idx * 13 + j * 5 + k) % 3 == 0))

/-- sweep L1 over every idx in [0, 2n]; report cross-shape diffs + distinct traces -/
def sweepL1 (n : Nat) (store : WordRAM.ReadStore) : IO Unit := do
  let fam := family n
  let s0 := fam.head!
  let mut diffs := 0
  let mut cases := 0
  let mut seen : List (List WordRAM.TraceEvent) := []
  for idx in List.range (2 * n + 2) do
    let r0 := concreteBPNativeSelectCloseGlobalWordTraceResultWithStore s0 store idx
    if !(seen.contains r0.trace) then seen := r0.trace :: seen
    for s in fam do
      let r := concreteBPNativeSelectCloseGlobalWordTraceResultWithStore s store idx
      cases := cases + 1
      if r.trace != r0.trace || !(r.value == r0.value) then diffs := diffs + 1
  IO.println s!"  L1 select n={n}: swept idx in [0,{2*n+1}] x {fam.length} shapes = {cases} cases | crossShapeDiffs={diffs} | ANTIVAC distinctTraces={seen.length}"

/-- sweep L3 over every pos in [0, 2n]; -/
def sweepL3 (n : Nat) (store : WordRAM.ReadStore) : IO Unit := do
  let fam := family n
  let s0 := fam.head!
  let mut diffs := 0
  let mut cases := 0
  let mut seen : List (List WordRAM.TraceEvent) := []
  for pos in List.range (2 * n + 2) do
    let r0 := concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s0 store 0 pos
    if !(seen.contains r0.trace) then seen := r0.trace :: seen
    for s in fam do
      let r := concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s store 0 pos
      cases := cases + 1
      if r.trace != r0.trace || !(r.value == r0.value) then diffs := diffs + 1
  IO.println s!"  L3 rank   n={n}: swept pos in [0,{2*n+1}] x {fam.length} shapes = {cases} cases | crossShapeDiffs={diffs} | ANTIVAC distinctTraces={seen.length}"

/-- sweep L2 over a grid of (leftClose, rightClose) -/
def sweepL2 (n : Nat) (store : WordRAM.ReadStore) (step : Nat) : IO Unit := do
  let fam := family n
  let s0 := fam.head!
  let mut diffs := 0
  let mut cases := 0
  let mut seen : List (List WordRAM.TraceEvent) := []
  let pts := (List.range (2 * n / step + 1)).map (fun i => i * step)
  for lc in pts do
    for rc in pts do
      let r0 := concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore s0 store lc rc
      if !(seen.contains r0.trace) then seen := r0.trace :: seen
      for s in fam do
        let r := concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore s store lc rc
        cases := cases + 1
        if r.trace != r0.trace || !(r.value == r0.value) then diffs := diffs + 1
  IO.println s!"  L2 LCA    n={n}: swept {pts.length}x{pts.length} (lc,rc) x {fam.length} shapes = {cases} cases | crossShapeDiffs={diffs} | ANTIVAC distinctTraces={seen.length}"

#eval show IO Unit from do
  IO.println "=== attack #5: full-range leaf sweeps, full-trace comparison ==="
  for n in [8, 16, 32] do
    IO.println s!"-- n={n} --"
    sweepL1 n (addrStore 1)
    sweepL3 n (addrStore 1)
    sweepL2 n (addrStore 1) (if n <= 8 then 2 else 4)

end AdvRxSweep
