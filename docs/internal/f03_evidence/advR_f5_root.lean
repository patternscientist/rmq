import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
ADVERSARIAL F5, attack 3: the FULL controller root, cross-shape, above n=3.

The coordinator's cross-shape transcript experiment was run only at n=3 (a
possibly degenerate regime, endpoints (0,3) only).  The benign F5 write-up
tested only SUBCOMPONENTS (summary / interior range-min).  Neither drove the
actual root named in the task at a size where the rmM hierarchy is live.

If any bpExcessAt-derived value reached an address, a branch, a divisor or a
selector, then two same-size shapes with DIFFERENT bpCode contents, under ONE
fixed shape-free store, would produce different ordered read footprints (or
different outputs) for some endpoint pair.

This sweeps ALL shapes of each size and ALL endpoint pairs.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal

namespace AdvRoot

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | n + 1 =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

/-- Address-varying, shape-free store (harder than a constant store). -/
def store1 : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 8).map fun i => ((seg * 7 + idx * 3 + i) % 5 == 0))

/-- A second, differently-shaped store, to rule out a degenerate-store artifact. -/
def store2 : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 12).map fun i => ((seg * 13 + idx * 11 + i * i) % 7 < 3))

def footprint (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :
    List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore s st l r

def outValue (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :
    Option Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    s st l r).value

def allEq {a : Type} [BEq a] : List a -> Bool
  | [] => true
  | x :: xs => xs.all (fun y => y == x)

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advR_f5_root_out.txt"

/-- All endpoint pairs l < r <= n. -/
def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range (n + 1)).flatMap fun l =>
    (List.range (n + 1)).filterMap fun r =>
      if l < r then some (l, r) else none

def rowFor (st : WordRAM.ReadStore) (tag : String) (n : Nat) : String := Id.run do
  let ss := shapesOfSize n
  let ps := pairs n
  let mut fpConst := true
  let mut valConst := true
  let mut fpLens : List Nat := []
  let mut worstPair : String := ""
  for (l, r) in ps do
    let fps := ss.map (fun s => footprint s st l r)
    let vals := ss.map (fun s => outValue s st l r)
    if !(allEq fps) then
      fpConst := false
      if worstPair == "" then worstPair := s!"({l},{r})"
    if !(allEq vals) then
      valConst := false
      if worstPair == "" then worstPair := s!"({l},{r})"
    fpLens := (fps.head?.getD []).length :: fpLens
  -- anti-vacuity: do the shapes actually differ in CONTENT (not just count)?
  let bps := ss.map (fun s => s.bpCode)
  return s!"{tag} n={n} shapes={ss.length} pairs={ps.length} " ++
    s!"FOOTPRINT_CONST={fpConst} VALUE_CONST={valConst} " ++
    s!"BPCODES_ALL_EQUAL={allEq bps} " ++
    s!"sampleFootprintLens={fpLens.reverse.take 6} firstDiffPair={worstPair}"

run_cmd do
  let mut acc : Array String := #[]
  for n in [2,3,4,5,6] do
    let l1 := rowFor store1 "S1" n
    acc := acc.push l1
    IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)
    Lean.logInfo m!"{l1}"
    let l2 := rowFor store2 "S2" n
    acc := acc.push l2
    IO.FS.writeFile outPath (String.intercalate "\n" acc.toList)
    Lean.logInfo m!"{l2}"

end AdvRoot
