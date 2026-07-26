import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Isolating the highest-risk F03 row: controller leaf L1, the select-close leaf.

`RMQ/Core/SuccinctFinalStoreParam.lean:645-653`

  def concreteBPNativeSelectCloseGlobalWordTraceResultWithStore shape store idx :=
    (GenericSelect.sparseExceptionSelectData shape.bpCode false)
      |>.bpChunkedSelectTraceResultWithStore ... store
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) idx

`sparseExceptionSelectData shape.bpCode false` is a genuine CONTENT-dependent
structure passed as an explicit VALUE (not a type index). Classical
sparse/dense select directories choose a per-superblock regime from the actual
distribution of set bits, so if the trace function reads a regime field off this
free record to pick an address, that is a free content input and an F03
obstruction. If instead every address it computes is size-derived and every
datum comes from `store`, the leaf is closed.

The discriminating inputs are structurally maximal: at size n,
  leftSpine  bpCode = true^n ++ false^n   (all opens, then all closes)
  rightSpine bpCode = (true false)^n      (perfectly alternating)
These have maximally different set-bit distributions at identical length, so any
sparsity-driven addressing must diverge between them.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose

namespace F03Sel

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty

def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (balanced (n / 2)) (balanced (n - n / 2))

def addrStore (salt : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 24).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)

def selLeaf (s : CartesianShape) (st : WordRAM.ReadStore) (idx : Nat) :=
  concreteBPNativeSelectCloseGlobalWordTraceResultWithStore s st idx

def rankLeaf (s : CartesianShape) (st : WordRAM.ReadStore) (pos : Nat) :=
  concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s st
    concreteBPNativeRankCloseTraceSegmentBase pos

def addrs (t : List WordRAM.TraceEvent) : List (Nat × Nat) :=
  t.filterMap fun
    | WordRAM.TraceEvent.readWord seg i _ => some (seg, i)
    | _ => none

#eval show IO Unit from do
  let st := addrStore 5
  for n in [8, 64, 512] do
    let ls := leftSpine n
    let rs := rightSpine n
    let bs := balanced n
    IO.println s!"--- n={n}  bpLen={ls.bpCode.length}"
    IO.println s!"    leftSpine  opens-then-closes, first 12 bits = {ls.bpCode.take 12}"
    IO.println s!"    rightSpine alternating,       first 12 bits = {rs.bpCode.take 12}"
    IO.println s!"    balanced,                     first 12 bits = {bs.bpCode.take 12}"
    for idx in [0, 1, n / 2, n - 1] do
      let a := selLeaf ls st idx
      let b := selLeaf rs st idx
      let c := selLeaf bs st idx
      let sameAB := a.trace == b.trace && a.value == b.value
      let sameAC := a.trace == c.trace && a.value == c.value
      IO.println s!"  SELECT idx={idx}: L(len={a.trace.length},v={a.value}) R(len={b.trace.length},v={b.value}) B(len={c.trace.length},v={c.value})  L==R:{sameAB} L==B:{sameAC}"
      if !sameAB then
        let z := (a.trace.zip b.trace).findIdx? (fun p => p.1 != p.2)
        IO.println s!"    *** SELECT DIVERGENCE L vs R at event {z}"
        match z with
        | some i =>
            IO.println s!"        L[{i}]={repr (a.trace[i]?)}"
            IO.println s!"        R[{i}]={repr (b.trace[i]?)}"
        | none => IO.println s!"        (prefix agrees; lengths differ)"
      if !sameAC then
        let z := (a.trace.zip c.trace).findIdx? (fun p => p.1 != p.2)
        IO.println s!"    *** SELECT DIVERGENCE L vs B at event {z}"
        match z with
        | some i =>
            IO.println s!"        L[{i}]={repr (a.trace[i]?)}"
            IO.println s!"        B[{i}]={repr (c.trace[i]?)}"
        | none => IO.println s!"        (prefix agrees; lengths differ)"
    for pos in [0, 1, n / 2] do
      let a := rankLeaf ls st pos
      let b := rankLeaf rs st pos
      let c := rankLeaf bs st pos
      let sameAB := a.trace == b.trace && a.value == b.value
      let sameAC := a.trace == c.trace && a.value == c.value
      IO.println s!"  RANK  pos={pos}: L(len={a.trace.length},v={a.value}) R(len={b.trace.length},v={b.value}) B(len={c.trace.length},v={c.value})  L==R:{sameAB} L==B:{sameAC}"
      if !sameAB then
        let z := (a.trace.zip b.trace).findIdx? (fun p => p.1 != p.2)
        IO.println s!"    *** RANK DIVERGENCE L vs R at event {z}"
        match z with
        | some i =>
            IO.println s!"        L[{i}]={repr (a.trace[i]?)}"
            IO.println s!"        R[{i}]={repr (b.trace[i]?)}"
        | none => IO.println s!"        (prefix agrees; lengths differ)"

end F03Sel
