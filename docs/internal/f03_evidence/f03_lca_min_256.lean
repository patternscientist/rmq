import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Minimal L2 (LCA-close) cross-shape probe: two maximally different shapes,
    one endpoint pair, one store. Sized by editing NSIZE below. -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose

namespace F03LcaMin

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def NSIZE : Nat := 256

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

#eval show IO Unit from do
  let n := NSIZE
  let st := addrStore 5
  let l := leftSpine n
  let r := rightSpine n
  let b := balanced n
  let active : Bool := decide (canonicalBPRelativeMinMaxArgSummaryTableActive l)
  IO.println s!"n={n} bpLen={l.bpCode.length} summaryTableActive={active}"
  let lc := 1
  let rc := n
  let a1 := concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore l st lc rc
  IO.println s!"  leftSpine : len={a1.trace.length} value={a1.value}"
  let a2 := concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore r st lc rc
  IO.println s!"  rightSpine: len={a2.trace.length} value={a2.value}  identical={a1.trace == a2.trace && a1.value == a2.value}"
  let a3 := concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore b st lc rc
  IO.println s!"  balanced  : len={a3.trace.length} value={a3.value}  identical={a1.trace == a3.trace && a1.value == a3.value}"
  if a1.trace != a2.trace then
    let z := (a1.trace.zip a2.trace).findIdx? (fun p => p.1 != p.2)
    IO.println s!"  *** DIVERGENCE L vs R at {z}"
    match z with
    | some i =>
        IO.println s!"      L[{i}]={repr (a1.trace[i]?)}"
        IO.println s!"      R[{i}]={repr (a2.trace[i]?)}"
    | none => IO.println s!"      (prefix agrees; lengths differ)"
  if a1.trace != a3.trace then
    let z := (a1.trace.zip a3.trace).findIdx? (fun p => p.1 != p.2)
    IO.println s!"  *** DIVERGENCE L vs B at {z}"
    match z with
    | some i =>
        IO.println s!"      L[{i}]={repr (a1.trace[i]?)}"
        IO.println s!"      B[{i}]={repr (a3.trace[i]?)}"
    | none => IO.println s!"      (prefix agrees; lengths differ)"

end F03LcaMin
