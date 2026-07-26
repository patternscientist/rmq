import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
The remaining untested controller leaf: L2, LCA-close.

  `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
     shape store leftClose rightClose`

L2 drives the relative-RMM interior/summary machinery -- the very machinery that
`canonicalBPRelativeMinMaxArgSummaryTableActive` switches ON between n=384 and
n=512. Leaves L1 (select) and L3 (rank) have already held identical traces and
values across maximally different same-size bit distributions at
n = 8, 64, 128, 256, 512. L2 in the ACTIVE regime is the untested case that
matters most.

n=384 is the inactive control; n=512 and n=640 are treatment.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose

namespace F03Lca

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

partial def pseudo (seed : Nat) : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      .node (pseudo (seed + 7) k) (pseudo (seed + 13) (n - k))

def addrStore (salt : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 24).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)

def lcaLeaf (s : CartesianShape) (st : WordRAM.ReadStore) (lc rc : Nat) :=
  concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore s st lc rc

#eval show IO Unit from do
  let st := addrStore 5
  let mut cmps := 0
  let mut divs := 0
  for n in [384, 512, 640] do
    let named : List (String × CartesianShape) :=
      [ ("leftSpine", leftSpine n)
      , ("rightSpine", rightSpine n)
      , ("balanced", balanced n)
      , ("pseudo1", pseudo 1 n) ]
    let (bn, b) := named.head!
    let active : Bool := decide (canonicalBPRelativeMinMaxArgSummaryTableActive b)
    IO.println s!"--- n={n} bpLen={b.bpCode.length} summaryTableActive={active}"
    for (lc, rc) in [(0, 2 * n - 1), (1, n), (n / 2, n + n / 2), (2, 5)] do
      let br := lcaLeaf b st lc rc
      IO.println s!"  LCA lc={lc} rc={rc}: base {bn} traceLen={br.trace.length} value={br.value}"
      for (nm, s) in named.tail! do
        cmps := cmps + 1
        let x := lcaLeaf s st lc rc
        if x.trace != br.trace || x.value != br.value then
          divs := divs + 1
          IO.println s!"    *** LCA DIVERGENCE vs {nm}: traceLen={x.trace.length} value={x.value}"
          let z := (br.trace.zip x.trace).findIdx? (fun p => p.1 != p.2)
          IO.println s!"        firstDifferingIndex={z}"
          match z with
          | some i =>
              IO.println s!"        base[{i}]={repr (br.trace[i]?)}"
              IO.println s!"        this[{i}]={repr (x.trace[i]?)}"
          | none => IO.println s!"        (prefix agrees; lengths differ)"
        else
          IO.println s!"    ok {nm}: identical ({x.trace.length} events, value={x.value})"
  IO.println s!"F03-LCA-LEAF comparisons={cmps} divergences={divs}"

end F03Lca
