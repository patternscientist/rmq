import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Minimal small-size probe under the CANONICAL store.  `#eval` only. -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace KsmSeg4

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 => CartesianShape.node (leftSpine n) CartesianShape.empty

def go (n l r : Nat) : String :=
  let s := leftSpine n
  let st := concreteBPNativeSuccinctRMQGlobalReadStore s
  let res := concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r
  let fp := concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore s st l r
  let failed := (res.trace.filter (fun e => match e with
    | WordRAM.TraceEvent.readWord _ _ none => true | _ => false)).length
  s!"n={n} q=({l},{r}) traceLen={res.trace.length} failedReads={failed} value={res.value} segs={(fp.map Prod.fst)}"

#eval go 0 0 0
#eval go 1 0 1
#eval go 1 0 0
#eval go 2 0 2
#eval go 3 0 3
#eval go 4 0 4

end KsmSeg4
