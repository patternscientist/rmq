import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Segment-20 threshold + failed-read localisation, canonical store.  `#eval` only. -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace KsmSeg5

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 => CartesianShape.node (leftSpine n) CartesianShape.empty

def dedup (l : List Nat) : List Nat :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def go (n l r : Nat) : String :=
  let s := leftSpine n
  let st := concreteBPNativeSuccinctRMQGlobalReadStore s
  let res := concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r
  let failedSegs := res.trace.filterMap (fun e => match e with
    | WordRAM.TraceEvent.readWord seg idx none => some (seg, idx) | _ => none)
  let fp := concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore s st l r
  s!"n={n} q=({l},{r}) len={res.trace.length} val={res.value} segs={(dedup (fp.map Prod.fst)).mergeSort (fun a b => a <= b)} FAILED={failedSegs}"

#eval go 21 0 21
#eval go 24 0 24
#eval go 28 0 28
#eval go 32 0 32
#eval go 36 0 36
