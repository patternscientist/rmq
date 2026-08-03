import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! EG-CP-F01 small-size SEGMENT scan under the CANONICAL store.  `#eval` only. -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace KsmSeg3

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def dedup : List Nat -> List Nat
  | [] => []
  | x :: xs => x :: dedup (xs.filter (fun y => y != x))

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 => CartesianShape.node (leftSpine n) CartesianShape.empty

def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 => CartesianShape.node CartesianShape.empty (rightSpine n)

def store (s : CartesianShape) : WordRAM.ReadStore :=
  concreteBPNativeSuccinctRMQGlobalReadStore s

def res (s : CartesianShape) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s (store s) l r

def footprint (s : CartesianShape) (l r : Nat) : List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore s (store s) l r

def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range (n + 1)).flatMap (fun l => (List.range (n + 1 - l)).map (fun d => (l, l + d)))

def segsOf (s : CartesianShape) : List Nat :=
  (dedup ((pairs s.size).flatMap (fun p => (footprint s p.1 p.2).map Prod.fst))).mergeSort
    (fun a b => a <= b)

def segsAt (n : Nat) : List Nat :=
  (dedup ([leftSpine n, rightSpine n].flatMap segsOf)).mergeSort (fun a b => a <= b)

/-- how many trace events are FAILED reads (reply `none`) -/
def failedReads (s : CartesianShape) (l r : Nat) : Nat :=
  ((res s l r).trace.filter (fun e => match e with
    | WordRAM.TraceEvent.readWord _ _ none => true
    | _ => false)).length

#eval s!"segments touched, per n: {(List.range 16).map (fun n => (n, segsAt n))}"
#eval s!"max trace len per n: {(List.range 16).map (fun n => (n, ((pairs n).flatMap (fun p => [(res (leftSpine n) p.1 p.2).trace.length, (res (rightSpine n) p.1 p.2).trace.length])).foldl max 0))}"
#eval s!"total failed reads per n: {(List.range 16).map (fun n => (n, ((pairs n).map (fun p => failedReads (leftSpine n) p.1 p.2)).foldl (·+·) 0))}"
#eval s!"max index per segment, n=1..12 (leftSpine): {(List.range' 1 12).map (fun n => (n, (dedup ((pairs n).flatMap (fun p => (footprint (leftSpine n) p.1 p.2).map (fun q => q.2)))).foldl max 0))}"
#eval s!"n=0: trace {(res (leftSpine 0) 0 0).trace.length}, value {(res (leftSpine 0) 0 0).value}"
#eval s!"n=1 footprints: {(pairs 1).map (fun p => (p, footprint (leftSpine 1) p.1 p.2))}"
#eval s!"n=1 values: {(pairs 1).map (fun p => (p, (res (leftSpine 1) p.1 p.2).value))}"
#eval s!"n=2 values: {(pairs 2).map (fun p => (p, (res (leftSpine 2) p.1 p.2).value))}"

end KsmSeg3
