import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! EG-CP-F01 small-size SEGMENT scan, trimmed.  Exploratory `#eval` only. -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace KsmSeg2

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 => CartesianShape.node (leftSpine n) CartesianShape.empty

def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 => CartesianShape.node CartesianShape.empty (rightSpine n)

def addrStore (k : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 16).map fun j => ((seg * 7 + idx * 13 + j * 5 + k) % 3 == 0))

def footprint (shape : CartesianShape) (l r : Nat) : List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
    shape (addrStore 3) l r

def traceLen (shape : CartesianShape) (l r : Nat) : Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    shape (addrStore 3) l r).trace.length

def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range (n + 1)).flatMap (fun l => (List.range (n + 1 - l)).map (fun d => (l, l + d)))

def segsOf (shape : CartesianShape) : List Nat :=
  ((pairs shape.size).flatMap
    (fun p => (footprint shape p.1 p.2).map Prod.fst)).eliminateDuplicates.mergeSort
      (fun a b => a <= b)

def segsAt (n : Nat) : List Nat :=
  ([leftSpine n, rightSpine n].flatMap segsOf).eliminateDuplicates.mergeSort (fun a b => a <= b)

#eval (List.range 14).map (fun n => (n, segsAt n))

#eval s!"n=0 footprint (0,0): {footprint (leftSpine 0) 0 0}"
#eval s!"n=0 trace length: {traceLen (leftSpine 0) 0 0}"
#eval s!"n=0 value: {(concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore (leftSpine 0) (addrStore 3) 0 0).value}"
#eval s!"n=1 footprints: {(pairs 1).map (fun p => (p, footprint (leftSpine 1) p.1 p.2))}"
#eval s!"n=1 values: {(pairs 1).map (fun p => (p, (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore (leftSpine 1) (addrStore 3) p.1 p.2).value))}"
#eval s!"max trace len per n: {(List.range 14).map (fun n => (n, ((pairs n).map (fun p => traceLen (leftSpine n) p.1 p.2)).foldl max 0))}"

end KsmSeg2
