import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
EG-CP-F01 small-size SEGMENT scan (exploratory `#eval` only).
Which logical segments does the executed controller touch at each small `n`?
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace KsmSeg

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 => CartesianShape.node (leftSpine n) CartesianShape.empty

def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 =>
      CartesianShape.node (balanced ((n + 1) / 2)) (balanced (n - (n + 1) / 2))
decreasing_by all_goals omega

def zig : Bool -> Nat -> CartesianShape
  | _, 0 => CartesianShape.empty
  | true, n + 1 => CartesianShape.node (zig false n) CartesianShape.empty
  | false, n + 1 => CartesianShape.node CartesianShape.empty (zig true n)

def addrStore (k : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 16).map fun j => ((seg * 7 + idx * 13 + j * 5 + k) % 3 == 0))

def footprint (shape : CartesianShape) (store : WordRAM.ReadStore) (l r : Nat) :
    List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore shape store l r

def fullTrace (shape : CartesianShape) (store : WordRAM.ReadStore) (l r : Nat) :
    List WordRAM.TraceEvent :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    shape store l r).trace

/-- every segment touched over every valid query, for one shape -/
def segsOf (shape : CartesianShape) (store : WordRAM.ReadStore) : List Nat :=
  let n := shape.size
  let pairs := (List.range (n + 1)).flatMap (fun l =>
    (List.range (n + 1 - l)).map (fun d => (l, l + d)))
  let segs := pairs.flatMap (fun p => (footprint shape store p.1 p.2).map Prod.fst)
  segs.eliminateDuplicates.mergeSort (fun a b => a <= b)

def fam (n : Nat) : List CartesianShape :=
  [leftSpine n, balanced n, zig true n, zig false n]

def segsAt (n : Nat) : List Nat :=
  ((fam n).flatMap (fun s => segsOf s (addrStore 3))).eliminateDuplicates.mergeSort
    (fun a b => a <= b)

#eval (List.range 26).map (fun n => (n, segsAt n))

#eval s!"n=0 footprints: {(footprint (leftSpine 0) (addrStore 3) 0 0)}"
#eval s!"n=1 footprints (0,0),(0,1),(1,1): {(footprint (leftSpine 1) (addrStore 3) 0 0, footprint (leftSpine 1) (addrStore 3) 0 1, footprint (leftSpine 1) (addrStore 3) 1 1)}"
#eval s!"n=0 full trace: {(fullTrace (leftSpine 0) (addrStore 3) 0 0).length}"
#eval s!"n=0 value: {(concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore (leftSpine 0) (addrStore 3) 0 0).value}"
#eval s!"n=1 value (0,1): {(concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore (leftSpine 1) (addrStore 3) 0 1).value}"

/-- max trace length over all valid queries, per n -/
def maxTrace (n : Nat) : Nat :=
  ((fam n).flatMap (fun s =>
    let pairs := (List.range (s.size + 1)).flatMap (fun l =>
      (List.range (s.size + 1 - l)).map (fun d => (l, l + d)))
    pairs.map (fun p => (fullTrace s (addrStore 3) p.1 p.2).length))).foldl max 0

#eval (List.range 26).map (fun n => (n, maxTrace n))

end KsmSeg
