import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ATTACK 2 (cheap): the REAL per-shape memory image with the free shape argument
SWAPPED, for the L3 leaf and for the whole store-parametric controller.
Snapshot is restricted to segments 0..25, indices 0..47.
-/

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian

namespace DPF2F

def lb {a b : Type} (l : List a) (f : a -> List b) : List b :=
  l.foldr (fun x acc => f x ++ acc) []

def shapesF : Nat -> Nat -> List CartesianShape
  | 0, _ => []
  | _ + 1, 0 => [CartesianShape.empty]
  | f + 1, n + 1 =>
      lb (List.range (n + 1)) (fun k =>
        lb (shapesF f k) (fun l =>
          (shapesF f (n - k)).map (fun r => CartesianShape.node l r)))

def shapes (n : Nat) : List CartesianShape := shapesF (n + 1) n

def snapTbl (s : CartesianShape) : Array (Array (Option (List Bool))) :=
  let st := concreteBPNativeSuccinctRMQGlobalReadStore s
  ((List.range 26).map (fun seg =>
    ((List.range 48).map (fun i => st.readWord? seg i)).toArray)).toArray

def ofTbl (tbl : Array (Array (Option (List Bool)))) : WordRAM.ReadStore where
  readWord? seg i :=
    match tbl[seg]? with
    | none => none
    | some row => match row[i]? with
      | none => none
      | some w => w

def leafSig (s : CartesianShape) (st : WordRAM.ReadStore) (base pos : Nat) :
    Nat × List WordRAM.TraceEvent :=
  let t := concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s st base pos
  (t.value, t.trace)

def wholeSig (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :
    Option Nat × List WordRAM.TraceEvent :=
  let t := concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r
  (t.value, t.trace)

/-- fidelity of the snapshot against the live store, for the leaf -/
def fidelity (n : Nat) : Nat :=
  (lb (shapes n) (fun s =>
    let real := concreteBPNativeSuccinctRMQGlobalReadStore s
    let sn := ofTbl (snapTbl s)
    lb (List.range (2 * n + 4)) (fun p =>
      if decide (leafSig s sn 17 p = leafSig s real 17 p) then [] else [(1 : Nat)]))).length

#eval (fidelity 2, fidelity 3)

/-- L3 swap on the real image -/
def swapL3 (n : Nat) : Nat × Nat :=
  let ss := shapes n
  let ps := List.range (2 * n + 4)
  let bad := lb ss (fun b =>
    let st := ofTbl (snapTbl b)
    lb ss (fun a =>
      lb ps (fun p =>
        if decide (leafSig a st 17 p = leafSig b st 17 p) then [] else [(1 : Nat)])))
  (ss.length * ss.length * ps.length, bad.length)

#eval swapL3 2
#eval swapL3 3
#eval swapL3 4

/-- anti-vacuity: with each shape's OWN image the leaf value varies by shape -/
#eval ((shapes 4).map (fun s => (leafSig s (ofTbl (snapTbl s)) 17 5).1)).eraseDups
#eval ((shapes 4).map (fun s => (leafSig s (ofTbl (snapTbl s)) 17 7).1)).eraseDups

/-- whole-controller swap on the real image (OUTSIDE the F2 row) -/
def swapWhole (n : Nat) : Nat × Nat :=
  let ss := shapes n
  let lrs := lb (List.range (n + 1)) (fun l => (List.range (n + 1)).map (fun r => (l, r)))
  let bad := lb ss (fun b =>
    let st := ofTbl (snapTbl b)
    lb ss (fun a =>
      lb lrs (fun lr =>
        if decide (wholeSig a st lr.1 lr.2 = wholeSig b st lr.1 lr.2) then []
        else [(1 : Nat)])))
  (ss.length * ss.length * lrs.length, bad.length)

#eval swapWhole 2
#eval swapWhole 3

end DPF2F
