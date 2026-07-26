import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ATTACK 2/5: the REAL per-shape memory image, with the free shape argument
SWAPPED to a different shape of the same size.

`snap s` materializes `concreteBPNativeSuccinctRMQGlobalReadStore s` into a
finite table (segments 0..25, indices 0..127) so lookups are O(1); fidelity of
the snapshot is checked first.
-/

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian

namespace DPF2B

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

def snap (s : CartesianShape) : WordRAM.ReadStore :=
  let st := concreteBPNativeSuccinctRMQGlobalReadStore s
  let tbl : Array (Array (Option (List Bool))) :=
    ((List.range 26).map (fun seg =>
      ((List.range 128).map (fun i => st.readWord? seg i)).toArray)).toArray
  { readWord? := fun seg i =>
      match tbl[seg]? with
      | none => none
      | some row =>
          match row[i]? with
          | none => none
          | some w => w }

def leafSig (s : CartesianShape) (st : WordRAM.ReadStore) (base pos : Nat) :
    Nat × List WordRAM.TraceEvent :=
  let t := concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s st base pos
  (t.value, t.trace)

/-! snapshot fidelity -/

def fidelity (n : Nat) : Nat :=
  (lb (shapes n) (fun s =>
    let real := concreteBPNativeSuccinctRMQGlobalReadStore s
    let sn := snap s
    lb (List.range (2 * n + 4)) (fun p =>
      if decide (leafSig s sn 17 p = leafSig s real 17 p) then [] else [(1 : Nat)]))).length

#eval (fidelity 1, fidelity 2, fidelity 3, fidelity 4)

/-! ## ATTACK 2: shape-argument swap against the real memory image -/

def swapDiv (n : Nat) : Nat × Nat :=
  let ss := shapes n
  let ps := List.range (2 * n + 4)
  let bad :=
    lb ss (fun b =>
      let st := snap b
      lb ss (fun a =>
        lb ps (fun p =>
          if decide (leafSig a st 17 p = leafSig b st 17 p) then [] else [(1 : Nat)])))
  (ss.length * ss.length * ps.length, bad.length)

#eval swapDiv 1
#eval swapDiv 2
#eval swapDiv 3
#eval swapDiv 4
#eval swapDiv 5

/-! anti-vacuity of ATTACK 2: with each shape's OWN real image the leaf value
really does depend on the shape (so the swap is not comparing constants). -/

#eval ((shapes 4).map (fun s => (leafSig s (snap s) 17 5).1)).eraseDups
#eval ((shapes 5).map (fun s => (leafSig s (snap s) 17 7).1)).eraseDups
#eval ((shapes 5).map (fun s => (leafSig s (snap s) 17 9).1)).eraseDups.length

/-! ## ATTACK 5: same swap on the WHOLE store-parametric controller.

Outside the F2 row, but decides whether F2's verdict alone closes F03. -/

def wholeSig (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :
    Option Nat × List WordRAM.TraceEvent :=
  let t := concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r
  (t.value, t.trace)

def wholeSwap (n : Nat) : Nat × Nat :=
  let ss := shapes n
  let lrs := lb (List.range (n + 1)) (fun l => (List.range (n + 1)).map (fun r => (l, r)))
  let bad :=
    lb ss (fun b =>
      let st := snap b
      lb ss (fun a =>
        lb lrs (fun lr =>
          if decide (wholeSig a st lr.1 lr.2 = wholeSig b st lr.1 lr.2) then []
          else [(1 : Nat)])))
  (ss.length * ss.length * lrs.length, bad.length)

#eval wholeSwap 2
#eval wholeSwap 3
#eval wholeSwap 4

end DPF2B
