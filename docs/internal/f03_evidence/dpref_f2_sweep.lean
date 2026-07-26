import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import RMQ.Core.SuccinctRMQClassic

/-!
ADVERSARIAL REFUTATION SWEEP for the verdict
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData` = S (size-only)

Attack: find two Cartesian shapes of the SAME size on which the controller leaf
L3 (`concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore`) differs in
value or in trace.

Exhaustive over ALL shapes of each size 1..6 (Catalan 1,2,5,14,42,132), over
five adversarial read stores (constant, index-keyed, ragged word lengths,
partial `none`, everywhere-`none`), over several segment bases, over every
position 0..2n+3.
-/

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian

namespace DPF2

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

/-! ## Adversarial stores -/

def storeConst : WordRAM.ReadStore where
  readWord? _ _ := some [true, false, true, true, false, false, true, false]

def storeKeyed : WordRAM.ReadStore where
  readWord? seg i :=
    some ((List.range 8).map (fun j => decide ((seg * 13 + i * 7 + j * 5) % 3 = 0)))

/-- Ragged: word LENGTH varies with the address (attacks the chunk fold count). -/
def storeRagged : WordRAM.ReadStore where
  readWord? seg i :=
    some (List.replicate ((seg * 3 + i * 5) % 11 + 1)
      (decide ((seg + i) % 2 = 0)))

/-- Partial: some addresses are absent (attacks the `| _,_,_ => pure 0` branch). -/
def storeSparse : WordRAM.ReadStore where
  readWord? seg i :=
    if (seg + i) % 4 = 3 then none
    else some (List.replicate (i % 5 + 1) (decide (i % 2 = 0)))

def storeNone : WordRAM.ReadStore where
  readWord? _ _ := none

def stores : List (String × WordRAM.ReadStore) :=
  [("const", storeConst), ("keyed", storeKeyed), ("ragged", storeRagged),
   ("sparse", storeSparse), ("none", storeNone)]

def bases : List Nat := [17, 0, 3, 40]

def sigOf (t : WordRAM.TraceResult Nat) : Nat × List WordRAM.TraceEvent :=
  (t.value, t.trace)

def leafSig (s : CartesianShape) (st : WordRAM.ReadStore) (base pos : Nat) :
    Nat × List WordRAM.TraceEvent :=
  sigOf (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s st base pos)

/-- Number of (store, base, pos) cells at which the shapes of size `n` do NOT
all produce the identical leaf signature, plus a witness cell. -/
def divergentCells (n : Nat) : List (String × Nat × Nat) :=
  let ss := shapes n
  lb stores (fun sp =>
    lb bases (fun b =>
      lb (List.range (2 * n + 4)) (fun p =>
        match ss with
        | [] => []
        | s0 :: rest =>
            let ref := leafSig s0 sp.2 b p
            if rest.all (fun s => decide (leafSig s sp.2 b p = ref)) then []
            else [(sp.1, b, p)])))

/-- Total leaf evaluations performed per size (for anti-vacuity of the sweep). -/
def cellsPerSize (n : Nat) : Nat :=
  (shapes n).length * stores.length * bases.length * (2 * n + 4)

/-! ## Attack 1: exhaustive same-size divergence hunt, shape-free stores -/

#eval (cellsPerSize 1, (divergentCells 1).length)
#eval (cellsPerSize 2, (divergentCells 2).length)
#eval (cellsPerSize 3, (divergentCells 3).length)
#eval (cellsPerSize 4, (divergentCells 4).length)
#eval (cellsPerSize 5, (divergentCells 5).length)
#eval (cellsPerSize 6, (divergentCells 6).length)

/-! ## Attack 2: the REAL per-shape memory image, shape argument swapped.

For shapes `a b` of the same size, run the leaf with `b`'s real memory image but
`a` supplied as the free shape argument, and compare against the honest run
`b, b`. If the free shape argument carried any information beyond `size`, the
swap would show up here. -/

def realStore (s : CartesianShape) : WordRAM.ReadStore :=
  concreteBPNativeSuccinctRMQGlobalReadStore s

def swapDivergences (n : Nat) : Nat :=
  let ss := shapes n
  (lb ss (fun b =>
    lb ss (fun a =>
      lb (List.range (2 * n + 4)) (fun p =>
        if decide (leafSig a (realStore b) 17 p = leafSig b (realStore b) 17 p)
        then [] else [(1 : Nat)])))).length

def swapCells (n : Nat) : Nat :=
  (shapes n).length * (shapes n).length * (2 * n + 4)

#eval (swapCells 1, swapDivergences 1)
#eval (swapCells 2, swapDivergences 2)
#eval (swapCells 3, swapDivergences 3)
#eval (swapCells 4, swapDivergences 4)
#eval (swapCells 5, swapDivergences 5)

/-! ## Attack 3: anti-vacuity of the sweep.

The leaf must actually MOVE with the real store, otherwise attacks 1-2 are
comparing constants. -/

-- distinct values across distinct shapes of the same size, with their OWN stores
#eval ((shapes 5).map (fun s => (leafSig s (realStore s) 17 7).1)).eraseDups.length
#eval ((shapes 5).map (fun s => (leafSig s (realStore s) 17 7).2.length)).eraseDups
-- and the address stream really does move with pos
#eval ((List.range 12).map (fun p =>
    (leafSig (List.headD (shapes 5) CartesianShape.empty) storeConst 17 p).1))

/-! ## Attack 4: geometry constants per shape -- constant within a size? -/

def geom (s : CartesianShape) : Nat × Nat × Nat × Nat × Nat :=
  ((builtRelativeSplitBPCloseRankData s).wordSize,
   (builtRelativeSplitBPCloseRankData s).blocksPerSuper,
   (builtRelativeSplitBPCloseRankData s).superWidth,
   (builtRelativeSplitBPCloseRankData s).blockWidth,
   SuccinctClose.bpFringeChunkBits s.bpCode.length)

#eval ((shapes 3).map geom).eraseDups
#eval ((shapes 4).map geom).eraseDups
#eval ((shapes 5).map geom).eraseDups
#eval ((shapes 6).map geom).eraseDups

/-! ## Attack 5: does anything ELSE in the whole-query controller leak shape?

Same swap experiment, but on the whole store-parametric controller root. This is
outside the F2 row, but if it FAILS then F2's S verdict does not by itself close
F03 -- and if it PASSES it is strong corroboration. -/

def wholeSig (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :
    Option Nat × List WordRAM.TraceEvent :=
  let t := concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r
  (t.value, t.trace)

def wholeSwapDivergences (n : Nat) : Nat :=
  let ss := shapes n
  (lb ss (fun b =>
    lb ss (fun a =>
      lb (List.range (n + 1)) (fun l =>
        lb (List.range (n + 1)) (fun r =>
          if decide (wholeSig a (realStore b) l r = wholeSig b (realStore b) l r)
          then [] else [(1 : Nat)]))))).length

def wholeSwapCells (n : Nat) : Nat :=
  (shapes n).length * (shapes n).length * (n + 1) * (n + 1)

#eval (wholeSwapCells 2, wholeSwapDivergences 2)
#eval (wholeSwapCells 3, wholeSwapDivergences 3)
#eval (wholeSwapCells 4, wholeSwapDivergences 4)

end DPF2
