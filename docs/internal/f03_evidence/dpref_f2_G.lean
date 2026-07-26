import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ATTACK 2 (real memory image, rank segments only).

`concreteBPCloseNavigationGlobalReadStore` (RMQ/Core/BPNavigationRAM.lean:816-887)
rebuilds every directory on EVERY probe, so it is unusable in the interpreter.
The four segments the L3 leaf reads are, verbatim from :822-824, :863-875:
  seg 17/18/19 := (builtRelativeSplitBPCloseRankData shape).rankRegisterWordRAMStore false
                    .readWord? 0/1/2 index
  seg 21       := (bpFringeChunkTable (bpFringeChunkBits shape.bpCode.length)).store.words[index]?
This file reconstructs exactly that, snapshots it, and swaps the free shape
argument against another shape of the same size.
-/

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian

namespace DPF2G

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

/-- The real image of the four rank segments, materialized. -/
def rankImage (s : CartesianShape) : Array (Array (Option (List Bool))) :=
  let rankStore := (builtRelativeSplitBPCloseRankData s).rankRegisterWordRAMStore false
  let chunk :=
    SuccinctClose.bpFringeChunkTable (SuccinctClose.bpFringeChunkBits s.bpCode.length)
  let idxs := List.range 48
  #[ (idxs.map (fun i => rankStore.readWord? 0 i)).toArray,
     (idxs.map (fun i => rankStore.readWord? 1 i)).toArray,
     (idxs.map (fun i => rankStore.readWord? 2 i)).toArray,
     (idxs.map (fun i => chunk.store.words[i]?)).toArray ]

def storeOf (img : Array (Array (Option (List Bool)))) : WordRAM.ReadStore where
  readWord? seg i :=
    let row? :=
      if seg = 17 then img[0]? else if seg = 18 then img[1]?
      else if seg = 19 then img[2]? else if seg = 21 then img[3]? else none
    match row? with
    | none => none
    | some row => match row[i]? with
      | none => none
      | some w => w

def leafSig (s : CartesianShape) (st : WordRAM.ReadStore) (pos : Nat) :
    Nat × List WordRAM.TraceEvent :=
  let t := concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s st 17 pos
  (t.value, t.trace)

/-- Fidelity: the reconstructed image agrees with the live global store. -/
def fidelity (n : Nat) : Nat :=
  (lb (shapes n) (fun s =>
    let real := BPNavigation.concreteBPCloseNavigationGlobalReadStore s
    let sn := storeOf (rankImage s)
    lb (List.range (2 * n + 4)) (fun p =>
      if decide (leafSig s sn p = leafSig s real p) then [] else [(1 : Nat)]))).length

#eval (fidelity 1, fidelity 2, fidelity 3)

/-- THE SWAP: run the leaf on `b`'s real memory image but hand it `a` as the
free shape argument. -/
def swapL3 (n : Nat) : Nat × Nat :=
  let ss := shapes n
  let ps := List.range (2 * n + 4)
  let bad := lb ss (fun b =>
    let st := storeOf (rankImage b)
    lb ss (fun a =>
      lb ps (fun p =>
        if decide (leafSig a st p = leafSig b st p) then [] else [(1 : Nat)])))
  (ss.length * ss.length * ps.length, bad.length)

#eval swapL3 1
#eval swapL3 2
#eval swapL3 3
#eval swapL3 4
#eval swapL3 5

/-! ANTI-VACUITY of the swap: with each shape's OWN real image the leaf's answer
genuinely varies across same-size shapes, so the swap is not comparing
constants -- the information arrives through the probes, not the argument. -/

#eval ((shapes 4).map (fun s => (leafSig s (storeOf (rankImage s)) 5).1)).eraseDups
#eval ((shapes 5).map (fun s => (leafSig s (storeOf (rankImage s)) 7).1)).eraseDups
#eval ((shapes 5).map (fun s =>
    (List.range 11).map (fun p => (leafSig s (storeOf (rankImage s)) p).1))).eraseDups.length
-- and the images themselves are distinct across same-size shapes
#eval ((shapes 5).map (fun s => rankImage s)).eraseDups.length

end DPF2G
