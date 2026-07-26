import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ATTACK 1/3/4: exhaustive same-size divergence hunt for leaf L3 under
shape-FREE adversarial stores, plus geometry constants.
-/

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian

namespace DPF2A

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

def storeConst : WordRAM.ReadStore where
  readWord? _ _ := some [true, false, true, true, false, false, true, false]

def storeKeyed : WordRAM.ReadStore where
  readWord? seg i :=
    some ((List.range 8).map (fun j => decide ((seg * 13 + i * 7 + j * 5) % 3 = 0)))

def storeRagged : WordRAM.ReadStore where
  readWord? seg i :=
    some (List.replicate ((seg * 3 + i * 5) % 11 + 1)
      (decide ((seg + i) % 2 = 0)))

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

def leafSig (s : CartesianShape) (st : WordRAM.ReadStore) (base pos : Nat) :
    Nat × List WordRAM.TraceEvent :=
  let t := concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s st base pos
  (t.value, t.trace)

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

def cellsPerSize (n : Nat) : Nat :=
  (shapes n).length * stores.length * bases.length * (2 * n + 4)

-- (leaf evaluations, divergent cells)
#eval (cellsPerSize 1, (divergentCells 1).length)
#eval (cellsPerSize 2, (divergentCells 2).length)
#eval (cellsPerSize 3, (divergentCells 3).length)
#eval (cellsPerSize 4, (divergentCells 4).length)
#eval (cellsPerSize 5, (divergentCells 5).length)
#eval (cellsPerSize 6, (divergentCells 6).length)

/-! anti-vacuity: the leaf is not a constant over the swept cells -/

#eval ((List.range 14).map (fun p =>
    (leafSig (List.headD (shapes 5) CartesianShape.empty) storeConst 17 p).1)).eraseDups
#eval ((List.range 14).map (fun p =>
    (leafSig (List.headD (shapes 5) CartesianShape.empty) storeConst 17 p).2.length)).eraseDups
#eval (stores.map (fun sp =>
    (leafSig (List.headD (shapes 5) CartesianShape.empty) sp.2 17 7).1))
#eval (bases.map (fun b =>
    (leafSig (List.headD (shapes 5) CartesianShape.empty) storeKeyed b 7 7).1))
-- sizes really do change the trace
#eval ([1,2,3,4,5,6].map (fun n =>
    (leafSig (List.headD (shapes n) CartesianShape.empty) storeKeyed 17 7).2.length))

/-! geometry constants: constant across all shapes of a size? -/

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

/-! but the CONTENTS of the built structure do vary within a size -/

#eval ((shapes 5).map (fun s =>
    (builtRelativeSplitBPCloseRankData s).blockTrueEntries)).eraseDups.length
#eval ((shapes 5).map (fun s =>
    (builtRelativeSplitBPCloseRankData s).superTrueEntries)).eraseDups.length
#eval ((shapes 5).map (fun s =>
    (builtRelativeSplitBPCloseRankData s).bitWords.store.words.toList)).eraseDups.length

end DPF2A
