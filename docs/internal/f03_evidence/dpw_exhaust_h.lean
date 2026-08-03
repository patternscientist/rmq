import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Exhaustive precision probe.

`allShapes k` enumerates EVERY `CartesianShape` of size `k` (Catalan many).
All of them share one `bpCode` length, `2 * k`.  So for a constant
`c : CartesianShape -> ... -> B`, the number of distinct values of
`c s args` as `s` ranges over `allShapes k` is a complete answer at that
size: 1 means the constant is size-only on all shapes of size `k`, more than
1 exhibits content dependence.

Exploratory only; the kernel-checked statements are in `dpw_kernel_f.lean`
and `dpw_kernel_i.lean`.
-/

namespace DPWExhaustH

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctFinal

/-- Structural on the fuel argument; `fuel > k` is enough because the
    recursion depth of a shape of size `k` is at most `k`. -/
def allShapesAux : Nat -> Nat -> List CartesianShape
  | 0, _ => []
  | _ + 1, 0 => [CartesianShape.empty]
  | fuel + 1, k + 1 =>
      (List.range (k + 1)).flatMap fun leftSize =>
        (allShapesAux fuel leftSize).flatMap fun l =>
          (allShapesAux fuel (k - leftSize)).map fun r =>
            CartesianShape.node l r

def allShapes (k : Nat) : List CartesianShape := allShapesAux (k + 1) k

#eval (allShapes 0).length
#eval (allShapes 1).length
#eval (allShapes 2).length
#eval (allShapes 3).length
#eval (allShapes 4).length
#eval (allShapes 5).length
#eval ((allShapes 5).map (fun s => s.size)).eraseDups
#eval ((allShapes 5).map (fun s => s.bpCode.length)).eraseDups
#eval ((allShapes 5).map (fun s => s.bpCode)).eraseDups.length

def distinct {a : Type} [BEq a] (xs : List a) : Nat := xs.eraseDups.length

/-! geometry candidates: how many distinct values over all shapes of size k -/

def geomReport (k : Nat) : List (String × Nat) :=
  let ss := allShapes k
  [ ("bpCode.length", distinct (ss.map fun s => s.bpCode.length))
  , ("builtRelativeSplitBPCloseRankWordSize",
      distinct (ss.map fun s => builtRelativeSplitBPCloseRankWordSize s))
  , ("builtRelativeSplitBPCloseRankBlocksPerSuper",
      distinct (ss.map fun s => builtRelativeSplitBPCloseRankBlocksPerSuper s))
  , ("builtRelativeSplitBPCloseRankBlockWidth",
      distinct (ss.map fun s => builtRelativeSplitBPCloseRankBlockWidth s))
  , ("builtRelativeSplitBPCloseRankSuperOverhead",
      distinct (ss.map fun s => builtRelativeSplitBPCloseRankSuperOverhead s))
  , ("builtRelativeSplitBPCloseRankBlockOverhead",
      distinct (ss.map fun s => builtRelativeSplitBPCloseRankBlockOverhead s))
  , ("canonicalRelativeRmmInteriorComponentOffsets",
      distinct (ss.map fun s => canonicalRelativeRmmInteriorComponentOffsets s))
  , ("localMachineStore.words.size",
      distinct (ss.map fun s => (canonicalRelativeRmmLocalMachineStore s).store.words.size))
  , ("globalMachineStore.words.size",
      distinct (ss.map fun s => (canonicalRelativeRmmGlobalMachineStore s).store.words.size))
  , ("summaryMachineStore.words.size",
      distinct (ss.map fun s => (canonicalRelativeRmmSummaryMachineStore s).store.words.size))
  , ("interiorComponentStore.words.size",
      distinct (ss.map fun s => (canonicalRelativeRmmInteriorComponentStore s).store.words.size))
  , ("localMachineStore.words",
      distinct (ss.map fun s => (canonicalRelativeRmmLocalMachineStore s).store.words))
  , ("globalMachineStore.words",
      distinct (ss.map fun s => (canonicalRelativeRmmGlobalMachineStore s).store.words))
  , ("summaryMachineStore.words",
      distinct (ss.map fun s => (canonicalRelativeRmmSummaryMachineStore s).store.words))
  , ("interiorComponentStore.words",
      distinct (ss.map fun s => (canonicalRelativeRmmInteriorComponentStore s).store.words))
  ]

#eval geomReport 3
#eval geomReport 4
#eval geomReport 5

/-! content candidates, for contrast, at the same sizes -/

def contentReport (k : Nat) : List (String × Nat) :=
  let ss := allShapes k
  [ ("bpExcessAt _ 2", distinct (ss.map fun s => bpExcessAt s 2))
  , ("bpBlockMinExcess _ 2 1", distinct (ss.map fun s => bpBlockMinExcess s 2 1))
  , ("bpBlockArgMinPrefixPos _ 4 1", distinct (ss.map fun s => bpBlockArgMinPrefixPos s 4 1))
  , ("bpRangeArgMinBlock _ 2 1 4", distinct (ss.map fun s => bpRangeArgMinBlock s 2 1 4))
  , ("bpSuperblockBaselineEntries _ 2 1 2",
      distinct (ss.map fun s => bpSuperblockBaselineEntries s 2 1 2))
  ]

#eval contentReport 4
#eval contentReport 5

end DPWExhaustH
