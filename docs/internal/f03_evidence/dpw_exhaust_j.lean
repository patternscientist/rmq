import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Exhaustive precision probe, part two.

(1) Bigger sizes for the local/global canonical machine stores, which were
    degenerate at size <= 5.
(2) Read FOOTPRINTS of the `FlatStoreComputation`-valued taint candidates.
    For a FIXED supplied store, the footprint is the address sequence the
    interior directory issues.  Counting distinct footprints over ALL shapes
    of one size answers the F03 question for those constants directly: 1
    means every address is determined by `n` and the arguments.
-/

namespace DPWExhaustJ

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctFinal RMQ.SuccinctSpace

def allShapesAux : Nat -> Nat -> List CartesianShape
  | 0, _ => []
  | _ + 1, 0 => [CartesianShape.empty]
  | fuel + 1, k + 1 =>
      (List.range (k + 1)).flatMap fun leftSize =>
        (allShapesAux fuel leftSize).flatMap fun l =>
          (allShapesAux fuel (k - leftSize)).map fun r =>
            CartesianShape.node l r

def allShapes (k : Nat) : List CartesianShape := allShapesAux (k + 1) k

def distinct {a : Type} [BEq a] (xs : List a) : Nat := xs.eraseDups.length

/-! ## (1) canonical local/global stores at larger sizes -/

def storeReport (k : Nat) : List (String × Nat) :=
  let ss := allShapes k
  [ ("shapes", ss.length)
  , ("localMachineStore.words.size",
      distinct (ss.map fun s => (canonicalRelativeRmmLocalMachineStore s).store.words.size))
  , ("localMachineStore.words",
      distinct (ss.map fun s => (canonicalRelativeRmmLocalMachineStore s).store.words))
  , ("globalMachineStore.words.size",
      distinct (ss.map fun s => (canonicalRelativeRmmGlobalMachineStore s).store.words.size))
  , ("globalMachineStore.words",
      distinct (ss.map fun s => (canonicalRelativeRmmGlobalMachineStore s).store.words))
  , ("summaryMachineStore.words.size",
      distinct (ss.map fun s => (canonicalRelativeRmmSummaryMachineStore s).store.words.size))
  , ("summaryMachineStore.words",
      distinct (ss.map fun s => (canonicalRelativeRmmSummaryMachineStore s).store.words))
  , ("interiorComponentStore.words.size",
      distinct (ss.map fun s => (canonicalRelativeRmmInteriorComponentStore s).store.words.size))
  , ("interiorComponentStore.words",
      distinct (ss.map fun s => (canonicalRelativeRmmInteriorComponentStore s).store.words))
  , ("interiorComponentOffsets",
      distinct (ss.map fun s => canonicalRelativeRmmInteriorComponentOffsets s))
  , ("rankSuperOverhead",
      distinct (ss.map fun s => builtRelativeSplitBPCloseRankSuperOverhead s))
  , ("rankBlockOverhead",
      distinct (ss.map fun s => builtRelativeSplitBPCloseRankBlockOverhead s))
  ]

#eval storeReport 6
#eval storeReport 7

/-! ## (2) footprints of the FlatStoreComputation candidates -/

/-- Two fixed supplied stores.  Neither depends on the shape. -/
def store0 : FlatWordStore := fun _ => none
def store1 : FlatWordStore := fun a => some (List.replicate 8 (a % 3 == 0))

def fp {alpha : Type} (c : FlatStoreComputation alpha) (st : FlatWordStore) : List Nat :=
  (c.run st).footprint

def compReport (k : Nat) (st : FlatWordStore) : List (String × Nat) :=
  let ss := allShapes k
  [ ("shapes", ss.length)
  , ("summaryComputation 0",
      distinct (ss.map fun s => fp (canonicalRelativeRmmMachineSummaryComputation s 0) st))
  , ("summaryComputation 1",
      distinct (ss.map fun s => fp (canonicalRelativeRmmMachineSummaryComputation s 1) st))
  , ("minCandidate 1",
      distinct (ss.map fun s => fp (canonicalRelativeRmmMachineMinCandidateComputation s 1) st))
  , ("localSpanCandidate 0 0 1",
      distinct (ss.map fun s =>
        fp (canonicalRelativeRmmMachineLocalSpanCandidateComputation s 0 0 1) st))
  , ("globalSpanCandidate 0 1",
      distinct (ss.map fun s =>
        fp (canonicalRelativeRmmMachineGlobalSpanCandidateComputation s 0 1) st))
  , ("localTwoSpanCandidate 0 0 2",
      distinct (ss.map fun s =>
        fp (canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation s 0 0 2) st))
  , ("globalTwoSpanCandidate 0 2",
      distinct (ss.map fun s =>
        fp (canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation s 0 2) st))
  , ("adjacentMacroCandidate 0 0 1",
      distinct (ss.map fun s =>
        fp (canonicalRelativeRmmMachineAdjacentMacroCandidateComputation s 0 0 1) st))
  , ("leftMiddleMacroCandidate 0 0 1",
      distinct (ss.map fun s =>
        fp (canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation s 0 0 1) st))
  , ("crossMacroCandidate 0 0 1 1",
      distinct (ss.map fun s =>
        fp (canonicalRelativeRmmMachineCrossMacroCandidateComputation s 0 0 1 1) st))
  , ("interiorRangeMin 0 2",
      distinct (ss.map fun s => fp (canonicalRelativeRmmInteriorRangeMinComputation s 0 2) st))
  , ("interiorRangeMin 1 3",
      distinct (ss.map fun s => fp (canonicalRelativeRmmInteriorRangeMinComputation s 1 3) st))
  , ("interiorRangeMin 2 5",
      distinct (ss.map fun s => fp (canonicalRelativeRmmInteriorRangeMinComputation s 2 5) st))
  ]

#eval compReport 5 store0
#eval compReport 5 store1
#eval compReport 6 store1
#eval compReport 7 store1

/-! and the VALUES, for contrast: with a shape-independent supplied store the
    answers should also be shape-independent -/

def valReport (k : Nat) (st : FlatWordStore) : List (String × Nat) :=
  let ss := allShapes k
  [ ("interiorRangeMin 0 2 value",
      distinct (ss.map fun s => (canonicalRelativeRmmInteriorRangeMinComputation s 0 2).run st |>.value))
  , ("interiorRangeMin 2 5 value",
      distinct (ss.map fun s => (canonicalRelativeRmmInteriorRangeMinComputation s 2 5).run st |>.value))
  , ("summaryComputation 1 value",
      distinct (ss.map fun s => (canonicalRelativeRmmMachineSummaryComputation s 1).run st |>.value))
  ]

#eval valReport 5 store1
#eval valReport 6 store1
#eval valReport 7 store1

end DPWExhaustJ
