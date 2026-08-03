import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

namespace DPWValuesK
open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctFinal

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node (leftSpine k) CartesianShape.empty
def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node CartesianShape.empty (rightSpine k)
def bal : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node (bal k) (bal k)

def sA : CartesianShape := leftSpine 5
def sB : CartesianShape := rightSpine 5

#eval ((builtRelativeSplitBPCloseRankData sA).superTrueEntries,
       (builtRelativeSplitBPCloseRankData sB).superTrueEntries)
#eval ((builtRelativeSplitBPCloseRankData sA).blockTrueEntries,
       (builtRelativeSplitBPCloseRankData sB).blockTrueEntries)
#eval ((canonicalRelativeRmmSummaryMachineStore sA).store.words ==
       (canonicalRelativeRmmSummaryMachineStore sB).store.words)
#eval ((canonicalRelativeRmmInteriorComponentStore sA).store.words ==
       (canonicalRelativeRmmInteriorComponentStore sB).store.words)

-- local/global sparse stores: search for a separating pair at growing sizes
def sep (k : Nat) : (Bool × Bool) :=
  let a := leftSpine k
  let b := rightSpine k
  ( (canonicalRelativeRmmLocalMachineStore a).store.words ==
      (canonicalRelativeRmmLocalMachineStore b).store.words
  , (canonicalRelativeRmmGlobalMachineStore a).store.words ==
      (canonicalRelativeRmmGlobalMachineStore b).store.words )
#eval (List.range 20).map fun k => (k, sep k)

def sep2 (k : Nat) : (Bool × Bool) :=
  let a := bal 4
  let b := leftSpine a.size
  let _ := k
  ( (canonicalRelativeRmmLocalMachineStore a).store.words ==
      (canonicalRelativeRmmLocalMachineStore b).store.words
  , (canonicalRelativeRmmGlobalMachineStore a).store.words ==
      (canonicalRelativeRmmGlobalMachineStore b).store.words )
#eval (bal 4).size
#eval sep2 0
#eval ((canonicalRelativeRmmLocalMachineStore (bal 4)).store.words.size,
       (canonicalRelativeRmmGlobalMachineStore (bal 4)).store.words.size)

end DPWValuesK
