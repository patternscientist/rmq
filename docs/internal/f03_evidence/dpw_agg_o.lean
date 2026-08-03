import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

namespace DPWAggO
open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctFinal

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node (leftSpine k) CartesianShape.empty
def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node CartesianShape.empty (rightSpine k)
def sA : CartesianShape := leftSpine 5
def sB : CartesianShape := rightSpine 5

-- [34] and [39] at the arguments where the ENTRIES were separated (n = 5 pair)
#eval ((concreteBPLocalSparseOffsetTable sA 2 5 4 1 2 3 (by decide)).table.payload ==
       (concreteBPLocalSparseOffsetTable sB 2 5 4 1 2 3 (by decide)).table.payload)
#eval ((concreteBPGlobalSparseBlockTable sA 1 8 2 4 2 4 (by decide) (by decide)).table.payload ==
       (concreteBPGlobalSparseBlockTable sB 1 8 2 4 2 4 (by decide) (by decide)).table.payload)

-- [38]/[40]: canonical global sparse table at growing n
#eval (List.range 10).map fun j =>
  let k := 16 + 24 * j
  let a := leftSpine k
  let b := rightSpine k
  (k, (canonicalRelativeRmmInteriorGlobalTable a).table.payload.length,
      (canonicalRelativeRmmInteriorGlobalTable a).table.payload ==
        (canonicalRelativeRmmInteriorGlobalTable b).table.payload,
      (canonicalRelativeRmmGlobalMachineStore a).store.words ==
        (canonicalRelativeRmmGlobalMachineStore b).store.words)

#eval let a := leftSpine 256; let b := rightSpine 256;
  ((canonicalRelativeRmmInteriorGlobalTable a).table.payload.length,
   (canonicalRelativeRmmInteriorGlobalTable a).table.payload ==
     (canonicalRelativeRmmInteriorGlobalTable b).table.payload,
   (canonicalRelativeRmmGlobalMachineStore a).store.words.size,
   (canonicalRelativeRmmGlobalMachineStore a).store.words ==
     (canonicalRelativeRmmGlobalMachineStore b).store.words)

end DPWAggO
