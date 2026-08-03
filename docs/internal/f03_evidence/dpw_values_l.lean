import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

namespace DPWValuesL
open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctFinal

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node (leftSpine k) CartesianShape.empty
def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node CartesianShape.empty (rightSpine k)
def zig : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | 1 => CartesianShape.node CartesianShape.empty CartesianShape.empty
  | k + 2 => CartesianShape.node (zig k) (CartesianShape.node CartesianShape.empty CartesianShape.empty)

#eval (List.range 12).map fun j =>
  let k := 20 + 4 * j
  let a := leftSpine k
  let b := rightSpine k
  (k, (canonicalRelativeRmmGlobalMachineStore a).store.words.size,
      (canonicalRelativeRmmGlobalMachineStore a).store.words ==
        (canonicalRelativeRmmGlobalMachineStore b).store.words,
      (canonicalRelativeRmmLocalMachineStore a).store.words ==
        (canonicalRelativeRmmLocalMachineStore b).store.words)

#eval (List.range 8).map fun j =>
  let k := 20 + 8 * j
  let a := zig k
  let b := leftSpine a.size
  (a.size, (canonicalRelativeRmmGlobalMachineStore a).store.words.size,
      (canonicalRelativeRmmGlobalMachineStore a).store.words ==
        (canonicalRelativeRmmGlobalMachineStore b).store.words)

#eval let a := leftSpine 12; let b := rightSpine 12;
  ((canonicalRelativeRmmLocalMachineStore a).store.words.size,
   (canonicalRelativeRmmLocalMachineStore a).store.words,
   (canonicalRelativeRmmLocalMachineStore b).store.words)

end DPWValuesL
