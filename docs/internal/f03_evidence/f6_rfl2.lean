import RMQ.Core.SuccinctFinalStoreParam

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace F6Rfl2

def noiseStore : WordRAM.ReadStore where
  readWord? segment index :=
    some ((List.range 16).map fun k =>
      (11 + segment * 7919 + index * 104729 + k * 1299709) % 3 == 0)

def leaf (shape : CartesianShape) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSelectCloseGlobalWordTraceResultWithStore shape noiseStore idx

def s2R : CartesianShape :=
  CartesianShape.node CartesianShape.empty
    (CartesianShape.node CartesianShape.empty CartesianShape.empty)
def s2L : CartesianShape :=
  CartesianShape.node
    (CartesianShape.node CartesianShape.empty CartesianShape.empty)
    CartesianShape.empty

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- Cheap, definitely-checked facts the S verdict rests on.
example : s2R.bpCode.length = s2L.bpCode.length := rfl
example :
    GenericSelect.occurrenceCount s2R.bpCode false =
      GenericSelect.occurrenceCount s2L.bpCode false := rfl
example : s2R.bpCode != s2L.bpCode := by decide

-- The expensive one: full definitional equality of the leaf.
example : leaf s2R 0 = leaf s2L 0 := rfl

end F6Rfl2
