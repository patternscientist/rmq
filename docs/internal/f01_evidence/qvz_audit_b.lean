import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL AUDIT part B: is the object the lane bounded the object the frozen
payload contains?
-/

namespace QvzB

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctSelect

/-- The segment the frozen reviewer payload actually stores at
`.selectLongRelative`. -/
def genericLongTablePayload (shape : CartesianShape) : List Bool :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
    .selectLongRelative

/-- The object the lane's refined-budget theorems talk about. -/
def builtLongTablePayload (shape : CartesianShape) : List Bool :=
  (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload

/-- TEST 1: definitional equality? -/
example (shape : CartesianShape) :
    genericLongTablePayload shape = builtLongTablePayload shape := by
  rfl

end QvzB
