import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

namespace QvzC

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctSelect

/-- TEST 2: the sparse segment. -/
example (shape : CartesianShape) :
    RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
        .selectSparseRelative =
      (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload := by
  rfl

/-- NEGATIVE CONTROL: an obviously different segment must NOT be `rfl`-equal,
so TEST 1/2 are not degenerate. -/
example (shape : CartesianShape) :
    RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
        .selectSparseFlagBits =
      (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload := by
  rfl

end QvzC
