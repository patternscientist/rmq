import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL AUDIT part E: the composition step the lane did NOT prove.

`ZkdK.selectPadRho_le_charged_overhead` proves  `A + B <= T`.
Space neutrality needs  `R + A + B <= T`  where `R` is the other regions.
`A + B <= T` does not entail `R + A + B <= T`.

Below is the statement the lane should have proved, built by taking the in-tree
region-wise proof (BuildProfile.lean:429-448) and replacing the long-region
`have hlong` by the budget itself.
-/

namespace QvzE

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctSelect

/-- The select payload with the LONG relative region padded to its `n`-only
budget still fits the same charged overhead. -/
theorem padded_long_composes (shape : CartesianShape) :
    (builtRelativeSplitFalseSelectSuperTable shape).payload.length +
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length +
        (builtRelativeSplitFalseSelectLongFlagRankData shape).auxPayload.length +
        compactLongSuperRelativeTableOverhead shape.size +
        (builtRelativeSplitFalseSelectLocalTable shape).payload.length +
        (builtRelativeSplitSparseExceptionDirectory shape).payload.length <=
      canonicalRelativeSplitSparseExceptionFalseSelectOverhead shape.size := by
  have hsuper :=
    builtRelativeSplitFalseSelectSuperTable_payload_le_overhead shape
  have hflags :=
    builtRelativeSplitFalseSelectLongSuperFlagBits_length_le_overhead shape
  have hrank :=
    builtRelativeSplitFalseSelectLongFlagRankData_auxPayload_le_overhead shape
  have hlocal :=
    builtRelativeSplitFalseSelectLocalTable_payload_le_overhead shape
  have hsparse :=
    (builtRelativeSplitSparseExceptionDirectory shape).payload_length_le_canonical
  have hbp : shape.bpCode.length = 2 * shape.size :=
    Cartesian.CartesianShape.bpCode_length shape
  rw [hbp] at hsuper hflags hrank hlocal
  simp [canonicalRelativeSplitSparseExceptionFalseSelectOverhead,
    compactLongSuperRelativeTableOverhead]
  omega

#print axioms padded_long_composes

end QvzE
