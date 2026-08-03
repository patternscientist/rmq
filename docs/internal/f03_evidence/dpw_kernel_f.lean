import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 content-dependence, kernel-checked.

Every claim below is closed by `decide`, so the kernel itself evaluates both
sides.  Unlike `isDefEq` (which may answer "not equal" without deciding) and
unlike `Lean.Meta.reduce` (which may stop on a stuck term whose residual
mentions the shape), `decide` cannot produce a false separation: it either
evaluates the `Decidable` instance to `isTrue` or the file does not compile.

`sA` and `sB` are two Cartesian shapes with the SAME `size` and therefore the
SAME `bpCode.length`, but different `bpCode`.  A constant separated here has a
value that depends on the CONTENTS of the balanced-parentheses bitvector, not
only on `n`.
-/

namespace DPWKernelF

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctFinal

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node (leftSpine k) CartesianShape.empty

def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node CartesianShape.empty (rightSpine k)

def sA : CartesianShape := leftSpine 5
def sB : CartesianShape := rightSpine 5

/-! ## The pair is a legitimate F03 witness pair -/

theorem pair_size : sA.size = sB.size := by decide
theorem pair_bpCode_length : sA.bpCode.length = sB.bpCode.length := by decide
theorem pair_bpCode_differs : Ne sA.bpCode sB.bpCode := by decide

/-! ## Genuinely content-dependent: the absolute excess layer -/

theorem cd_bpExcessAt :
    Ne (bpExcessAt sA 2) (bpExcessAt sB 2) := by decide

theorem cd_bpBlockExcessSamples :
    Ne (bpBlockExcessSamples sA 2 0) (bpBlockExcessSamples sB 2 0) := by decide

theorem cd_bpBlockMinExcess :
    Ne (bpBlockMinExcess sA 2 1) (bpBlockMinExcess sB 2 1) := by decide

theorem cd_bpBlockMaxExcess :
    Ne (bpBlockMaxExcess sA 2 0) (bpBlockMaxExcess sB 2 0) := by decide

/-! ## Genuinely content-dependent: the relative excess layer -/

theorem cd_bpBlockRelativeMinExcess :
    Ne (bpBlockRelativeMinExcess sA 2 0 1) (bpBlockRelativeMinExcess sB 2 0 1) := by decide

theorem cd_bpBlockRelativeMaxExcess :
    Ne (bpBlockRelativeMaxExcess sA 2 0 1) (bpBlockRelativeMaxExcess sB 2 0 1) := by decide

theorem cd_bpRelativeExcessEntry :
    Ne (bpRelativeExcessEntry sA 2 1 1 2) (bpRelativeExcessEntry sB 2 1 1 2) := by decide

/-! ## Genuinely content-dependent: the argmin/position layer -/

theorem cd_bpBlockArgMinPrefixPosFrom :
    Ne (bpBlockArgMinPrefixPosFrom sA 0 1 2) (bpBlockArgMinPrefixPosFrom sB 0 1 2) := by decide

theorem cd_bpBlockArgMinPrefixPos :
    Ne (bpBlockArgMinPrefixPos sA 4 1) (bpBlockArgMinPrefixPos sB 4 1) := by decide

theorem cd_bpBlockArgMinLocalOffset :
    Ne (bpBlockArgMinLocalOffset sA 4 1) (bpBlockArgMinLocalOffset sB 4 1) := by decide

theorem cd_bpBetterArgMinBlock :
    Ne (bpBetterArgMinBlock sA 2 1 0) (bpBetterArgMinBlock sB 2 1 0) := by decide

theorem cd_bpRangeArgMinBlockFrom :
    Ne (bpRangeArgMinBlockFrom sA 2 0 1 1) (bpRangeArgMinBlockFrom sB 2 0 1 1) := by decide

theorem cd_bpRangeArgMinBlock :
    Ne (bpRangeArgMinBlock sA 2 1 4) (bpRangeArgMinBlock sB 2 1 4) := by decide

/-! ## Genuinely content-dependent: the sparse-cell layer -/

theorem cd_bpLocalSparseCellOffset :
    Ne (bpLocalSparseCellOffset sA 2 5 4 0 2 1) (bpLocalSparseCellOffset sB 2 5 4 0 2 1) := by decide

theorem cd_bpGlobalSparseCellBlock :
    Ne (bpGlobalSparseCellBlock sA 1 8 2 4 2 1) (bpGlobalSparseCellBlock sB 1 8 2 4 2 1) := by decide

/-! ## Genuinely content-dependent: the entry-list layer (the stored payloads) -/

theorem cd_bpSuperblockBaselineEntries :
    Ne (bpSuperblockBaselineEntries sA 2 1 2) (bpSuperblockBaselineEntries sB 2 1 2) := by decide

theorem cd_bpBlockRelativeMinExcessEntries :
    Ne (bpBlockRelativeMinExcessEntries sA 2 0 2) (bpBlockRelativeMinExcessEntries sB 2 0 2) := by decide

theorem cd_bpBlockRelativeMaxExcessEntries :
    Ne (bpBlockRelativeMaxExcessEntries sA 2 0 1) (bpBlockRelativeMaxExcessEntries sB 2 0 1) := by decide

theorem cd_bpBlockArgMinLocalOffsetEntries :
    Ne (bpBlockArgMinLocalOffsetEntries sA 1 2) (bpBlockArgMinLocalOffsetEntries sB 1 2) := by decide

theorem cd_bpLocalSparseOffsetEntries :
    Ne (bpLocalSparseOffsetEntries sA 2 5 4 1 2) (bpLocalSparseOffsetEntries sB 2 5 4 1 2) := by decide

theorem cd_bpGlobalSparseBlockEntries :
    Ne (bpGlobalSparseBlockEntries sA 1 8 2 4 2) (bpGlobalSparseBlockEntries sB 1 8 2 4 2) := by decide

#print axioms pair_size
#print axioms pair_bpCode_length
#print axioms pair_bpCode_differs
#print axioms cd_bpExcessAt
#print axioms cd_bpBlockExcessSamples
#print axioms cd_bpBlockMinExcess
#print axioms cd_bpBlockMaxExcess
#print axioms cd_bpBlockRelativeMinExcess
#print axioms cd_bpBlockRelativeMaxExcess
#print axioms cd_bpRelativeExcessEntry
#print axioms cd_bpBlockArgMinPrefixPosFrom
#print axioms cd_bpBlockArgMinPrefixPos
#print axioms cd_bpBlockArgMinLocalOffset
#print axioms cd_bpBetterArgMinBlock
#print axioms cd_bpRangeArgMinBlockFrom
#print axioms cd_bpRangeArgMinBlock
#print axioms cd_bpLocalSparseCellOffset
#print axioms cd_bpGlobalSparseCellBlock
#print axioms cd_bpSuperblockBaselineEntries
#print axioms cd_bpBlockRelativeMinExcessEntries
#print axioms cd_bpBlockRelativeMaxExcessEntries
#print axioms cd_bpBlockArgMinLocalOffsetEntries
#print axioms cd_bpLocalSparseOffsetEntries
#print axioms cd_bpGlobalSparseBlockEntries

end DPWKernelF
