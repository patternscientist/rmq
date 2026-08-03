import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Exploratory values for the F03 content-dependence witnesses.
Nothing here is load-bearing; the kernel-checked claims live in
`dpw_kernel_f.lean`.
-/

namespace DPWValuesE

open RMQ RMQ.Cartesian

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node (leftSpine k) CartesianShape.empty

def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node CartesianShape.empty (rightSpine k)

def sA : CartesianShape := leftSpine 5
def sB : CartesianShape := rightSpine 5

#eval (sA.bpCode, sB.bpCode)
#eval (sA.bpCode.length, sB.bpCode.length)
#eval (sA.size, sB.size)

#eval (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankWordSize sA,
       RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankWordSize sB)
#eval (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankSuperOverhead sA,
       RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankSuperOverhead sB)
#eval (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlockOverhead sA,
       RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlockOverhead sB)

#eval (RMQ.SuccinctClose.bpExcessAt sA 2, RMQ.SuccinctClose.bpExcessAt sB 2)
#eval (RMQ.SuccinctClose.bpBlockMinExcess sA 2 1, RMQ.SuccinctClose.bpBlockMinExcess sB 2 1)
#eval (RMQ.SuccinctClose.bpBlockMaxExcess sA 2 0, RMQ.SuccinctClose.bpBlockMaxExcess sB 2 0)
#eval (RMQ.SuccinctClose.bpBlockArgMinPrefixPos sA 4 1,
       RMQ.SuccinctClose.bpBlockArgMinPrefixPos sB 4 1)
#eval (RMQ.SuccinctClose.bpBlockArgMinLocalOffset sA 4 1,
       RMQ.SuccinctClose.bpBlockArgMinLocalOffset sB 4 1)

-- the four the automated grid could not separate
#eval ((List.range 6).map fun s =>
        (List.range 6).map fun b =>
          (RMQ.SuccinctClose.bpBlockArgMinPrefixPosFrom sA 0 s b,
           RMQ.SuccinctClose.bpBlockArgMinPrefixPosFrom sB 0 s b))
#eval ((List.range 5).map fun l =>
        (List.range 5).map fun r =>
          (RMQ.SuccinctClose.bpBetterArgMinBlock sA 2 l r,
           RMQ.SuccinctClose.bpBetterArgMinBlock sB 2 l r))
#eval ((List.range 5).map fun st =>
        (List.range 5).map fun c =>
          (RMQ.SuccinctClose.bpRangeArgMinBlock sA 2 st c,
           RMQ.SuccinctClose.bpRangeArgMinBlock sB 2 st c))
#eval ((List.range 5).map fun bs =>
        (List.range 5).map fun bc =>
          (RMQ.SuccinctClose.bpBlockArgMinLocalOffsetEntries sA bs bc,
           RMQ.SuccinctClose.bpBlockArgMinLocalOffsetEntries sB bs bc))

-- the six-argument sparse cells the sweep skipped
#eval ((List.range 3).map fun lvl =>
        (RMQ.SuccinctClose.bpLocalSparseCellOffset sA 2 5 4 0 0 lvl,
         RMQ.SuccinctClose.bpLocalSparseCellOffset sB 2 5 4 0 0 lvl))
#eval ((List.range 3).map fun lvl =>
        (RMQ.SuccinctClose.bpGlobalSparseCellBlock sA 1 8 2 4 0 lvl,
         RMQ.SuccinctClose.bpGlobalSparseCellBlock sB 1 8 2 4 0 lvl))
#eval (RMQ.SuccinctClose.bpLocalSparseOffsetEntries sA 2 5 4 1 2,
       RMQ.SuccinctClose.bpLocalSparseOffsetEntries sB 2 5 4 1 2)
#eval (RMQ.SuccinctClose.bpGlobalSparseBlockEntries sA 1 8 2 4 2,
       RMQ.SuccinctClose.bpGlobalSparseBlockEntries sB 1 8 2 4 2)

end DPWValuesE
