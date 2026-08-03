import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 BUILD-TIME aggregates: separation by COMPILER evaluation.

`decide` cannot close these -- the kernel gets stuck unfolding the aggregate
constructions -- so this file records `#eval` separations instead, and is
labelled as weaker evidence than `dpw_kernel_f.lean`.  Each aggregate is in
any case indexed in its TYPE by an entry list that `dpw_kernel_f.lean`
separates in the kernel.

Every printed pair is (value at sA, value at sB) or a boolean `==` test;
`false` on a `==` test means the two shapes give different values.
-/

namespace DPWAggN

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctFinal

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node (leftSpine k) CartesianShape.empty

def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node CartesianShape.empty (rightSpine k)

def sA : CartesianShape := leftSpine 5
def sB : CartesianShape := rightSpine 5
def tA : CartesianShape := leftSpine 12
def tB : CartesianShape := rightSpine 12

#eval (sA.size, sB.size, sA.bpCode.length, sB.bpCode.length)
#eval (tA.size, tB.size, tA.bpCode.length, tB.bpCode.length)

-- [12] canonicalRelativeRmmSummaryTable, via each sub-table payload
#eval ((canonicalRelativeRmmSummaryTable sA).baselineTable.payload ==
       (canonicalRelativeRmmSummaryTable sB).baselineTable.payload,
       (canonicalRelativeRmmSummaryTable sA).minRelTable.payload ==
       (canonicalRelativeRmmSummaryTable sB).minRelTable.payload,
       (canonicalRelativeRmmSummaryTable sA).maxRelTable.payload ==
       (canonicalRelativeRmmSummaryTable sB).maxRelTable.payload,
       (canonicalRelativeRmmSummaryTable sA).argOffsetTable.payload ==
       (canonicalRelativeRmmSummaryTable sB).argOffsetTable.payload)

-- [13] concreteBPRelativeMinMaxArgSummaryTable is the same construction with
-- the layout scalars supplied explicitly; canonicalRelativeRmmSummaryTable is
-- literally an application of it, so the row above covers it.

-- [33] canonicalRelativeRmmInteriorLocalTable
#eval ((canonicalRelativeRmmInteriorLocalTable tA).table.payload ==
       (canonicalRelativeRmmInteriorLocalTable tB).table.payload)
#eval ((canonicalRelativeRmmInteriorLocalTable sA).table.payload ==
       (canonicalRelativeRmmInteriorLocalTable sB).table.payload)

-- [38] canonicalRelativeRmmInteriorGlobalTable
#eval ((canonicalRelativeRmmInteriorGlobalTable tA).table.payload ==
       (canonicalRelativeRmmInteriorGlobalTable tB).table.payload)
#eval ((canonicalRelativeRmmInteriorGlobalTable tA).table.payload.length,
       (canonicalRelativeRmmInteriorGlobalTable tA).table.payload)

-- [35] canonicalRelativeRmmLocalMachineStore
#eval ((canonicalRelativeRmmLocalMachineStore tA).store.words ==
       (canonicalRelativeRmmLocalMachineStore tB).store.words)

-- [40] canonicalRelativeRmmGlobalMachineStore
#eval ((canonicalRelativeRmmGlobalMachineStore tA).store.words ==
       (canonicalRelativeRmmGlobalMachineStore tB).store.words,
       (canonicalRelativeRmmGlobalMachineStore tA).store.words.size)

-- [41] canonicalRelativeRmmInteriorComponentStore
#eval ((canonicalRelativeRmmInteriorComponentStore sA).store.words ==
       (canonicalRelativeRmmInteriorComponentStore sB).store.words)

-- [42] canonicalRelativeRmmSummaryMachineStore
#eval ((canonicalRelativeRmmSummaryMachineStore sA).store.words ==
       (canonicalRelativeRmmSummaryMachineStore sB).store.words)

-- [55] builtRelativeSplitBPCloseRankData
#eval ((builtRelativeSplitBPCloseRankData sA).blockTrueEntries ==
       (builtRelativeSplitBPCloseRankData sB).blockTrueEntries,
       (builtRelativeSplitBPCloseRankData sA).blockTrueEntries,
       (builtRelativeSplitBPCloseRankData sB).blockTrueEntries)

-- [34] concreteBPLocalSparseOffsetTable and [39] concreteBPGlobalSparseBlockTable
-- at explicit arguments (the canonical tables above are their applications).
#eval ((concreteBPLocalSparseOffsetTable tA 2 5 4 1 2 3 (by decide)).table.payload ==
       (concreteBPLocalSparseOffsetTable tB 2 5 4 1 2 3 (by decide)).table.payload)
#eval ((concreteBPGlobalSparseBlockTable tA 1 8 2 4 2 4 (by decide) (by decide)).table.payload ==
       (concreteBPGlobalSparseBlockTable tB 1 8 2 4 2 4 (by decide) (by decide)).table.payload)

end DPWAggN
