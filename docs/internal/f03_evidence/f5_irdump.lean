import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

open Lean

namespace F5Dump

def names : List Name :=
  [ `RMQ.SuccinctClose.canonicalRelativeRmmMachineSummaryComputation
  , `RMQ.SuccinctClose.canonicalRelativeRmmMachineSummaryComputation._lam_1
  , `RMQ.SuccinctClose.canonicalRelativeRmmMachineSummaryComputation._lam_2
  , `RMQ.SuccinctClose.canonicalRelativeRmmMachineSummaryComputation._lam_3
  , `RMQ.SuccinctClose.canonicalRelativeRmmMachineLocalSpanCandidateComputation
  , `RMQ.SuccinctClose.canonicalRelativeRmmMachineGlobalSpanCandidateComputation
  , `RMQ.SuccinctClose.canonicalRelativeRmmInteriorComponentOffsets
  , `RMQ.SuccinctClose.canonicalRelativeRmmMachineReadNatComputation._redArg
  , `RMQ.SuccinctSpace.FixedWidthNatTable.machineReadComputationAt._redArg
  , `RMQ.SuccinctSpace.FixedWidthNatTable.machineReadComputationAt ]

run_cmd do
  let env <- Lean.getEnv
  let mut out : Array String := #[]
  for n in names do
    out := out.push s!"=================== {n}"
    match IR.findEnvDecl env n with
    | none => out := out.push "  (no IR)"
    | some d => out := out.push (toString (format d))
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/f5_irdump2_out.txt"
    (String.intercalate "\n" out.toList)
  Lean.logInfo "dumped"

end F5Dump
