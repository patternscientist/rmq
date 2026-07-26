import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F5, strongest instrument: closure over the COMPILED IR rather than over the
definitional value.  Lean's code generator erases types, type indices and
proofs, so an IR-level dependency edge is exactly "this constant can influence
what the executed program does".  A constant that appears in the *value* only
as an implicit `entries` index of a `FixedWidthNatTable` disappears here.
-/

open Lean

namespace F5IR

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def watch : List Name :=
  [ `RMQ.SuccinctClose.bpExcessAt
  , `RMQ.SuccinctClose.bpBlockMinExcess
  , `RMQ.SuccinctClose.bpBlockMaxExcess
  , `RMQ.SuccinctClose.bpBlockArgMinPrefixPos
  , `RMQ.SuccinctClose.bpBlockArgMinPrefixPosFrom
  , `RMQ.SuccinctClose.bpBlockExcessSamples
  , `RMQ.SuccinctClose.bpSuperblockBaselineEntries
  , `RMQ.SuccinctClose.bpBlockRelativeMinExcessEntries
  , `RMQ.SuccinctClose.bpBlockRelativeMaxExcessEntries
  , `RMQ.SuccinctClose.bpBlockArgMinLocalOffsetEntries
  , `RMQ.SuccinctClose.bpLocalSparseOffsetEntries
  , `RMQ.SuccinctClose.bpGlobalSparseBlockEntries
  , `RMQ.SuccinctClose.bpBetterArgMinBlock
  , `RMQ.SuccinctClose.bpRangeArgMinBlock
  , `RMQ.SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable
  , `RMQ.SuccinctClose.canonicalRelativeRmmSummaryTable
  , `RMQ.SuccinctClose.canonicalRelativeRmmInteriorComponentOffsets
  , `RMQ.SuccinctClose.canonicalRelativeRmmMachineSummaryComputation
  , `RMQ.SuccinctClose.canonicalRelativeRmmMachineReadNatComputation
  , `RMQ.SuccinctSpace.FixedWidthNatTable.machineReadComputationAt
  , `RMQ.Cartesian.CartesianShape.bpCode
  , `RMQ.Cartesian.CartesianShape.size
  ]

def irDeps (env : Environment) (n : Name) : Option (List Name) :=
  match IR.findEnvDecl env n with
  | none => none
  | some d =>
      let s : NameSet := (((IR.CollectUsedDecls.collectDecl d).run env).run {}).1
      some (s.toList)

partial def closureAux (env : Environment) (seen : Std.HashSet Name)
    (out : Array Name) (missing : Array Name) :
    List Name -> Std.HashSet Name × Array Name × Array Name
  | [] => (seen, out, missing)
  | n :: rest =>
      if seen.contains n then closureAux env seen out missing rest
      else
        let seen := seen.insert n
        let out := out.push n
        match irDeps env n with
        | none => closureAux env seen out (missing.push n) rest
        | some ds => closureAux env seen out missing (ds ++ rest)

run_cmd do
  let env <- Lean.getEnv
  let (seen, out, missing) := closureAux env {} #[] #[] [root]
  let mut lines : Array String := #[]
  lines := lines.push s!"ROOT_HAS_IR {(IR.findEnvDecl env root).isSome}"
  lines := lines.push s!"IR_CLOSURE_TOTAL {out.size}"
  lines := lines.push s!"NO_IR_DECL_COUNT {missing.size}"
  lines := lines.push ""
  lines := lines.push "== watched constants: present in the EXECUTED (IR) closure? =="
  for w in watch do
    let tag := if seen.contains w then "IN_IR " else "ABSENT"
    lines := lines.push s!"  {tag}  {w}"
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/f5_ir_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"ir closure={out.size} missing={missing.size}"

end F5IR
