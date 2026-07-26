import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

open Lean

namespace F5IRPath

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def irDeps (env : Environment) (n : Name) : List Name :=
  match IR.findEnvDecl env n with
  | none => []
  | some d =>
      let s : NameSet := (((IR.CollectUsedDecls.collectDecl d).run env).run {}).1
      s.toList.filter (fun m => m != n)

partial def bfsGo (env : Environment) (tgt : Name)
    (frontier : List (List Name)) (seen : Std.HashSet Name) (fuel : Nat) :
    Option (List Name) := Id.run do
  match fuel with
  | 0 => return none
  | fuel' + 1 =>
    if frontier.isEmpty then return none
    let mut nextF : List (List Name) := []
    let mut seen := seen
    let mut found : Option (List Name) := none
    for path in frontier do
      match path with
      | [] => pure ()
      | n :: _ =>
        for d in irDeps env n do
          if d == tgt then
            if found.isNone then found := some (d :: path)
          else if !seen.contains d then
            seen := seen.insert d
            nextF := (d :: path) :: nextF
    match found with
    | some p => return some p
    | none => return bfsGo env tgt nextF seen fuel'

partial def closureAux (env : Environment) (seen : Std.HashSet Name)
    (out : Array Name) : List Name -> Std.HashSet Name × Array Name
  | [] => (seen, out)
  | n :: rest =>
      if seen.contains n then closureAux env seen out rest
      else
        let seen := seen.insert n
        let out := out.push n
        closureAux env seen out (irDeps env n ++ rest)

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]?).getD .anonymous
  | none => .anonymous

def targets : List Name :=
  [ `RMQ.SuccinctClose.bpExcessAt
  , `RMQ.SuccinctClose.canonicalRelativeRmmSummaryTable
  , `RMQ.SuccinctClose.bpSuperblockBaselineEntries
  , `RMQ.SuccinctClose.bpBlockRelativeMinExcessEntries
  , `RMQ.SuccinctClose.bpBlockRelativeMaxExcessEntries
  , `RMQ.SuccinctClose.bpBlockArgMinLocalOffsetEntries
  , `RMQ.SuccinctClose.bpLocalSparseOffsetEntries
  , `RMQ.SuccinctClose.bpGlobalSparseBlockEntries ]

run_cmd do
  let env <- Lean.getEnv
  let core := (closureAux env {} #[] [root]).2
  let mut lines : Array String := #[]
  lines := lines.push s!"IR_CORE {core.size}"
  for t in targets do
    lines := lines.push ""
    lines := lines.push s!"===== IR TARGET {t} ====="
    let mut callers : Array Name := #[]
    for n in core do
      if (irDeps env n).contains t then callers := callers.push n
    lines := lines.push s!"  IR_DIRECT_CALLERS {callers.size}"
    for c in callers do
      lines := lines.push s!"    IRCALLER {c}  mod={moduleOf env c}"
    match bfsGo env t [[root]] (({} : Std.HashSet Name).insert root) 200 with
    | none => lines := lines.push "  NO_IR_PATH"
    | some p =>
        lines := lines.push s!"  IR_SHORTEST_PATH_LEN {p.length}"
        let mut i := 0
        for n in p.reverse do
          lines := lines.push s!"    [{i}] {n}"
          i := i + 1
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/f5_irpath2_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"ircore={core.size}"

end F5IRPath
