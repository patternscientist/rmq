import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F5 caller enumeration: who calls `RMQ.SuccinctClose.bpExcessAt` inside the
computational (value-only, theorem-free) closure of the store-parametric
whole-query controller, and what are the explicit call paths from the root?
-/

open Lean

namespace F5Callers

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def targets : List Name :=
  [ `RMQ.SuccinctClose.bpExcessAt
  , `RMQ.SuccinctClose.bpBlockMinExcess
  , `RMQ.SuccinctClose.bpBlockMaxExcess
  , `RMQ.SuccinctClose.bpBlockArgMinPrefixPos
  , `RMQ.SuccinctClose.bpBlockArgMinPrefixPosFrom
  , `RMQ.SuccinctClose.bpBlockExcessSamples
  , `RMQ.SuccinctClose.localBPWindowBase
  , `RMQ.SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable
  ]

def isTheorem (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

def compDeps (env : Environment) (n : Name) : List Name :=
  if isTheorem env n then []
  else
    match env.find? n with
    | none => []
    | some ci =>
        match ci.value? with
        | some v => v.foldConsts [] (fun c a => c :: a)
        | none => []

partial def closureAux (env : Environment) (seen : Std.HashSet Name)
    (out : Array Name) : List Name -> Std.HashSet Name × Array Name
  | [] => (seen, out)
  | n :: rest =>
      if seen.contains n then closureAux env seen out rest
      else
        let seen := seen.insert n
        let out := out.push n
        closureAux env seen out (compDeps env n ++ rest)

/-- One BFS layer. -/
partial def bfsGo (env : Environment) (tgt : Name)
    (frontier : List (List Name)) (seen : Std.HashSet Name)
    (fuel : Nat) : Option (List Name) := Id.run do
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
        for d in compDeps env n do
          if d == tgt then
            if found.isNone then found := some (d :: path)
          else if !seen.contains d then
            seen := seen.insert d
            nextF := (d :: path) :: nextF
    match found with
    | some p => return some p
    | none => return bfsGo env tgt nextF seen fuel'

/-- BFS shortest path from root to target following compDeps. -/
def bfs (env : Environment) (tgt : Name) : Option (List Name) :=
  if root == tgt then some [root]
  else bfsGo env tgt [[root]] (({} : Std.HashSet Name).insert root) 200

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => m
      | none => .anonymous
  | none => .anonymous

run_cmd do
  let env <- Lean.getEnv
  let (seen, cl) := closureAux env {} #[] [root]
  let mut lines : Array String := #[]
  lines := lines.push s!"COMPUTATIONAL_CLOSURE_TOTAL {cl.size}"
  for tgt in targets do
    lines := lines.push ""
    lines := lines.push s!"===== TARGET {tgt}  inClosure={seen.contains tgt} ====="
    -- all direct callers within the closure
    let mut callers : Array Name := #[]
    for n in cl do
      if compDeps env n |>.contains tgt then
        callers := callers.push n
    lines := lines.push s!"  DIRECT_CALLERS_IN_CORE {callers.size}"
    for c in callers do
      lines := lines.push s!"    CALLER {c}  mod={moduleOf env c}"
    match bfs env tgt with
    | none => lines := lines.push "  NO_PATH_FROM_ROOT"
    | some p =>
        lines := lines.push s!"  SHORTEST_PATH_LEN {p.length}"
        let mut i := 0
        for n in p.reverse do
          lines := lines.push s!"    [{i}] {n}  mod={moduleOf env n}"
          i := i + 1
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/f5_callers_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"done closure={cl.size}"

end F5Callers
