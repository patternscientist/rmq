import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F5 reverse-reachability: every constant in the computational core of the
store-parametric whole-query controller that transitively (value-only) reaches
`RMQ.SuccinctClose.bpExcessAt`, together with the induced subgraph edges.
-/

open Lean

namespace F5Sub

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def tgt : Name := `RMQ.SuccinctClose.bpExcessAt

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

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => m
      | none => .anonymous
  | none => .anonymous

/-- Iterate reverse reachability to fixpoint over the core. -/
partial def fix (core : Array Name) (deps : Std.HashMap Name (List Name))
    (r : Std.HashSet Name) : Std.HashSet Name := Id.run do
  let mut r := r
  let mut changed := false
  for n in core do
    if r.contains n then continue
    let ds := deps.getD n []
    if ds.any (fun d => r.contains d) then
      r := r.insert n
      changed := true
  if changed then return fix core deps r else return r

run_cmd do
  let env <- Lean.getEnv
  let core := (closureAux env {} #[] [root]).2
  let mut deps : Std.HashMap Name (List Name) := {}
  for n in core do
    deps := deps.insert n (compDeps env n)
  let r0 : Std.HashSet Name := ({} : Std.HashSet Name).insert tgt
  let r := fix core deps r0
  let mut lines : Array String := #[]
  lines := lines.push s!"CORE {core.size}"
  let mut inR : Array Name := #[]
  for n in core do
    if r.contains n then inR := inR.push n
  lines := lines.push s!"REACH_BPEXCESSAT_COUNT {inR.size}"
  lines := lines.push ""
  lines := lines.push "== subgraph: node -> deps that also reach bpExcessAt =="
  for n in inR do
    let ds := (deps.getD n []).eraseDups.filter (fun d => r.contains d)
    lines := lines.push s!"NODE {n}"
    lines := lines.push s!"  mod={moduleOf env n}"
    for d in ds do
      lines := lines.push s!"  -> {d}"
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/f5_subgraph_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"core={core.size} reach={inR.size}"

end F5Sub
