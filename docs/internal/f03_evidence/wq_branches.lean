import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
EXHAUSTIVE BRANCH INVENTORY over the controller's computational closure Q.

F03 demands an exhaustive typed inventory, not representative rows.  A
data-dependent BRANCH in Q can only read tree contents through one of the two
bit-reading primitives `RMQ.Succinct.select` / `RMQ.Succinct.rankPrefix`
(everything else consumes lengths).  So:

  * enumerate every constant in Q whose result type is `Bool` or `Prop`
    (i.e. everything that can serve as a branch condition or a decidable test);
  * mark those that transitively depend, through VALUES only, on a bit-reading
    primitive -- these are the only branches whose outcome can depend on tree
    CONTENTS rather than on n;
  * print the complete list.  The claim to audit is that this list is exactly
    the select-layer span predicates.
-/

open Lean

namespace WQBranches

def qRoot : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def bitReaders : List Name :=
  [ `RMQ.Succinct.select, `RMQ.Succinct.rankPrefix ]

def isTheorem (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

def compDeps (env : Environment) (n : Name) : List Name :=
  if isTheorem env n then []
  else
    match env.find? n with
    | none => []
    | some ci => match ci.value? with
      | some v => v.foldConsts [] (fun c a => c :: a)
      | none => []

partial def closureAux (env : Environment) (seen : Std.HashSet Name)
    (out : Array Name) : List Name -> Std.HashSet Name × Array Name
  | [] => (seen, out)
  | n :: rest =>
      if seen.contains n then closureAux env seen out rest
      else closureAux env (seen.insert n) (out.push n) (compDeps env n ++ rest)

def resultHead (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | none => .anonymous
  | some ci =>
      let rec peel : Expr -> Expr
        | .forallE _ _ b _ => peel b
        | e => e
      match (peel ci.type).getAppFn with
      | .const c _ => c
      | .sort _ => `Sort
      | _ => .anonymous

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => match env.header.moduleNames[idx.toNat]? with
    | some m => m
    | none => .anonymous
  | none => .anonymous

run_cmd do
  let env <- Lean.getEnv
  let (qSeen, qArr) := closureAux env {} #[] [qRoot]
  -- for each constant in Q, does its own value-closure reach a bit reader?
  let mut readsBits : Std.HashSet Name := {}
  for n in qArr do
    let (s, _) := closureAux env {} #[] [n]
    if bitReaders.any (fun b => s.contains b) then
      readsBits := readsBits.insert n
  let mut boolProp : Array Name := #[]
  for n in qArr do
    let rh := resultHead env n
    if rh == `Bool || rh == `Sort || rh == `Prop then
      boolProp := boolProp.push n
  let mut contentBranches : Array Name := #[]
  let mut sizeBranches : Array Name := #[]
  for n in boolProp do
    if readsBits.contains n then contentBranches := contentBranches.push n
    else sizeBranches := sizeBranches.push n
  let mut lines : Array String := #[]
  lines := lines.push s!"Q closure size = {qArr.size}"
  lines := lines.push s!"constants in Q whose value-closure reaches select/rankPrefix = {readsBits.size}"
  lines := lines.push s!"constants in Q returning Bool/Prop/Sort (candidate branch conditions) = {boolProp.size}"
  lines := lines.push s!"  of which CONTENT-DEPENDENT (reach a bit reader) = {contentBranches.size}"
  lines := lines.push s!"  of which size-only = {sizeBranches.size}"
  lines := lines.push ""
  lines := lines.push "== EVERY CONTENT-DEPENDENT BRANCH CONDITION IN THE CONTROLLER CLOSURE =="
  for n in contentBranches do
    lines := lines.push s!"  BRANCH {n} :: ret={resultHead env n} mod={moduleOf env n}"
  lines := lines.push ""
  lines := lines.push "== size-only Bool/Prop constants in Q (first 60, for calibration) =="
  for n in sizeBranches[0:60] do
    lines := lines.push s!"  sizeonly {n} :: ret={resultHead env n}"
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/wq_branches_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"Q={qArr.size} boolProp={boolProp.size} contentBranches={contentBranches.size}"

end WQBranches
