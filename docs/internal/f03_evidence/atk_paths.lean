import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import RMQ.Core.SuccinctRMQClassic
import Lean

/-!
Who actually CALLS the shape eliminators? A shortest-path witness from the
controller root to each primitive shape observer, plus the full direct-referrer
set. This is what decides whether `reprCartesianShape.match_1` is dead Repr
infrastructure or a REUSED generic 2-way case split that some geometry function
compiles down to.
-/

open Lean

namespace AtkP

partial def allConsts : Expr -> Array Name -> Array Name
  | .const c _,        acc => acc.push c
  | .app f a,          acc => allConsts a (allConsts f acc)
  | .lam _ t b _,      acc => allConsts b (allConsts t acc)
  | .forallE _ t b _,  acc => allConsts b (allConsts t acc)
  | .letE _ t v b _,   acc => allConsts b (allConsts v (allConsts t acc))
  | .mdata _ e,        acc => allConsts e acc
  | .proj s _ e,       acc => allConsts e (acc.push s)
  | _,                 acc => acc

def isThm (env : Environment) (n : Name) : Bool :=
  match env.find? n with | some (.thmInfo _) => true | _ => false

def valOf (env : Environment) (n : Name) : Option Expr :=
  match env.find? n with
  | some (.defnInfo v)   => some v.value
  | some (.thmInfo v)    => some v.value
  | some (.opaqueInfo v) => some v.value
  | _ => none

def compDeps (env : Environment) (n : Name) : Array Name :=
  if isThm env n then #[] else (valOf env n).map (allConsts · #[]) |>.getD #[]

/-- BFS from root recording a parent pointer, so we can exhibit a real call
    path rather than merely asserting reachability. -/
partial def bfs (env : Environment) (frontier : List Name)
    (parent : Std.HashMap Name Name) : Std.HashMap Name Name :=
  match frontier with
  | [] => parent
  | _ =>
    let (nextFrontier, parent') :=
      frontier.foldl (fun (acc : List Name × Std.HashMap Name Name) n =>
        (compDeps env n).foldl (fun (acc2 : List Name × Std.HashMap Name Name) c =>
          if acc2.2.contains c then acc2
          else (c :: acc2.1, acc2.2.insert c n)) acc) ([], parent)
    bfs env nextFrontier parent'

partial def pathTo (parent : Std.HashMap Name Name) (root : Name) (n : Name)
    (fuel : Nat) (acc : List Name) : List Name :=
  match fuel with
  | 0 => n :: acc
  | fuel + 1 =>
    if n == root then n :: acc
    else match parent[n]? with
      | some p => if p == n then n :: acc else pathTo parent root p fuel (n :: acc)
      | none => n :: acc

partial def closureAux (env : Environment) (seen : Std.HashSet Name)
    (out : Array Name) : List Name -> Std.HashSet Name × Array Name
  | [] => (seen, out)
  | n :: rest =>
      if seen.contains n then closureAux env seen out rest
      else closureAux env (seen.insert n) (out.push n) ((compDeps env n).toList ++ rest)

def baseTargets : List Name :=
  [ `RMQ.Cartesian.CartesianShape.casesOn
  , `RMQ.Cartesian.CartesianShape.brecOn
  , `RMQ.Cartesian.CartesianShape.below
  , `RMQ.Cartesian.CartesianShape.rec
  , `RMQ.Cartesian.CartesianShape.bpCode
  , `RMQ.Cartesian.CartesianShape.size
  , `WellFounded.fix
  , `Decidable.decide ]

def run (env : Environment) (label : String) (root : Name)
    (lines : Array String) : Array String := Id.run do
  let mut lines := lines
  let cl := (closureAux env {} #[] [root]).2
  let clSet : Std.HashSet Name := cl.foldl (fun s n => s.insert n) {}
  let parent := bfs env [root] (Std.HashMap.emptyWithCapacity.insert root root)
  -- every matcher / hygienic auxiliary in the closure that mentions the shape
  let extra := (cl.filter (fun n =>
    (n.toString.splitOn "reprCartesianShape").length > 1 ||
    ((n.toString.splitOn "match_").length > 1 &&
     ((valOf env n).map (fun v => (allConsts v #[]).any (fun c =>
        c == `RMQ.Cartesian.CartesianShape.empty ||
        c == `RMQ.Cartesian.CartesianShape.node ||
        c == `RMQ.Cartesian.CartesianShape.rec))).getD false))).toList
  let targets := extra ++ baseTargets
  lines := lines.push ""
  lines := lines.push s!"############ {label}  root={root}  closure={cl.size} ############"
  lines := lines.push s!"  shape-mentioning matchers found in closure: {extra}"
  for t in targets do
    lines := lines.push ""
    lines := lines.push s!"=== TARGET {t} ==="
    if !clSet.contains t then
      lines := lines.push "    NOT IN CLOSURE"
    else
      -- all direct referrers inside the closure
      let mut refs : Array Name := #[]
      for n in cl do
        if (compDeps env n).contains t then refs := refs.push n
      lines := lines.push s!"    DIRECT_REFERRERS ({refs.size}):"
      for r in refs do lines := lines.push s!"       <- {r}"
      let p := pathTo parent root t 200 []
      lines := lines.push s!"    SHORTEST_PATH_FROM_ROOT ({p.length} hops):"
      for x in p do lines := lines.push s!"       . {x}"
  return lines

run_cmd do
  let env <- Lean.getEnv
  let mut lines : Array String := #[]
  lines := run env "ROOT-A store-param whole query"
    `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore lines
  lines := run env "ROOT-B public queryTraceResultWithStore"
    `RMQ.SuccinctClassic.queryTraceResultWithStore lines
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/atk_paths_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"wrote atk_paths_out.txt ({lines.size} lines)"

end AtkP
