import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-! Shortest value-only dependency path from the L2 (lcaClose) leaf to F2. -/

open Lean

namespace F03F2Path

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

partial def bfs (env : Environment) (goal : Name)
    (seen : Std.HashSet Name) (parent : Std.HashMap Name Name)
    : List Name -> Option (Std.HashMap Name Name)
  | [] => none
  | n :: rest =>
      if n == goal then some parent
      else
        let ds := compDeps env n
        let (seen, parent, queue) :=
          ds.foldl (fun (acc : Std.HashSet Name × Std.HashMap Name Name × List Name) d =>
            if acc.1.contains d then acc
            else (acc.1.insert d, acc.2.1.insert d n, acc.2.2 ++ [d]))
            (seen, parent, ([] : List Name))
        bfs env goal seen parent (rest ++ queue)

partial def unwind (parent : Std.HashMap Name Name) (n : Name) (fuel : Nat)
    : List Name :=
  match fuel with
  | 0 => [n]
  | fuel + 1 =>
      match parent[n]? with
      | none => [n]
      | some p => n :: unwind parent p fuel

def target : Name := `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData

run_cmd do
  let env <- Lean.getEnv
  for (label, root) in
    [ ("L2-lcaClose",
       `RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore) ] do
    let seen0 : Std.HashSet Name := ({} : Std.HashSet Name).insert root
    match bfs env target seen0 ({} : Std.HashMap Name Name) [root] with
    | none => Lean.logInfo m!"{label}: NOT REACHABLE"
    | some parent =>
        let path := (unwind parent target 200).reverse
        Lean.logInfo m!"{label} path length {path.length}"
        for p in path do
          Lean.logInfo m!"   {p}"

end F03F2Path
