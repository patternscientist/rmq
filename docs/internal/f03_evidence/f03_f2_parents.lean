import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F03 / F2, exhaustive: EVERY constant in the whole-query controller's
value-only closure that directly mentions `builtRelativeSplitBPCloseRankData`.
Plus the same for the concrete global read store (the BUILD side).
-/

open Lean

namespace F03F2Par

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
      else closureAux env (seen.insert n) (out.push n) (compDeps env n ++ rest)

def target : Name := `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData

run_cmd do
  let env <- Lean.getEnv
  for (label, root) in
    [ ("CONTROLLER (whole query, store-parametric)",
       `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore),
      ("BUILD SIDE (concrete global read store)",
       `RMQ.BPNavigation.concreteBPCloseNavigationGlobalReadStore) ] do
    let cl := (closureAux env {} #[] [root]).2
    let mut parents : Array Name := #[]
    for n in cl do
      if (compDeps env n).contains target && n != target then
        parents := parents.push n
    Lean.logInfo m!"{label}: closure={cl.size}  directParentsOfF2={parents.size}"
    for p in parents do
      Lean.logInfo m!"    <- {p}"

end F03F2Par
