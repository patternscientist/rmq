import RMQ.Core.SuccinctRMQClassic
import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.SuccinctFinal
import Lean

open Lean

/-- Constants in the definitional VALUE of `n`; theorems skipped entirely. -/
def advValueDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some (.thmInfo _) => #[]
  | some ci =>
      match ci.value? with
      | some e => e.getUsedConstants
      | none => #[]
  | none => #[]

partial def advPath (env : Environment) (start : Name) (target : Name) :
    Option (List Name) :=
  let rec go (frontier : List Name) (seen : Std.HashSet Name)
      (parent : Std.HashMap Name Name) (fuel : Nat) :
      Option (Std.HashMap Name Name) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      if frontier.isEmpty then none
      else
        let (next, seen, parent) :=
          frontier.foldl
            (fun (acc : List Name × Std.HashSet Name × Std.HashMap Name Name) c =>
              (advValueDeps env c).foldl
                (fun (acc2 : List Name × Std.HashSet Name × Std.HashMap Name Name) d =>
                  let (nx2, sn2, pr2) := acc2
                  if sn2.contains d then acc2
                  else (d :: nx2, sn2.insert d, pr2.insert d c))
                acc)
            ([], seen, parent)
        if seen.contains target then some parent
        else go next seen parent fuel'
  match go [start] ((Std.HashSet.emptyWithCapacity : Std.HashSet Name).insert start)
      (Std.HashMap.emptyWithCapacity) 300 with
  | none => none
  | some parent =>
      let rec build (cur : Name) (acc : List Name) (fuel : Nat) : List Name :=
        match fuel with
        | 0 => acc
        | fuel' + 1 =>
            if cur == start then start :: acc
            else match parent[cur]? with
              | some p => build p (cur :: acc) fuel'
              | none => cur :: acc
      some (build target [] 300)

def advTargets : List Name :=
  [``RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankSuperOverhead,
   ``RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlockOverhead]

def advStarts : List Name :=
  [``RMQ.SuccinctClassic.queryTraceResultWithStore,
   ``RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore,
   ``RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram,
   ``RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore,
   ``RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore]

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env <- getEnv
  for s in advStarts do
    for t in advTargets do
      match advPath env s t with
      | none => logInfo m!"UNREACHABLE: {s}  -X->  {t}"
      | some p => logInfo m!"REACHABLE depth={p.length - 1}: {p}"
