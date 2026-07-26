import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F3/F4 reachability probe.

Value-only (proof-free) dependency BFS with parent tracking, so we can print the
SHORTEST definitional chain from each root to
  RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankSuperOverhead   (F4)
  RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlockOverhead   (F3)
-/

open Lean

namespace F34Reach

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

/-- BFS from `root`, returning parent map. -/
partial def bfs (env : Environment) (root : Name) :
    Std.HashMap Name Name := Id.run do
  let mut parent : Std.HashMap Name Name := Std.HashMap.emptyWithCapacity
  let mut seen : Std.HashSet Name := Std.HashSet.emptyWithCapacity
  let mut queue : Array Name := #[root]
  seen := seen.insert root
  parent := parent.insert root root
  let mut i := 0
  while i < queue.size do
    let n := queue[i]!
    i := i + 1
    for d in compDeps env n do
      if !seen.contains d then
        seen := seen.insert d
        parent := parent.insert d n
        queue := queue.push d
  return parent

def chain (parent : Std.HashMap Name Name) (root target : Name) : Option (List Name) := Id.run do
  if !parent.contains target then return none
  let mut path : List Name := [target]
  let mut cur := target
  let mut fuel := 200
  while cur != root && fuel > 0 do
    fuel := fuel - 1
    match parent[cur]? with
    | none => return none
    | some p =>
        path := p :: path
        cur := p
  return some path

def f3 : Name := `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlockOverhead
def f4 : Name := `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankSuperOverhead

def roots : List (String × Name) :=
  [ ("TOP whole-query with store",
      `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore),
    ("dispatcher evalGlobalWordTraceWithStore",
      `RMQ.SuccinctFinal.WholeQueryInstr.evalGlobalWordTraceWithStore),
    ("L1 selectClose leaf",
      `RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore),
    ("L2 lcaClose leaf",
      `RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore),
    ("L3 rankClose leaf",
      `RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore),
    ("STORE construction (26-segment read store)",
      `RMQ.BPNavigation.concreteBPCloseNavigationGlobalReadStore),
    ("program instruction list",
      `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram) ]

def report : MetaM Unit := do
  let env <- Lean.getEnv
  for (label, r) in roots do
    if env.find? r |>.isNone then
      IO.println s!"ROOT MISSING: {label} = {r}"
    else
      let parent := bfs env r
      for (tag, t) in [("F3 BlockOverhead", f3), ("F4 SuperOverhead", f4)] do
        match chain parent r t with
        | none => IO.println s!"[{label}] {tag}: NOT REACHABLE"
        | some p =>
            IO.println s!"[{label}] {tag}: REACHABLE, depth {p.length - 1}"
            for step in p do
              IO.println s!"      {step}"
    IO.println "---"

end F34Reach

open Lean Elab Meta in
run_cmd Command.liftTermElabM F34Reach.report
