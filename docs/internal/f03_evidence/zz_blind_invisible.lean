import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
The INVISIBLE CONSUMER set.

The instrument lists exactly the 25 constants that syntactically apply
`CartesianShape.bpCode`. F03 additionally demands "universal consumers".
Here we compute every core constant that transitively depends on one of the
6 CONTENT constants but is itself absent from the instrument's 25 rows.
-/

open Lean

namespace ZZInv

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

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

/-- The 6 CONTENT constants (genuine shape-content readers). -/
def contentSix : List Name := [
  `RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore,
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData,
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlockOverhead,
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankSuperOverhead,
  `RMQ.SuccinctClose.bpExcessAt,
  `RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
]

def bpCodeN : Name := `RMQ.Cartesian.CartesianShape.bpCode

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => m
      | none => .anonymous
  | none => .anonymous

run_cmd do
  let env <- Lean.getEnv
  let cl := (closureAux env {} #[] [root]).2
  let clSet : Std.HashSet Name := cl.foldl (fun s n => s.insert n) {}

  -- Set A: the instrument's 25 rows = core constants naming bpCode in their value.
  let mut setA : Std.HashSet Name := {}
  for n in cl do
    if isTheorem env n then continue
    match (env.find? n).bind (fun ci => ci.value?) with
    | none => pure ()
    | some v =>
      if v.foldConsts false (fun c a => a || c == bpCodeN) then
        setA := setA.insert n

  -- reverse edges restricted to the core
  let mut rev : Std.HashMap Name (Array Name) := {}
  for n in cl do
    if isTheorem env n then continue
    for d in compDeps env n do
      if clSet.contains d then
        rev := rev.insert d ((rev.getD d #[]).push n)

  -- reverse reachability from the 6 content constants
  let mut reached : Std.HashSet Name := {}
  let mut work : List Name := contentSix
  while !work.isEmpty do
    match work with
    | [] => pure ()
    | n :: rest =>
      work := rest
      for r in rev.getD n #[] do
        if !reached.contains r then
          reached := reached.insert r
          work := r :: work

  let mut invisible : Array Name := #[]
  for n in cl do
    if reached.contains n && !setA.contains n then
      invisible := invisible.push n

  let mut lines : Array String := #[]
  lines := lines.push s!"CORE {cl.size}"
  lines := lines.push s!"INSTRUMENT_ROWS_SET_A {setA.size}"
  lines := lines.push s!"CONTENT_DEPENDENT_REACHABLE {reached.size}"
  lines := lines.push s!"INVISIBLE_CONSUMERS {invisible.size}"
  lines := lines.push ""
  lines := lines.push "== CONTENT-DEPENDENT CORE CONSTANTS ABSENT FROM ALL 25 INSTRUMENT ROWS =="
  for n in invisible do
    lines := lines.push s!"  INVISIBLE {n} :: mod={moduleOf env n}"

  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/zz_blind_invisible_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"setA={setA.size} reached={reached.size} invisible={invisible.size}"

end ZZInv
