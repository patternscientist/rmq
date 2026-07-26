import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
ADVERSARIAL F5 attack, reachability lens.

The benign verdict P for `bpExcessAt` rests on a VERTEX-CUT claim: every
executed path from the whole-query root to `bpExcessAt` passes through one of
six content-bearing entries lists, and each of those six is consumed only
through `List.length`.

This file attacks that claim directly:
  (A) forward reachability root -> bpExcessAt with the six lists BLOCKED
      (value level and IR level).  A surviving path = uncovered channel.
  (B) full parent inventory of the six lists (value level, superset of IR).
  (C) parent inventory of canonicalRelativeRmmInteriorComponentOffsets and of
      canonicalRelativeRmmSummaryTable -- the "build side" constructor that the
      benign write-up called pure-build but which the offsets computation uses.
-/

open Lean

namespace AdvR

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def tgt : Name := `RMQ.SuccinctClose.bpExcessAt

def six : List Name :=
  [ `RMQ.SuccinctClose.bpSuperblockBaselineEntries
  , `RMQ.SuccinctClose.bpBlockRelativeMinExcessEntries
  , `RMQ.SuccinctClose.bpBlockRelativeMaxExcessEntries
  , `RMQ.SuccinctClose.bpBlockArgMinLocalOffsetEntries
  , `RMQ.SuccinctClose.bpLocalSparseOffsetEntries
  , `RMQ.SuccinctClose.bpGlobalSparseBlockEntries ]

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

/-- Forward closure, skipping a blocked set entirely (cannot route through). -/
partial def closureBlocked (env : Environment) (blocked : Std.HashSet Name)
    (seen : Std.HashSet Name) (out : Array Name) :
    List Name -> Std.HashSet Name × Array Name
  | [] => (seen, out)
  | n :: rest =>
      if seen.contains n || blocked.contains n then
        closureBlocked env blocked seen out rest
      else
        let seen := seen.insert n
        let out := out.push n
        closureBlocked env blocked seen out (compDeps env n ++ rest)

def irDeps (env : Environment) (n : Name) : Option (List Name) :=
  match IR.findEnvDecl env n with
  | none => none
  | some d =>
      let s : NameSet := (((IR.CollectUsedDecls.collectDecl d).run env).run {}).1
      some (s.toList)

partial def irClosureBlocked (env : Environment) (blocked : Std.HashSet Name)
    (seen : Std.HashSet Name) (out : Array Name) :
    List Name -> Std.HashSet Name × Array Name
  | [] => (seen, out)
  | n :: rest =>
      if seen.contains n || blocked.contains n then
        irClosureBlocked env blocked seen out rest
      else
        let seen := seen.insert n
        let out := out.push n
        match irDeps env n with
        | none => irClosureBlocked env blocked seen out rest
        | some ds => irClosureBlocked env blocked seen out (ds ++ rest)

/-- Shortest path root -> tgt in the blocked graph, if any (value level). -/
partial def bfsPath (env : Environment) (blocked : Std.HashSet Name)
    (tgt : Name) : Option (List Name) := Id.run do
  let mut frontier : Array (List Name) := #[[root]]
  let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert root
  for _ in List.range 40 do
    let mut next : Array (List Name) := #[]
    for p in frontier do
      match p with
      | [] => pure ()
      | cur :: _ =>
        for d in (compDeps env cur).eraseDups do
          if d == tgt then
            return some ((d :: p).reverse)
          if !seen.contains d && !blocked.contains d then
            seen := seen.insert d
            next := next.push (d :: p)
    if next.isEmpty then return none
    frontier := next
  return none

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advR_f5_cut_out.txt"

run_cmd do
  let env <- Lean.getEnv
  let mut lines : Array String := #[]

  -- baseline: unblocked
  let (seen0, out0) := closureBlocked env {} {} #[] [root]
  lines := lines.push s!"VALUE_CORE {out0.size} bpExcessAt_reachable={seen0.contains tgt}"

  -- (A) value level with the six blocked
  let blocked : Std.HashSet Name := six.foldl (fun s n => s.insert n) {}
  let (seenB, outB) := closureBlocked env blocked {} #[] [root]
  lines := lines.push s!"VALUE_CORE_SIX_BLOCKED {outB.size} bpExcessAt_reachable={seenB.contains tgt}"
  match bfsPath env blocked tgt with
  | none => lines := lines.push "VALUE_BYPASS_PATH none"
  | some p =>
      lines := lines.push "VALUE_BYPASS_PATH FOUND:"
      for x in p do lines := lines.push s!"   {x}"

  -- (A') IR level
  let (seenI, outI) := irClosureBlocked env {} {} #[] [root]
  lines := lines.push s!"IR_CLOSURE {outI.size} bpExcessAt_reachable={seenI.contains tgt}"
  let (seenIB, outIB) := irClosureBlocked env blocked {} #[] [root]
  lines := lines.push s!"IR_CLOSURE_SIX_BLOCKED {outIB.size} bpExcessAt_reachable={seenIB.contains tgt}"

  -- which of the five direct callers survive the cut at IR level
  let callers : List Name :=
    [ `RMQ.SuccinctClose.bpBetterArgMinBlock
    , `RMQ.SuccinctClose.bpBlockArgMinPrefixPosFrom
    , `RMQ.SuccinctClose.bpBlockExcessSamples
    , `RMQ.SuccinctClose.bpRelativeExcessEntry
    , `RMQ.SuccinctClose.bpBlockMinExcess
    , `RMQ.SuccinctClose.bpBlockMaxExcess
    , `RMQ.SuccinctClose.bpBlockArgMinPrefixPos
    , `RMQ.SuccinctClose.bpRangeMinExcess
    , `RMQ.SuccinctClose.bpRangeArgMinPrefixPos ]
  lines := lines.push "== direct/near callers still reachable with six blocked =="
  for c in callers do
    lines := lines.push s!"  value={seenB.contains c} ir={seenIB.contains c}  {c}"

  -- (B) full parent inventory of the six, value level
  lines := lines.push ""
  lines := lines.push "== VALUE-LEVEL parents of each of the six entries lists (within core) =="
  for s in six do
    let mut ps : Array Name := #[]
    for n in out0 do
      if (compDeps env n).contains s then ps := ps.push n
    lines := lines.push s!"  {s}  parents={ps.size}"
    for p in ps do lines := lines.push s!"      <- {p}"

  -- (C) parents of the offsets and of the summary table constructor
  lines := lines.push ""
  lines := lines.push "== VALUE-LEVEL parents of offsets / table constructors =="
  for s in [`RMQ.SuccinctClose.canonicalRelativeRmmInteriorComponentOffsets,
            `RMQ.SuccinctClose.canonicalRelativeRmmSummaryTable,
            `RMQ.SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable,
            `RMQ.SuccinctSpace.FixedWidthNatTable.machineStore,
            `RMQ.SuccinctSpace.fixedWidthNatTableMachineWords] do
    let mut ps : Array Name := #[]
    for n in out0 do
      if (compDeps env n).contains s then ps := ps.push n
    lines := lines.push s!"  {s}  parents={ps.size} inIR={seenI.contains s}"
    for p in ps do lines := lines.push s!"      <- {p}"

  IO.FS.writeFile outPath (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"done value={out0.size} valueBlocked={outB.size} ir={outI.size} irBlocked={outIB.size}"

end AdvR
