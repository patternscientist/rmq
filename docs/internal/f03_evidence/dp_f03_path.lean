import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
DP-F03 (b) part 5: shortest VALUE-LEVEL dependency paths from the controller
root to each constant that hosts a content-reading branch, and the exact field
values of the rank directory that feed the two divisor slots flagged
X-CANDIDATE by the backward slice.
-/

open Lean

namespace DPF03Path

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def isTheorem (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

def valueOf (env : Environment) (n : Name) : Option Expr :=
  if isTheorem env n then none
  else match env.find? n with
    | none => none
    | some ci => ci.value?

def compDeps (env : Environment) (n : Name) : List Name :=
  match valueOf env n with
  | some v => v.foldConsts [] (fun c a => c :: a)
  | none => []

def targets : List Name :=
  [`RMQ.SuccinctClose.bpExcessAt,
   `RMQ.SuccinctClose.bpBetterArgMinBlock,
   `RMQ.SuccinctClose.bpBlockArgMinPrefixPosFrom,
   `RMQ.Succinct.rankPrefix,
   `RMQ.Succinct.selectFrom,
   `RMQ.RAM.boolRankPrefix,
   `RMQ.RAM.boolSelectFrom,
   `RMQ.GenericSelect.occurrenceCount,
   `RMQ.GenericSelect.superIsLong,
   `RMQ.GenericSelect.localIsSparseException,
   `RMQ.SuccinctClose.bpSuperblockBaselineEntries,
   `RMQ.SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable,
   `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex,
   `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex,
   `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData]

run_cmd do
  let env <- Lean.getEnv
  -- BFS from root over value dependencies, recording parents
  let mut parent : Std.HashMap Name Name := {}
  let mut seen : Std.HashSet Name := {}
  seen := seen.insert root
  let mut frontier : Array Name := #[root]
  while frontier.size > 0 do
    let mut next : Array Name := #[]
    for n in frontier do
      for d in compDeps env n do
        if !seen.contains d then
          seen := seen.insert d
          parent := parent.insert d n
          next := next.push d
    frontier := next
  let mut lines : Array String := #[]
  for t in targets do
    if !seen.contains t then
      lines := lines.push s!"NOT_REACHABLE {t}"
    else
      let mut path : Array Name := #[t]
      let mut cur := t
      let mut guard := 0
      while cur != root && guard < 200 do
        guard := guard + 1
        match parent[cur]? with
        | some p => path := path.push p; cur := p
        | none => break
      let rev := path.reverse
      lines := lines.push s!"PATH to {t} (length {rev.size}):"
      for (i, n) in rev.toList.zipIdx do
        lines := lines.push s!"    [{i}] {n}"
      lines := lines.push ""
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/dp_f03_path_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"paths written, reachableTotal={seen.size}"

end DPF03Path
