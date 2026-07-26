import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
REGIME RELEVANCE: is each regime predicate on the QUERY path or only on the
STORE-CONSTRUCTION path?

The cross-shape sweep is only informative about a regime if that regime is
reachable from the controller.  We compute two computational closures (values
only, theorems skipped, same method as f03_inventory2.lean):

  Q = closure of `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore`
      -- the STORE-PARAMETRIC controller (what the sweep varies the shape of)
  S = closure of `BPNavigation.concreteBPCloseNavigationGlobalReadStore`
      -- the memory image (a data structure MAY depend on the data; class B)

A regime constant in S \ Q is BUILD-ONLY (B): the query learns its outcome by
probing.  A regime constant in Q is a live query-time branch and the sweep must
straddle its threshold.
-/

open Lean

namespace WQRegime

def qRoot : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
def sRoot : Name :=
  `RMQ.BPNavigation.concreteBPCloseNavigationGlobalReadStore

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

/-- The regime / branch predicates we care about. -/
def probes : List (String × Name) :=
  [ ("summaryTableActive",        `RMQ.SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive)
  , ("summaryTableActive_dec",    `RMQ.SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive_decidable)
  , ("summaryBlockSize(if)",      `RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSize)
  , ("summaryBlockCount(if)",     `RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockCount)
  , ("summaryBlocksPerSuper(if)", `RMQ.SuccinctClose.canonicalBPRelativeSummaryBlocksPerSuper)
  , ("summaryRelativeWidth(if)",  `RMQ.SuccinctClose.canonicalBPRelativeSummaryRelativeWidth)
  , ("summarySuperCount(if)",     `RMQ.SuccinctClose.canonicalBPRelativeSummarySuperCount)
  , ("summaryLargeRegime",        `RMQ.SuccinctClose.canonicalBPRelativeSummaryLargeRegime)
  , ("rmmInteriorReadyThreshold", `RMQ.SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold)
  , ("superIsLong",               `RMQ.GenericSelect.superIsLong)
  , ("localIsSparse",             `RMQ.GenericSelect.localIsSparse)
  , ("localIsSparseException",    `RMQ.GenericSelect.localIsSparseException)
  , ("compactLocalEntryIsLive",   `RMQ.GenericSelect.compactLocalEntryIsLive)
  , ("sparseExceptionSelectData", `RMQ.GenericSelect.sparseExceptionSelectData)
  , ("localSpan",                 `RMQ.GenericSelect.localSpan)
  , ("superSpan",                 `RMQ.GenericSelect.superSpan)
  , ("occurrenceCount",           `RMQ.GenericSelect.occurrenceCount)
  , ("Succinct.select",           `RMQ.Succinct.select)
  , ("Succinct.rankPrefix",       `RMQ.Succinct.rankPrefix)
  , ("bpExcessAt",                `RMQ.SuccinctClose.bpExcessAt)
  , ("bpCode",                    `RMQ.Cartesian.CartesianShape.bpCode)
  , ("size",                      `RMQ.Cartesian.CartesianShape.size)
  , ("summaryTable_canonical",    `RMQ.SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical)
  , ("rmmInteriorLocalTable",     `RMQ.SuccinctClose.concreteBPRelativeRmmInteriorLocalTable)
  , ("rmmInteriorGlobalTable",    `RMQ.SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable)
  ]

run_cmd do
  let env <- Lean.getEnv
  let (qSeen, qArr) := closureAux env {} #[] [qRoot]
  let (sSeen, sArr) := closureAux env {} #[] [sRoot]
  let mut lines : Array String := #[]
  lines := lines.push s!"Q = closure({qRoot})  size={qArr.size}"
  lines := lines.push s!"S = closure({sRoot})  size={sArr.size}"
  lines := lines.push ""
  lines := lines.push "name | inQuery | inStore | verdict"
  for (label, n) in probes do
    let inQ := qSeen.contains n
    let inS := sSeen.contains n
    let exists? := (env.find? n).isSome
    let verdict :=
      if !exists? then "NAME-NOT-FOUND (check spelling)"
      else if inQ then "LIVE ON QUERY PATH"
      else if inS then "BUILD-ONLY (B): in store closure, NOT in query closure"
      else "in neither closure"
    lines := lines.push s!"{label} | inQ={inQ} | inS={inS} | {verdict}"
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/wq_regimemember_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"Q={qArr.size} S={sArr.size}"

end WQRegime
