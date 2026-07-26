import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
Reverse-dependency closure inside the computational core.

Two questions the forward instrument cannot answer:
 (1) WHO drags the shape eliminators (rec/casesOn/brecOn/below, the Repr
     matcher, the constructors) into the core?
 (2) Are the 19 "LENGTH-ONLY, derivable from n" constants really benign, or
     do they hand `shape` on to a CONTENT constant?
-/

open Lean

namespace ZZRev

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

/-- The 6 CONTENT constants reported by the coordinator's instrument. -/
def contentSix : List Name := [
  `RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore,
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData,
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlockOverhead,
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankSuperOverhead,
  `RMQ.SuccinctClose.bpExcessAt,
  `RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
]

/-- The 19 constants the instrument called "length-only, derivable from n". -/
def lengthOnly19 : List Name := [
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankWordSize,
  `RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore,
  `RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPBlockWordsTraceResultWithStore,
  `RMQ.SuccinctClose.localBPWindowBase,
  `RMQ.SuccinctClose.bpBlockArgMinPrefixPos,
  `RMQ.SuccinctClose.bpBlockArgMinPrefixPosFrom,
  `RMQ.SuccinctClose.bpBlockMinExcess,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineReadNatComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmInteriorComponentOffsets,
  `RMQ.SuccinctClose.canonicalRelativeRmmInteriorComponentStore,
  `RMQ.SuccinctClose.canonicalRelativeRmmGlobalLevelMachineStore,
  `RMQ.SuccinctClose.canonicalRelativeRmmLocalLevelMachineStore,
  `RMQ.SuccinctClose.canonicalRelativeRmmGlobalMachineStore,
  `RMQ.SuccinctClose.canonicalRelativeRmmLocalMachineStore,
  `RMQ.SuccinctClose.canonicalRelativeRmmSummaryMachineStore,
  `RMQ.SuccinctClose.RelativeRmm.Layout.superWidth,
  `RMQ.SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable,
  `RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore,
  `RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
]

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

  -- direct reverse edges within the core
  let mut rev : Std.HashMap Name (Array Name) := {}
  for n in cl do
    if isTheorem env n then continue
    for d in compDeps env n do
      if clSet.contains d then
        rev := rev.insert d ((rev.getD d #[]).push n)

  let mut lines : Array String := #[]

  -- Q1: who drags in the eliminators / Repr matcher / constructors?
  lines := lines.push "== DIRECT CORE REFERENCERS OF SHAPE ELIMINATORS/CTORS =="
  let elims : List Name := [
    `RMQ.Cartesian.CartesianShape.rec,
    `RMQ.Cartesian.CartesianShape.casesOn,
    `RMQ.Cartesian.CartesianShape.brecOn,
    `RMQ.Cartesian.CartesianShape.below,
    `RMQ.Cartesian.CartesianShape.node,
    `RMQ.Cartesian.CartesianShape.empty,
    `RMQ.Cartesian.CartesianShape.bpCode,
    `RMQ.Cartesian.CartesianShape.size
  ]
  -- the Repr matcher carries a hygienic suffix, so resolve it by scanning
  let mut elims := elims
  for n in cl do
    if (n.toString.splitOn "reprCartesianShape").length > 1 then
      elims := elims ++ [n]
  for e in elims do
    let rs := rev.getD e #[]
    let mut uniq : Array Name := #[]
    for r in rs do
      if !uniq.contains r then uniq := uniq.push r
    lines := lines.push s!"  {e}"
    if uniq.isEmpty then
      lines := lines.push "      <no core referencer -- reached as a ROOT-side entry only>"
    for r in uniq do
      lines := lines.push s!"      <- {r}"

  -- Q2: do the 19 "length-only" constants reach a CONTENT constant?
  lines := lines.push ""
  lines := lines.push "== DO THE 19 LENGTH-ONLY CONSTANTS REACH A CONTENT CONSTANT? =="
  let contentSet : Std.HashSet Name := contentSix.foldl (fun s n => s.insert n) {}
  for n in lengthOnly19 do
    let sub := (closureAux env {} #[] [n]).2
    let mut hits : Array Name := #[]
    for m in sub do
      if contentSet.contains m && m != n then hits := hits.push m
    let verdict := if hits.isEmpty then "pure-size" else "REACHES CONTENT"
    let hs := String.intercalate "," (hits.toList.map (fun c => c.toString))
    lines := lines.push s!"  {n} :: {verdict} [{hs}]"

  -- Q3: is any CONTENT constant reachable ONLY through a length-only one?
  lines := lines.push ""
  lines := lines.push "== CORE REFERENCERS OF EACH CONTENT CONSTANT =="
  for c in contentSix do
    let rs := rev.getD c #[]
    let mut uniq : Array Name := #[]
    for r in rs do
      if !uniq.contains r then uniq := uniq.push r
    lines := lines.push s!"  {c}  (inCore={clSet.contains c})"
    for r in uniq do
      lines := lines.push s!"      <- {r}"

  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/zz_blind_rev_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"core={cl.size} done"

end ZZRev
