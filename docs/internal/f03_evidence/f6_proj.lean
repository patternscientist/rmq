import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
Machine inventory: which projections of the CONTENT-carrying structures does
the L1 trace EVALUATOR actually read?

`concreteBPNativeSelectCloseGlobalWordTraceResultWithStore` is definitionally
  EVAL (sparseExceptionSelectData shape.bpCode false) LAYOUT 21 22 store C idx
where EVAL = `SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore`.
The content lives in the ARGUMENT; the question is what EVAL reads out of it.

Take the transitive constant closure over definitional VALUES only (theorems
skipped: a proof term cannot influence an executed address) of EVAL alone, and
print every structure projection in it.
-/

open Lean

namespace F6Proj

def root : Name :=
  `RMQ.GenericSelect.SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore

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

def structs : List Name :=
  [ `RMQ.GenericSelect.SparseExceptionSelectData
  , `RMQ.GenericSelect.SparseExceptionDirectory
  , `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
  , `RMQ.GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
  , `RMQ.SuccinctSpace.BoundedPayloadWordStore
  , `RMQ.SuccinctSpace.FixedWidthNatTable
  , `RMQ.SuccinctSpace.PayloadWordStore ]

def suspects : List Name :=
  [ `RMQ.GenericSelect.superEntries
  , `RMQ.GenericSelect.localEntries
  , `RMQ.GenericSelect.longSuperRelativeEntries
  , `RMQ.GenericSelect.sparseExceptionRelativeEntries
  , `RMQ.GenericSelect.longSuperFlagBits
  , `RMQ.GenericSelect.sparseExceptionEffectiveFlagBits
  , `RMQ.GenericSelect.occurrenceCount
  , `RMQ.Succinct.rankPrefix
  , `RMQ.Cartesian.CartesianShape.bpCode
  , `RMQ.SuccinctSpace.BoundedPayloadWordStore.ofChunks
  , `RMQ.GenericSelect.sparseExceptionSelectData
  , `RMQ.GenericSelect.superStride
  , `RMQ.GenericSelect.localStride
  , `RMQ.GenericSelect.wordBits ]

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env <- getEnv
  let (seen, out) := closureAux env {} #[] [root]
  logInfo m!"EVAL closure size (values only, theorems skipped) = {out.size}"
  for s in structs do
    let fields := out.toList.filter (fun n => s.isPrefixOf n && n != s)
    logInfo m!"--- {s} : {fields.length} reachable members ---"
    for f in fields do
      logInfo m!"      {f}"
  for s in suspects do
    logInfo m!"reaches {s} : {seen.contains s}"

end F6Proj
