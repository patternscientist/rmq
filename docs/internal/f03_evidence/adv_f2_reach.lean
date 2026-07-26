import RMQ.Core.SuccinctRMQClassic
import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
ADVERSARIAL re-check of the F2 (`builtRelativeSplitBPCloseRankData`) verdict S.

Independent of the defending agent's scripts. Three questions:

Q1. Direct parents of F2 in the value-only closure of FOUR roots, not one:
    the store-parametric whole query (their root), the NON-store whole query
    (used by the primary public entry `SuccinctClassic.queryTraceResult`), and
    both public entries.

Q2. Sharper than Q1: does any constant in each controller closure mention a
    CONTENT-bearing projection/derived accessor of
    `TwoLevelPayloadLiveStoredWordRankData` at all? A consumer could receive
    `data` as an argument and project `.bitWords` without ever naming F2.
    Q1 alone would miss that. This is the real exhaustiveness test.

Q3. Which projections does the leaf itself mention (ground truth)?
-/

open Lean

namespace AdvF2

def isThm (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

/-- value-only dependencies: theorems contribute nothing executable. -/
def deps (env : Environment) (n : Name) : List Name :=
  if isThm env n then []
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
      else closureAux env (seen.insert n) (out.push n) (deps env n ++ rest)

def closure (env : Environment) (root : Name) : Array Name :=
  (closureAux env {} #[] [root]).2

def F2 : Name := `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData

/-- Every accessor of the rank structure that can expose CONTENT (as opposed
to the three size-only scalars `wordSize`, `blocksPerSuper`, and `bits.length`). -/
def contentAccessors : List Name :=
  [ `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bitWords,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superTables,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockTables,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superTrueEntries,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superFalseEntries,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockTrueEntries,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockFalseEntries,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superWidth,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockWidth,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superSampleWords,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockSampleWords,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superPayload,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockPayload,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.auxPayload,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankCosted,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.mk ]

def roots : List (String × Name) :=
  [ ("A store-param whole query (defender's root)",
     `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore),
    ("B NON-STORE whole query (primary public route)",
     `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult),
    ("C public queryTraceResult (List Int)",
     `RMQ.SuccinctClassic.queryTraceResult),
    ("D public queryTraceResultWithStore (List Int)",
     `RMQ.SuccinctClassic.queryTraceResultWithStore),
    ("E L3 leaf store-param",
     `RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore),
    ("F L3 leaf NON-store",
     `RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegment),
    ("G leaf body (generic)",
     `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore) ]

run_cmd do
  let env <- Lean.getEnv
  for (label, root) in roots do
    match env.find? root with
    | none => Lean.logInfo m!"{label}: ROOT NOT FOUND {root}"
    | some _ =>
      let cl := closure env root
      -- Q1: direct parents of F2
      let mut parents : Array Name := #[]
      for n in cl do
        if n != F2 && (deps env n).contains F2 then parents := parents.push n
      -- Q2: any constant mentioning a content accessor
      let mut hits : Array (Name × Name) := #[]
      for n in cl do
        let d := deps env n
        for a in contentAccessors do
          if d.contains a then hits := hits.push (n, a)
      Lean.logInfo m!"{label}\n  closure={cl.size}  containsF2={cl.contains F2}  directParentsOfF2={parents.size}  contentAccessorHits={hits.size}"
      for p in parents do Lean.logInfo m!"    PARENT <- {p}"
      for (n, a) in hits do Lean.logInfo m!"    CONTENT-ACCESSOR {n}  uses  {a}"

/-! ## Q3: ground truth on the generic leaf body -/
run_cmd do
  let env <- Lean.getEnv
  let leaf := `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  let d := (deps env leaf).eraseDups
  let structProj := d.filter fun n =>
    (`RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData).isPrefixOf n
  Lean.logInfo m!"LEAF BODY direct deps={d.length}; structure-namespace deps: {structProj}"

end AdvF2
