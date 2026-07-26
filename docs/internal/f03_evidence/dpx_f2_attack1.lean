import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import RMQ.Core.SuccinctRMQClassic
import Lean

/-!
ADVERSARIAL re-verification of the F2 (`builtRelativeSplitBPCloseRankData`)
"S" verdict.  Independent closure implementation.

Differences from the audited script (deliberately MORE inclusive):
  * traverses BOTH the value and the type of every non-theorem constant
  * additionally reports, for each root, every PROJECTION FUNCTION of
    `TwoLevelPayloadLiveStoredWordRankData` that appears anywhere in the
    closure -- this tests "only bits.length / wordSize / blocksPerSuper are
    consumed" at the whole-closure level, not just inside one `simp only`.
  * runs from FOUR roots, including the public list-facing entry.
-/

open Lean

namespace DPXF2

def isThm (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

/-- value-only deps (matches the audited notion). -/
def valDeps (env : Environment) (n : Name) : List Name :=
  if isThm env n then []
  else
    match env.find? n with
    | none => []
    | some ci =>
        match ci.value? with
        | some v => v.foldConsts [] (fun c a => c :: a)
        | none => []

/-- OVER-approximation: value deps PLUS type deps (types are erased at runtime,
so anything this finds and the value-only pass misses is provably irrelevant to
an executed address -- but we want to see it anyway). -/
def valTypeDeps (env : Environment) (n : Name) : List Name :=
  if isThm env n then []
  else
    match env.find? n with
    | none => []
    | some ci =>
        let fromVal := match ci.value? with
          | some v => v.foldConsts [] (fun c a => c :: a)
          | none => []
        ci.type.foldConsts fromVal (fun c a => c :: a)

partial def closureAux (env : Environment) (deps : Environment -> Name -> List Name)
    (seen : Std.HashSet Name) (out : Array Name) :
    List Name -> Std.HashSet Name × Array Name
  | [] => (seen, out)
  | n :: rest =>
      if seen.contains n then closureAux env deps seen out rest
      else closureAux env deps (seen.insert n) (out.push n) (deps env n ++ rest)

def F2 : Name := `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData

def structNs : Name := `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData

/-- every field / derived accessor of the rank structure we care about -/
def fieldNames : List Name :=
  [ `wordSize, `wordSize_pos, `wordSize_le_machine, `blocksPerSuper,
    `blocksPerSuper_pos, `superWidth, `blockWidth,
    `superTrueEntries, `superFalseEntries, `blockTrueEntries, `blockFalseEntries,
    `superTables, `blockTables, `bitWords,
    `superPayload, `blockPayload, `auxPayload,
    `superSampleWords, `blockSampleWords,
    `queryPos, `wordIndex, `superIndex, `wordOffset ].map (structNs ++ ·)

def roots : List (String × Name) :=
  [ ("CONTROLLER root (StoreParam:2418)",
     `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore),
    ("PUBLIC entry (SuccinctRMQClassic:200)",
     `RMQ.SuccinctClassic.queryTraceResultWithStore),
    ("PUBLIC entry, no store (SuccinctRMQClassic:191)",
     `RMQ.SuccinctClassic.queryTraceResult),
    ("L3 leaf",
     `RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore) ]

run_cmd do
  let env <- Lean.getEnv
  for (label, root) in roots do
    if (env.find? root).isNone then
      Lean.logInfo m!"!!! ROOT NOT FOUND: {root}"
    else
    -- value-only
    let cl := (closureAux env valDeps {} #[] [root]).2
    let mut parents : Array Name := #[]
    for n in cl do
      if n != F2 && (valDeps env n).contains F2 then parents := parents.push n
    -- value+type over-approximation
    let cl2 := (closureAux env valTypeDeps {} #[] [root]).2
    let mut parents2 : Array Name := #[]
    for n in cl2 do
      if n != F2 && (valTypeDeps env n).contains F2 then parents2 := parents2.push n
    -- which structure fields are touched anywhere in the value-only closure
    let clSet := (closureAux env valDeps {} #[] [root]).1
    let mut touched : Array Name := #[]
    for f in fieldNames do
      if clSet.contains f then touched := touched.push f
    Lean.logInfo m!"=== {label}"
    Lean.logInfo m!"  valueOnly closure={cl.size}  F2parents={parents.size}"
    for p in parents do Lean.logInfo m!"      <- {p}"
    Lean.logInfo m!"  value+TYPE closure={cl2.size}  F2parents={parents2.size}"
    for p in parents2 do Lean.logInfo m!"      <T- {p}"
    Lean.logInfo m!"  rank-structure accessors reachable in value-only closure ({touched.size}):"
    for t in touched do Lean.logInfo m!"      * {t}"

end DPXF2
