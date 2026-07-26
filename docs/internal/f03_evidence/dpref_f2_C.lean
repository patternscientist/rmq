import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import RMQ.Core.SuccinctRMQClassic
import Lean

/-!
ATTACK 3: exhaustiveness of the consumer set for
`RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData` (F2).

Independent re-derivation, over SEVERAL roots including the PUBLIC list-facing
entry points -- not just the store-parametric controller root the other agent
used. Also lists every parent, and every constant in the closure that mentions
any of F2's field projections.
-/

open Lean

namespace DPF2C

def isThm (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

def valDeps (env : Environment) (n : Name) : List Name :=
  if isThm env n then []
  else
    match env.find? n with
    | none => []
    | some ci =>
        match ci.value? with
        | some v => v.foldConsts [] (fun c a => c :: a)
        | none => []

partial def clo (env : Environment) (seen : Std.HashSet Name) (acc : Array Name)
    : List Name -> Std.HashSet Name × Array Name
  | [] => (seen, acc)
  | n :: rest =>
      if seen.contains n then clo env seen acc rest
      else clo env (seen.insert n) (acc.push n) (valDeps env n ++ rest)

def F2 : Name := `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData

/-- Field projections of the rank structure; a consumer of any of these on any
instance would show up as one of these constants in the closure. -/
def projs : List Name :=
  [ `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordSize,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blocksPerSuper,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superWidth,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockWidth,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superTables,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockTables,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bitWords,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superTrueEntries,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superFalseEntries,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockTrueEntries,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockFalseEntries ]

def roots : List (String × Name) :=
  [ ("PUBLIC queryTraceResultWithStore", `RMQ.SuccinctRMQClassic.queryTraceResultWithStore),
    ("PUBLIC queryTraceResult (NON-store-param)", `RMQ.SuccinctRMQClassic.queryTraceResult),
    ("CONTROLLER store-param root",
     `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore),
    ("CONTROLLER non-store-param root",
     `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult),
    ("L1 selectClose",
     `RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore),
    ("L2 lcaClose",
     `RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore),
    ("L3 rankClose",
     `RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore) ]

run_cmd do
  let env <- Lean.getEnv
  for (label, r) in roots do
    match env.find? r with
    | none => Lean.logInfo m!"{label}: ROOT NOT FOUND ({r})"
    | some _ =>
      let cl := (clo env {} #[] [r]).2
      let mut parents : Array Name := #[]
      for n in cl do
        if n != F2 && (valDeps env n).contains F2 then parents := parents.push n
      let mut projUsers : Array (Name × Name) := #[]
      for n in cl do
        let ds := valDeps env n
        for p in projs do
          if ds.contains p then projUsers := projUsers.push (n, p)
      Lean.logInfo m!"{label}: closure={cl.size} hasF2={cl.contains F2} parentsOfF2={parents.size} projUses={projUsers.size}"
      for p in parents do Lean.logInfo m!"      parent <- {p}"
      for (n, p) in projUsers do Lean.logInfo m!"      proj   <- {n}  uses  {p}"

end DPF2C
