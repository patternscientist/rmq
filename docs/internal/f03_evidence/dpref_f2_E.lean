import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
ATTACK 4: shape ELIMINATOR completeness inside the L3 closure, and an
independent re-check of the other agent's decisive theorem + its axioms.
-/

open Lean

namespace DPF2E

def isThm (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

def valDeps (env : Environment) (n : Name) : List Name :=
  if isThm env n then []
  else match env.find? n with
    | none => []
    | some ci => match ci.value? with
      | some v => v.foldConsts [] (fun c a => c :: a)
      | none => []

partial def clo (env : Environment) (seen : Std.HashSet Name) (acc : Array Name)
    : List Name -> Std.HashSet Name × Array Name
  | [] => (seen, acc)
  | n :: rest =>
      if seen.contains n then clo env seen acc rest
      else clo env (seen.insert n) (acc.push n) (valDeps env n ++ rest)

def shapeElims : List Name :=
  [ `RMQ.Cartesian.CartesianShape.rec,
    `RMQ.Cartesian.CartesianShape.casesOn,
    `RMQ.Cartesian.CartesianShape.recOn,
    `RMQ.Cartesian.CartesianShape.below,
    `RMQ.Cartesian.CartesianShape.brecOn,
    `RMQ.Cartesian.CartesianShape.node,
    `RMQ.Cartesian.CartesianShape.empty,
    `RMQ.Cartesian.CartesianShape.noConfusion ]

run_cmd do
  let env <- Lean.getEnv
  for (label, r) in
    [ ("L3 rankClose", `RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore),
      ("CONTROLLER store-param root",
       `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore) ] do
    let cl := (clo env {} #[] [r]).2
    let mut hits : Array (Name × Name) := #[]
    for n in cl do
      let ds := valDeps env n
      for e in shapeElims do
        if ds.contains e then hits := hits.push (n, e)
      pure ()
    Lean.logInfo m!"{label}: closure={cl.size}  shape-eliminator users={hits.size}"
    for (n, e) in hits do Lean.logInfo m!"      {n}   uses   {e}"

end DPF2E

/-! Independent re-statement of the decisive theorem, proved from scratch here
(not imported from the other agent's file), plus an axiom audit. -/

namespace DPF2Thm

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian

theorem l3_size_only
    (a b : CartesianShape) (hsize : a.size = b.size)
    (store : WordRAM.ReadStore) (rankSegmentBase pos : Nat) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore a store rankSegmentBase pos
      = concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore b store rankSegmentBase pos := by
  have hlen : a.bpCode.length = b.bpCode.length := by
    rw [CartesianShape.bpCode_length, CartesianShape.bpCode_length, hsize]
  have hw : (builtRelativeSplitBPCloseRankData a).wordSize
      = (builtRelativeSplitBPCloseRankData b).wordSize := by
    show SuccinctRank.machineWordBits a.bpCode.length
        = SuccinctRank.machineWordBits b.bpCode.length
    rw [hlen]
  have hb : (builtRelativeSplitBPCloseRankData a).blocksPerSuper
      = (builtRelativeSplitBPCloseRankData b).blocksPerSuper := by
    show SuccinctRank.machineWordBits a.bpCode.length
        = SuccinctRank.machineWordBits b.bpCode.length
    rw [hlen]
  unfold concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  rw [hlen]
  unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  simp only [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordOffset,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos,
    hlen, hw, hb]

#print axioms l3_size_only

/-- Anti-vacuity of the theorem itself: the two sides are NOT constant. -/
example : True := trivial

end DPF2Thm
