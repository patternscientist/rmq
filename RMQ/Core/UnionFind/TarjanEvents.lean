import RMQ.Core.UnionFind.Sequence

/-!
# Union-find Tarjan event accounting

This module starts the sequence-level event surface needed for a true Tarjan
analysis.  The existing amortized backends prove local potential inequalities;
the inverse-Ackermann theorem needs a whole-run accounting target.  Here we
separate modeled public-operation cost into compression-trace events and
rank-link events for the charged full-compression backend.
-/

namespace RMQ

namespace UnionFind
namespace Forest
namespace ParentForest
namespace NoCompressionRankedMassBackendState

/-- Compression events charged by one successful or failed full-compression find. -/
def fullCompressFindEventCount
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  (backend.fullCompressFindTrace x).length

/--
Compression events charged by public union: the two representative searches
before the final rank-guided link.
-/
def chargedUnionFindEventCount
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) : Nat :=
  backend.fullCompressFindEventCount x +
    let afterX := (backend.fullCompressFindCosted x).erase.1
    afterX.fullCompressFindEventCount y

/-- Number of rank-link events in a mixed operation sequence. -/
def runChargedFullCompressionLinkCount : List UFOp -> Nat
  | [] => 0
  | UFOp.find _ :: ops => runChargedFullCompressionLinkCount ops
  | UFOp.union _ _ :: ops => 1 + runChargedFullCompressionLinkCount ops

/--
Compression-trace event count accumulated by the charged full-compression
backend along a mixed operation sequence.
-/
def runChargedFullCompressionFindEventCount
    (backend : NoCompressionRankedMassBackendState) :
    List UFOp -> Nat
  | [] => 0
  | UFOp.find x :: ops =>
      backend.fullCompressFindEventCount x +
        let after := (backend.fullCompressFindCosted x).erase.1
        after.runChargedFullCompressionFindEventCount ops
  | UFOp.union x y :: ops =>
      backend.chargedUnionFindEventCount x y +
        let after := (backend.chargedUnionCosted x y).erase
        after.runChargedFullCompressionFindEventCount ops

theorem chargedUnionCosted_cost_eq_findEvents_add_one
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.chargedUnionCosted x y).cost =
      backend.chargedUnionFindEventCount x y + 1 := by
  let afterX := (backend.fullCompressFindCosted x).erase.1
  have hcost := backend.chargedUnionCosted_cost x y
  have hx := backend.fullCompressFindCosted_cost_eq_trace_length x
  have hy := afterX.fullCompressFindCosted_cost_eq_trace_length y
  rw [hcost, hx, hy]
  simp [chargedUnionFindEventCount, fullCompressFindEventCount, afterX,
    Nat.add_assoc]

theorem runChargedFullCompressionLinkCount_le_length :
    forall ops : List UFOp,
      runChargedFullCompressionLinkCount ops <= ops.length
  | [] => by
      exact Nat.le_refl 0
  | UFOp.find _ :: ops => by
      have htail := runChargedFullCompressionLinkCount_le_length ops
      simp [runChargedFullCompressionLinkCount]
      omega
  | UFOp.union _ _ :: ops => by
      have htail := runChargedFullCompressionLinkCount_le_length ops
      simp [runChargedFullCompressionLinkCount]
      omega

theorem runChargedFullCompressionOpsCosted_cost_eq_events
    (backend : NoCompressionRankedMassBackendState) :
    forall ops : List UFOp,
      (backend.runChargedFullCompressionOpsCosted ops).cost =
        backend.runChargedFullCompressionFindEventCount ops +
          runChargedFullCompressionLinkCount ops
  | [] => by
      rfl
  | UFOp.find x :: ops => by
      let after := (backend.fullCompressFindCosted x).value.1
      have htail :=
        runChargedFullCompressionOpsCosted_cost_eq_events after ops
      have hfind := backend.fullCompressFindCosted_cost_eq_trace_length x
      have hrun :
          (backend.runChargedFullCompressionOpsCosted
              (UFOp.find x :: ops)).cost =
            (backend.fullCompressFindCosted x).cost +
              (after.runChargedFullCompressionOpsCosted ops).cost := by
        simp [runChargedFullCompressionOpsCosted,
          RepresentationBackend.runOpsCosted,
          chargedFullCompressionRepresentationBackend, after]
      rw [hrun, htail, hfind]
      simp [runChargedFullCompressionFindEventCount,
        runChargedFullCompressionLinkCount, fullCompressFindEventCount,
        after, Costed.erase, Nat.add_assoc]
  | UFOp.union x y :: ops => by
      let after := (backend.chargedUnionCosted x y).value
      have htail :=
        runChargedFullCompressionOpsCosted_cost_eq_events after ops
      have hunion :=
        backend.chargedUnionCosted_cost_eq_findEvents_add_one x y
      have hrun :
          (backend.runChargedFullCompressionOpsCosted
              (UFOp.union x y :: ops)).cost =
            (backend.chargedUnionCosted x y).cost +
              (after.runChargedFullCompressionOpsCosted ops).cost := by
        simp [runChargedFullCompressionOpsCosted,
          RepresentationBackend.runOpsCosted,
          chargedFullCompressionRepresentationBackend, after]
      rw [hrun, htail, hunion]
      simp [runChargedFullCompressionFindEventCount,
        runChargedFullCompressionLinkCount,
        after, Costed.erase,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem runChargedFullCompressionOpsCosted_cost_le_findEvents_add_length
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp) :
    (backend.runChargedFullCompressionOpsCosted ops).cost <=
      backend.runChargedFullCompressionFindEventCount ops + ops.length := by
  rw [backend.runChargedFullCompressionOpsCosted_cost_eq_events ops]
  have hlinks := runChargedFullCompressionLinkCount_le_length ops
  omega

/--
Event-level cost profile for the charged public-operation backend.

The modeled cost of a whole mixed run is exactly compression-trace events plus
one rank-link event per public union.  Future Tarjan/Ackermann accounting must
bound the first term; the second is linearly bounded by the operation count.
-/
theorem runChargedFullCompressionEventCost_profile
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp) :
    (backend.runChargedFullCompressionOpsCosted ops).cost =
        backend.runChargedFullCompressionFindEventCount ops +
          runChargedFullCompressionLinkCount ops /\
      runChargedFullCompressionLinkCount ops <= ops.length /\
      (backend.runChargedFullCompressionOpsCosted ops).cost <=
        backend.runChargedFullCompressionFindEventCount ops + ops.length := by
  constructor
  · exact backend.runChargedFullCompressionOpsCosted_cost_eq_events ops
  · constructor
    · exact runChargedFullCompressionLinkCount_le_length ops
    · exact backend.runChargedFullCompressionOpsCosted_cost_le_findEvents_add_length ops

/--
Rank schedule used to classify compression events.

The true Tarjan proof will instantiate this with an Ackermann-indexed schedule.
The current module only needs an executable level map; monotonicity lemmas live
with concrete schedules that use them.
-/
structure RankSchedule where
  level : Nat -> Nat

/-- Current checked schedule: the existing iterated-log rank level. -/
def iteratedLogRankSchedule : RankSchedule where
  level := tarjanRankLevel

def nodeRootParentScheduleTerminalCount
    (_schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (_root x : Nat) : Nat :=
  match backend.state.forest.parent? x with
  | none => 1
  | some parent => if parent = x then 1 else 0

def nodeRootParentScheduleCrossCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) : Nat :=
  match backend.state.forest.parent? x with
  | none => 0
  | some parent =>
      if parent = x then
        0
      else if schedule.level (backend.state.rank parent) <
          schedule.level (backend.state.rank root) then
        1
      else
        0

def nodeRootParentScheduleResidualCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) : Nat :=
  match backend.state.forest.parent? x with
  | none => 0
  | some parent =>
      if parent = x then
        0
      else if schedule.level (backend.state.rank parent) <
          schedule.level (backend.state.rank root) then
        0
      else
        1

theorem nodeRootParentScheduleEventCounts_eq_one
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) :
    backend.nodeRootParentScheduleTerminalCount schedule root x +
        backend.nodeRootParentScheduleCrossCount schedule root x +
        backend.nodeRootParentScheduleResidualCount schedule root x = 1 := by
  unfold nodeRootParentScheduleTerminalCount
    nodeRootParentScheduleCrossCount
    nodeRootParentScheduleResidualCount
  cases hparent : backend.state.forest.parent? x with
  | none =>
      simp
  | some parent =>
      by_cases hsame : parent = x
      · simp [hsame]
      · by_cases hcross :
          schedule.level (backend.state.rank parent) <
            schedule.level (backend.state.rank root)
        · simp [hsame, hcross]
        · simp [hsame, hcross]

def traceRootParentScheduleTerminalCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeRootParentScheduleTerminalCount schedule root x +
        backend.traceRootParentScheduleTerminalCount schedule root xs

def traceRootParentScheduleCrossCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeRootParentScheduleCrossCount schedule root x +
        backend.traceRootParentScheduleCrossCount schedule root xs

def traceRootParentScheduleResidualCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeRootParentScheduleResidualCount schedule root x +
        backend.traceRootParentScheduleResidualCount schedule root xs

theorem traceRootParentScheduleEventCounts_eq_length
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    forall trace : List Nat,
      backend.traceRootParentScheduleTerminalCount schedule root trace +
          backend.traceRootParentScheduleCrossCount schedule root trace +
          backend.traceRootParentScheduleResidualCount schedule root trace =
        trace.length
  | [] => by
      simp [traceRootParentScheduleTerminalCount,
        traceRootParentScheduleCrossCount,
        traceRootParentScheduleResidualCount]
  | x :: xs => by
      have hnode :=
        backend.nodeRootParentScheduleEventCounts_eq_one schedule root x
      have htail :=
        traceRootParentScheduleEventCounts_eq_length schedule backend root xs
      simp [traceRootParentScheduleTerminalCount,
        traceRootParentScheduleCrossCount,
        traceRootParentScheduleResidualCount]
      omega

def fullCompressFindScheduleTerminalCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.fullCompressFindEventCount x
  | some root =>
      backend.traceRootParentScheduleTerminalCount schedule root
        (backend.fullCompressFindTrace x)

def fullCompressFindScheduleCrossCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => 0
  | some root =>
      backend.traceRootParentScheduleCrossCount schedule root
        (backend.fullCompressFindTrace x)

def fullCompressFindScheduleResidualCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => 0
  | some root =>
      backend.traceRootParentScheduleResidualCount schedule root
        (backend.fullCompressFindTrace x)

theorem fullCompressFindScheduleEventCounts_eq_findEventCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    backend.fullCompressFindScheduleTerminalCount schedule x +
        backend.fullCompressFindScheduleCrossCount schedule x +
        backend.fullCompressFindScheduleResidualCount schedule x =
      backend.fullCompressFindEventCount x := by
  unfold fullCompressFindScheduleTerminalCount
    fullCompressFindScheduleCrossCount fullCompressFindScheduleResidualCount
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp
  | some root =>
      have htrace :=
        backend.traceRootParentScheduleEventCounts_eq_length schedule root
          (backend.fullCompressFindTrace x)
      simpa [hfind, fullCompressFindEventCount] using htrace

def chargedUnionScheduleTerminalCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) : Nat :=
  backend.fullCompressFindScheduleTerminalCount schedule x +
    let afterX := (backend.fullCompressFindCosted x).erase.1
    afterX.fullCompressFindScheduleTerminalCount schedule y

def chargedUnionScheduleCrossCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) : Nat :=
  backend.fullCompressFindScheduleCrossCount schedule x +
    let afterX := (backend.fullCompressFindCosted x).erase.1
    afterX.fullCompressFindScheduleCrossCount schedule y

def chargedUnionScheduleResidualCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) : Nat :=
  backend.fullCompressFindScheduleResidualCount schedule x +
    let afterX := (backend.fullCompressFindCosted x).erase.1
    afterX.fullCompressFindScheduleResidualCount schedule y

theorem chargedUnionScheduleEventCounts_eq_findEventCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    backend.chargedUnionScheduleTerminalCount schedule x y +
        backend.chargedUnionScheduleCrossCount schedule x y +
        backend.chargedUnionScheduleResidualCount schedule x y =
      backend.chargedUnionFindEventCount x y := by
  let afterX := (backend.fullCompressFindCosted x).erase.1
  have hx :=
    backend.fullCompressFindScheduleEventCounts_eq_findEventCount schedule x
  have hy :=
    afterX.fullCompressFindScheduleEventCounts_eq_findEventCount schedule y
  unfold chargedUnionScheduleTerminalCount chargedUnionScheduleCrossCount
    chargedUnionScheduleResidualCount chargedUnionFindEventCount
  change
    (backend.fullCompressFindScheduleTerminalCount schedule x +
          afterX.fullCompressFindScheduleTerminalCount schedule y) +
        (backend.fullCompressFindScheduleCrossCount schedule x +
          afterX.fullCompressFindScheduleCrossCount schedule y) +
        (backend.fullCompressFindScheduleResidualCount schedule x +
          afterX.fullCompressFindScheduleResidualCount schedule y) =
      backend.fullCompressFindEventCount x +
        afterX.fullCompressFindEventCount y
  omega

def runChargedFullCompressionScheduleTerminalCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    List UFOp -> Nat
  | [] => 0
  | UFOp.find x :: ops =>
      backend.fullCompressFindScheduleTerminalCount schedule x +
        let after := (backend.fullCompressFindCosted x).erase.1
        after.runChargedFullCompressionScheduleTerminalCount schedule ops
  | UFOp.union x y :: ops =>
      backend.chargedUnionScheduleTerminalCount schedule x y +
        let after := (backend.chargedUnionCosted x y).erase
        after.runChargedFullCompressionScheduleTerminalCount schedule ops

def runChargedFullCompressionScheduleCrossCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    List UFOp -> Nat
  | [] => 0
  | UFOp.find x :: ops =>
      backend.fullCompressFindScheduleCrossCount schedule x +
        let after := (backend.fullCompressFindCosted x).erase.1
        after.runChargedFullCompressionScheduleCrossCount schedule ops
  | UFOp.union x y :: ops =>
      backend.chargedUnionScheduleCrossCount schedule x y +
        let after := (backend.chargedUnionCosted x y).erase
        after.runChargedFullCompressionScheduleCrossCount schedule ops

def runChargedFullCompressionScheduleResidualCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    List UFOp -> Nat
  | [] => 0
  | UFOp.find x :: ops =>
      backend.fullCompressFindScheduleResidualCount schedule x +
        let after := (backend.fullCompressFindCosted x).erase.1
        after.runChargedFullCompressionScheduleResidualCount schedule ops
  | UFOp.union x y :: ops =>
      backend.chargedUnionScheduleResidualCount schedule x y +
        let after := (backend.chargedUnionCosted x y).erase
        after.runChargedFullCompressionScheduleResidualCount schedule ops

theorem runChargedFullCompressionScheduleEventCounts_eq_findEventCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    forall ops : List UFOp,
      backend.runChargedFullCompressionScheduleTerminalCount schedule ops +
          backend.runChargedFullCompressionScheduleCrossCount schedule ops +
          backend.runChargedFullCompressionScheduleResidualCount schedule ops =
        backend.runChargedFullCompressionFindEventCount ops
  | [] => by
      rfl
  | UFOp.find x :: ops => by
      let after := (backend.fullCompressFindCosted x).erase.1
      have hhead :=
        backend.fullCompressFindScheduleEventCounts_eq_findEventCount
          schedule x
      have htail :=
        runChargedFullCompressionScheduleEventCounts_eq_findEventCount
          schedule after ops
      unfold runChargedFullCompressionScheduleTerminalCount
        runChargedFullCompressionScheduleCrossCount
        runChargedFullCompressionScheduleResidualCount
        runChargedFullCompressionFindEventCount
      change
        (backend.fullCompressFindScheduleTerminalCount schedule x +
              after.runChargedFullCompressionScheduleTerminalCount
                schedule ops) +
            (backend.fullCompressFindScheduleCrossCount schedule x +
              after.runChargedFullCompressionScheduleCrossCount
                schedule ops) +
            (backend.fullCompressFindScheduleResidualCount schedule x +
              after.runChargedFullCompressionScheduleResidualCount
                schedule ops) =
          backend.fullCompressFindEventCount x +
            after.runChargedFullCompressionFindEventCount ops
      omega
  | UFOp.union x y :: ops => by
      let after := (backend.chargedUnionCosted x y).erase
      have hhead :=
        backend.chargedUnionScheduleEventCounts_eq_findEventCount
          schedule x y
      have htail :=
        runChargedFullCompressionScheduleEventCounts_eq_findEventCount
          schedule after ops
      unfold runChargedFullCompressionScheduleTerminalCount
        runChargedFullCompressionScheduleCrossCount
        runChargedFullCompressionScheduleResidualCount
        runChargedFullCompressionFindEventCount
      change
        (backend.chargedUnionScheduleTerminalCount schedule x y +
              after.runChargedFullCompressionScheduleTerminalCount
                schedule ops) +
            (backend.chargedUnionScheduleCrossCount schedule x y +
              after.runChargedFullCompressionScheduleCrossCount
                schedule ops) +
            (backend.chargedUnionScheduleResidualCount schedule x y +
              after.runChargedFullCompressionScheduleResidualCount
                schedule ops) =
          backend.chargedUnionFindEventCount x y +
            after.runChargedFullCompressionFindEventCount ops
      omega

theorem runChargedFullCompressionScheduledEventCost_profile
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp) :
    backend.runChargedFullCompressionScheduleTerminalCount schedule ops +
        backend.runChargedFullCompressionScheduleCrossCount schedule ops +
        backend.runChargedFullCompressionScheduleResidualCount schedule ops =
      backend.runChargedFullCompressionFindEventCount ops /\
    (backend.runChargedFullCompressionOpsCosted ops).cost =
      (backend.runChargedFullCompressionScheduleTerminalCount schedule ops +
          backend.runChargedFullCompressionScheduleCrossCount schedule ops +
          backend.runChargedFullCompressionScheduleResidualCount schedule ops) +
        runChargedFullCompressionLinkCount ops := by
  have hfind :=
    backend.runChargedFullCompressionScheduleEventCounts_eq_findEventCount
      schedule ops
  have hcost :=
    backend.runChargedFullCompressionOpsCosted_cost_eq_events ops
  constructor
  · exact hfind
  · rw [hcost, ← hfind]

theorem unionCosted_forest_size_eq
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    ((backend.unionCosted x y).erase).state.forest.size =
      backend.state.forest.size := by
  simp [unionCosted, unionResult, NoCompressionRankedMassForest.unionCosted]

theorem chargedUnionCosted_forest_size_eq
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.chargedUnionCosted x y).erase.state.forest.size =
      backend.state.forest.size := by
  let afterX := (backend.fullCompressFindCosted x).erase.1
  let afterY := (afterX.fullCompressFindCosted y).erase.1
  have hx : afterX.state.forest.size = backend.state.forest.size := by
    simpa [afterX] using backend.fullCompressFindCosted_forest_size_eq x
  have hy : afterY.state.forest.size = afterX.state.forest.size := by
    simpa [afterY] using afterX.fullCompressFindCosted_forest_size_eq y
  have hu :
      ((afterY.unionCosted x y).erase).state.forest.size =
        afterY.state.forest.size :=
    afterY.unionCosted_forest_size_eq x y
  have herase :
      (backend.chargedUnionCosted x y).erase =
        (afterY.unionCosted x y).erase := by
    simp [chargedUnionCosted, afterX, afterY, Costed.erase]
  rw [herase]
  omega

theorem runChargedFullCompressionOpsCosted_forest_size_eq
    (backend : NoCompressionRankedMassBackendState) :
    forall ops : List UFOp,
      (backend.runChargedFullCompressionOpsCosted ops).erase.1.state.forest.size =
        backend.state.forest.size
  | [] => by
      rfl
  | UFOp.find x :: ops => by
      let after := (backend.fullCompressFindCosted x).value.1
      have hstep : after.state.forest.size = backend.state.forest.size := by
        simpa [after, Costed.erase] using
          backend.fullCompressFindCosted_forest_size_eq x
      have htail :=
        runChargedFullCompressionOpsCosted_forest_size_eq after ops
      have hrun :
          (backend.runChargedFullCompressionOpsCosted
              (UFOp.find x :: ops)).erase.1.state.forest.size =
            (after.runChargedFullCompressionOpsCosted ops).erase.1.state.forest.size := by
        simp [runChargedFullCompressionOpsCosted,
          RepresentationBackend.runOpsCosted,
          chargedFullCompressionRepresentationBackend, after, Costed.erase]
      rw [hrun, htail, hstep]
  | UFOp.union x y :: ops => by
      let after := (backend.chargedUnionCosted x y).value
      have hstep : after.state.forest.size = backend.state.forest.size := by
        simpa [after, Costed.erase] using
          backend.chargedUnionCosted_forest_size_eq x y
      have htail :=
        runChargedFullCompressionOpsCosted_forest_size_eq after ops
      have hrun :
          (backend.runChargedFullCompressionOpsCosted
              (UFOp.union x y :: ops)).erase.1.state.forest.size =
            (after.runChargedFullCompressionOpsCosted ops).erase.1.state.forest.size := by
        simp [runChargedFullCompressionOpsCosted,
          RepresentationBackend.runOpsCosted,
          chargedFullCompressionRepresentationBackend, after, Costed.erase]
      rw [hrun, htail, hstep]

theorem runChargedFullCompressionFixedUniverse_profile
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp) :
    (backend.runChargedFullCompressionOpsCosted ops).erase.1.state.forest.size =
      backend.state.forest.size := by
  exact backend.runChargedFullCompressionOpsCosted_forest_size_eq ops

def opValidForSize (n : Nat) : UFOp -> Prop
  | UFOp.find x => x < n
  | UFOp.union x y => x < n /\ y < n

def opsValidForSize (n : Nat) (ops : List UFOp) : Prop :=
  forall op, op ∈ ops -> opValidForSize n op

def runChargedFullCompressionPublicFindCount : List UFOp -> Nat
  | [] => 0
  | UFOp.find _ :: ops =>
      1 + runChargedFullCompressionPublicFindCount ops
  | UFOp.union _ _ :: ops =>
      2 + runChargedFullCompressionPublicFindCount ops

theorem runChargedFullCompressionPublicFindCount_le_two_mul_length :
    forall ops : List UFOp,
      runChargedFullCompressionPublicFindCount ops <= 2 * ops.length
  | [] => by
      exact Nat.le_refl 0
  | UFOp.find _ :: ops => by
      have htail := runChargedFullCompressionPublicFindCount_le_two_mul_length ops
      simp [runChargedFullCompressionPublicFindCount]
      omega
  | UFOp.union _ _ :: ops => by
      have htail := runChargedFullCompressionPublicFindCount_le_two_mul_length ops
      simp [runChargedFullCompressionPublicFindCount]
      omega

theorem nodeRootParentScheduleTerminalCount_le_one
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) :
    backend.nodeRootParentScheduleTerminalCount schedule root x <= 1 := by
  unfold nodeRootParentScheduleTerminalCount
  cases backend.state.forest.parent? x with
  | none =>
      simp
  | some parent =>
      by_cases hsame : parent = x
      · simp [hsame]
      · simp [hsame]

theorem nodeRootParentScheduleTerminalCount_eq_zero_of_parent_ne
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {root x parent : Nat}
    (hparent : backend.state.forest.parent? x = some parent)
    (hne : parent ≠ x) :
    backend.nodeRootParentScheduleTerminalCount schedule root x = 0 := by
  simp [nodeRootParentScheduleTerminalCount, hparent, hne]

theorem compressPathFindFuelTrace_terminalCount_le_one_of_findRoot?
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root : Nat},
      backend.state.forest.findRoot? x = some root ->
      backend.traceRootParentScheduleTerminalCount schedule root
          (backend.compressPathFindFuelTrace fuel x) <= 1
  | 0, x, root, _hfind => by
      simp [compressPathFindFuelTrace, traceRootParentScheduleTerminalCount]
      exact backend.nodeRootParentScheduleTerminalCount_le_one schedule root x
  | fuel + 1, x, root, hfind => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simp [compressPathFindFuelTrace, traceRootParentScheduleTerminalCount,
            hparent]
          exact backend.nodeRootParentScheduleTerminalCount_le_one schedule root x
      | some parent =>
          by_cases hsame : parent = x
          · simpa [compressPathFindFuelTrace,
              traceRootParentScheduleTerminalCount, hparent, hsame] using
              backend.nodeRootParentScheduleTerminalCount_le_one
                schedule root x
          · have hparentFind :
                backend.state.forest.findRoot? parent = some root :=
              backend.findRoot?_parent_eq_of_parent?_ne hparent hsame hfind
            have htail :=
              compressPathFindFuelTrace_terminalCount_le_one_of_findRoot?
                schedule backend fuel hparentFind
            have hhead :
                backend.nodeRootParentScheduleTerminalCount schedule root x =
                  0 :=
              backend.nodeRootParentScheduleTerminalCount_eq_zero_of_parent_ne
                schedule hparent hsame
            simp [compressPathFindFuelTrace,
              traceRootParentScheduleTerminalCount, hparent, hsame, hhead]
            exact htail

theorem fullCompressFindScheduleTerminalCount_le_one_of_findRoot?
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    backend.fullCompressFindScheduleTerminalCount schedule x <= 1 := by
  simpa [fullCompressFindScheduleTerminalCount, hfind,
    fullCompressFindTrace] using
    backend.compressPathFindFuelTrace_terminalCount_le_one_of_findRoot?
      schedule backend.state.forest.maxSearchFuel hfind

theorem fullCompressFindScheduleTerminalCount_le_one_of_valid
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {x : Nat} (hx : x < backend.state.forest.size) :
    backend.fullCompressFindScheduleTerminalCount schedule x <= 1 := by
  rcases backend.state.forest.findRoot?_total_of_valid
      backend.inv.toInvariant hx with
    ⟨root, hfind, _hvalid, _hroot⟩
  exact
    backend.fullCompressFindScheduleTerminalCount_le_one_of_findRoot?
      schedule hfind

theorem chargedUnionScheduleTerminalCount_le_two_of_valid
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {x y : Nat}
    (hx : x < backend.state.forest.size)
    (hy : y < backend.state.forest.size) :
    backend.chargedUnionScheduleTerminalCount schedule x y <= 2 := by
  let afterX := (backend.fullCompressFindCosted x).erase.1
  have hxTerm :=
    backend.fullCompressFindScheduleTerminalCount_le_one_of_valid
      schedule hx
  have hsize : afterX.state.forest.size = backend.state.forest.size := by
    simpa [afterX] using backend.fullCompressFindCosted_forest_size_eq x
  have hyAfter : y < afterX.state.forest.size := by
    omega
  have hyTerm :=
    afterX.fullCompressFindScheduleTerminalCount_le_one_of_valid
      schedule hyAfter
  unfold chargedUnionScheduleTerminalCount
  change
    backend.fullCompressFindScheduleTerminalCount schedule x +
      afterX.fullCompressFindScheduleTerminalCount schedule y <= 2
  omega

theorem runChargedFullCompressionScheduleTerminalCount_le_publicFindCount_of_valid
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    forall ops : List UFOp,
      opsValidForSize backend.state.forest.size ops ->
      backend.runChargedFullCompressionScheduleTerminalCount schedule ops <=
        runChargedFullCompressionPublicFindCount ops
  | [], _hvalid => by
      exact Nat.le_refl 0
  | UFOp.find x :: ops, hvalid => by
      let after := (backend.fullCompressFindCosted x).erase.1
      have hx : x < backend.state.forest.size := by
        exact hvalid (UFOp.find x) (by simp)
      have hhead :=
        backend.fullCompressFindScheduleTerminalCount_le_one_of_valid
          schedule hx
      have hsize : after.state.forest.size = backend.state.forest.size := by
        simpa [after] using backend.fullCompressFindCosted_forest_size_eq x
      have htailValid :
          opsValidForSize after.state.forest.size ops := by
        intro op hop
        have hopValid : opValidForSize backend.state.forest.size op :=
          hvalid op (by simp [hop])
        simpa [hsize] using hopValid
      have htail :=
        runChargedFullCompressionScheduleTerminalCount_le_publicFindCount_of_valid
          schedule after ops htailValid
      unfold runChargedFullCompressionScheduleTerminalCount
        runChargedFullCompressionPublicFindCount
      change
        backend.fullCompressFindScheduleTerminalCount schedule x +
          after.runChargedFullCompressionScheduleTerminalCount schedule ops <=
        1 + runChargedFullCompressionPublicFindCount ops
      omega
  | UFOp.union x y :: ops, hvalid => by
      let after := (backend.chargedUnionCosted x y).erase
      have hxy : x < backend.state.forest.size /\ y < backend.state.forest.size := by
        exact hvalid (UFOp.union x y) (by simp)
      have hhead :=
        backend.chargedUnionScheduleTerminalCount_le_two_of_valid
          schedule hxy.1 hxy.2
      have hsize : after.state.forest.size = backend.state.forest.size := by
        simpa [after] using backend.chargedUnionCosted_forest_size_eq x y
      have htailValid :
          opsValidForSize after.state.forest.size ops := by
        intro op hop
        have hopValid : opValidForSize backend.state.forest.size op :=
          hvalid op (by simp [hop])
        simpa [hsize] using hopValid
      have htail :=
        runChargedFullCompressionScheduleTerminalCount_le_publicFindCount_of_valid
          schedule after ops htailValid
      unfold runChargedFullCompressionScheduleTerminalCount
        runChargedFullCompressionPublicFindCount
      change
        backend.chargedUnionScheduleTerminalCount schedule x y +
          after.runChargedFullCompressionScheduleTerminalCount schedule ops <=
        2 + runChargedFullCompressionPublicFindCount ops
      omega

theorem runChargedFullCompressionCost_le_scheduledResiduals_add_three_mul_length_of_valid
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp)
    (hvalid : opsValidForSize backend.state.forest.size ops) :
    (backend.runChargedFullCompressionOpsCosted ops).cost <=
      backend.runChargedFullCompressionScheduleCrossCount schedule ops +
        backend.runChargedFullCompressionScheduleResidualCount schedule ops +
        3 * ops.length := by
  have hcost :=
    (backend.runChargedFullCompressionScheduledEventCost_profile
      schedule ops).2
  have hterminal :=
    backend.runChargedFullCompressionScheduleTerminalCount_le_publicFindCount_of_valid
      schedule ops hvalid
  have hpublic := runChargedFullCompressionPublicFindCount_le_two_mul_length ops
  have hlinks := runChargedFullCompressionLinkCount_le_length ops
  rw [hcost]
  omega

/--
Root-edge-aware cheap events for the Tarjan classifier.

The first schedule split counted only the self-parent root as terminal.  Tarjan
accounting also treats the edge directly into the root as a per-find constant.
This classifier therefore reserves the event for `parent = x` or
`parent = root` before deciding whether an edge crosses a schedule level.
-/
def nodeRootParentScheduleRootEdgeCount
    (_schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) : Nat :=
  match backend.state.forest.parent? x with
  | none => 1
  | some parent => if parent = x ∨ parent = root then 1 else 0

def nodeRootParentScheduleStrictCrossCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) : Nat :=
  match backend.state.forest.parent? x with
  | none => 0
  | some parent =>
      if parent = x ∨ parent = root then
        0
      else if schedule.level (backend.state.rank parent) <
          schedule.level (backend.state.rank root) then
        1
      else
        0

def nodeRootParentScheduleStrictResidualCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) : Nat :=
  match backend.state.forest.parent? x with
  | none => 0
  | some parent =>
      if parent = x ∨ parent = root then
        0
      else if schedule.level (backend.state.rank parent) <
          schedule.level (backend.state.rank root) then
        0
      else
        1

theorem nodeRootParentScheduleStrictEventCounts_eq_one
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) :
    backend.nodeRootParentScheduleRootEdgeCount schedule root x +
        backend.nodeRootParentScheduleStrictCrossCount schedule root x +
        backend.nodeRootParentScheduleStrictResidualCount schedule root x = 1 := by
  unfold nodeRootParentScheduleRootEdgeCount
    nodeRootParentScheduleStrictCrossCount
    nodeRootParentScheduleStrictResidualCount
  cases hparent : backend.state.forest.parent? x with
  | none =>
      simp
  | some parent =>
      by_cases hcheap : parent = x ∨ parent = root
      · simp [hcheap]
      · by_cases hcross :
          schedule.level (backend.state.rank parent) <
            schedule.level (backend.state.rank root)
        · simp [hcheap, hcross]
        · simp [hcheap, hcross]

def traceRootParentScheduleRootEdgeCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeRootParentScheduleRootEdgeCount schedule root x +
        backend.traceRootParentScheduleRootEdgeCount schedule root xs

def traceRootParentScheduleStrictCrossCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeRootParentScheduleStrictCrossCount schedule root x +
        backend.traceRootParentScheduleStrictCrossCount schedule root xs

def traceRootParentScheduleStrictResidualCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeRootParentScheduleStrictResidualCount schedule root x +
        backend.traceRootParentScheduleStrictResidualCount schedule root xs

theorem traceRootParentScheduleStrictEventCounts_eq_length
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    forall trace : List Nat,
      backend.traceRootParentScheduleRootEdgeCount schedule root trace +
          backend.traceRootParentScheduleStrictCrossCount schedule root trace +
          backend.traceRootParentScheduleStrictResidualCount schedule root trace =
        trace.length
  | [] => by
      simp [traceRootParentScheduleRootEdgeCount,
        traceRootParentScheduleStrictCrossCount,
        traceRootParentScheduleStrictResidualCount]
  | x :: xs => by
      have hhead :=
        backend.nodeRootParentScheduleStrictEventCounts_eq_one
          schedule root x
      have htail :=
        traceRootParentScheduleStrictEventCounts_eq_length
          schedule backend root xs
      simp [traceRootParentScheduleRootEdgeCount,
        traceRootParentScheduleStrictCrossCount,
        traceRootParentScheduleStrictResidualCount]
      omega

def fullCompressFindScheduleRootEdgeCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.fullCompressFindEventCount x
  | some root =>
      backend.traceRootParentScheduleRootEdgeCount schedule root
        (backend.fullCompressFindTrace x)

def fullCompressFindScheduleStrictCrossCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => 0
  | some root =>
      backend.traceRootParentScheduleStrictCrossCount schedule root
        (backend.fullCompressFindTrace x)

def fullCompressFindScheduleStrictResidualCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => 0
  | some root =>
      backend.traceRootParentScheduleStrictResidualCount schedule root
        (backend.fullCompressFindTrace x)

theorem fullCompressFindScheduleStrictEventCounts_eq_findEventCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    backend.fullCompressFindScheduleRootEdgeCount schedule x +
        backend.fullCompressFindScheduleStrictCrossCount schedule x +
        backend.fullCompressFindScheduleStrictResidualCount schedule x =
      backend.fullCompressFindEventCount x := by
  unfold fullCompressFindScheduleRootEdgeCount
    fullCompressFindScheduleStrictCrossCount
    fullCompressFindScheduleStrictResidualCount
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp
  | some root =>
      have htrace :=
        backend.traceRootParentScheduleStrictEventCounts_eq_length
          schedule root (backend.fullCompressFindTrace x)
      simpa [hfind, fullCompressFindEventCount] using htrace

def chargedUnionScheduleRootEdgeCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) : Nat :=
  backend.fullCompressFindScheduleRootEdgeCount schedule x +
    let afterX := (backend.fullCompressFindCosted x).erase.1
    afterX.fullCompressFindScheduleRootEdgeCount schedule y

def chargedUnionScheduleStrictCrossCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) : Nat :=
  backend.fullCompressFindScheduleStrictCrossCount schedule x +
    let afterX := (backend.fullCompressFindCosted x).erase.1
    afterX.fullCompressFindScheduleStrictCrossCount schedule y

def chargedUnionScheduleStrictResidualCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) : Nat :=
  backend.fullCompressFindScheduleStrictResidualCount schedule x +
    let afterX := (backend.fullCompressFindCosted x).erase.1
    afterX.fullCompressFindScheduleStrictResidualCount schedule y

theorem chargedUnionScheduleStrictEventCounts_eq_findEventCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    backend.chargedUnionScheduleRootEdgeCount schedule x y +
        backend.chargedUnionScheduleStrictCrossCount schedule x y +
        backend.chargedUnionScheduleStrictResidualCount schedule x y =
      backend.chargedUnionFindEventCount x y := by
  let afterX := (backend.fullCompressFindCosted x).erase.1
  have hx :=
    backend.fullCompressFindScheduleStrictEventCounts_eq_findEventCount
      schedule x
  have hy :=
    afterX.fullCompressFindScheduleStrictEventCounts_eq_findEventCount
      schedule y
  unfold chargedUnionScheduleRootEdgeCount
    chargedUnionScheduleStrictCrossCount
    chargedUnionScheduleStrictResidualCount chargedUnionFindEventCount
  change
    (backend.fullCompressFindScheduleRootEdgeCount schedule x +
          afterX.fullCompressFindScheduleRootEdgeCount schedule y) +
        (backend.fullCompressFindScheduleStrictCrossCount schedule x +
          afterX.fullCompressFindScheduleStrictCrossCount schedule y) +
        (backend.fullCompressFindScheduleStrictResidualCount schedule x +
          afterX.fullCompressFindScheduleStrictResidualCount schedule y) =
      backend.fullCompressFindEventCount x +
        afterX.fullCompressFindEventCount y
  omega

def runChargedFullCompressionScheduleRootEdgeCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    List UFOp -> Nat
  | [] => 0
  | UFOp.find x :: ops =>
      backend.fullCompressFindScheduleRootEdgeCount schedule x +
        let after := (backend.fullCompressFindCosted x).erase.1
        after.runChargedFullCompressionScheduleRootEdgeCount schedule ops
  | UFOp.union x y :: ops =>
      backend.chargedUnionScheduleRootEdgeCount schedule x y +
        let after := (backend.chargedUnionCosted x y).erase
        after.runChargedFullCompressionScheduleRootEdgeCount schedule ops

def runChargedFullCompressionScheduleStrictCrossCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    List UFOp -> Nat
  | [] => 0
  | UFOp.find x :: ops =>
      backend.fullCompressFindScheduleStrictCrossCount schedule x +
        let after := (backend.fullCompressFindCosted x).erase.1
        after.runChargedFullCompressionScheduleStrictCrossCount schedule ops
  | UFOp.union x y :: ops =>
      backend.chargedUnionScheduleStrictCrossCount schedule x y +
        let after := (backend.chargedUnionCosted x y).erase
        after.runChargedFullCompressionScheduleStrictCrossCount schedule ops

def runChargedFullCompressionScheduleStrictResidualCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    List UFOp -> Nat
  | [] => 0
  | UFOp.find x :: ops =>
      backend.fullCompressFindScheduleStrictResidualCount schedule x +
        let after := (backend.fullCompressFindCosted x).erase.1
        after.runChargedFullCompressionScheduleStrictResidualCount schedule ops
  | UFOp.union x y :: ops =>
      backend.chargedUnionScheduleStrictResidualCount schedule x y +
        let after := (backend.chargedUnionCosted x y).erase
        after.runChargedFullCompressionScheduleStrictResidualCount schedule ops

theorem runChargedFullCompressionScheduleStrictEventCounts_eq_findEventCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    forall ops : List UFOp,
      backend.runChargedFullCompressionScheduleRootEdgeCount schedule ops +
          backend.runChargedFullCompressionScheduleStrictCrossCount schedule ops +
          backend.runChargedFullCompressionScheduleStrictResidualCount
            schedule ops =
        backend.runChargedFullCompressionFindEventCount ops
  | [] => by
      rfl
  | UFOp.find x :: ops => by
      let after := (backend.fullCompressFindCosted x).erase.1
      have hhead :=
        backend.fullCompressFindScheduleStrictEventCounts_eq_findEventCount
          schedule x
      have htail :=
        runChargedFullCompressionScheduleStrictEventCounts_eq_findEventCount
          schedule after ops
      unfold runChargedFullCompressionScheduleRootEdgeCount
        runChargedFullCompressionScheduleStrictCrossCount
        runChargedFullCompressionScheduleStrictResidualCount
        runChargedFullCompressionFindEventCount
      change
        (backend.fullCompressFindScheduleRootEdgeCount schedule x +
              after.runChargedFullCompressionScheduleRootEdgeCount
                schedule ops) +
            (backend.fullCompressFindScheduleStrictCrossCount schedule x +
              after.runChargedFullCompressionScheduleStrictCrossCount
                schedule ops) +
            (backend.fullCompressFindScheduleStrictResidualCount schedule x +
              after.runChargedFullCompressionScheduleStrictResidualCount
                schedule ops) =
          backend.fullCompressFindEventCount x +
            after.runChargedFullCompressionFindEventCount ops
      omega
  | UFOp.union x y :: ops => by
      let after := (backend.chargedUnionCosted x y).erase
      have hhead :=
        backend.chargedUnionScheduleStrictEventCounts_eq_findEventCount
          schedule x y
      have htail :=
        runChargedFullCompressionScheduleStrictEventCounts_eq_findEventCount
          schedule after ops
      unfold runChargedFullCompressionScheduleRootEdgeCount
        runChargedFullCompressionScheduleStrictCrossCount
        runChargedFullCompressionScheduleStrictResidualCount
        runChargedFullCompressionFindEventCount
      change
        (backend.chargedUnionScheduleRootEdgeCount schedule x y +
              after.runChargedFullCompressionScheduleRootEdgeCount
                schedule ops) +
            (backend.chargedUnionScheduleStrictCrossCount schedule x y +
              after.runChargedFullCompressionScheduleStrictCrossCount
                schedule ops) +
            (backend.chargedUnionScheduleStrictResidualCount schedule x y +
              after.runChargedFullCompressionScheduleStrictResidualCount
                schedule ops) =
          backend.chargedUnionFindEventCount x y +
            after.runChargedFullCompressionFindEventCount ops
      omega

theorem runChargedFullCompressionStrictScheduledEventCost_profile
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp) :
    backend.runChargedFullCompressionScheduleRootEdgeCount schedule ops +
        backend.runChargedFullCompressionScheduleStrictCrossCount schedule ops +
        backend.runChargedFullCompressionScheduleStrictResidualCount
          schedule ops =
      backend.runChargedFullCompressionFindEventCount ops /\
    (backend.runChargedFullCompressionOpsCosted ops).cost =
      (backend.runChargedFullCompressionScheduleRootEdgeCount schedule ops +
          backend.runChargedFullCompressionScheduleStrictCrossCount
            schedule ops +
          backend.runChargedFullCompressionScheduleStrictResidualCount
            schedule ops) +
        runChargedFullCompressionLinkCount ops := by
  have hfind :=
    backend.runChargedFullCompressionScheduleStrictEventCounts_eq_findEventCount
      schedule ops
  have hcost :=
    backend.runChargedFullCompressionOpsCosted_cost_eq_events ops
  constructor
  · exact hfind
  · rw [hcost, ← hfind]

theorem nodeRootParentScheduleRootEdgeCount_le_one
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) :
    backend.nodeRootParentScheduleRootEdgeCount schedule root x <= 1 := by
  unfold nodeRootParentScheduleRootEdgeCount
  cases backend.state.forest.parent? x with
  | none =>
      simp
  | some parent =>
      by_cases hcheap : parent = x ∨ parent = root
      · simp [hcheap]
      · simp [hcheap]

theorem compressPathFindFuelTrace_rootEdgeCount_le_one_of_root
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {root : Nat},
      backend.state.forest.IsRoot root ->
      backend.traceRootParentScheduleRootEdgeCount schedule root
          (backend.compressPathFindFuelTrace fuel root) <= 1
  | fuel, root, hroot => by
      have htrace :=
        backend.compressPathFindFuelTrace_eq_singleton_of_root fuel hroot
      have hnode :=
        backend.nodeRootParentScheduleRootEdgeCount_le_one
          schedule root root
      rw [htrace]
      simpa [traceRootParentScheduleRootEdgeCount] using hnode

theorem compressPathFindFuelTrace_rootEdgeCount_le_two_of_findRoot?
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root : Nat},
      backend.state.forest.findRoot? x = some root ->
      backend.traceRootParentScheduleRootEdgeCount schedule root
          (backend.compressPathFindFuelTrace fuel x) <= 2
  | 0, x, root, _hfind => by
      simp [compressPathFindFuelTrace,
        traceRootParentScheduleRootEdgeCount]
      have hnode :=
        backend.nodeRootParentScheduleRootEdgeCount_le_one schedule root x
      omega
  | fuel + 1, x, root, hfind => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simp [compressPathFindFuelTrace,
            traceRootParentScheduleRootEdgeCount, hparent]
          have hnode :=
            backend.nodeRootParentScheduleRootEdgeCount_le_one
              schedule root x
          omega
      | some parent =>
          by_cases hsame : parent = x
          · simp [compressPathFindFuelTrace,
              traceRootParentScheduleRootEdgeCount, hparent, hsame]
            have hnode :=
              backend.nodeRootParentScheduleRootEdgeCount_le_one
                schedule root x
            omega
          · by_cases hparentRoot : parent = root
            · have hroot :
                  backend.state.forest.IsRoot root :=
                backend.state.forest.findRoot?_some_root
                  backend.inv.toInvariant hfind
              have htail :
                  backend.traceRootParentScheduleRootEdgeCount schedule root
                      (backend.compressPathFindFuelTrace fuel parent) <= 1 := by
                subst hparentRoot
                exact
                  backend.compressPathFindFuelTrace_rootEdgeCount_le_one_of_root
                    schedule fuel hroot
              have hhead :
                  backend.nodeRootParentScheduleRootEdgeCount schedule root x =
                    1 := by
                simp [nodeRootParentScheduleRootEdgeCount, hparent,
                  hparentRoot]
              simp [compressPathFindFuelTrace,
                traceRootParentScheduleRootEdgeCount, hparent, hsame, hhead]
              omega
            · have hparentFind :
                  backend.state.forest.findRoot? parent = some root :=
                backend.findRoot?_parent_eq_of_parent?_ne
                  hparent hsame hfind
              have htail :=
                compressPathFindFuelTrace_rootEdgeCount_le_two_of_findRoot?
                  schedule backend fuel hparentFind
              have hhead :
                  backend.nodeRootParentScheduleRootEdgeCount schedule root x =
                    0 := by
                simp [nodeRootParentScheduleRootEdgeCount, hparent,
                  hsame, hparentRoot]
              simp [compressPathFindFuelTrace,
                traceRootParentScheduleRootEdgeCount, hparent, hsame, hhead]
              exact htail

theorem fullCompressFindScheduleRootEdgeCount_le_two_of_findRoot?
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    backend.fullCompressFindScheduleRootEdgeCount schedule x <= 2 := by
  simpa [fullCompressFindScheduleRootEdgeCount, hfind,
    fullCompressFindTrace] using
    backend.compressPathFindFuelTrace_rootEdgeCount_le_two_of_findRoot?
      schedule backend.state.forest.maxSearchFuel hfind

theorem fullCompressFindScheduleRootEdgeCount_le_two_of_valid
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {x : Nat} (hx : x < backend.state.forest.size) :
    backend.fullCompressFindScheduleRootEdgeCount schedule x <= 2 := by
  rcases backend.state.forest.findRoot?_total_of_valid
      backend.inv.toInvariant hx with
    ⟨root, hfind, _hvalid, _hroot⟩
  exact
    backend.fullCompressFindScheduleRootEdgeCount_le_two_of_findRoot?
      schedule hfind

theorem chargedUnionScheduleRootEdgeCount_le_four_of_valid
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {x y : Nat}
    (hx : x < backend.state.forest.size)
    (hy : y < backend.state.forest.size) :
    backend.chargedUnionScheduleRootEdgeCount schedule x y <= 4 := by
  let afterX := (backend.fullCompressFindCosted x).erase.1
  have hxCheap :=
    backend.fullCompressFindScheduleRootEdgeCount_le_two_of_valid
      schedule hx
  have hsize : afterX.state.forest.size = backend.state.forest.size := by
    simpa [afterX] using backend.fullCompressFindCosted_forest_size_eq x
  have hyAfter : y < afterX.state.forest.size := by
    omega
  have hyCheap :=
    afterX.fullCompressFindScheduleRootEdgeCount_le_two_of_valid
      schedule hyAfter
  unfold chargedUnionScheduleRootEdgeCount
  change
    backend.fullCompressFindScheduleRootEdgeCount schedule x +
      afterX.fullCompressFindScheduleRootEdgeCount schedule y <= 4
  omega

theorem runChargedFullCompressionScheduleRootEdgeCount_le_two_mul_publicFindCount_of_valid
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    forall ops : List UFOp,
      opsValidForSize backend.state.forest.size ops ->
      backend.runChargedFullCompressionScheduleRootEdgeCount schedule ops <=
        2 * runChargedFullCompressionPublicFindCount ops
  | [], _hvalid => by
      exact Nat.le_refl 0
  | UFOp.find x :: ops, hvalid => by
      let after := (backend.fullCompressFindCosted x).erase.1
      have hx : x < backend.state.forest.size := by
        exact hvalid (UFOp.find x) (by simp)
      have hhead :=
        backend.fullCompressFindScheduleRootEdgeCount_le_two_of_valid
          schedule hx
      have hsize : after.state.forest.size = backend.state.forest.size := by
        simpa [after] using backend.fullCompressFindCosted_forest_size_eq x
      have htailValid :
          opsValidForSize after.state.forest.size ops := by
        intro op hop
        have hopValid : opValidForSize backend.state.forest.size op :=
          hvalid op (by simp [hop])
        simpa [hsize] using hopValid
      have htail :=
        runChargedFullCompressionScheduleRootEdgeCount_le_two_mul_publicFindCount_of_valid
          schedule after ops htailValid
      unfold runChargedFullCompressionScheduleRootEdgeCount
        runChargedFullCompressionPublicFindCount
      change
        backend.fullCompressFindScheduleRootEdgeCount schedule x +
          after.runChargedFullCompressionScheduleRootEdgeCount schedule ops <=
        2 * (1 + runChargedFullCompressionPublicFindCount ops)
      omega
  | UFOp.union x y :: ops, hvalid => by
      let after := (backend.chargedUnionCosted x y).erase
      have hxy : x < backend.state.forest.size /\ y < backend.state.forest.size := by
        exact hvalid (UFOp.union x y) (by simp)
      have hhead :=
        backend.chargedUnionScheduleRootEdgeCount_le_four_of_valid
          schedule hxy.1 hxy.2
      have hsize : after.state.forest.size = backend.state.forest.size := by
        simpa [after] using backend.chargedUnionCosted_forest_size_eq x y
      have htailValid :
          opsValidForSize after.state.forest.size ops := by
        intro op hop
        have hopValid : opValidForSize backend.state.forest.size op :=
          hvalid op (by simp [hop])
        simpa [hsize] using hopValid
      have htail :=
        runChargedFullCompressionScheduleRootEdgeCount_le_two_mul_publicFindCount_of_valid
          schedule after ops htailValid
      unfold runChargedFullCompressionScheduleRootEdgeCount
        runChargedFullCompressionPublicFindCount
      change
        backend.chargedUnionScheduleRootEdgeCount schedule x y +
          after.runChargedFullCompressionScheduleRootEdgeCount schedule ops <=
        2 * (2 + runChargedFullCompressionPublicFindCount ops)
      omega

theorem runChargedFullCompressionCost_le_strictScheduledResiduals_add_five_mul_length_of_valid
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp)
    (hvalid : opsValidForSize backend.state.forest.size ops) :
    (backend.runChargedFullCompressionOpsCosted ops).cost <=
      backend.runChargedFullCompressionScheduleStrictCrossCount schedule ops +
        backend.runChargedFullCompressionScheduleStrictResidualCount schedule ops +
        5 * ops.length := by
  have hcost :=
    (backend.runChargedFullCompressionStrictScheduledEventCost_profile
      schedule ops).2
  have hroot :=
    backend.runChargedFullCompressionScheduleRootEdgeCount_le_two_mul_publicFindCount_of_valid
      schedule ops hvalid
  have hpublic := runChargedFullCompressionPublicFindCount_le_two_mul_length ops
  have hlinks := runChargedFullCompressionLinkCount_le_length ops
  rw [hcost]
  omega

theorem nodeRootParentScheduleStrictResidualCount_le_nodeRootParentRankSlack_of_findRoot?
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    backend.nodeRootParentScheduleStrictResidualCount schedule root x <=
      backend.nodeRootParentRankSlack root x := by
  unfold nodeRootParentScheduleStrictResidualCount nodeRootParentRankSlack
  cases hparent : backend.state.forest.parent? x with
  | none =>
      simp
  | some parent =>
      by_cases hcheap : parent = x ∨ parent = root
      · simp [hcheap]
      · by_cases hcross :
          schedule.level (backend.state.rank parent) <
            schedule.level (backend.state.rank root)
        · simp [hcheap, hcross]
        · have hsame : parent ≠ x := by
            intro h
            exact hcheap (Or.inl h)
          have hparentRoot : parent ≠ root := by
            intro h
            exact hcheap (Or.inr h)
          have hparentFind :
              backend.state.forest.findRoot? parent = some root :=
            backend.findRoot?_parent_eq_of_parent?_ne hparent hsame hfind
          have hrank :
              backend.state.rank parent < backend.state.rank root :=
            backend.state.forest.findRoot?_rank_lt_of_ne
              backend.state.rank backend.inv.toRankInvariant
              hparentFind hparentRoot
          simp [hcheap, hcross]
          omega

theorem compressPathFindFuelTrace_strictResidualCount_le_traceRootParentRankSlack_of_findRoot?
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root : Nat},
      backend.state.forest.findRoot? x = some root ->
      backend.traceRootParentScheduleStrictResidualCount schedule root
          (backend.compressPathFindFuelTrace fuel x) <=
        backend.traceRootParentRankSlack root
          (backend.compressPathFindFuelTrace fuel x)
  | 0, x, root, hfind => by
      simp [compressPathFindFuelTrace,
        traceRootParentScheduleStrictResidualCount,
        traceRootParentRankSlack]
      exact
        backend.nodeRootParentScheduleStrictResidualCount_le_nodeRootParentRankSlack_of_findRoot?
          schedule hfind
  | fuel + 1, x, root, hfind => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simp [compressPathFindFuelTrace,
            traceRootParentScheduleStrictResidualCount,
            traceRootParentRankSlack, hparent]
          exact
            backend.nodeRootParentScheduleStrictResidualCount_le_nodeRootParentRankSlack_of_findRoot?
              schedule hfind
      | some parent =>
          by_cases hsame : parent = x
          · simp [compressPathFindFuelTrace,
              traceRootParentScheduleStrictResidualCount,
              traceRootParentRankSlack, hparent, hsame]
            exact
              backend.nodeRootParentScheduleStrictResidualCount_le_nodeRootParentRankSlack_of_findRoot?
                schedule hfind
          · have hparentFind :
                backend.state.forest.findRoot? parent = some root :=
              backend.findRoot?_parent_eq_of_parent?_ne hparent hsame hfind
            have hhead :=
              backend.nodeRootParentScheduleStrictResidualCount_le_nodeRootParentRankSlack_of_findRoot?
                schedule hfind
            have htail :=
              compressPathFindFuelTrace_strictResidualCount_le_traceRootParentRankSlack_of_findRoot?
                schedule backend fuel hparentFind
            simp [compressPathFindFuelTrace,
              traceRootParentScheduleStrictResidualCount,
              traceRootParentRankSlack, hparent, hsame]
            omega

theorem fullCompressFindScheduleStrictResidualCount_le_traceRootParentRankSlack_of_findRoot?
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    backend.fullCompressFindScheduleStrictResidualCount schedule x <=
      backend.traceRootParentRankSlack root
        (backend.fullCompressFindTrace x) := by
  simpa [fullCompressFindScheduleStrictResidualCount, hfind,
    fullCompressFindTrace] using
    backend.compressPathFindFuelTrace_strictResidualCount_le_traceRootParentRankSlack_of_findRoot?
      schedule backend.state.forest.maxSearchFuel hfind

/--
A strict residual event makes concrete progress on that node's parent rank.

Once direct root edges have been removed from the residual bucket, any trace
node counted as a strict residual has an old parent that is neither itself nor
the root.  Full compression rewrites the node to the root, and ranks are
unchanged by compression, so the new parent has strictly larger rank than the
old parent.
-/
theorem fullCompressFindCosted_strictResidual_parent_rank_progress_of_trace_mem
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {x root y parent : Nat}
    (hfind : backend.state.forest.findRoot? x = some root)
    (hmem : y ∈ backend.fullCompressFindTrace x)
    (hparent : backend.state.forest.parent? y = some parent)
    (hres :
      backend.nodeRootParentScheduleStrictResidualCount schedule root y = 1) :
    ((backend.fullCompressFindCosted x).erase.1).state.forest.parent? y =
        some root /\
      backend.state.rank parent <
        ((backend.fullCompressFindCosted x).erase.1).state.rank root := by
  have hnewParent :
      ((backend.fullCompressFindCosted x).erase.1).state.forest.parent? y =
        some root :=
    backend.fullCompressFindCosted_trace_parent?_eq_root_of_findRoot?
      hfind hmem
  have hyFind :
      backend.state.forest.findRoot? y = some root :=
    backend.fullCompressFindTrace_mem_findRoot?_eq_of_findRoot?
      hfind hmem
  have hrankEq :
      ((backend.fullCompressFindCosted x).erase.1).state.rank =
        backend.state.rank :=
    backend.fullCompressFindCosted_rank_eq x
  have hrankOld : backend.state.rank parent < backend.state.rank root := by
    unfold nodeRootParentScheduleStrictResidualCount at hres
    rw [hparent] at hres
    by_cases hcheap : parent = y ∨ parent = root
    · simp [hcheap] at hres
    · by_cases hcross :
        schedule.level (backend.state.rank parent) <
          schedule.level (backend.state.rank root)
      · simp [hcheap, hcross] at hres
      · have hparentNeY : parent ≠ y := by
          intro h
          exact hcheap (Or.inl h)
        have hparentNeRoot : parent ≠ root := by
          intro h
          exact hcheap (Or.inr h)
        have hparentFind :
            backend.state.forest.findRoot? parent = some root :=
          backend.findRoot?_parent_eq_of_parent?_ne
            hparent hparentNeY hyFind
        exact
          backend.state.forest.findRoot?_rank_lt_of_ne
            backend.state.rank backend.inv.toRankInvariant
            hparentFind hparentNeRoot
  constructor
  · exact hnewParent
  · simpa [hrankEq] using hrankOld

theorem nodeRootParentScheduleStrictResidualCount_le_one
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) :
    backend.nodeRootParentScheduleStrictResidualCount schedule root x <= 1 := by
  unfold nodeRootParentScheduleStrictResidualCount
  cases backend.state.forest.parent? x with
  | none =>
      simp
  | some parent =>
      by_cases hcheap : parent = x ∨ parent = root
      · simp [hcheap]
      · by_cases hcross :
          schedule.level (backend.state.rank parent) <
            schedule.level (backend.state.rank root)
        · simp [hcheap, hcross]
        · simp [hcheap, hcross]

/-- The trace nodes that are actually counted as strict residual events. -/
def traceRootParentScheduleStrictResidualNodes
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    List Nat -> List Nat
  | [] => []
  | x :: xs =>
      let tail :=
        backend.traceRootParentScheduleStrictResidualNodes schedule root xs
      if backend.nodeRootParentScheduleStrictResidualCount schedule root x = 1 then
        x :: tail
      else
        tail

theorem traceRootParentScheduleStrictResidualNodes_length
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    forall trace : List Nat,
      (backend.traceRootParentScheduleStrictResidualNodes
          schedule root trace).length =
        backend.traceRootParentScheduleStrictResidualCount schedule root trace
  | [] => by
      rfl
  | x :: xs => by
      have htail :=
        traceRootParentScheduleStrictResidualNodes_length
          schedule backend root xs
      by_cases hx :
          backend.nodeRootParentScheduleStrictResidualCount schedule root x = 1
      · simp [traceRootParentScheduleStrictResidualNodes,
          traceRootParentScheduleStrictResidualCount, hx, htail]
        omega
      · have hxle :=
          backend.nodeRootParentScheduleStrictResidualCount_le_one
            schedule root x
        have hxzero :
            backend.nodeRootParentScheduleStrictResidualCount schedule root x =
              0 := by
          omega
        simp [traceRootParentScheduleStrictResidualNodes,
          traceRootParentScheduleStrictResidualCount, hxzero, htail]

theorem mem_traceRootParentScheduleStrictResidualNodes
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    forall {trace : List Nat} {y : Nat},
      y ∈ backend.traceRootParentScheduleStrictResidualNodes
          schedule root trace ->
      y ∈ trace /\
        backend.nodeRootParentScheduleStrictResidualCount schedule root y = 1
  | [], y, hmem => by
      simp [traceRootParentScheduleStrictResidualNodes] at hmem
  | x :: xs, y, hmem => by
      by_cases hx :
          backend.nodeRootParentScheduleStrictResidualCount schedule root x = 1
      · have hcases :
            y = x ∨
              y ∈ backend.traceRootParentScheduleStrictResidualNodes
                schedule root xs := by
          simpa [traceRootParentScheduleStrictResidualNodes, hx] using hmem
        rcases hcases with hyx | htail
        · subst y
          constructor
          · simp
          · exact hx
        · rcases
            mem_traceRootParentScheduleStrictResidualNodes
              schedule backend root (trace := xs) (y := y) htail with
            ⟨hmemTail, hyResidual⟩
          constructor
          · simp [hmemTail]
          · exact hyResidual
      · have htail :
            y ∈ backend.traceRootParentScheduleStrictResidualNodes
              schedule root xs := by
          simpa [traceRootParentScheduleStrictResidualNodes, hx] using hmem
        rcases
          mem_traceRootParentScheduleStrictResidualNodes
            schedule backend root (trace := xs) (y := y) htail with
          ⟨hmemTail, hyResidual⟩
        constructor
        · simp [hmemTail]
        · exact hyResidual

def fullCompressFindScheduleStrictResidualNodes
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : List Nat :=
  match backend.state.forest.findRoot? x with
  | none => []
  | some root =>
      backend.traceRootParentScheduleStrictResidualNodes schedule root
        (backend.fullCompressFindTrace x)

theorem fullCompressFindScheduleStrictResidualNodes_length
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindScheduleStrictResidualNodes schedule x).length =
      backend.fullCompressFindScheduleStrictResidualCount schedule x := by
  unfold fullCompressFindScheduleStrictResidualNodes
    fullCompressFindScheduleStrictResidualCount
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp
  | some root =>
      simpa [hfind] using
        backend.traceRootParentScheduleStrictResidualNodes_length
          schedule root (backend.fullCompressFindTrace x)

theorem mem_fullCompressFindScheduleStrictResidualNodes
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {x y : Nat}
    (hmem :
      y ∈ backend.fullCompressFindScheduleStrictResidualNodes schedule x) :
    ∃ root,
      backend.state.forest.findRoot? x = some root /\
        y ∈ backend.fullCompressFindTrace x /\
        backend.nodeRootParentScheduleStrictResidualCount schedule root y = 1 := by
  unfold fullCompressFindScheduleStrictResidualNodes at hmem
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp [hfind] at hmem
  | some root =>
      have htrace :=
        mem_traceRootParentScheduleStrictResidualNodes
          schedule backend root
          (trace := backend.fullCompressFindTrace x) (y := y)
          (by simpa [hfind] using hmem)
      exact ⟨root, rfl, htrace.1, htrace.2⟩

theorem fullCompressFindCosted_strictResidual_parent_rank_progress_of_residual_node_mem
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {x root y : Nat}
    (hfind : backend.state.forest.findRoot? x = some root)
    (hmem :
      y ∈ backend.fullCompressFindScheduleStrictResidualNodes schedule x) :
    ∃ parent,
      backend.state.forest.parent? y = some parent /\
        ((backend.fullCompressFindCosted x).erase.1).state.forest.parent? y =
          some root /\
        backend.state.rank parent <
          ((backend.fullCompressFindCosted x).erase.1).state.rank root := by
  rcases
      backend.mem_fullCompressFindScheduleStrictResidualNodes
        schedule hmem with
    ⟨root', hfind', htrace, hres⟩
  rw [hfind] at hfind'
  cases hfind'
  unfold nodeRootParentScheduleStrictResidualCount at hres
  cases hparent : backend.state.forest.parent? y with
  | none =>
      simp [hparent] at hres
  | some parent =>
      have hprogress :=
        backend.fullCompressFindCosted_strictResidual_parent_rank_progress_of_trace_mem
          schedule hfind htrace hparent hres
      exact ⟨parent, rfl, hprogress.1, hprogress.2⟩

def chargedUnionScheduleStrictResidualNodes
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    List Nat :=
  backend.fullCompressFindScheduleStrictResidualNodes schedule x ++
    let afterX := (backend.fullCompressFindCosted x).erase.1
    afterX.fullCompressFindScheduleStrictResidualNodes schedule y

theorem chargedUnionScheduleStrictResidualNodes_length
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.chargedUnionScheduleStrictResidualNodes schedule x y).length =
      backend.chargedUnionScheduleStrictResidualCount schedule x y := by
  let afterX := (backend.fullCompressFindCosted x).erase.1
  have hx :=
    backend.fullCompressFindScheduleStrictResidualNodes_length schedule x
  have hy :=
    afterX.fullCompressFindScheduleStrictResidualNodes_length schedule y
  unfold chargedUnionScheduleStrictResidualNodes
    chargedUnionScheduleStrictResidualCount
  change
    (backend.fullCompressFindScheduleStrictResidualNodes schedule x ++
      afterX.fullCompressFindScheduleStrictResidualNodes schedule y).length =
      backend.fullCompressFindScheduleStrictResidualCount schedule x +
        afterX.fullCompressFindScheduleStrictResidualCount schedule y
  simp [List.length_append, hx, hy]

def runChargedFullCompressionScheduleStrictResidualNodes
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    List UFOp -> List Nat
  | [] => []
  | UFOp.find x :: ops =>
      backend.fullCompressFindScheduleStrictResidualNodes schedule x ++
        let after := (backend.fullCompressFindCosted x).erase.1
        after.runChargedFullCompressionScheduleStrictResidualNodes schedule ops
  | UFOp.union x y :: ops =>
      backend.chargedUnionScheduleStrictResidualNodes schedule x y ++
        let after := (backend.chargedUnionCosted x y).erase
        after.runChargedFullCompressionScheduleStrictResidualNodes schedule ops

theorem runChargedFullCompressionScheduleStrictResidualNodes_length
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    forall ops : List UFOp,
      (backend.runChargedFullCompressionScheduleStrictResidualNodes
          schedule ops).length =
        backend.runChargedFullCompressionScheduleStrictResidualCount
          schedule ops
  | [] => by
      rfl
  | UFOp.find x :: ops => by
      let after := (backend.fullCompressFindCosted x).erase.1
      have hhead :=
        backend.fullCompressFindScheduleStrictResidualNodes_length
          schedule x
      have htail :=
        runChargedFullCompressionScheduleStrictResidualNodes_length
          schedule after ops
      unfold runChargedFullCompressionScheduleStrictResidualNodes
        runChargedFullCompressionScheduleStrictResidualCount
      change
        (backend.fullCompressFindScheduleStrictResidualNodes schedule x ++
            after.runChargedFullCompressionScheduleStrictResidualNodes
              schedule ops).length =
          backend.fullCompressFindScheduleStrictResidualCount schedule x +
            after.runChargedFullCompressionScheduleStrictResidualCount
              schedule ops
      simp [List.length_append, hhead, htail]
  | UFOp.union x y :: ops => by
      let after := (backend.chargedUnionCosted x y).erase
      have hhead :=
        backend.chargedUnionScheduleStrictResidualNodes_length
          schedule x y
      have htail :=
        runChargedFullCompressionScheduleStrictResidualNodes_length
          schedule after ops
      unfold runChargedFullCompressionScheduleStrictResidualNodes
        runChargedFullCompressionScheduleStrictResidualCount
      change
        (backend.chargedUnionScheduleStrictResidualNodes schedule x y ++
            after.runChargedFullCompressionScheduleStrictResidualNodes
              schedule ops).length =
          backend.chargedUnionScheduleStrictResidualCount schedule x y +
            after.runChargedFullCompressionScheduleStrictResidualCount
              schedule ops
      simp [List.length_append, hhead, htail]

/--
A strict residual event records the local snapshot needed for later Tarjan
counting: a compressed node, its old parent, the root it is rewired to, and
the two ranks at the moment of the compression step.
-/
structure StrictResidualEvent where
  node : Nat
  oldParent : Nat
  root : Nat
  oldParentRank : Nat
  rootRank : Nat
deriving Repr, DecidableEq

namespace StrictResidualEvent

/-- The useful payload fact carried by every strict residual event. -/
def RankProgress (event : StrictResidualEvent) : Prop :=
  event.oldParentRank < event.rootRank

end StrictResidualEvent

/-- Optional one-node strict-residual event with rank snapshot data. -/
def nodeRootParentScheduleStrictResidualEvent?
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) : Option StrictResidualEvent :=
  match backend.state.forest.parent? x with
  | none => none
  | some parent =>
      if parent = x ∨ parent = root then
        none
      else if
          schedule.level (backend.state.rank parent) <
            schedule.level (backend.state.rank root) then
        none
      else
        some
          { node := x
            oldParent := parent
            root := root
            oldParentRank := backend.state.rank parent
            rootRank := backend.state.rank root }

/-- List wrapper for one-node strict-residual event extraction. -/
def nodeRootParentScheduleStrictResidualEvents
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) : List StrictResidualEvent :=
  match backend.nodeRootParentScheduleStrictResidualEvent? schedule root x with
  | none => []
  | some event => [event]

theorem nodeRootParentScheduleStrictResidualEvents_length
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) :
    (backend.nodeRootParentScheduleStrictResidualEvents schedule root x).length =
      backend.nodeRootParentScheduleStrictResidualCount schedule root x := by
  unfold nodeRootParentScheduleStrictResidualEvents
    nodeRootParentScheduleStrictResidualEvent?
    nodeRootParentScheduleStrictResidualCount
  cases hparent : backend.state.forest.parent? x with
  | none =>
      simp
  | some parent =>
      by_cases hcheap : parent = x ∨ parent = root
      · simp [hcheap]
      · by_cases hcross :
          schedule.level (backend.state.rank parent) <
            schedule.level (backend.state.rank root)
        · simp [hcheap, hcross]
        · simp [hcheap, hcross]

theorem mem_nodeRootParentScheduleStrictResidualEvents_event?
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {root x : Nat} {event : StrictResidualEvent}
    (hmem :
      List.Mem event
        (backend.nodeRootParentScheduleStrictResidualEvents
          schedule root x)) :
    backend.nodeRootParentScheduleStrictResidualEvent?
        schedule root x = some event := by
  cases hevent :
      backend.nodeRootParentScheduleStrictResidualEvent? schedule root x with
  | none =>
      have hnil : List.Mem event ([] : List StrictResidualEvent) := by
        simpa [nodeRootParentScheduleStrictResidualEvents, hevent] using hmem
      cases hnil
  | some event' =>
      have hsingle : List.Mem event [event'] := by
        simpa [nodeRootParentScheduleStrictResidualEvents, hevent] using hmem
      rcases List.mem_cons.mp hsingle with heq | hnil
      ·
        simp [heq]
      ·
        cases hnil

theorem nodeRootParentScheduleStrictResidualEvent?_rankProgress_of_findRoot?
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {root x : Nat} {event : StrictResidualEvent}
    (hfind : backend.state.forest.findRoot? x = some root)
    (hevent :
      backend.nodeRootParentScheduleStrictResidualEvent?
        schedule root x = some event) :
    event.RankProgress := by
  unfold nodeRootParentScheduleStrictResidualEvent? at hevent
  cases hparent : backend.state.forest.parent? x with
  | none =>
      simp [hparent] at hevent
  | some parent =>
      rw [hparent] at hevent
      by_cases hcheap : parent = x ∨ parent = root
      · simp [hcheap] at hevent
      · by_cases hcross :
          schedule.level (backend.state.rank parent) <
            schedule.level (backend.state.rank root)
        · simp [hcheap, hcross] at hevent
        · have hparentNeX : parent ≠ x := by
            intro h
            exact hcheap (Or.inl h)
          have hparentNeRoot : parent ≠ root := by
            intro h
            exact hcheap (Or.inr h)
          have hparentFind :
              backend.state.forest.findRoot? parent = some root :=
            backend.findRoot?_parent_eq_of_parent?_ne
              hparent hparentNeX hfind
          have hrank :
              backend.state.rank parent < backend.state.rank root :=
            backend.state.forest.findRoot?_rank_lt_of_ne
              backend.state.rank backend.inv.toRankInvariant
              hparentFind hparentNeRoot
          simp [hcheap, hcross] at hevent
          cases hevent
          simpa [StrictResidualEvent.RankProgress] using hrank

/-- Field-level meaning of a one-node strict-residual event snapshot. -/
theorem nodeRootParentScheduleStrictResidualEvent?_fields
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {root x : Nat} {event : StrictResidualEvent}
    (hevent :
      backend.nodeRootParentScheduleStrictResidualEvent?
        schedule root x = some event) :
    event.node = x /\
      event.root = root /\
      backend.state.forest.parent? x = some event.oldParent /\
      event.oldParentRank = backend.state.rank event.oldParent /\
      event.rootRank = backend.state.rank root := by
  unfold nodeRootParentScheduleStrictResidualEvent? at hevent
  cases hparent : backend.state.forest.parent? x with
  | none =>
      simp [hparent] at hevent
  | some parent =>
      rw [hparent] at hevent
      by_cases hcheap : parent = x ∨ parent = root
      · simp [hcheap] at hevent
      · by_cases hcross :
          schedule.level (backend.state.rank parent) <
            schedule.level (backend.state.rank root)
        · simp [hcheap, hcross] at hevent
        · simp [hcheap, hcross] at hevent
          cases hevent
          simp

theorem mem_nodeRootParentScheduleStrictResidualEvents_rankProgress_of_findRoot?
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    {root x : Nat} {event : StrictResidualEvent}
    (hfind : backend.state.forest.findRoot? x = some root)
    (hmem :
      List.Mem event
        (backend.nodeRootParentScheduleStrictResidualEvents
          schedule root x)) :
    event.RankProgress :=
  nodeRootParentScheduleStrictResidualEvent?_rankProgress_of_findRoot?
    schedule backend hfind
    (mem_nodeRootParentScheduleStrictResidualEvents_event?
      schedule backend hmem)

/-- Strict residual events extracted from a trace. -/
def traceRootParentScheduleStrictResidualEvents
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    List Nat -> List StrictResidualEvent
  | [] => []
  | x :: xs =>
      backend.nodeRootParentScheduleStrictResidualEvents schedule root x ++
        backend.traceRootParentScheduleStrictResidualEvents schedule root xs

theorem traceRootParentScheduleStrictResidualEvents_length
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    forall trace : List Nat,
      (backend.traceRootParentScheduleStrictResidualEvents
          schedule root trace).length =
        backend.traceRootParentScheduleStrictResidualCount schedule root trace
  | [] => by
      rfl
  | x :: xs => by
      have hhead :=
        backend.nodeRootParentScheduleStrictResidualEvents_length
          schedule root x
      have htail :=
        traceRootParentScheduleStrictResidualEvents_length
          schedule backend root xs
      simp [traceRootParentScheduleStrictResidualEvents,
        traceRootParentScheduleStrictResidualCount,
        List.length_append, hhead, htail]

theorem mem_traceRootParentScheduleStrictResidualEvents
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    forall {trace : List Nat} {event : StrictResidualEvent},
      List.Mem event
        (backend.traceRootParentScheduleStrictResidualEvents
          schedule root trace) ->
      Exists fun y =>
        List.Mem y trace /\
          List.Mem event
            (backend.nodeRootParentScheduleStrictResidualEvents
              schedule root y)
  | [], event, hmem => by
      cases hmem
  | x :: xs, event, hmem => by
      have hmem' :
          List.Mem event
            (backend.nodeRootParentScheduleStrictResidualEvents
                schedule root x ++
              backend.traceRootParentScheduleStrictResidualEvents
                schedule root xs) := by
        simpa [traceRootParentScheduleStrictResidualEvents] using hmem
      have hcases :
          List.Mem event
              (backend.nodeRootParentScheduleStrictResidualEvents
                schedule root x) ∨
            List.Mem event
              (backend.traceRootParentScheduleStrictResidualEvents
                schedule root xs) :=
        List.mem_append.mp hmem'
      rcases hcases with hhead | htail
      · exact ⟨x, List.Mem.head xs, hhead⟩
      · rcases
          mem_traceRootParentScheduleStrictResidualEvents
            schedule backend root (trace := xs) (event := event) htail with
          ⟨y, hyTrace, hyEvent⟩
        exact ⟨y, List.Mem.tail x hyTrace, hyEvent⟩

def fullCompressFindScheduleStrictResidualEvents
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    List StrictResidualEvent :=
  match backend.state.forest.findRoot? x with
  | none => []
  | some root =>
      backend.traceRootParentScheduleStrictResidualEvents schedule root
        (backend.fullCompressFindTrace x)

theorem fullCompressFindScheduleStrictResidualEvents_length
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindScheduleStrictResidualEvents schedule x).length =
      backend.fullCompressFindScheduleStrictResidualCount schedule x := by
  unfold fullCompressFindScheduleStrictResidualEvents
    fullCompressFindScheduleStrictResidualCount
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp
  | some root =>
      simpa [hfind] using
        backend.traceRootParentScheduleStrictResidualEvents_length
          schedule root (backend.fullCompressFindTrace x)

theorem fullCompressFindScheduleStrictResidualEvents_rankProgress
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat)
    {event : StrictResidualEvent}
    (hmem :
      List.Mem event
        (backend.fullCompressFindScheduleStrictResidualEvents schedule x)) :
    event.RankProgress := by
  unfold fullCompressFindScheduleStrictResidualEvents at hmem
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      have hnil : List.Mem event ([] : List StrictResidualEvent) := by
        simpa [hfind] using hmem
      cases hnil
  | some root =>
      rcases
          mem_traceRootParentScheduleStrictResidualEvents
            schedule backend root
            (trace := backend.fullCompressFindTrace x)
            (event := event)
            (by simpa [hfind] using hmem) with
        ⟨y, hyTrace, hyEvent⟩
      have hyFind :
          backend.state.forest.findRoot? y = some root :=
        backend.fullCompressFindTrace_mem_findRoot?_eq_of_findRoot?
          hfind hyTrace
      exact
        mem_nodeRootParentScheduleStrictResidualEvents_rankProgress_of_findRoot?
          schedule backend hyFind hyEvent

/--
Every extracted full-find residual event is the node whose parent is rewritten
to the event root by that full compression step.
-/
theorem fullCompressFindScheduleStrictResidualEvents_parent?_eq_root_of_mem
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat)
    {event : StrictResidualEvent}
    (hmem :
      List.Mem event
        (backend.fullCompressFindScheduleStrictResidualEvents schedule x)) :
    ((backend.fullCompressFindCosted x).erase.1).state.forest.parent?
        event.node = some event.root := by
  unfold fullCompressFindScheduleStrictResidualEvents at hmem
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      have hnil : List.Mem event ([] : List StrictResidualEvent) := by
        simpa [hfind] using hmem
      cases hnil
  | some root =>
      rcases
          mem_traceRootParentScheduleStrictResidualEvents
            schedule backend root
            (trace := backend.fullCompressFindTrace x)
            (event := event)
            (by simpa [hfind] using hmem) with
        ⟨y, hyTrace, hyEvent⟩
      have hevent? :
          backend.nodeRootParentScheduleStrictResidualEvent?
              schedule root y = some event :=
        mem_nodeRootParentScheduleStrictResidualEvents_event?
          schedule backend hyEvent
      rcases
          nodeRootParentScheduleStrictResidualEvent?_fields
            schedule backend hevent? with
        ⟨hnode, hroot, _hparent, _hrankParent, _hrankRoot⟩
      have hparentAfter :
          ((backend.fullCompressFindCosted x).erase.1).state.forest.parent?
              y = some root :=
        backend.fullCompressFindCosted_trace_parent?_eq_root_of_findRoot?
          hfind hyTrace
      simpa [hnode, hroot] using hparentAfter

theorem fullCompressFindScheduleStrictResidualEvents_rootRank_eq_after_rank_of_mem
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x : Nat)
    {event : StrictResidualEvent}
    (hmem :
      List.Mem event
        (backend.fullCompressFindScheduleStrictResidualEvents schedule x)) :
    event.rootRank =
      ((backend.fullCompressFindCosted x).erase.1).state.rank event.root := by
  unfold fullCompressFindScheduleStrictResidualEvents at hmem
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      have hnil : List.Mem event ([] : List StrictResidualEvent) := by
        simpa [hfind] using hmem
      cases hnil
  | some root =>
      rcases
          mem_traceRootParentScheduleStrictResidualEvents
            schedule backend root
            (trace := backend.fullCompressFindTrace x)
            (event := event)
            (by simpa [hfind] using hmem) with
        ⟨y, _hyTrace, hyEvent⟩
      have hevent? :
          backend.nodeRootParentScheduleStrictResidualEvent?
              schedule root y = some event :=
        mem_nodeRootParentScheduleStrictResidualEvents_event?
          schedule backend hyEvent
      rcases
          nodeRootParentScheduleStrictResidualEvent?_fields
            schedule backend hevent? with
        ⟨_hnode, hroot, _hparent, _hrankParent, hrankRoot⟩
      have hrankEq :
          ((backend.fullCompressFindCosted x).erase.1).state.rank =
            backend.state.rank :=
        backend.fullCompressFindCosted_rank_eq x
      simpa [hroot, hrankEq] using hrankRoot

def chargedUnionScheduleStrictResidualEvents
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    List StrictResidualEvent :=
  backend.fullCompressFindScheduleStrictResidualEvents schedule x ++
    let afterX := (backend.fullCompressFindCosted x).erase.1
    afterX.fullCompressFindScheduleStrictResidualEvents schedule y

theorem chargedUnionScheduleStrictResidualEvents_length
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.chargedUnionScheduleStrictResidualEvents schedule x y).length =
      backend.chargedUnionScheduleStrictResidualCount schedule x y := by
  let afterX := (backend.fullCompressFindCosted x).erase.1
  have hx :=
    backend.fullCompressFindScheduleStrictResidualEvents_length schedule x
  have hy :=
    afterX.fullCompressFindScheduleStrictResidualEvents_length schedule y
  unfold chargedUnionScheduleStrictResidualEvents
    chargedUnionScheduleStrictResidualCount
  change
    (backend.fullCompressFindScheduleStrictResidualEvents schedule x ++
      afterX.fullCompressFindScheduleStrictResidualEvents schedule y).length =
      backend.fullCompressFindScheduleStrictResidualCount schedule x +
        afterX.fullCompressFindScheduleStrictResidualCount schedule y
  simp [List.length_append, hx, hy]

theorem chargedUnionScheduleStrictResidualEvents_rankProgress
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (x y : Nat)
    {event : StrictResidualEvent}
    (hmem :
      List.Mem event
        (backend.chargedUnionScheduleStrictResidualEvents schedule x y)) :
    event.RankProgress := by
  let afterX := (backend.fullCompressFindCosted x).erase.1
  have hmem' :
      List.Mem event
        (backend.fullCompressFindScheduleStrictResidualEvents schedule x ++
          afterX.fullCompressFindScheduleStrictResidualEvents schedule y) := by
    simpa [chargedUnionScheduleStrictResidualEvents, afterX] using hmem
  have hcases :
      List.Mem event
          (backend.fullCompressFindScheduleStrictResidualEvents schedule x) ∨
        List.Mem event
          (afterX.fullCompressFindScheduleStrictResidualEvents schedule y) :=
    List.mem_append.mp hmem'
  rcases hcases with hx | hy
  · exact
      backend.fullCompressFindScheduleStrictResidualEvents_rankProgress
        schedule x hx
  · exact
      afterX.fullCompressFindScheduleStrictResidualEvents_rankProgress
        schedule y hy

def runChargedFullCompressionScheduleStrictResidualEvents
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    List UFOp -> List StrictResidualEvent
  | [] => []
  | UFOp.find x :: ops =>
      backend.fullCompressFindScheduleStrictResidualEvents schedule x ++
        let after := (backend.fullCompressFindCosted x).erase.1
        after.runChargedFullCompressionScheduleStrictResidualEvents schedule ops
  | UFOp.union x y :: ops =>
      backend.chargedUnionScheduleStrictResidualEvents schedule x y ++
        let after := (backend.chargedUnionCosted x y).erase
        after.runChargedFullCompressionScheduleStrictResidualEvents schedule ops

theorem runChargedFullCompressionScheduleStrictResidualEvents_length
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    forall ops : List UFOp,
      (backend.runChargedFullCompressionScheduleStrictResidualEvents
          schedule ops).length =
        backend.runChargedFullCompressionScheduleStrictResidualCount
          schedule ops
  | [] => by
      rfl
  | UFOp.find x :: ops => by
      let after := (backend.fullCompressFindCosted x).erase.1
      have hhead :=
        backend.fullCompressFindScheduleStrictResidualEvents_length
          schedule x
      have htail :=
        runChargedFullCompressionScheduleStrictResidualEvents_length
          schedule after ops
      unfold runChargedFullCompressionScheduleStrictResidualEvents
        runChargedFullCompressionScheduleStrictResidualCount
      change
        (backend.fullCompressFindScheduleStrictResidualEvents schedule x ++
            after.runChargedFullCompressionScheduleStrictResidualEvents
              schedule ops).length =
          backend.fullCompressFindScheduleStrictResidualCount schedule x +
            after.runChargedFullCompressionScheduleStrictResidualCount
              schedule ops
      simp [List.length_append, hhead, htail]
  | UFOp.union x y :: ops => by
      let after := (backend.chargedUnionCosted x y).erase
      have hhead :=
        backend.chargedUnionScheduleStrictResidualEvents_length
          schedule x y
      have htail :=
        runChargedFullCompressionScheduleStrictResidualEvents_length
          schedule after ops
      unfold runChargedFullCompressionScheduleStrictResidualEvents
        runChargedFullCompressionScheduleStrictResidualCount
      change
        (backend.chargedUnionScheduleStrictResidualEvents schedule x y ++
            after.runChargedFullCompressionScheduleStrictResidualEvents
              schedule ops).length =
          backend.chargedUnionScheduleStrictResidualCount schedule x y +
            after.runChargedFullCompressionScheduleStrictResidualCount
              schedule ops
      simp [List.length_append, hhead, htail]

theorem runChargedFullCompressionScheduleStrictResidualEvents_rankProgress
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) :
    forall {ops : List UFOp} {event : StrictResidualEvent},
      List.Mem event
        (backend.runChargedFullCompressionScheduleStrictResidualEvents
          schedule ops) ->
        event.RankProgress
  | [], event, hmem => by
      cases hmem
  | UFOp.find x :: ops, event, hmem => by
      let after := (backend.fullCompressFindCosted x).erase.1
      have hmem' :
          List.Mem event
            (backend.fullCompressFindScheduleStrictResidualEvents
                schedule x ++
              after.runChargedFullCompressionScheduleStrictResidualEvents
                schedule ops) := by
        simpa [runChargedFullCompressionScheduleStrictResidualEvents,
          after] using hmem
      have hcases :
          List.Mem event
              (backend.fullCompressFindScheduleStrictResidualEvents
                schedule x) ∨
            List.Mem event
              (after.runChargedFullCompressionScheduleStrictResidualEvents
                schedule ops) :=
        List.mem_append.mp hmem'
      rcases hcases with hhead | htail
      · exact
          backend.fullCompressFindScheduleStrictResidualEvents_rankProgress
            schedule x hhead
      · exact
          runChargedFullCompressionScheduleStrictResidualEvents_rankProgress
            schedule after (ops := ops) htail
  | UFOp.union x y :: ops, event, hmem => by
      let after := (backend.chargedUnionCosted x y).erase
      have hmem' :
          List.Mem event
            (backend.chargedUnionScheduleStrictResidualEvents
                schedule x y ++
              after.runChargedFullCompressionScheduleStrictResidualEvents
                schedule ops) := by
        simpa [runChargedFullCompressionScheduleStrictResidualEvents,
          after] using hmem
      have hcases :
          List.Mem event
              (backend.chargedUnionScheduleStrictResidualEvents
                schedule x y) ∨
            List.Mem event
              (after.runChargedFullCompressionScheduleStrictResidualEvents
                schedule ops) :=
        List.mem_append.mp hmem'
      rcases hcases with hhead | htail
      · exact
          backend.chargedUnionScheduleStrictResidualEvents_rankProgress
            schedule x y hhead
      · exact
          runChargedFullCompressionScheduleStrictResidualEvents_rankProgress
            schedule after (ops := ops) htail

theorem nodeRootParentScheduleStrictCrossCount_le_scheduleCrossCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) :
    backend.nodeRootParentScheduleStrictCrossCount schedule root x <=
      backend.nodeRootParentScheduleCrossCount schedule root x := by
  unfold nodeRootParentScheduleStrictCrossCount nodeRootParentScheduleCrossCount
  cases hparent : backend.state.forest.parent? x with
  | none =>
      simp
  | some parent =>
      by_cases hsame : parent = x
      · simp [hsame]
      · by_cases hparentRoot : parent = root
        · simp [hparentRoot]
        · have hcheap : ¬(parent = x ∨ parent = root) := by
            intro h
            cases h with
            | inl hx => exact hsame hx
            | inr hr => exact hparentRoot hr
          by_cases hcross :
            schedule.level (backend.state.rank parent) <
              schedule.level (backend.state.rank root)
          · have hleft :
                (if parent = root then 0 else 1) = 1 := by
              simp [hparentRoot]
            simp [hsame, hparentRoot, hcross]
          · simp [hsame, hparentRoot, hcross]

theorem traceRootParentScheduleStrictCrossCount_le_scheduleCrossCount
    (schedule : RankSchedule)
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    forall trace : List Nat,
      backend.traceRootParentScheduleStrictCrossCount schedule root trace <=
        backend.traceRootParentScheduleCrossCount schedule root trace
  | [] => by
      simp [traceRootParentScheduleStrictCrossCount,
        traceRootParentScheduleCrossCount]
  | x :: xs => by
      have hhead :=
        backend.nodeRootParentScheduleStrictCrossCount_le_scheduleCrossCount
          schedule root x
      have htail :=
        traceRootParentScheduleStrictCrossCount_le_scheduleCrossCount
          schedule backend root xs
      simp [traceRootParentScheduleStrictCrossCount,
        traceRootParentScheduleCrossCount]
      omega

theorem nodeRootParentIteratedLogScheduleCrossCount_le_tarjanLevelGap
    (backend : NoCompressionRankedMassBackendState) (root x : Nat) :
    backend.nodeRootParentScheduleCrossCount iteratedLogRankSchedule root x <=
      backend.nodeRootParentTarjanLevelGap root x := by
  unfold nodeRootParentScheduleCrossCount nodeRootParentTarjanLevelGap
    iteratedLogRankSchedule
  cases hparent : backend.state.forest.parent? x with
  | none =>
      simp
  | some parent =>
      by_cases hsame : parent = x
      · simp [hsame]
      · by_cases hcross :
          tarjanRankLevel (backend.state.rank parent) <
            tarjanRankLevel (backend.state.rank root)
        · simp [hsame, hcross]
          omega
        · simp [hsame, hcross]

theorem traceRootParentIteratedLogScheduleCrossCount_le_tarjanLevelGap
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    forall trace : List Nat,
      backend.traceRootParentScheduleCrossCount
          iteratedLogRankSchedule root trace <=
        backend.traceRootParentTarjanLevelGap root trace
  | [] => by
      simp [traceRootParentScheduleCrossCount,
        traceRootParentTarjanLevelGap]
  | x :: xs => by
      have hhead :=
        backend.nodeRootParentIteratedLogScheduleCrossCount_le_tarjanLevelGap
          root x
      have htail :=
        traceRootParentIteratedLogScheduleCrossCount_le_tarjanLevelGap
          backend root xs
      simp [traceRootParentScheduleCrossCount,
        traceRootParentTarjanLevelGap]
      omega

theorem fullCompressFindIteratedLogScheduleCrossCount_le_traceLevelGap_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    backend.fullCompressFindScheduleCrossCount iteratedLogRankSchedule x <=
      backend.traceRootParentTarjanLevelGap root
        (backend.fullCompressFindTrace x) := by
  simpa [fullCompressFindScheduleCrossCount, hfind] using
    backend.traceRootParentIteratedLogScheduleCrossCount_le_tarjanLevelGap
      root (backend.fullCompressFindTrace x)

theorem fullCompressFindStrictIteratedLogScheduleCrossCount_le_traceLevelGap_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    backend.fullCompressFindScheduleStrictCrossCount iteratedLogRankSchedule x <=
      backend.traceRootParentTarjanLevelGap root
        (backend.fullCompressFindTrace x) := by
  have hstrict :
      backend.fullCompressFindScheduleStrictCrossCount
          iteratedLogRankSchedule x <=
        backend.fullCompressFindScheduleCrossCount iteratedLogRankSchedule x := by
    simpa [fullCompressFindScheduleStrictCrossCount,
      fullCompressFindScheduleCrossCount, hfind] using
      backend.traceRootParentScheduleStrictCrossCount_le_scheduleCrossCount
        iteratedLogRankSchedule root (backend.fullCompressFindTrace x)
  have hcross :=
    backend.fullCompressFindIteratedLogScheduleCrossCount_le_traceLevelGap_of_findRoot?
      hfind
  omega

end NoCompressionRankedMassBackendState
end ParentForest
end Forest

end UnionFind

end RMQ
