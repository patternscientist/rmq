import RMQ.Core.UnionFind.Forest

/-!
# Union-find operation sequences

This module is the first sequence-level surface for the union-find spoke.  The
current forest backend already has one-step refinement and amortized profiles;
Tarjan-style inverse-Ackermann analysis needs a whole-run scorecard.  We define
a mixed `find`/`union` operation language, reference and representation-backed
runners, a representative-insensitive refinement theorem, and a generic
potential-method telescope theorem.
-/

namespace RMQ

namespace UnionFind

/-- Mixed operation language for sequence-level union-find analyses. -/
inductive UFOp where
  | find : Nat -> UFOp
  | union : Nat -> Nat -> UFOp
deriving Repr, DecidableEq

namespace State

/--
Reference execution for mixed operation sequences.

The output list is aligned with the operation list: `find x` records
`state.find? x`, while `union x y` records `none`.  Refinement theorems below
use `SamePartition` for final states, because concrete union-by-rank backends
are allowed to choose representatives different from the fixed `unionSpec`
orientation.
-/
def runOpsSpec (state : State) : List UFOp -> State × List (Option Nat)
  | [] => (state, [])
  | UFOp.find x :: ops =>
      let tail := state.runOpsSpec ops
      (tail.1, state.find? x :: tail.2)
  | UFOp.union x y :: ops =>
      let next := state.unionSpec x y
      let tail := next.runOpsSpec ops
      (tail.1, none :: tail.2)

@[simp] theorem runOpsSpec_nil (state : State) :
    state.runOpsSpec [] = (state, []) := by
  rfl

@[simp] theorem runOpsSpec_find_cons
    (state : State) (x : Nat) (ops : List UFOp) :
    state.runOpsSpec (UFOp.find x :: ops) =
      let tail := state.runOpsSpec ops
      (tail.1, state.find? x :: tail.2) := by
  rfl

@[simp] theorem runOpsSpec_union_cons
    (state : State) (x y : Nat) (ops : List UFOp) :
    state.runOpsSpec (UFOp.union x y :: ops) =
      let tail := (state.unionSpec x y).runOpsSpec ops
      (tail.1, none :: tail.2) := by
  rfl

theorem runOpsSpec_outputs_length
    (state : State) :
    forall ops : List UFOp, (state.runOpsSpec ops).2.length = ops.length
  | [] => by
      rfl
  | UFOp.find x :: ops => by
      have htail := runOpsSpec_outputs_length state ops
      simp [runOpsSpec, htail]
  | UFOp.union x y :: ops => by
      have htail := runOpsSpec_outputs_length (state.unionSpec x y) ops
      simp [runOpsSpec, htail]

theorem runOpsSpec_samePartition
    {left right : State} (h : left.SamePartition right) :
    forall ops : List UFOp,
      ((left.runOpsSpec ops).1).SamePartition
        ((right.runOpsSpec ops).1)
  | [] => by
      simpa [runOpsSpec] using h
  | UFOp.find _x :: ops => by
      simpa [runOpsSpec] using runOpsSpec_samePartition h ops
  | UFOp.union x y :: ops => by
      exact runOpsSpec_samePartition
        (samePartition_unionSpec h x y) ops

end State

namespace RepresentationBackend

variable {Rep : Type}

/--
Run a mixed sequence against a representation-backed backend.

`find` outputs are kept in an aligned list.  The generic refinement theorem
below states final partition refinement and output-list length; it deliberately
does not claim raw representative-name equality against `State.runOpsSpec`.
-/
def runOpsCosted (backend : RepresentationBackend Rep) :
    Rep -> List UFOp -> Costed (Rep × List (Option Nat))
  | rep, [] => Costed.pure (rep, [])
  | rep, UFOp.find x :: ops =>
      Costed.bind (backend.findCosted rep x)
        (fun result =>
          Costed.map
            (fun tail => (tail.1, result.2 :: tail.2))
            (runOpsCosted backend result.1 ops))
  | rep, UFOp.union x y :: ops =>
      Costed.bind (backend.unionCosted rep x y)
        (fun rep' =>
          Costed.map
            (fun tail => (tail.1, none :: tail.2))
            (runOpsCosted backend rep' ops))

@[simp] theorem runOpsCosted_nil
    (backend : RepresentationBackend Rep) (rep : Rep) :
    backend.runOpsCosted rep [] = Costed.pure (rep, []) := by
  rfl

@[simp] theorem runOpsCosted_find_cons
    (backend : RepresentationBackend Rep) (rep : Rep) (x : Nat)
    (ops : List UFOp) :
    backend.runOpsCosted rep (UFOp.find x :: ops) =
      Costed.bind (backend.findCosted rep x)
        (fun result =>
          Costed.map
            (fun tail => (tail.1, result.2 :: tail.2))
            (backend.runOpsCosted result.1 ops)) := by
  rfl

@[simp] theorem runOpsCosted_union_cons
    (backend : RepresentationBackend Rep) (rep : Rep) (x y : Nat)
    (ops : List UFOp) :
    backend.runOpsCosted rep (UFOp.union x y :: ops) =
      Costed.bind (backend.unionCosted rep x y)
        (fun rep' =>
          Costed.map
            (fun tail => (tail.1, none :: tail.2))
            (backend.runOpsCosted rep' ops)) := by
  rfl

theorem runOpsCosted_outputs_length
    (backend : RepresentationBackend Rep) :
    forall (rep : Rep) (ops : List UFOp),
      (backend.runOpsCosted rep ops).erase.2.length = ops.length
  | rep, [] => by
      rfl
  | rep, UFOp.find x :: ops => by
      have htail :=
        runOpsCosted_outputs_length backend
          (backend.findCosted rep x).erase.1 ops
      simp [runOpsCosted, htail]
  | rep, UFOp.union x y :: ops => by
      have htail :=
        runOpsCosted_outputs_length backend
          (backend.unionCosted rep x y).erase ops
      simp [runOpsCosted, htail]

theorem runOpsCosted_refinement_profile
    (backend : RepresentationBackend Rep) :
    forall (rep : Rep) (ops : List UFOp),
      (backend.runOpsCosted rep ops).erase.2.length = ops.length /\
        State.SamePartition
          (backend.abstractState (backend.runOpsCosted rep ops).erase.1)
          ((backend.abstractState rep).runOpsSpec ops).1
  | rep, [] => by
      constructor
      · rfl
      · simpa [runOpsCosted, State.runOpsSpec] using
          State.samePartition_refl (backend.abstractState rep)
  | rep, UFOp.find x :: ops => by
      let step := backend.findCosted rep x
      rcases runOpsCosted_refinement_profile backend step.erase.1 ops with
        ⟨hlen, htail⟩
      have hstep :
          State.SamePartition
            (backend.abstractState step.erase.1)
            (backend.abstractState rep) := by
        simpa [step] using backend.find_refines rep x
      have hspec :
          State.SamePartition
            ((backend.abstractState step.erase.1).runOpsSpec ops).1
            ((backend.abstractState rep).runOpsSpec ops).1 :=
        State.runOpsSpec_samePartition hstep ops
      constructor
      · simp [runOpsCosted, step, hlen]
      · simpa [runOpsCosted, State.runOpsSpec, step] using
          State.samePartition_trans htail hspec
  | rep, UFOp.union x y :: ops => by
      let step := backend.unionCosted rep x y
      rcases runOpsCosted_refinement_profile backend step.erase ops with
        ⟨hlen, htail⟩
      have hstep :
          State.SamePartition
            (backend.abstractState step.erase)
            ((backend.abstractState rep).unionSpec x y) := by
        simpa [step] using backend.union_refines rep x y
      have hspec :
          State.SamePartition
            ((backend.abstractState step.erase).runOpsSpec ops).1
            (((backend.abstractState rep).unionSpec x y).runOpsSpec ops).1 :=
        State.runOpsSpec_samePartition hstep ops
      constructor
      · simp [runOpsCosted, step, hlen]
      · simpa [runOpsCosted, State.runOpsSpec, step] using
          State.samePartition_trans htail hspec

end RepresentationBackend

namespace RepresentationAmortizedBackend

variable {Rep : Type}
variable {potential : Rep -> Nat}
variable {findCredit : Rep -> Nat -> Nat}
variable {unionCredit : Rep -> Nat -> Nat -> Nat}

/-- Sum of the one-step credits actually supplied along a mixed run. -/
def runOpsCredit
    (backend :
      RepresentationAmortizedBackend Rep potential findCredit unionCredit) :
    Rep -> List UFOp -> Nat
  | _rep, [] => 0
  | rep, UFOp.find x :: ops =>
      findCredit rep x +
        runOpsCredit backend (backend.findCosted rep x).erase.1 ops
  | rep, UFOp.union x y :: ops =>
      unionCredit rep x y +
        runOpsCredit backend (backend.unionCosted rep x y).erase ops

/--
Generic sequence telescope for representation amortization.

This is intentionally not an inverse-Ackermann theorem: it says that local
one-step bounds compose to the sum of the credits supplied along the run.  A
future Tarjan proof must separately bound this credit sum by an alpha-shaped
expression.
-/
theorem runOpsCosted_amortized
    (backend :
      RepresentationAmortizedBackend Rep potential findCredit unionCredit) :
    forall (rep : Rep) (ops : List UFOp),
      Amortized.CostedBound
        (backend.toRepresentationBackend.runOpsCosted rep ops)
        (potential rep)
        (potential (backend.toRepresentationBackend.runOpsCosted rep ops).erase.1)
        (backend.runOpsCredit rep ops)
  | rep, [] => by
      simpa [RepresentationBackend.runOpsCosted, runOpsCredit] using
        Amortized.costed_pure (rep, ([] : List (Option Nat))) (potential rep)
  | rep, UFOp.find x :: ops => by
      let step := backend.findCosted rep x
      have hstep :
          Amortized.CostedBound step
            (potential rep)
            (potential step.erase.1)
            (findCredit rep x) := by
        simpa [step] using backend.find_amortized rep x
      have htail :=
        runOpsCosted_amortized backend step.erase.1 ops
      have htailMap :
          Amortized.CostedBound
            (Costed.map
              (fun tail => (tail.1, step.erase.2 :: tail.2))
              (backend.toRepresentationBackend.runOpsCosted step.erase.1 ops))
            (potential step.erase.1)
            (potential
              (Costed.map
                (fun tail => (tail.1, step.erase.2 :: tail.2))
                (backend.toRepresentationBackend.runOpsCosted
                  step.erase.1 ops)).erase.1)
            (backend.runOpsCredit step.erase.1 ops) := by
        simpa using
          Amortized.costed_map
            (fun tail => (tail.1, step.erase.2 :: tail.2))
            htail
      simpa [RepresentationBackend.runOpsCosted, runOpsCredit, step] using
        Amortized.costed_bind hstep htailMap
  | rep, UFOp.union x y :: ops => by
      let step := backend.unionCosted rep x y
      have hstep :
          Amortized.CostedBound step
            (potential rep)
            (potential step.erase)
            (unionCredit rep x y) := by
        simpa [step] using backend.union_amortized rep x y
      have htail :=
        runOpsCosted_amortized backend step.erase ops
      have htailMap :
          Amortized.CostedBound
            (Costed.map
              (fun tail => (tail.1, none :: tail.2))
              (backend.toRepresentationBackend.runOpsCosted step.erase ops))
            (potential step.erase)
            (potential
              (Costed.map
                (fun tail => (tail.1, none :: tail.2))
                (backend.toRepresentationBackend.runOpsCosted
                  step.erase ops)).erase.1)
            (backend.runOpsCredit step.erase ops) := by
        simpa using
          Amortized.costed_map
            (fun tail => (tail.1, none :: tail.2))
            htail
      simpa [RepresentationBackend.runOpsCosted, runOpsCredit, step] using
        Amortized.costed_bind hstep htailMap

end RepresentationAmortizedBackend

namespace Forest
namespace ParentForest
namespace NoCompressionRankedMassBackendState

/--
Classical-operation-style union: charge the two representative searches, then
perform the rank-guided link/update.  The existing `unionCosted` remains the
root-link-style one-tick checkpoint; this wrapper is the honest public union
operation shape used by future sequence bounds.
-/
def chargedUnionCosted
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    Costed NoCompressionRankedMassBackendState :=
  Costed.bind (backend.fullCompressFindCosted x)
    (fun xResult =>
      Costed.bind (xResult.1.fullCompressFindCosted y)
        (fun yResult => yResult.1.unionCosted x y))

theorem chargedUnionCosted_cost
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.chargedUnionCosted x y).cost =
      (backend.fullCompressFindCosted x).cost +
        (((backend.fullCompressFindCosted x).erase.1).fullCompressFindCosted y).cost +
          1 := by
  simp [chargedUnionCosted, Costed.erase, Nat.add_assoc]

theorem chargedUnionCosted_rank_le
    (backend : NoCompressionRankedMassBackendState) (x y i : Nat) :
    backend.state.rank i <=
      ((backend.chargedUnionCosted x y).erase).state.rank i := by
  let afterX := (backend.fullCompressFindCosted x).erase.1
  let afterY := (afterX.fullCompressFindCosted y).erase.1
  have hx :
      afterX.state.rank = backend.state.rank := by
    simpa [afterX] using backend.fullCompressFindCosted_rank_eq x
  have hy :
      afterY.state.rank = afterX.state.rank := by
    simpa [afterY] using afterX.fullCompressFindCosted_rank_eq y
  have hstep :
      afterY.state.rank i <=
        ((afterY.unionCosted x y).erase).state.rank i :=
    afterY.unionCosted_rank_le x y i
  calc
    backend.state.rank i = afterX.state.rank i := by
      exact (congrFun hx i).symm
    _ = afterY.state.rank i := by
      exact (congrFun hy i).symm
    _ <= ((backend.chargedUnionCosted x y).erase).state.rank i := by
      simpa [chargedUnionCosted, afterX, afterY, Costed.erase] using hstep

theorem chargedUnionCosted_refinement_profile
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    State.SamePartition
      (abstractState (backend.chargedUnionCosted x y).erase)
      (backend.abstractState.unionSpec x y) := by
  let afterX := (backend.fullCompressFindCosted x).erase.1
  let afterY := (afterX.fullCompressFindCosted y).erase.1
  have hx :
      State.SamePartition (abstractState afterX) backend.abstractState := by
    simpa [afterX] using
      (backend.fullCompressFindCosted_refinement_profile x).2.2.2
  have hy :
      State.SamePartition (abstractState afterY) (abstractState afterX) := by
    simpa [afterY] using
      (afterX.fullCompressFindCosted_refinement_profile y).2.2.2
  have hbefore :
      State.SamePartition (abstractState afterY) backend.abstractState :=
    State.samePartition_trans hy hx
  have hstep :
      State.SamePartition
        (abstractState (afterY.unionCosted x y).erase)
        ((abstractState afterY).unionSpec x y) :=
    (afterY.unionCosted_refinement_profile x y).2
  have hspec :
      State.SamePartition
        ((abstractState afterY).unionSpec x y)
        (backend.abstractState.unionSpec x y) :=
    State.samePartition_unionSpec hbefore x y
  simpa [chargedUnionCosted, afterX, afterY] using
    State.samePartition_trans hstep hspec

/--
Credit for charged public union under the level-index potential.

The credit mirrors the implementation: a compressed `find x`, a compressed
`find y` in the state produced by the first find, and finally the rank-guided
root link in the state produced by both finds.
-/
def chargedTarjanLevelIndexUnionCredit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) : Nat :=
  backend.tarjanLevelIndexFindCredit x +
    let afterX := (backend.fullCompressFindCosted x).erase.1
    afterX.tarjanLevelIndexFindCredit y +
      let afterY := (afterX.fullCompressFindCosted y).erase.1
      afterY.tarjanLevelIndexDeltaUnionCredit x y

theorem chargedUnionCosted_cost_add_tarjanLevelIndexPotential_le_credit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.chargedUnionCosted x y).cost +
        tarjanLevelIndexPotential (backend.chargedUnionCosted x y).erase <=
      backend.chargedTarjanLevelIndexUnionCredit x y +
        tarjanLevelIndexPotential backend := by
  let afterX := (backend.fullCompressFindCosted x).erase.1
  let afterY := (afterX.fullCompressFindCosted y).erase.1
  have hx :
      (backend.fullCompressFindCosted x).cost +
          tarjanLevelIndexPotential afterX <=
        backend.tarjanLevelIndexFindCredit x +
          tarjanLevelIndexPotential backend := by
    simpa [afterX] using
      backend.fullCompressFindCosted_cost_add_tarjanLevelIndexPotential_le_tarjanLevelIndexFindCredit
        x
  have hy :
      (afterX.fullCompressFindCosted y).cost +
          tarjanLevelIndexPotential afterY <=
        afterX.tarjanLevelIndexFindCredit y +
          tarjanLevelIndexPotential afterX := by
    simpa [afterY] using
      afterX.fullCompressFindCosted_cost_add_tarjanLevelIndexPotential_le_tarjanLevelIndexFindCredit
        y
  have hlink :
      (afterY.unionCosted x y).cost +
          tarjanLevelIndexPotential (afterY.unionCosted x y).erase <=
        afterY.tarjanLevelIndexDeltaUnionCredit x y +
          tarjanLevelIndexPotential afterY := by
    simpa using
      afterY.unionCosted_cost_add_tarjanLevelIndexPotential_le_tarjanLevelIndexDeltaUnionCredit
        x y
  have hcost :
      (backend.chargedUnionCosted x y).cost =
        (backend.fullCompressFindCosted x).cost +
          (afterX.fullCompressFindCosted y).cost +
            (afterY.unionCosted x y).cost := by
    simp [chargedUnionCosted, afterX, afterY, Costed.erase, Nat.add_assoc]
  have herase :
      (backend.chargedUnionCosted x y).erase =
        (afterY.unionCosted x y).erase := by
    simp [chargedUnionCosted, afterX, afterY, Costed.erase]
  rw [hcost, herase]
  change
    (backend.fullCompressFindCosted x).cost +
          (afterX.fullCompressFindCosted y).cost +
            (afterY.unionCosted x y).cost +
        tarjanLevelIndexPotential (afterY.unionCosted x y).erase <=
      (backend.tarjanLevelIndexFindCredit x +
          (afterX.tarjanLevelIndexFindCredit y +
            afterY.tarjanLevelIndexDeltaUnionCredit x y)) +
        tarjanLevelIndexPotential backend
  omega

/-- Mixed full-compression `find` and rank-guided `union` runner. -/
def runFullCompressionOpsCosted
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp) :
    Costed (NoCompressionRankedMassBackendState × List (Option Nat)) :=
  fullCompressionRepresentationBackend.runOpsCosted backend ops

theorem runFullCompressionOpsCosted_refinement_profile
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp) :
    (backend.runFullCompressionOpsCosted ops).erase.2.length = ops.length /\
      State.SamePartition
        (abstractState (backend.runFullCompressionOpsCosted ops).erase.1)
        ((backend.abstractState.runOpsSpec ops).1) := by
  simpa [runFullCompressionOpsCosted] using
    fullCompressionRepresentationBackend.runOpsCosted_refinement_profile
      backend ops

def fullCompressionTarjanLevelIndexRunCredit
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp) : Nat :=
  fullCompressionTarjanLevelIndexAmortizedBackend.runOpsCredit backend ops

theorem runFullCompressionTarjanLevelIndexAmortized_profile
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp) :
    Amortized.CostedBound
      (backend.runFullCompressionOpsCosted ops)
      (tarjanLevelIndexPotential backend)
      (tarjanLevelIndexPotential
        (backend.runFullCompressionOpsCosted ops).erase.1)
      (backend.fullCompressionTarjanLevelIndexRunCredit ops) := by
  simpa [runFullCompressionOpsCosted,
    fullCompressionTarjanLevelIndexRunCredit] using
    fullCompressionTarjanLevelIndexAmortizedBackend.runOpsCosted_amortized
      backend ops

/--
Representation backend whose public `union` charges the two compressed finds
before the final rank-guided link.  This is the sequence-facing API shape for
classical union-find operation costs.
-/
def chargedFullCompressionRepresentationBackend :
    RepresentationBackend NoCompressionRankedMassBackendState where
  abstractState := abstractState
  findCosted := fun backend x => backend.fullCompressFindCosted x
  unionCosted := fun backend x y => backend.chargedUnionCosted x y
  find_exact := by
    intro backend x
    exact (backend.fullCompressFindCosted_refinement_profile x).2.1
  find_refines := by
    intro backend x
    exact (backend.fullCompressFindCosted_refinement_profile x).2.2.2
  union_refines := by
    intro backend x y
    exact backend.chargedUnionCosted_refinement_profile x y

def runChargedFullCompressionOpsCosted
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp) :
    Costed (NoCompressionRankedMassBackendState × List (Option Nat)) :=
  chargedFullCompressionRepresentationBackend.runOpsCosted backend ops

theorem runChargedFullCompressionOpsCosted_refinement_profile
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp) :
    (backend.runChargedFullCompressionOpsCosted ops).erase.2.length =
        ops.length /\
      State.SamePartition
        (abstractState (backend.runChargedFullCompressionOpsCosted ops).erase.1)
        ((backend.abstractState.runOpsSpec ops).1) := by
  simpa [runChargedFullCompressionOpsCosted] using
    chargedFullCompressionRepresentationBackend.runOpsCosted_refinement_profile
      backend ops

theorem runChargedFullCompressionOpsCosted_rank_le
    (backend : NoCompressionRankedMassBackendState) :
    forall (ops : List UFOp) (i : Nat),
      backend.state.rank i <=
        ((backend.runChargedFullCompressionOpsCosted ops).erase.1).state.rank i
  | [], i => by
      simp [runChargedFullCompressionOpsCosted,
        RepresentationBackend.runOpsCosted]
  | UFOp.find x :: ops, i => by
      let after := (backend.fullCompressFindCosted x).erase.1
      have hfind :
          after.state.rank = backend.state.rank := by
        simpa [after] using backend.fullCompressFindCosted_rank_eq x
      have htail :=
        runChargedFullCompressionOpsCosted_rank_le after ops i
      calc
        backend.state.rank i = after.state.rank i := by
          exact (congrFun hfind i).symm
        _ <=
            ((backend.runChargedFullCompressionOpsCosted
                (UFOp.find x :: ops)).erase.1).state.rank i := by
          simpa [runChargedFullCompressionOpsCosted,
            chargedFullCompressionRepresentationBackend,
            RepresentationBackend.runOpsCosted, after, Costed.erase] using
            htail
  | UFOp.union x y :: ops, i => by
      let after := (backend.chargedUnionCosted x y).erase
      have hstep : backend.state.rank i <= after.state.rank i := by
        simpa [after] using backend.chargedUnionCosted_rank_le x y i
      have htail :=
        runChargedFullCompressionOpsCosted_rank_le after ops i
      calc
        backend.state.rank i <= after.state.rank i := hstep
        _ <=
            ((backend.runChargedFullCompressionOpsCosted
                (UFOp.union x y :: ops)).erase.1).state.rank i := by
          simpa [runChargedFullCompressionOpsCosted,
            chargedFullCompressionRepresentationBackend,
            RepresentationBackend.runOpsCosted, after, Costed.erase] using
            htail

/--
Charged public-operation backend under the level-index potential.

This consumes the charged public `union` wrapper in the same potential method
as compressed `find`, instead of assigning the link-only one-tick union credit
to the public operation.
-/
def chargedFullCompressionTarjanLevelIndexAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      tarjanLevelIndexPotential
      tarjanLevelIndexFindCredit
      chargedTarjanLevelIndexUnionCredit where
  toRepresentationBackend := chargedFullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.fullCompressFindCosted x).cost +
        tarjanLevelIndexPotential
          ((backend.fullCompressFindCosted x).erase.1) <=
      backend.tarjanLevelIndexFindCredit x +
        tarjanLevelIndexPotential backend
    exact
      backend.fullCompressFindCosted_cost_add_tarjanLevelIndexPotential_le_tarjanLevelIndexFindCredit
        x
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    exact
      backend.chargedUnionCosted_cost_add_tarjanLevelIndexPotential_le_credit
        x y

def chargedFullCompressionTarjanLevelIndexRunCredit
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp) : Nat :=
  chargedFullCompressionTarjanLevelIndexAmortizedBackend.runOpsCredit
    backend ops

theorem runChargedFullCompressionTarjanLevelIndexAmortized_profile
    (backend : NoCompressionRankedMassBackendState) (ops : List UFOp) :
    Amortized.CostedBound
      (backend.runChargedFullCompressionOpsCosted ops)
      (tarjanLevelIndexPotential backend)
      (tarjanLevelIndexPotential
        (backend.runChargedFullCompressionOpsCosted ops).erase.1)
      (backend.chargedFullCompressionTarjanLevelIndexRunCredit ops) := by
  simpa [runChargedFullCompressionOpsCosted,
    chargedFullCompressionTarjanLevelIndexRunCredit] using
    chargedFullCompressionTarjanLevelIndexAmortizedBackend.runOpsCosted_amortized
      backend ops

end NoCompressionRankedMassBackendState
end ParentForest
end Forest

end UnionFind

end RMQ
