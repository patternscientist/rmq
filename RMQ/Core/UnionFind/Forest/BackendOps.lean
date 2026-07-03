import RMQ.Core.UnionFind.Forest.NoCompression

namespace RMQ

namespace UnionFind

namespace Forest

namespace ParentForest

/--
Invariant-carrying representation state for the no-compression union-by-rank
forest backend.

This is deliberately a representation-state adapter rather than an instance of
the abstract `UnionFind.Backend`: the executable state carries parent pointers,
proof ranks, and root masses, while `abstractState` exposes the induced
partition boundary.
-/
structure NoCompressionRankedMassBackendState where
  state : NoCompressionRankedMassForest
  inv : state.forest.RankPowerMassInvariant state.rank state.mass

namespace NoCompressionRankedMassBackendState

def abstractState (backend : NoCompressionRankedMassBackendState) : State :=
  backend.state.forest.toState backend.inv.toInvariant

/-- Concrete backend state with singleton components. -/
def identity (n : Nat) : NoCompressionRankedMassBackendState where
  state := NoCompressionRankedMassForest.identity n
  inv := NoCompressionRankedMassForest.identity_rankPowerMassInvariant n

def findCosted (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    Costed (NoCompressionRankedMassBackendState × Option Nat) :=
  Costed.tickValue 1 (backend, backend.state.forest.findRoot? x)

def compressedStateOfRoot
    (backend : NoCompressionRankedMassBackendState)
    (x root : Nat)
    (hfind : backend.state.forest.findRoot? x = some root) :
    NoCompressionRankedMassBackendState where
  state :=
    { forest := backend.state.forest.compressNode x root
      rank := backend.state.rank
      mass := backend.state.mass }
  inv :=
    backend.state.forest.compressNode_rankPowerMassInvariant
      backend.state.rank backend.state.mass backend.inv
      (backend.state.forest.valid_of_findRoot?_eq_some hfind)
      (backend.state.forest.findRoot?_some_valid
        backend.inv.toInvariant hfind)
      (backend.state.forest.findRoot?_some_root
        backend.inv.toInvariant hfind)
      (fun hne =>
        backend.state.forest.findRoot?_rank_lt_of_ne
          backend.state.rank backend.inv.toRankInvariant hfind hne)

def compressedStateOrSelf
    (backend : NoCompressionRankedMassBackendState) (x root : Nat) :
    NoCompressionRankedMassBackendState :=
  if hfind : backend.state.forest.findRoot? x = some root then
    backend.compressedStateOfRoot x root hfind
  else
    backend

def compressFindResult
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    NoCompressionRankedMassBackendState × Option Nat :=
  match backend.state.forest.findRoot? x with
  | none => (backend, none)
  | some root => (backend.compressedStateOrSelf x root, some root)

@[simp] theorem compressFindResult_none
    (backend : NoCompressionRankedMassBackendState) (x : Nat)
    (hfind : backend.state.forest.findRoot? x = none) :
    backend.compressFindResult x = (backend, none) := by
  unfold compressFindResult
  rw [hfind]

@[simp] theorem compressFindResult_some
    (backend : NoCompressionRankedMassBackendState) (x root : Nat)
    (hfind : backend.state.forest.findRoot? x = some root) :
    backend.compressFindResult x =
      (backend.compressedStateOrSelf x root, some root) := by
  unfold compressFindResult
  rw [hfind]

def compressFindCosted
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    Costed (NoCompressionRankedMassBackendState × Option Nat) :=
  Costed.tickValue 1 (backend.compressFindResult x)

def compressPathFindFuelCosted
    (backend : NoCompressionRankedMassBackendState) :
    Nat -> Nat -> Costed (NoCompressionRankedMassBackendState × Option Nat)
  | 0, x => backend.compressFindCosted x
  | fuel + 1, x =>
      match backend.state.forest.parent? x with
      | none => backend.compressFindCosted x
      | some parent =>
          if parent = x then
            backend.compressFindCosted x
          else
            Costed.bind (backend.compressPathFindFuelCosted fuel parent)
              (fun result => result.1.compressFindCosted x)

def fullCompressFindCosted
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    Costed (NoCompressionRankedMassBackendState × Option Nat) :=
  backend.compressPathFindFuelCosted backend.state.forest.maxSearchFuel x

/-- Parent-chain trace followed by `compressPathFindFuelCosted` at the same fuel. -/
def compressPathFindFuelTrace
    (backend : NoCompressionRankedMassBackendState) :
    Nat -> Nat -> List Nat
  | 0, x => [x]
  | fuel + 1, x =>
      match backend.state.forest.parent? x with
      | none => [x]
      | some parent =>
          if parent = x then
            [x]
          else
            x :: backend.compressPathFindFuelTrace fuel parent

/-- Full-compression trace with the backend's standard search fuel. -/
def fullCompressFindTrace
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    List Nat :=
  backend.compressPathFindFuelTrace backend.state.forest.maxSearchFuel x

theorem compressPathFindFuelTrace_eq_singleton_of_root
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {root : Nat},
      backend.state.forest.IsRoot root ->
        backend.compressPathFindFuelTrace fuel root = [root]
  | 0, root, _hroot => by
      simp [compressPathFindFuelTrace]
  | fuel + 1, root, hroot => by
      have hparent : backend.state.forest.parent? root = some root := hroot
      simp [compressPathFindFuelTrace, hparent]

def unionResult
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    NoCompressionRankedMassBackendState where
  state := (backend.state.unionCosted x y).erase
  inv := (backend.state.unionCosted_rankPowerMassInvariant_profile
    x y backend.inv).1

def unionCosted (backend : NoCompressionRankedMassBackendState)
    (x y : Nat) : Costed NoCompressionRankedMassBackendState :=
  Costed.tickValue 1 (backend.unionResult x y)

/-- Execute a finite list of union requests while carrying the invariant. -/
def unionManyCosted (backend : NoCompressionRankedMassBackendState) :
    List (Nat × Nat) -> Costed NoCompressionRankedMassBackendState
  | [] => Costed.pure backend
  | (x, y) :: ops =>
      Costed.bind (backend.unionCosted x y)
        (fun backend' => backend'.unionManyCosted ops)

@[simp] theorem findCosted_cost
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.findCosted x).cost = 1 := by
  rfl

@[simp] theorem compressFindCosted_cost
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.compressFindCosted x).cost = 1 := by
  rfl

theorem compressPathFindFuelCosted_cost_le
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel x : Nat),
      (backend.compressPathFindFuelCosted fuel x).cost <= fuel + 1
  | 0, x => by
      simp [compressPathFindFuelCosted]
  | fuel + 1, x => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simp [compressPathFindFuelCosted, hparent]
      | some parent =>
          by_cases hsame : parent = x
          · simp [compressPathFindFuelCosted, hparent, hsame]
          · have htail :=
              compressPathFindFuelCosted_cost_le backend fuel parent
            simp [compressPathFindFuelCosted, hparent, hsame]
            omega

theorem fullCompressFindCosted_cost_le
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost <=
      backend.state.forest.maxSearchFuel + 1 := by
  simpa [fullCompressFindCosted] using
    backend.compressPathFindFuelCosted_cost_le
      backend.state.forest.maxSearchFuel x

theorem compressPathFindFuelTrace_length_le
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel x : Nat),
      (backend.compressPathFindFuelTrace fuel x).length <= fuel + 1
  | 0, x => by
      simp [compressPathFindFuelTrace]
  | fuel + 1, x => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simp [compressPathFindFuelTrace, hparent]
      | some parent =>
          by_cases hsame : parent = x
          · simp [compressPathFindFuelTrace, hparent, hsame]
          · have htail :=
              compressPathFindFuelTrace_length_le backend fuel parent
            simp [compressPathFindFuelTrace, hparent, hsame]
            omega

theorem fullCompressFindTrace_length_le
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindTrace x).length <=
      backend.state.forest.maxSearchFuel + 1 := by
  simpa [fullCompressFindTrace] using
    backend.compressPathFindFuelTrace_length_le
      backend.state.forest.maxSearchFuel x

theorem compressPathFindFuelCosted_cost_eq_trace_length
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel x : Nat),
      (backend.compressPathFindFuelCosted fuel x).cost =
        (backend.compressPathFindFuelTrace fuel x).length
  | 0, x => by
      simp [compressPathFindFuelCosted, compressPathFindFuelTrace]
  | fuel + 1, x => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simp [compressPathFindFuelCosted, compressPathFindFuelTrace, hparent]
      | some parent =>
          by_cases hsame : parent = x
          · simp [compressPathFindFuelCosted, compressPathFindFuelTrace,
              hparent, hsame]
          · have htail :=
              compressPathFindFuelCosted_cost_eq_trace_length
                backend fuel parent
            simp [compressPathFindFuelCosted, compressPathFindFuelTrace,
              hparent, hsame, htail]

theorem fullCompressFindCosted_cost_eq_trace_length
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost =
      (backend.fullCompressFindTrace x).length := by
  simpa [fullCompressFindCosted, fullCompressFindTrace] using
    backend.compressPathFindFuelCosted_cost_eq_trace_length
      backend.state.forest.maxSearchFuel x

@[simp] theorem unionCosted_cost
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.unionCosted x y).cost = 1 := by
  rfl

theorem unionCosted_rank_le
    (backend : NoCompressionRankedMassBackendState) (x y i : Nat) :
    backend.state.rank i <=
      ((backend.unionCosted x y).erase).state.rank i := by
  unfold unionCosted unionResult
  simp [NoCompressionRankedMassForest.unionCosted]
  exact
    backend.state.forest.rank_le_rankAfterUnionByRank
      backend.state.rank x y i

@[simp] theorem unionManyCosted_nil
    (backend : NoCompressionRankedMassBackendState) :
    backend.unionManyCosted [] = Costed.pure backend := by
  rfl

@[simp] theorem unionManyCosted_cons
    (backend : NoCompressionRankedMassBackendState) (x y : Nat)
    (ops : List (Nat × Nat)) :
    backend.unionManyCosted ((x, y) :: ops) =
      Costed.bind (backend.unionCosted x y)
        (fun backend' => backend'.unionManyCosted ops) := by
  rfl

theorem findCosted_refinement_profile
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.findCosted x).cost = 1 /\
      (backend.findCosted x).erase.2 =
        backend.abstractState.find? x /\
      State.SamePartition
        (abstractState (backend.findCosted x).erase.1)
        backend.abstractState := by
  constructor
  · rfl
  · constructor
    · simpa [findCosted, abstractState] using
        backend.state.forest.findRoot?_refines_State_find?
          backend.inv.toInvariant x
    · simpa [findCosted, abstractState] using
        State.samePartition_refl backend.abstractState

theorem compressedStateOfRoot_refinement_profile
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    State.SamePartition
      (abstractState (backend.compressedStateOfRoot x root hfind))
      backend.abstractState := by
  have hprofile :=
    backend.state.forest.compressNode_rootMassInvariant_refinement_profile
      backend.state.rank backend.state.mass backend.inv.toRootMassInvariant hfind
      (fun hne =>
        backend.state.forest.findRoot?_rank_lt_of_ne
          backend.state.rank backend.inv.toRankInvariant hfind hne)
  simpa [compressedStateOfRoot, abstractState] using hprofile.2

theorem compressedStateOrSelf_refinement_profile
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    State.SamePartition
      (abstractState (backend.compressedStateOrSelf x root))
      backend.abstractState := by
  simpa [compressedStateOrSelf, hfind] using
    backend.compressedStateOfRoot_refinement_profile hfind

theorem compressFindCosted_parent?_eq_root_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    ((backend.compressFindCosted x).erase.1).state.forest.parent? x =
      some root := by
  have hx : backend.state.forest.valid x :=
    backend.state.forest.valid_of_findRoot?_eq_some hfind
  have hparent :
      (backend.state.forest.compressNode x root).parent? x = some root :=
    backend.state.forest.compressNode_parent?_eq_root hx
  simpa [compressFindCosted,
    backend.compressFindResult_some x root hfind,
    compressedStateOrSelf, hfind, compressedStateOfRoot] using hparent

theorem compressFindCosted_parent?_eq_old_of_ne
    (backend : NoCompressionRankedMassBackendState)
    {x y parent : Nat} (hne : y ≠ x)
    (hparent : backend.state.forest.parent? y = some parent) :
    ((backend.compressFindCosted x).erase.1).state.forest.parent? y =
      some parent := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp [compressFindCosted,
        backend.compressFindResult_none x hfind, hparent]
  | some root =>
      have hy : backend.state.forest.valid y :=
        backend.state.forest.valid_of_parent?_eq_some hparent
      have hnew :
          (backend.state.forest.compressNode x root).parent? y =
            some parent :=
        backend.state.forest.compressNode_parent?_eq_old_of_ne
          hy hne hparent
      simpa [compressFindCosted,
        backend.compressFindResult_some x root hfind,
        compressedStateOrSelf, hfind, compressedStateOfRoot] using hnew

theorem compressedStateOfRoot_findRoot?_eq
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) (i : Nat) :
    (backend.compressedStateOfRoot x root hfind).state.forest.findRoot? i =
      backend.state.forest.findRoot? i := by
  have hlink : backend.state.forest.LinkableInvariant :=
    backend.state.forest.rankInvariant_linkable
      backend.state.rank backend.inv.toRankInvariant
  simpa [compressedStateOfRoot] using
    backend.state.forest.compressNode_findRoot?_eq_of_findRoot?
      hlink hfind i

theorem compressedStateOrSelf_findRoot?_eq
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) (i : Nat) :
    (backend.compressedStateOrSelf x root).state.forest.findRoot? i =
      backend.state.forest.findRoot? i := by
  simpa [compressedStateOrSelf, hfind] using
    backend.compressedStateOfRoot_findRoot?_eq hfind i

theorem compressFindCosted_findRoot?_eq
    (backend : NoCompressionRankedMassBackendState) (x i : Nat) :
    ((backend.compressFindCosted x).erase.1).state.forest.findRoot? i =
      backend.state.forest.findRoot? i := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp [compressFindCosted, backend.compressFindResult_none x hfind]
  | some root =>
      simpa [compressFindCosted,
        backend.compressFindResult_some x root hfind] using
        backend.compressedStateOrSelf_findRoot?_eq hfind i

theorem compressFindCosted_forest_size_eq
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    ((backend.compressFindCosted x).erase.1).state.forest.size =
      backend.state.forest.size := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp [compressFindCosted, backend.compressFindResult_none x hfind]
  | some root =>
      simp [compressFindCosted,
        compressedStateOrSelf, hfind, compressedStateOfRoot]

theorem compressFindCosted_rank_eq
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    ((backend.compressFindCosted x).erase.1).state.rank =
      backend.state.rank := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp [compressFindCosted, backend.compressFindResult_none x hfind]
  | some root =>
      simp [compressFindCosted,
        compressedStateOrSelf, hfind, compressedStateOfRoot]

theorem compressPathFindFuelCosted_findRoot?_eq
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel x i : Nat),
      ((backend.compressPathFindFuelCosted fuel x).erase.1).state.forest.findRoot? i =
        backend.state.forest.findRoot? i
  | 0, x, i => by
      simpa [compressPathFindFuelCosted] using
        backend.compressFindCosted_findRoot?_eq x i
  | fuel + 1, x, i => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simpa [compressPathFindFuelCosted, hparent] using
            backend.compressFindCosted_findRoot?_eq x i
      | some parent =>
          by_cases hsame : parent = x
          · simpa [compressPathFindFuelCosted, hparent, hsame] using
              backend.compressFindCosted_findRoot?_eq x i
          · let tail :=
              (backend.compressPathFindFuelCosted fuel parent).erase.1
            have htail :
                tail.state.forest.findRoot? i =
                  backend.state.forest.findRoot? i := by
              simpa [tail] using
                compressPathFindFuelCosted_findRoot?_eq
                  backend fuel parent i
            have hstep :
                ((tail.compressFindCosted x).erase.1).state.forest.findRoot?
                    i =
                  tail.state.forest.findRoot? i :=
              tail.compressFindCosted_findRoot?_eq x i
            simpa [compressPathFindFuelCosted, hparent, hsame, tail] using
              hstep.trans htail

theorem compressPathFindFuelCosted_rank_eq
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel x : Nat),
      ((backend.compressPathFindFuelCosted fuel x).erase.1).state.rank =
        backend.state.rank
  | 0, x => by
      simpa [compressPathFindFuelCosted] using
        backend.compressFindCosted_rank_eq x
  | fuel + 1, x => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simpa [compressPathFindFuelCosted, hparent] using
            backend.compressFindCosted_rank_eq x
      | some parent =>
          by_cases hsame : parent = x
          · simpa [compressPathFindFuelCosted, hparent, hsame] using
              backend.compressFindCosted_rank_eq x
          · let tail :=
              (backend.compressPathFindFuelCosted fuel parent).erase.1
            have htail :
                tail.state.rank = backend.state.rank := by
              simpa [tail] using
                compressPathFindFuelCosted_rank_eq
                  backend fuel parent
            have hstep :
                ((tail.compressFindCosted x).erase.1).state.rank =
                  tail.state.rank :=
              tail.compressFindCosted_rank_eq x
            simpa [compressPathFindFuelCosted, hparent, hsame, tail] using
              hstep.trans htail

theorem compressPathFindFuelCosted_forest_size_eq
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel x : Nat),
      ((backend.compressPathFindFuelCosted fuel x).erase.1).state.forest.size =
        backend.state.forest.size
  | 0, x => by
      simpa [compressPathFindFuelCosted] using
        backend.compressFindCosted_forest_size_eq x
  | fuel + 1, x => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simpa [compressPathFindFuelCosted, hparent] using
            backend.compressFindCosted_forest_size_eq x
      | some parent =>
          by_cases hsame : parent = x
          · simpa [compressPathFindFuelCosted, hparent, hsame] using
              backend.compressFindCosted_forest_size_eq x
          · let tail :=
              (backend.compressPathFindFuelCosted fuel parent).erase.1
            have htail :
                tail.state.forest.size = backend.state.forest.size := by
              simpa [tail] using
                compressPathFindFuelCosted_forest_size_eq
                  backend fuel parent
            have hstep :
                ((tail.compressFindCosted x).erase.1).state.forest.size =
                  tail.state.forest.size :=
              tail.compressFindCosted_forest_size_eq x
            simpa [compressPathFindFuelCosted, hparent, hsame, tail] using
              hstep.trans htail

theorem fullCompressFindCosted_findRoot?_eq
    (backend : NoCompressionRankedMassBackendState) (x i : Nat) :
    ((backend.fullCompressFindCosted x).erase.1).state.forest.findRoot? i =
      backend.state.forest.findRoot? i := by
  simpa [fullCompressFindCosted] using
    backend.compressPathFindFuelCosted_findRoot?_eq
      backend.state.forest.maxSearchFuel x i

theorem fullCompressFindCosted_forest_size_eq
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    ((backend.fullCompressFindCosted x).erase.1).state.forest.size =
      backend.state.forest.size := by
  simpa [fullCompressFindCosted] using
    backend.compressPathFindFuelCosted_forest_size_eq
      backend.state.forest.maxSearchFuel x

theorem fullCompressFindCosted_rank_eq
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    ((backend.fullCompressFindCosted x).erase.1).state.rank =
      backend.state.rank := by
  simpa [fullCompressFindCosted] using
    backend.compressPathFindFuelCosted_rank_eq
      backend.state.forest.maxSearchFuel x

theorem compressFindCosted_refinement_profile
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.compressFindCosted x).cost = 1 /\
      (backend.compressFindCosted x).erase.2 =
        backend.abstractState.find? x /\
      State.SamePartition
        (abstractState (backend.compressFindCosted x).erase.1)
        backend.abstractState := by
  constructor
  · rfl
  · constructor
    · cases hfind : backend.state.forest.findRoot? x with
      | none =>
          have hstate :
              backend.abstractState.find? x = none := by
            rw [abstractState]
            rw [backend.state.forest.toState_find?_eq_findRoot?
              backend.inv.toInvariant x]
            exact hfind
          simp [compressFindCosted,
            backend.compressFindResult_none x hfind, hstate]
      | some root =>
          have hstate :
              backend.abstractState.find? x = some root := by
            rw [abstractState]
            rw [backend.state.forest.toState_find?_eq_findRoot?
              backend.inv.toInvariant x]
            exact hfind
          simp [compressFindCosted,
            backend.compressFindResult_some x root hfind, hstate]
    · cases hfind : backend.state.forest.findRoot? x with
      | none =>
          have hfirst :
              (backend.compressFindCosted x).erase.1 = backend := by
            simp [compressFindCosted,
              backend.compressFindResult_none x hfind]
          simpa [hfirst] using
            State.samePartition_refl backend.abstractState
      | some root =>
          simpa [compressFindCosted,
            backend.compressFindResult_some x root hfind] using
            backend.compressedStateOrSelf_refinement_profile hfind

theorem abstractState_find?_eq_of_findRoot?_eq
    {left right : NoCompressionRankedMassBackendState}
    (hfind : forall i,
      left.state.forest.findRoot? i = right.state.forest.findRoot? i)
    (i : Nat) :
    left.abstractState.find? i = right.abstractState.find? i := by
  rw [abstractState]
  rw [abstractState]
  rw [left.state.forest.toState_find?_eq_findRoot?
    left.inv.toInvariant i]
  rw [right.state.forest.toState_find?_eq_findRoot?
    right.inv.toInvariant i]
  exact hfind i

theorem samePartition_of_backend_findRoot?_eq
    {left right : NoCompressionRankedMassBackendState}
    (hfind : forall i,
      left.state.forest.findRoot? i = right.state.forest.findRoot? i) :
    State.SamePartition left.abstractState right.abstractState := by
  apply State.samePartition_of_find?_eq
  intro i
  exact abstractState_find?_eq_of_findRoot?_eq hfind i

theorem compressFindCosted_answer_eq_final_abstractState
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.compressFindCosted x).erase.2 =
      (abstractState (backend.compressFindCosted x).erase.1).find? x := by
  have hanswer :=
    (backend.compressFindCosted_refinement_profile x).2.1
  have hfindEq :
      forall i,
        ((backend.compressFindCosted x).erase.1).state.forest.findRoot? i =
          backend.state.forest.findRoot? i := by
    intro i
    exact backend.compressFindCosted_findRoot?_eq x i
  have habstract :
      (abstractState (backend.compressFindCosted x).erase.1).find? x =
        backend.abstractState.find? x :=
    abstractState_find?_eq_of_findRoot?_eq hfindEq x
  exact hanswer.trans habstract.symm

theorem compressPathFindFuelCosted_answer_eq_final_abstractState
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel x : Nat),
      (backend.compressPathFindFuelCosted fuel x).erase.2 =
        (abstractState (backend.compressPathFindFuelCosted fuel x).erase.1).find?
          x
  | 0, x => by
      simpa [compressPathFindFuelCosted] using
        backend.compressFindCosted_answer_eq_final_abstractState x
  | fuel + 1, x => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simpa [compressPathFindFuelCosted, hparent] using
            backend.compressFindCosted_answer_eq_final_abstractState x
      | some parent =>
          by_cases hsame : parent = x
          · simpa [compressPathFindFuelCosted, hparent, hsame] using
              backend.compressFindCosted_answer_eq_final_abstractState x
          · let tail :=
              (backend.compressPathFindFuelCosted fuel parent).erase.1
            have htailAnswer :
                (tail.compressFindCosted x).erase.2 =
                  (abstractState (tail.compressFindCosted x).erase.1).find?
                    x :=
              tail.compressFindCosted_answer_eq_final_abstractState x
            simpa [compressPathFindFuelCosted, hparent, hsame, tail] using
              htailAnswer

theorem fullCompressFindCosted_answer_eq_final_abstractState
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).erase.2 =
      (abstractState (backend.fullCompressFindCosted x).erase.1).find? x := by
  simpa [fullCompressFindCosted] using
    backend.compressPathFindFuelCosted_answer_eq_final_abstractState
      backend.state.forest.maxSearchFuel x

theorem findRoot?_parent_eq_of_parent?_ne
    (backend : NoCompressionRankedMassBackendState)
    {x parent root : Nat}
    (hparent : backend.state.forest.parent? x = some parent)
    (hne : parent ≠ x)
    (hfind : backend.state.forest.findRoot? x = some root) :
    backend.state.forest.findRoot? parent = some root := by
  have hx : backend.state.forest.valid x :=
    backend.state.forest.valid_of_findRoot?_eq_some hfind
  have hparentValid : backend.state.forest.valid parent :=
    backend.inv.toInvariant.parent_lt hparent
  have hfuel :
      backend.state.forest.findRootFuel?
          backend.state.forest.maxSearchFuel x =
        some root := by
    simpa [ParentForest.findRoot?, hx] using hfind
  have hparentFuel :
      backend.state.forest.findRootFuel?
          backend.state.forest.size parent =
        some root := by
    simpa [ParentForest.maxSearchFuel, ParentForest.findRootFuel?,
      hparent, hne] using hfuel
  have hparentFuelMore :
      backend.state.forest.findRootFuel?
          (backend.state.forest.size + 1) parent =
        some root :=
    backend.state.forest.findRootFuel?_succ_eq_some_of_eq_some
      hparentFuel
  simpa [ParentForest.findRoot?, ParentForest.maxSearchFuel,
    hparentValid] using hparentFuelMore

theorem rank_le_root_rank_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    backend.state.rank x <= backend.state.rank root := by
  by_cases hsame : x = root
  · subst hsame
    omega
  · have hlt :=
      backend.state.forest.findRoot?_rank_lt_of_ne
        backend.state.rank backend.inv.toRankInvariant hfind hsame
    omega

theorem compressPathFindFuelTrace_length_le_rank_gap_of_findRoot?
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root : Nat},
      backend.state.forest.findRoot? x = some root ->
      (backend.compressPathFindFuelTrace fuel x).length <=
        backend.state.rank root - backend.state.rank x + 1
  | 0, x, root, hfind => by
      simp [compressPathFindFuelTrace]
  | fuel + 1, x, root, hfind => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simp [compressPathFindFuelTrace, hparent]
      | some parent =>
          by_cases hsame : parent = x
          · simp [compressPathFindFuelTrace, hparent, hsame]
          · have hparentFind :
                backend.state.forest.findRoot? parent = some root :=
              backend.findRoot?_parent_eq_of_parent?_ne hparent hsame hfind
            have htail :=
              compressPathFindFuelTrace_length_le_rank_gap_of_findRoot?
                backend fuel hparentFind
            have hparentRank :
                backend.state.rank x < backend.state.rank parent :=
              backend.inv.toRankInvariant.parent_rank_lt hparent hsame
            have hparentLeRoot :
                backend.state.rank parent <= backend.state.rank root :=
              backend.rank_le_root_rank_of_findRoot? hparentFind
            simp [compressPathFindFuelTrace, hparent, hsame]
            omega

theorem fullCompressFindTrace_length_le_rank_gap_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    (backend.fullCompressFindTrace x).length <=
      backend.state.rank root - backend.state.rank x + 1 := by
  simpa [fullCompressFindTrace] using
    backend.compressPathFindFuelTrace_length_le_rank_gap_of_findRoot?
      backend.state.forest.maxSearchFuel hfind

theorem findRoot?_rank_lt_rootMass
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    backend.state.rank root < backend.state.mass root :=
  backend.inv.rank_lt_mass
    (backend.state.forest.findRoot?_some_valid
      backend.inv.toInvariant hfind)
    (backend.state.forest.findRoot?_some_root
      backend.inv.toInvariant hfind)

theorem findRoot?_root_rank_le_log2_mass
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    backend.state.rank root <= Nat.log2 (backend.state.mass root) :=
  backend.inv.rank_le_log2_mass
    (backend.state.forest.findRoot?_some_valid
      backend.inv.toInvariant hfind)
    (backend.state.forest.findRoot?_some_root
      backend.inv.toInvariant hfind)

theorem findRoot?_root_rank_le_log2_size
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    backend.state.rank root <= Nat.log2 backend.state.forest.size :=
  backend.inv.rank_le_log2_size
    (backend.state.forest.findRoot?_some_valid
      backend.inv.toInvariant hfind)
    (backend.state.forest.findRoot?_some_root
      backend.inv.toInvariant hfind)

theorem fullCompressFindTrace_length_le_rootMass_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    (backend.fullCompressFindTrace x).length <= backend.state.mass root := by
  have hgap :=
    backend.fullCompressFindTrace_length_le_rank_gap_of_findRoot? hfind
  have hmass := backend.findRoot?_rank_lt_rootMass hfind
  omega

theorem fullCompressFindTrace_length_le_log2_size_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    (backend.fullCompressFindTrace x).length <=
      Nat.log2 backend.state.forest.size + 1 := by
  have hgap :=
    backend.fullCompressFindTrace_length_le_rank_gap_of_findRoot? hfind
  have hroot :=
    backend.findRoot?_root_rank_le_log2_size hfind
  have hsub :
      backend.state.rank root - backend.state.rank x <=
        backend.state.rank root := Nat.sub_le _ _
  omega

theorem compressPathFindFuelCosted_parent?_eq_root_of_findRoot?
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root : Nat},
      backend.state.forest.findRoot? x = some root ->
      ((backend.compressPathFindFuelCosted fuel x).erase.1).state.forest.parent?
        x =
        some root
  | 0, x, root, hfind => by
      simpa [compressPathFindFuelCosted] using
        backend.compressFindCosted_parent?_eq_root_of_findRoot? hfind
  | fuel + 1, x, root, hfind => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simpa [compressPathFindFuelCosted, hparent] using
            backend.compressFindCosted_parent?_eq_root_of_findRoot? hfind
      | some parent =>
          by_cases hsame : parent = x
          · simpa [compressPathFindFuelCosted, hparent, hsame] using
              backend.compressFindCosted_parent?_eq_root_of_findRoot? hfind
          · let tail :=
              (backend.compressPathFindFuelCosted fuel parent).erase.1
            have htailFind :
                tail.state.forest.findRoot? x = some root := by
              rw [show tail.state.forest.findRoot? x =
                    backend.state.forest.findRoot? x by
                simpa [tail] using
                  backend.compressPathFindFuelCosted_findRoot?_eq
                    fuel parent x]
              exact hfind
            have htailParent :
                ((tail.compressFindCosted x).erase.1).state.forest.parent? x =
                  some root :=
              tail.compressFindCosted_parent?_eq_root_of_findRoot?
                htailFind
            simpa [compressPathFindFuelCosted, hparent, hsame, tail] using
              htailParent

theorem fullCompressFindCosted_parent?_eq_root_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    ((backend.fullCompressFindCosted x).erase.1).state.forest.parent? x =
      some root := by
  simpa [fullCompressFindCosted] using
    backend.compressPathFindFuelCosted_parent?_eq_root_of_findRoot?
      backend.state.forest.maxSearchFuel hfind

theorem compressPathFindFuelCosted_trace_parent?_eq_root_of_findRoot?
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root y : Nat},
      backend.state.forest.findRoot? x = some root ->
      y ∈ backend.compressPathFindFuelTrace fuel x ->
      ((backend.compressPathFindFuelCosted fuel x).erase.1).state.forest.parent?
        y =
        some root
  | 0, x, root, y, hfind, hmem => by
      have hyx : y = x := by
        simpa [compressPathFindFuelTrace] using hmem
      subst y
      simpa [compressPathFindFuelCosted] using
        backend.compressFindCosted_parent?_eq_root_of_findRoot? hfind
  | fuel + 1, x, root, y, hfind, hmem => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          have hyx : y = x := by
            simpa [compressPathFindFuelTrace, hparent] using hmem
          subst y
          simpa [compressPathFindFuelCosted, hparent] using
            backend.compressFindCosted_parent?_eq_root_of_findRoot? hfind
      | some parent =>
          by_cases hsame : parent = x
          · have hyx : y = x := by
              simpa [compressPathFindFuelTrace, hparent, hsame] using hmem
            subst y
            simpa [compressPathFindFuelCosted, hparent, hsame] using
              backend.compressFindCosted_parent?_eq_root_of_findRoot? hfind
          · have hmemCases :
                y = x ∨
                  y ∈ backend.compressPathFindFuelTrace fuel parent := by
              simpa [compressPathFindFuelTrace, hparent, hsame] using hmem
            let tail :=
              (backend.compressPathFindFuelCosted fuel parent).erase.1
            have htailFindX :
                tail.state.forest.findRoot? x = some root := by
              rw [show tail.state.forest.findRoot? x =
                    backend.state.forest.findRoot? x by
                simpa [tail] using
                  backend.compressPathFindFuelCosted_findRoot?_eq
                    fuel parent x]
              exact hfind
            rcases hmemCases with hyx | htailMem
            · subst y
              have htailParent :
                  ((tail.compressFindCosted x).erase.1).state.forest.parent?
                    x =
                    some root :=
                tail.compressFindCosted_parent?_eq_root_of_findRoot?
                  htailFindX
              simpa [compressPathFindFuelCosted, hparent, hsame, tail] using
                htailParent
            · by_cases hyx : y = x
              · subst y
                have htailParent :
                    ((tail.compressFindCosted x).erase.1).state.forest.parent?
                      x =
                      some root :=
                  tail.compressFindCosted_parent?_eq_root_of_findRoot?
                    htailFindX
                simpa [compressPathFindFuelCosted, hparent, hsame, tail] using
                  htailParent
              · have hparentFind :
                    backend.state.forest.findRoot? parent = some root :=
                  backend.findRoot?_parent_eq_of_parent?_ne
                    hparent hsame hfind
                have htailParentOld :
                    tail.state.forest.parent? y = some root := by
                  simpa [tail] using
                    compressPathFindFuelCosted_trace_parent?_eq_root_of_findRoot?
                      backend fuel hparentFind htailMem
                have htailParent :
                    ((tail.compressFindCosted x).erase.1).state.forest.parent?
                      y =
                      some root :=
                  tail.compressFindCosted_parent?_eq_old_of_ne
                    hyx htailParentOld
                simpa [compressPathFindFuelCosted, hparent, hsame, tail] using
                  htailParent

theorem fullCompressFindCosted_trace_parent?_eq_root_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root y : Nat}
    (hfind : backend.state.forest.findRoot? x = some root)
    (hmem : y ∈ backend.fullCompressFindTrace x) :
    ((backend.fullCompressFindCosted x).erase.1).state.forest.parent? y =
      some root := by
  simpa [fullCompressFindCosted, fullCompressFindTrace] using
    backend.compressPathFindFuelCosted_trace_parent?_eq_root_of_findRoot?
      backend.state.forest.maxSearchFuel hfind hmem

theorem compressPathFindFuelTrace_mem_findRoot?_eq_of_findRoot?
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root y : Nat},
      backend.state.forest.findRoot? x = some root ->
      y ∈ backend.compressPathFindFuelTrace fuel x ->
      backend.state.forest.findRoot? y = some root
  | 0, x, root, y, hfind, hmem => by
      have hyx : y = x := by
        simpa [compressPathFindFuelTrace] using hmem
      subst y
      exact hfind
  | fuel + 1, x, root, y, hfind, hmem => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          have hyx : y = x := by
            simpa [compressPathFindFuelTrace, hparent] using hmem
          subst y
          exact hfind
      | some parent =>
          by_cases hsame : parent = x
          · have hyx : y = x := by
              simpa [compressPathFindFuelTrace, hparent, hsame] using hmem
            subst y
            exact hfind
          · have hmemCases :
                y = x ∨
                  y ∈ backend.compressPathFindFuelTrace fuel parent := by
              simpa [compressPathFindFuelTrace, hparent, hsame] using hmem
            rcases hmemCases with hyx | htailMem
            · subst y
              exact hfind
            · have hparentFind :
                  backend.state.forest.findRoot? parent = some root :=
                backend.findRoot?_parent_eq_of_parent?_ne
                  hparent hsame hfind
              exact
                compressPathFindFuelTrace_mem_findRoot?_eq_of_findRoot?
                  backend fuel hparentFind htailMem

theorem fullCompressFindTrace_mem_findRoot?_eq_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root y : Nat}
    (hfind : backend.state.forest.findRoot? x = some root)
    (hmem : y ∈ backend.fullCompressFindTrace x) :
    backend.state.forest.findRoot? y = some root := by
  simpa [fullCompressFindTrace] using
    backend.compressPathFindFuelTrace_mem_findRoot?_eq_of_findRoot?
      backend.state.forest.maxSearchFuel hfind hmem

theorem compressPathFindFuelCosted_parent?_eq_old_of_not_mem_trace
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x y parent : Nat},
      y ∉ backend.compressPathFindFuelTrace fuel x ->
      backend.state.forest.parent? y = some parent ->
      ((backend.compressPathFindFuelCosted fuel x).erase.1).state.forest.parent?
        y =
        some parent
  | 0, x, y, parent, hnot, hparent => by
      have hyx : y ≠ x := by
        intro hyx
        exact hnot (by simp [compressPathFindFuelTrace, hyx])
      simpa [compressPathFindFuelCosted] using
        backend.compressFindCosted_parent?_eq_old_of_ne hyx hparent
  | fuel + 1, x, y, parent, hnot, hparent => by
      cases hxparent : backend.state.forest.parent? x with
      | none =>
          have hyx : y ≠ x := by
            intro hyx
            exact hnot (by simp [compressPathFindFuelTrace, hxparent, hyx])
          simpa [compressPathFindFuelCosted, hxparent] using
            backend.compressFindCosted_parent?_eq_old_of_ne hyx hparent
      | some xparent =>
          by_cases hsame : xparent = x
          · have hyx : y ≠ x := by
              intro hyx
              exact hnot (by
                simp [compressPathFindFuelTrace, hxparent, hsame, hyx])
            simpa [compressPathFindFuelCosted, hxparent, hsame] using
              backend.compressFindCosted_parent?_eq_old_of_ne hyx hparent
          · have hyx : y ≠ x := by
              intro hyx
              exact hnot (by
                simp [compressPathFindFuelTrace, hxparent, hsame, hyx])
            have hnotTail :
                y ∉ backend.compressPathFindFuelTrace fuel xparent := by
              intro htail
              exact hnot (by
                simp [compressPathFindFuelTrace, hxparent, hsame, htail])
            let tail :=
              (backend.compressPathFindFuelCosted fuel xparent).erase.1
            have htailParent :
                tail.state.forest.parent? y = some parent := by
              simpa [tail] using
                compressPathFindFuelCosted_parent?_eq_old_of_not_mem_trace
                  backend fuel hnotTail hparent
            have hstep :
                ((tail.compressFindCosted x).erase.1).state.forest.parent? y =
                  some parent :=
              tail.compressFindCosted_parent?_eq_old_of_ne hyx htailParent
            simpa [compressPathFindFuelCosted, hxparent, hsame, tail] using
              hstep

theorem fullCompressFindCosted_parent?_eq_old_of_not_mem_trace
    (backend : NoCompressionRankedMassBackendState)
    {x y parent : Nat}
    (hnot : y ∉ backend.fullCompressFindTrace x)
    (hparent : backend.state.forest.parent? y = some parent) :
    ((backend.fullCompressFindCosted x).erase.1).state.forest.parent? y =
      some parent := by
  simpa [fullCompressFindCosted, fullCompressFindTrace] using
    backend.compressPathFindFuelCosted_parent?_eq_old_of_not_mem_trace
      backend.state.forest.maxSearchFuel hnot hparent

theorem fullCompressFindCosted_refinement_profile
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost <=
        backend.state.forest.maxSearchFuel + 1 /\
      (backend.fullCompressFindCosted x).erase.2 =
        backend.abstractState.find? x /\
      (forall i,
        ((backend.fullCompressFindCosted x).erase.1).state.forest.findRoot?
          i =
        backend.state.forest.findRoot? i) /\
      State.SamePartition
        (abstractState (backend.fullCompressFindCosted x).erase.1)
        backend.abstractState := by
  have hfindEq :
      forall i,
        ((backend.fullCompressFindCosted x).erase.1).state.forest.findRoot?
          i =
        backend.state.forest.findRoot? i := by
    intro i
    exact backend.fullCompressFindCosted_findRoot?_eq x i
  refine ⟨backend.fullCompressFindCosted_cost_le x, ?_, hfindEq, ?_⟩
  · exact (backend.fullCompressFindCosted_answer_eq_final_abstractState x).trans
      (abstractState_find?_eq_of_findRoot?_eq hfindEq x)
  · exact samePartition_of_backend_findRoot?_eq hfindEq

theorem unionCosted_refinement_profile
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.unionCosted x y).cost = 1 /\
      State.SamePartition
        (abstractState (backend.unionCosted x y).erase)
        (backend.abstractState.unionSpec x y) := by
  constructor
  · rfl
  · rcases backend.state.unionCosted_rankPowerMassInvariant_profile
        x y backend.inv with
      ⟨_hstep, hlinked, hsameLinked⟩
    have hsameInv :
        State.SamePartition
          (abstractState (backend.unionResult x y))
          (((backend.state.unionCosted x y).erase).forest.toState
            hlinked.toInvariant) :=
      ParentForest.toState_samePartition_of_invariants
        ((backend.state.unionCosted x y).erase).forest
        (backend.unionResult x y).inv.toInvariant
        hlinked.toInvariant
    exact State.samePartition_trans hsameInv hsameLinked

theorem unionManyCosted_cost
    (backend : NoCompressionRankedMassBackendState) :
    forall ops : List (Nat × Nat),
      (backend.unionManyCosted ops).cost = ops.length
  | [] => by
      rfl
  | (x, y) :: ops => by
      have htail :=
        unionManyCosted_cost ((backend.unionCosted x y).value) ops
      simp [unionManyCosted, htail]
      omega

theorem unionManyCosted_refinement_profile
    (backend : NoCompressionRankedMassBackendState) :
    forall ops : List (Nat × Nat),
      (backend.unionManyCosted ops).cost = ops.length /\
        State.SamePartition
          (abstractState (backend.unionManyCosted ops).erase)
          (backend.abstractState.unionSpecMany ops)
  | [] => by
      constructor
      · rfl
      · simpa [unionManyCosted, State.unionSpecMany, abstractState] using
          State.samePartition_refl backend.abstractState
  | (x, y) :: ops => by
      rcases unionManyCosted_refinement_profile
          ((backend.unionCosted x y).value) ops with
        ⟨hcostTail, hsameTail⟩
      have hsameStep :
          State.SamePartition
            (abstractState (backend.unionCosted x y).value)
            (backend.abstractState.unionSpec x y) := by
        simpa [Costed.erase] using
          (unionCosted_refinement_profile backend x y).2
      have hsameMany :
          State.SamePartition
            ((abstractState (backend.unionCosted x y).value).unionSpecMany
              ops)
            ((backend.abstractState.unionSpec x y).unionSpecMany ops) :=
        State.samePartition_unionSpecMany hsameStep ops
      constructor
      · simp [unionManyCosted, hcostTail]
        omega
      · simpa [unionManyCosted, State.unionSpecMany] using
          State.samePartition_trans hsameTail hsameMany

theorem identity_unionManyCosted_refinement_profile
    (n : Nat) (ops : List (Nat × Nat)) :
    ((identity n).unionManyCosted ops).cost = ops.length /\
      State.SamePartition
        (abstractState (((identity n).unionManyCosted ops).erase))
        ((identity n).abstractState.unionSpecMany ops) :=
  unionManyCosted_refinement_profile (identity n) ops

/-- Representation-backed boundary using full path compression for `find`. -/
def fullCompressionRepresentationBackend :
    RepresentationBackend NoCompressionRankedMassBackendState where
  abstractState := abstractState
  findCosted := fun backend x => backend.fullCompressFindCosted x
  unionCosted := fun backend x y => backend.unionCosted x y
  find_exact := by
    intro backend x
    exact (backend.fullCompressFindCosted_refinement_profile x).2.1
  find_refines := by
    intro backend x
    exact (backend.fullCompressFindCosted_refinement_profile x).2.2.2
  union_refines := by
    intro backend x y
    exact (backend.unionCosted_refinement_profile x y).2

theorem fullCompressionRepresentationBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      (fullCompressionRepresentationBackend.findCosted backend x).cost <=
          backend.state.forest.maxSearchFuel + 1 /\
        (fullCompressionRepresentationBackend.findCosted backend x).erase.2 =
          (fullCompressionRepresentationBackend.abstractState backend).find?
            x /\
        State.SamePartition
          (fullCompressionRepresentationBackend.abstractState
            (fullCompressionRepresentationBackend.findCosted backend x).erase.1)
          (fullCompressionRepresentationBackend.abstractState backend)) /\
      (forall (backend : NoCompressionRankedMassBackendState)
        {x root y : Nat},
        backend.state.forest.findRoot? x = some root ->
        y ∈ backend.fullCompressFindTrace x ->
        (((fullCompressionRepresentationBackend.findCosted backend x).erase.1).state.forest.parent? y) =
          some root) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        (fullCompressionRepresentationBackend.unionCosted backend x y).cost =
            1 /\
          State.SamePartition
            (fullCompressionRepresentationBackend.abstractState
              ((fullCompressionRepresentationBackend.unionCosted backend x y).erase))
            ((fullCompressionRepresentationBackend.abstractState backend).unionSpec
              x y)) := by
  constructor
  · intro backend x
    have hprofile := backend.fullCompressFindCosted_refinement_profile x
    exact ⟨hprofile.1, hprofile.2.1, hprofile.2.2.2⟩
  · constructor
    · intro backend x root y hfind hmem
      simpa [fullCompressionRepresentationBackend] using
        backend.fullCompressFindCosted_trace_parent?_eq_root_of_findRoot?
          hfind hmem
    · intro backend x y
      exact backend.unionCosted_refinement_profile x y

end NoCompressionRankedMassBackendState

end ParentForest

end Forest

end UnionFind

end RMQ
