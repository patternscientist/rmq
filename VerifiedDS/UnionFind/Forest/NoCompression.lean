import VerifiedDS.UnionFind.Forest.Base

namespace VerifiedDS

open RMQ

namespace UnionFind

namespace Forest

namespace ParentForest

/-- Executable no-compression union-by-rank state for the forest layer. -/
structure NoCompressionRankedForest where
  forest : ParentForest
  rank : Nat -> Nat

namespace NoCompressionRankedForest

def findCosted (state : NoCompressionRankedForest) (x : Nat) :
    Costed (NoCompressionRankedForest × Option Nat) :=
  Costed.tickValue 1 (state, state.forest.findRoot? x)

def unionCosted (state : NoCompressionRankedForest) (x y : Nat) :
    Costed NoCompressionRankedForest :=
  Costed.tickValue 1
    { forest := state.forest.unionByRank state.rank x y
      rank := state.forest.rankAfterUnionByRank state.rank x y }

@[simp] theorem findCosted_cost
    (state : NoCompressionRankedForest) (x : Nat) :
    (state.findCosted x).cost = 1 := by
  rfl

@[simp] theorem findCosted_erase
    (state : NoCompressionRankedForest) (x : Nat) :
    (state.findCosted x).erase =
      (state, state.forest.findRoot? x) := by
  rfl

@[simp] theorem unionCosted_cost
    (state : NoCompressionRankedForest) (x y : Nat) :
    (state.unionCosted x y).cost = 1 := by
  rfl

@[simp] theorem unionCosted_erase
    (state : NoCompressionRankedForest) (x y : Nat) :
    (state.unionCosted x y).erase =
      { forest := state.forest.unionByRank state.rank x y
        rank := state.forest.rankAfterUnionByRank state.rank x y } := by
  rfl

theorem findCosted_exact
    (state : NoCompressionRankedForest) (x : Nat) :
    (state.findCosted x).erase.2 = state.forest.findRoot? x := by
  rfl

theorem unionCosted_rankSizeInvariant_profile
    (state : NoCompressionRankedForest) (x y : Nat)
    (h : state.forest.RankComponentInvariant state.rank) :
    ((state.unionCosted x y).erase).forest.RankSizeInvariant
        ((state.unionCosted x y).erase).rank /\
      exists hlinked :
        ((state.unionCosted x y).erase).forest.LinkableInvariant,
          State.SamePartition
            (((state.unionCosted x y).erase).forest.toState
              hlinked.toInvariant)
            ((state.forest.toState h.toInvariant).unionSpec x y) := by
  simpa [unionCosted] using
    state.forest.unionByRank_rankSizeInvariant_profile state.rank h x y

theorem profile
    (state : NoCompressionRankedForest) :
    (forall x,
      (state.findCosted x).cost = 1 /\
        (state.findCosted x).erase =
          (state, state.forest.findRoot? x)) /\
      (forall x y,
        (state.unionCosted x y).cost = 1 /\
          (state.unionCosted x y).erase =
            { forest := state.forest.unionByRank state.rank x y
              rank := state.forest.rankAfterUnionByRank state.rank x y }) := by
  constructor
  · intro x
    exact ⟨rfl, rfl⟩
  · intro x y
    exact ⟨rfl, rfl⟩

end NoCompressionRankedForest

/--
Executable no-compression union-by-rank state that carries root mass data.

The `mass` function is model data for component-size accounting: `unionCosted`
updates it with `rootMassAfterUnionByRank`, so the accompanying invariant can
be carried across repeated union steps without reintroducing the old
fixed-arity `RankComponentInvariant` premise.
-/
structure NoCompressionRankedMassForest where
  forest : ParentForest
  rank : Nat -> Nat
  mass : Nat -> Nat

namespace NoCompressionRankedMassForest

def findCosted (state : NoCompressionRankedMassForest) (x : Nat) :
    Costed (NoCompressionRankedMassForest × Option Nat) :=
  Costed.tickValue 1 (state, state.forest.findRoot? x)

def unionCosted (state : NoCompressionRankedMassForest) (x y : Nat) :
    Costed NoCompressionRankedMassForest :=
  Costed.tickValue 1
    { forest := state.forest.unionByRank state.rank x y
      rank := state.forest.rankAfterUnionByRank state.rank x y
      mass := state.forest.rootMassAfterUnionByRank state.rank state.mass x y }

@[simp] theorem findCosted_cost
    (state : NoCompressionRankedMassForest) (x : Nat) :
    (state.findCosted x).cost = 1 := by
  rfl

@[simp] theorem findCosted_erase
    (state : NoCompressionRankedMassForest) (x : Nat) :
    (state.findCosted x).erase =
      (state, state.forest.findRoot? x) := by
  rfl

@[simp] theorem unionCosted_cost
    (state : NoCompressionRankedMassForest) (x y : Nat) :
    (state.unionCosted x y).cost = 1 := by
  rfl

@[simp] theorem unionCosted_erase
    (state : NoCompressionRankedMassForest) (x y : Nat) :
    (state.unionCosted x y).erase =
      { forest := state.forest.unionByRank state.rank x y
        rank := state.forest.rankAfterUnionByRank state.rank x y
        mass := state.forest.rootMassAfterUnionByRank
          state.rank state.mass x y } := by
  rfl

theorem findCosted_exact
    (state : NoCompressionRankedMassForest) (x : Nat) :
    (state.findCosted x).erase.2 = state.forest.findRoot? x := by
  rfl

theorem unionCosted_rootMassInvariant_profile
    (state : NoCompressionRankedMassForest) (x y : Nat)
    (h : state.forest.RootMassInvariant state.rank state.mass) :
    ((state.unionCosted x y).erase).forest.RootMassInvariant
        ((state.unionCosted x y).erase).rank
        ((state.unionCosted x y).erase).mass /\
      exists hlinked :
        ((state.unionCosted x y).erase).forest.LinkableInvariant,
          State.SamePartition
            (((state.unionCosted x y).erase).forest.toState
              hlinked.toInvariant)
            ((state.forest.toState h.toInvariant).unionSpec x y) := by
  simpa [unionCosted] using
    state.forest.unionByRank_rootMassInvariant_profile
      state.rank state.mass h x y

theorem unionCosted_rankPowerMassInvariant_profile
    (state : NoCompressionRankedMassForest) (x y : Nat)
    (h : state.forest.RankPowerMassInvariant state.rank state.mass) :
    ((state.unionCosted x y).erase).forest.RankPowerMassInvariant
        ((state.unionCosted x y).erase).rank
        ((state.unionCosted x y).erase).mass /\
      exists hlinked :
        ((state.unionCosted x y).erase).forest.LinkableInvariant,
          State.SamePartition
            (((state.unionCosted x y).erase).forest.toState
              hlinked.toInvariant)
            ((state.forest.toState h.toInvariant).unionSpec x y) := by
  simpa [unionCosted] using
    state.forest.unionByRank_rankPowerMassInvariant_profile
      state.rank state.mass h x y

theorem profile
    (state : NoCompressionRankedMassForest) :
    (forall x,
      (state.findCosted x).cost = 1 /\
        (state.findCosted x).erase =
          (state, state.forest.findRoot? x)) /\
      (forall x y,
        (state.unionCosted x y).cost = 1 /\
          (state.unionCosted x y).erase =
            { forest := state.forest.unionByRank state.rank x y
              rank := state.forest.rankAfterUnionByRank state.rank x y
              mass := state.forest.rootMassAfterUnionByRank
                state.rank state.mass x y }) := by
  constructor
  · intro x
    exact ⟨rfl, rfl⟩
  · intro x y
    exact ⟨rfl, rfl⟩

end NoCompressionRankedMassForest

/-- The concrete forest with `n` singleton components. -/
def identity (n : Nat) : ParentForest where
  parents := List.range n

@[simp] theorem identity_size (n : Nat) :
    (identity n).size = n := by
  simp [identity, size]

theorem identity_parent?_eq_some_of_valid
    (n : Nat) {x : Nat} (hx : (identity n).valid x) :
    (identity n).parent? x = some x := by
  have hx' : x < n := by
    simpa [identity, size] using hx
  simpa [identity, parent?] using List.getElem?_range hx'

theorem identity_isRoot_of_valid
    (n : Nat) {x : Nat} (hx : (identity n).valid x) :
    (identity n).IsRoot x := by
  exact identity_parent?_eq_some_of_valid n hx

theorem identity_findRootFuel?_eq_some_of_valid
    (n : Nat) {x : Nat} (hx : (identity n).valid x) :
    (identity n).findRootFuel? (identity n).maxSearchFuel x = some x := by
  have hparent := identity_parent?_eq_some_of_valid n hx
  simp [maxSearchFuel, findRootFuel?, hparent]

theorem identity_findRootFuel_size_eq_some_of_valid
    (n : Nat) {x : Nat} (hx : (identity n).valid x) :
    (identity n).findRootFuel? (identity n).size x = some x := by
  have hparent := identity_parent?_eq_some_of_valid n hx
  cases n with
  | zero =>
      simp [identity, size] at hx
  | succ n' =>
      have hparent' : (identity (n' + 1)).parent? x = some x := by
        simpa using hparent
      simp [identity_size, findRootFuel?, hparent']

theorem identity_findRoot?_eq_some_of_valid
    (n : Nat) {x : Nat} (hx : (identity n).valid x) :
    (identity n).findRoot? x = some x := by
  have hfind := identity_findRootFuel?_eq_some_of_valid n hx
  have hx' : x < n := by
    simpa [identity, size] using hx
  simpa [findRoot?, identity, size, hx'] using hfind

theorem identity_findRoot?
    (n x : Nat) :
    (identity n).findRoot? x =
      if _hx : x < n then some x else none := by
  by_cases hx : (identity n).valid x
  · have hx' : x < n := by
      simpa [identity, size] using hx
    simp [hx', identity_findRoot?_eq_some_of_valid n hx]
  · have hx' : Not (x < n) := by
      simpa [identity, size] using hx
    simp [findRoot?, identity, size, hx']

theorem identity_invariant (n : Nat) :
    (identity n).Invariant where
  parent_lt := by
    intro x parent hparent
    by_cases hx : (identity n).valid x
    · have hself := identity_parent?_eq_some_of_valid n hx
      rw [hself] at hparent
      cases hparent
      simpa [identity, size] using hx
    · have hle : (List.range n).length <= x := by
        have hx' : Not (x < n) := by
          simpa [identity, size] using hx
        simp [List.length_range]
        omega
      have hnone : (identity n).parent? x = none := by
        simpa [identity, parent?] using
          (List.getElem?_eq_none hle :
            (List.range n)[x]? = none)
      rw [hnone] at hparent
      cases hparent
  bounded_depth := by
    intro x hx
    exact ⟨x,
      identity_findRootFuel?_eq_some_of_valid n hx,
      hx,
      identity_isRoot_of_valid n hx⟩

theorem identity_linkable (n : Nat) :
    (identity n).LinkableInvariant where
  toInvariant := identity_invariant n
  strict_depth := by
    intro x hx
    exact ⟨x,
      identity_findRootFuel_size_eq_some_of_valid n hx,
      hx,
      identity_isRoot_of_valid n hx⟩

theorem identity_rankInvariant (n : Nat) :
    (identity n).RankInvariant (fun _ => 0) where
  toInvariant := identity_invariant n
  rank_lt_size := by
    intro x hx
    have hxNat : x < n := by
      simpa [identity, size] using hx
    omega
  parent_rank_lt := by
    intro x parent hparent hne
    have hx : (identity n).valid x :=
      (identity n).valid_of_parent?_eq_some hparent
    have hself := identity_parent?_eq_some_of_valid n hx
    rw [hself] at hparent
    cases hparent
    exact False.elim (hne rfl)

theorem identity_rankSizeInvariant (n : Nat) :
    (identity n).RankSizeInvariant (fun _ => 0) where
  toRankInvariant := identity_rankInvariant n
  equal_rank_root_bump_lt := by
    intro rootX rootY hx hy _hrootX _hrootY hne _hrankEq
    have hxNat : rootX < n := by
      simpa [identity, size] using hx
    have hyNat : rootY < n := by
      simpa [identity, size] using hy
    simp [identity_size]
    omega

theorem identity_rankComponentInvariant (n : Nat) :
    (identity n).RankComponentInvariant (fun _ => 0) where
  toRankSizeInvariant := identity_rankSizeInvariant n
  equal_pair_next_rank_bump_lt := by
    intro rootX rootY rootZ hx hy hz hrootX hrootY hrootZ
      hneYX hneZX hneZY hrankEq hnext
    omega

theorem identity_rootMassInvariant (n : Nat) :
    (identity n).RootMassInvariant (fun _ => 0) (fun _ => 1) where
  toRankInvariant := identity_rankInvariant n
  root_mass_pos := by
    intro root hvalid hroot
    simp
  rank_lt_mass := by
    intro root hvalid hroot
    simp
  rootMassSum_le_size := by
    intro roots hnodup hroots
    have hbounded :
        forall {root : Nat}, root ∈ roots -> root < n := by
      intro root hmem
      have hvalid : (identity n).valid root := (hroots hmem).1
      simpa [identity, size] using hvalid
    have hlen :=
      nodup_length_le_of_forall_lt n roots hnodup hbounded
    simpa [identity_size, rootMassSum_one_eq_length roots] using hlen

theorem identity_rankPowerMassInvariant (n : Nat) :
    (identity n).RankPowerMassInvariant (fun _ => 0) (fun _ => 1) where
  toRootMassInvariant := identity_rootMassInvariant n
  rank_power_le_mass := by
    intro root hvalid hroot
    simp

theorem identity_toState_find?
    (n x : Nat) :
    ((identity n).toState (identity_invariant n)).find? x =
      if _hx : x < n then some x else none := by
  rw [(identity n).toState_find?_eq_findRoot? (identity_invariant n) x]
  exact identity_findRoot? n x

theorem identity_toState_repr_eq_self_of_valid
    (n : Nat) {x : Nat} (hx : (identity n).valid x) :
    ((identity n).toState (identity_invariant n)).repr x = x := by
  have hfind := identity_findRoot?_eq_some_of_valid n hx
  exact (identity n).toState_repr_eq_of_findRoot?
    (identity_invariant n) hfind

theorem identity_profile (n : Nat) :
    (identity n).Invariant /\
      (identity n).LinkableInvariant /\
      (identity n).RankInvariant (fun _ => 0) /\
      (identity n).RankSizeInvariant (fun _ => 0) /\
      (identity n).RankComponentInvariant (fun _ => 0) /\
      (identity n).RootMassInvariant (fun _ => 0) (fun _ => 1) /\
      (identity n).RankPowerMassInvariant (fun _ => 0) (fun _ => 1) /\
      (forall {x : Nat}, (identity n).valid x ->
        (identity n).findRoot? x = some x) /\
      (forall x,
        ((identity n).toState (identity_invariant n)).find? x =
          if _hx : x < n then some x else none) := by
  constructor
  · exact identity_invariant n
  · constructor
    · exact identity_linkable n
    · constructor
      · exact identity_rankInvariant n
      · constructor
        · exact identity_rankSizeInvariant n
        · constructor
          · exact identity_rankComponentInvariant n
          · constructor
            · exact identity_rootMassInvariant n
            · constructor
              · exact identity_rankPowerMassInvariant n
              · constructor
                · intro x hx
                  exact identity_findRoot?_eq_some_of_valid n hx
                · intro x
                  exact identity_toState_find? n x

namespace NoCompressionRankedMassForest

/-- Concrete no-compression union-by-rank mass state with singleton roots. -/
def identity (n : Nat) : NoCompressionRankedMassForest where
  forest := ParentForest.identity n
  rank := fun _ => 0
  mass := fun _ => 1

@[simp] theorem identity_forest (n : Nat) :
    (identity n).forest = ParentForest.identity n := by
  rfl

@[simp] theorem identity_rank (n : Nat) :
    (identity n).rank = fun _ => 0 := by
  rfl

@[simp] theorem identity_mass (n : Nat) :
    (identity n).mass = fun _ => 1 := by
  rfl

theorem identity_rootMassInvariant (n : Nat) :
    (identity n).forest.RootMassInvariant
      (identity n).rank (identity n).mass := by
  simpa [identity] using ParentForest.identity_rootMassInvariant n

theorem identity_rankPowerMassInvariant (n : Nat) :
    (identity n).forest.RankPowerMassInvariant
      (identity n).rank (identity n).mass := by
  simpa [identity] using ParentForest.identity_rankPowerMassInvariant n

theorem identity_profile (n : Nat) :
    (identity n).forest = ParentForest.identity n /\
      (identity n).rank = (fun _ => 0) /\
      (identity n).mass = (fun _ => 1) /\
      (identity n).forest.RootMassInvariant
        (identity n).rank (identity n).mass /\
      (identity n).forest.RankPowerMassInvariant
        (identity n).rank (identity n).mass /\
      (forall x,
        ((identity n).findCosted x).erase.2 =
          (ParentForest.identity n).findRoot? x) := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · exact identity_rootMassInvariant n
        · constructor
          · exact identity_rankPowerMassInvariant n
          · intro x
            rfl

/-- Execute a finite list of no-compression union-by-rank requests. -/
def unionManyCosted (state : NoCompressionRankedMassForest) :
    List (Nat × Nat) -> Costed NoCompressionRankedMassForest
  | [] => Costed.pure state
  | (x, y) :: ops =>
      Costed.bind (state.unionCosted x y)
        (fun state' => unionManyCosted state' ops)

@[simp] theorem unionManyCosted_nil
    (state : NoCompressionRankedMassForest) :
    state.unionManyCosted [] = Costed.pure state := by
  rfl

@[simp] theorem unionManyCosted_cons
    (state : NoCompressionRankedMassForest) (x y : Nat)
    (ops : List (Nat × Nat)) :
    state.unionManyCosted ((x, y) :: ops) =
      Costed.bind (state.unionCosted x y)
        (fun state' => state'.unionManyCosted ops) := by
  rfl

theorem unionManyCosted_cost
    (state : NoCompressionRankedMassForest) :
    forall ops : List (Nat × Nat),
      (state.unionManyCosted ops).cost = ops.length
  | [] => by
      rfl
  | (x, y) :: ops => by
      have htail :=
        unionManyCosted_cost ((state.unionCosted x y).value) ops
      simp [unionManyCosted, htail]
      omega

theorem unionManyCosted_rootMassInvariant_profile
    (state : NoCompressionRankedMassForest) :
    forall ops : List (Nat × Nat),
      state.forest.RootMassInvariant state.rank state.mass ->
      ((state.unionManyCosted ops).erase).forest.RootMassInvariant
        ((state.unionManyCosted ops).erase).rank
        ((state.unionManyCosted ops).erase).mass
  | [], h => by
      simpa [unionManyCosted] using h
  | (x, y) :: ops, h => by
      have hstep :=
        (state.unionCosted_rootMassInvariant_profile x y h).1
      have htail :=
        unionManyCosted_rootMassInvariant_profile
          ((state.unionCosted x y).erase) ops hstep
      simpa [unionManyCosted] using htail

theorem unionManyCosted_rankPowerMassInvariant_profile
    (state : NoCompressionRankedMassForest) :
    forall ops : List (Nat × Nat),
      state.forest.RankPowerMassInvariant state.rank state.mass ->
      ((state.unionManyCosted ops).erase).forest.RankPowerMassInvariant
        ((state.unionManyCosted ops).erase).rank
        ((state.unionManyCosted ops).erase).mass
  | [], h => by
      simpa [unionManyCosted] using h
  | (x, y) :: ops, h => by
      have hstep :=
        (state.unionCosted_rankPowerMassInvariant_profile x y h).1
      have htail :=
        unionManyCosted_rankPowerMassInvariant_profile
          ((state.unionCosted x y).erase) ops hstep
      simpa [unionManyCosted] using htail

theorem unionManyCosted_profile
    (state : NoCompressionRankedMassForest) (ops : List (Nat × Nat))
    (h : state.forest.RootMassInvariant state.rank state.mass) :
    (state.unionManyCosted ops).cost = ops.length /\
      ((state.unionManyCosted ops).erase).forest.RootMassInvariant
        ((state.unionManyCosted ops).erase).rank
        ((state.unionManyCosted ops).erase).mass := by
  exact ⟨
    unionManyCosted_cost state ops,
    unionManyCosted_rootMassInvariant_profile state ops h⟩

theorem unionManyCosted_rankPowerMass_profile
    (state : NoCompressionRankedMassForest) (ops : List (Nat × Nat))
    (h : state.forest.RankPowerMassInvariant state.rank state.mass) :
    (state.unionManyCosted ops).cost = ops.length /\
      ((state.unionManyCosted ops).erase).forest.RankPowerMassInvariant
        ((state.unionManyCosted ops).erase).rank
        ((state.unionManyCosted ops).erase).mass := by
  exact ⟨
    unionManyCosted_cost state ops,
    unionManyCosted_rankPowerMassInvariant_profile state ops h⟩

theorem unionManyCosted_samePartition_profile
    (state : NoCompressionRankedMassForest) :
    forall ops : List (Nat × Nat),
      (h : state.forest.RootMassInvariant state.rank state.mass) ->
      exists hlinked :
        ((state.unionManyCosted ops).erase).forest.LinkableInvariant,
          State.SamePartition
            (((state.unionManyCosted ops).erase).forest.toState
              hlinked.toInvariant)
            ((state.forest.toState h.toInvariant).unionSpecMany ops)
  | [], h => by
      let hlinked : state.forest.LinkableInvariant :=
        state.forest.rankInvariant_linkable state.rank h.toRankInvariant
      refine ⟨hlinked, ?_⟩
      simpa [unionManyCosted, State.unionSpecMany] using
        state.forest.toState_samePartition_of_invariants
          hlinked.toInvariant h.toInvariant
  | (x, y) :: ops, h => by
      rcases state.unionCosted_rootMassInvariant_profile x y h with
        ⟨hstep, hstepLinked, hsameStep⟩
      rcases unionManyCosted_samePartition_profile
          ((state.unionCosted x y).erase) ops hstep with
        ⟨hfinalLinked, hsameTail⟩
      have hsameStepWithMassInvariant :
          State.SamePartition
            (((state.unionCosted x y).erase).forest.toState
              hstep.toInvariant)
            ((state.forest.toState h.toInvariant).unionSpec x y) := by
        have hsameInv :
            State.SamePartition
              (((state.unionCosted x y).erase).forest.toState
                hstep.toInvariant)
              (((state.unionCosted x y).erase).forest.toState
                hstepLinked.toInvariant) :=
          ParentForest.toState_samePartition_of_invariants
            (((state.unionCosted x y).erase).forest)
              hstep.toInvariant hstepLinked.toInvariant
        exact State.samePartition_trans hsameInv hsameStep
      have hsameMany :
          State.SamePartition
            ((((state.unionCosted x y).erase).forest.toState
              hstep.toInvariant).unionSpecMany ops)
            (((state.forest.toState h.toInvariant).unionSpec x y).unionSpecMany
              ops) :=
        State.samePartition_unionSpecMany hsameStepWithMassInvariant ops
      refine ⟨hfinalLinked, ?_⟩
      simpa [unionManyCosted, State.unionSpecMany] using
        State.samePartition_trans hsameTail hsameMany

theorem unionManyCosted_refinement_profile
    (state : NoCompressionRankedMassForest) (ops : List (Nat × Nat))
    (h : state.forest.RootMassInvariant state.rank state.mass) :
    (state.unionManyCosted ops).cost = ops.length /\
      ((state.unionManyCosted ops).erase).forest.RootMassInvariant
        ((state.unionManyCosted ops).erase).rank
        ((state.unionManyCosted ops).erase).mass /\
      exists hlinked :
        ((state.unionManyCosted ops).erase).forest.LinkableInvariant,
          State.SamePartition
            (((state.unionManyCosted ops).erase).forest.toState
              hlinked.toInvariant)
            ((state.forest.toState h.toInvariant).unionSpecMany ops) := by
  exact ⟨
    unionManyCosted_cost state ops,
    unionManyCosted_rootMassInvariant_profile state ops h,
    unionManyCosted_samePartition_profile state ops h⟩

theorem identity_unionManyCosted_profile
    (n : Nat) (ops : List (Nat × Nat)) :
    ((identity n).unionManyCosted ops).cost = ops.length /\
      (((identity n).unionManyCosted ops).erase).forest.RootMassInvariant
        (((identity n).unionManyCosted ops).erase).rank
        (((identity n).unionManyCosted ops).erase).mass := by
  exact unionManyCosted_profile
    (identity n) ops (identity_rootMassInvariant n)

theorem identity_unionManyCosted_rankPowerMass_profile
    (n : Nat) (ops : List (Nat × Nat)) :
    ((identity n).unionManyCosted ops).cost = ops.length /\
      (((identity n).unionManyCosted ops).erase).forest.RankPowerMassInvariant
        (((identity n).unionManyCosted ops).erase).rank
        (((identity n).unionManyCosted ops).erase).mass := by
  exact unionManyCosted_rankPowerMass_profile
    (identity n) ops (identity_rankPowerMassInvariant n)

theorem identity_unionManyCosted_refinement_profile
    (n : Nat) (ops : List (Nat × Nat)) :
    ((identity n).unionManyCosted ops).cost = ops.length /\
      (((identity n).unionManyCosted ops).erase).forest.RootMassInvariant
        (((identity n).unionManyCosted ops).erase).rank
        (((identity n).unionManyCosted ops).erase).mass /\
      exists hlinked :
        (((identity n).unionManyCosted ops).erase).forest.LinkableInvariant,
          State.SamePartition
            ((((identity n).unionManyCosted ops).erase).forest.toState
              hlinked.toInvariant)
            (((identity n).forest.toState
              (identity_rootMassInvariant n).toInvariant).unionSpecMany ops) :=
  unionManyCosted_refinement_profile
    (identity n) ops (identity_rootMassInvariant n)

end NoCompressionRankedMassForest

end ParentForest

end Forest

end UnionFind

end VerifiedDS
