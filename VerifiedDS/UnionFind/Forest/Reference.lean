import VerifiedDS.UnionFind.Forest.Amortized

namespace VerifiedDS

open RMQ

namespace UnionFind

namespace Forest

namespace ParentForest

/-- Direct parent-pointer realization of a representative state: each valid
node points directly to its abstract representative. -/
def ofState (state : State) : ParentForest where
  parents := (List.range state.size).map state.repr

@[simp] theorem ofState_size (state : State) :
    (ofState state).size = state.size := by
  simp [ofState, size]

theorem ofState_parent?_eq_some_of_valid
    (state : State) {x : Nat} (hx : state.valid x) :
    (ofState state).parent? x = some (state.repr x) := by
  have hrange : (List.range state.size)[x]? = some x :=
    List.getElem?_range hx
  simp [ofState, parent?, hrange]

theorem ofState_findRootFuel?_eq_some_of_valid
    (state : State)
    (hidempotent :
      forall {x : Nat}, state.valid x ->
        state.repr (state.repr x) = state.repr x)
    {x : Nat} (hx : state.valid x) :
    (ofState state).findRootFuel? (ofState state).maxSearchFuel x =
      some (state.repr x) := by
  have hparent := ofState_parent?_eq_some_of_valid state hx
  by_cases hsame : state.repr x = x
  · simp [maxSearchFuel, findRootFuel?, hparent, hsame]
  · have hreprValid : state.valid (state.repr x) := state.repr_lt hx
    have hrootParent := ofState_parent?_eq_some_of_valid state hreprValid
    have hidem := hidempotent hx
    have hrootParent' :
        (ofState state).parent? (state.repr x) =
          some (state.repr x) := by
      simpa [hidem] using hrootParent
    have hstep :
        (ofState state).findRootFuel? (ofState state).maxSearchFuel x =
          (ofState state).findRootFuel? state.size (state.repr x) := by
      simp [maxSearchFuel, ofState_size, findRootFuel?, hparent, hsame]
    cases hsize : state.size with
    | zero =>
        have hxNat : x < state.size := hx
        rw [hsize] at hxNat
        omega
    | succ n =>
        rw [hstep, hsize]
        simp [findRootFuel?, hrootParent']

theorem ofState_findRoot?_eq_some_of_valid
    (state : State)
    (hidempotent :
      forall {x : Nat}, state.valid x ->
        state.repr (state.repr x) = state.repr x)
    {x : Nat} (hx : state.valid x) :
    (ofState state).findRoot? x = some (state.repr x) := by
  have hfind :=
    ofState_findRootFuel?_eq_some_of_valid state hidempotent hx
  have hxForest : (ofState state).valid x := by
    simpa [ofState, size] using hx
  have hxNat : x < state.size := hx
  simp [findRoot?, ofState_size, hxNat] at hfind ⊢
  exact hfind

theorem ofState_invariant
    (state : State)
    (hidempotent :
      forall {x : Nat}, state.valid x ->
        state.repr (state.repr x) = state.repr x) :
    (ofState state).Invariant where
  parent_lt := by
    intro x parent hparent
    by_cases hx : state.valid x
    · have hself := ofState_parent?_eq_some_of_valid state hx
      rw [hself] at hparent
      cases hparent
      simpa [ofState_size] using state.repr_lt hx
    · have hle : ((List.range state.size).map state.repr).length <= x := by
        simp [List.length_range]
        omega
      have hnone : (ofState state).parent? x = none := by
        simpa [ofState, parent?] using
          (List.getElem?_eq_none hle :
            ((List.range state.size).map state.repr)[x]? = none)
      rw [hnone] at hparent
      cases hparent
  bounded_depth := by
    intro x hxForest
    have hx : state.valid x := by
      simpa [ofState, size] using hxForest
    have hreprValid : (ofState state).valid (state.repr x) := by
      simpa [ofState, size] using state.repr_lt hx
    have hrootParent :=
      ofState_parent?_eq_some_of_valid state (state.repr_lt hx)
    have hidem := hidempotent hx
    have hroot : (ofState state).IsRoot (state.repr x) := by
      simpa [IsRoot, hidem] using hrootParent
    exact ⟨state.repr x,
      ofState_findRootFuel?_eq_some_of_valid state hidempotent hx,
      hreprValid,
      hroot⟩

theorem ofState_toState_find?_eq
    (state : State)
    (hidempotent :
      forall {x : Nat}, state.valid x ->
        state.repr (state.repr x) = state.repr x)
    (x : Nat) :
    ((ofState state).toState
      (ofState_invariant state hidempotent)).find? x =
      state.find? x := by
  rw [(ofState state).toState_find?_eq_findRoot?
    (ofState_invariant state hidempotent) x]
  by_cases hx : state.valid x
  · have hfind :=
      ofState_findRoot?_eq_some_of_valid state hidempotent hx
    simp [State.find?, hx, hfind]
  · have hxForest : Not ((ofState state).valid x) := by
      simpa [ofState, size] using hx
    simp [State.find?, hx, findRoot?, ofState_size]

theorem unionSpec_repr_idempotent
    (state : State)
    (hidempotent :
      forall {i : Nat}, state.valid i ->
        state.repr (state.repr i) = state.repr i)
    (x y : Nat) {i : Nat}
    (hi : (state.unionSpec x y).valid i) :
    (state.unionSpec x y).repr ((state.unionSpec x y).repr i) =
      (state.unionSpec x y).repr i := by
  have hiOld : state.valid i := by
    simpa [State.unionSpec_valid_iff] using hi
  change
    State.mergeRepr state x y (State.mergeRepr state x y i) =
      State.mergeRepr state x y i
  unfold State.mergeRepr
  by_cases hxy : state.valid x /\ state.valid y
  · have hxIdem := hidempotent hxy.1
    have hyIdem := hidempotent hxy.2
    have hiIdem := hidempotent hiOld
    by_cases hiy : state.repr i = state.repr y
    · by_cases hxyRepr : state.repr x = state.repr y
      · simp [hxy, hiy, hyIdem, hxyRepr]
      · simp [hxy, hiy, hxIdem, hxyRepr]
    · simp [hxy, hiy, hiIdem]
  · simp [hxy, hidempotent hiOld]

/-- Concrete forest union by direct-parent rebuilding from the abstract
`State.unionSpec`.  This is the first executable refinement checkpoint for
union; rank heuristics and in-place root linking come later. -/
def union
    (forest : ParentForest) (h : forest.Invariant) (x y : Nat) :
    ParentForest :=
  ofState ((forest.toState h).unionSpec x y)

theorem union_invariant
    (forest : ParentForest) (h : forest.Invariant) (x y : Nat) :
    (forest.union h x y).Invariant := by
  unfold union
  apply ofState_invariant
  intro i hi
  exact unionSpec_repr_idempotent (forest.toState h)
    (fun {j} hj => forest.toState_repr_idempotent h hj) x y hi

theorem union_toState_find?_eq_unionSpec_find?
    (forest : ParentForest) (h : forest.Invariant) (x y i : Nat) :
    ((forest.union h x y).toState
      (forest.union_invariant h x y)).find? i =
      ((forest.toState h).unionSpec x y).find? i := by
  unfold union union_invariant
  exact ofState_toState_find?_eq ((forest.toState h).unionSpec x y)
    (fun {i} hi =>
      unionSpec_repr_idempotent (forest.toState h)
        (fun {j} hj => forest.toState_repr_idempotent h hj) x y hi)
    i

theorem union_findRoot?_eq_unionSpec_find?
    (forest : ParentForest) (h : forest.Invariant) (x y i : Nat) :
    (forest.union h x y).findRoot? i =
      ((forest.toState h).unionSpec x y).find? i := by
  rw [← (forest.union h x y).toState_find?_eq_findRoot?
    (forest.union_invariant h x y) i]
  exact forest.union_toState_find?_eq_unionSpec_find? h x y i

theorem union_profile
    (forest : ParentForest) (h : forest.Invariant) (x y : Nat) :
    (forest.union h x y).Invariant /\
      (forall i,
        ((forest.union h x y).toState
          (forest.union_invariant h x y)).find? i =
          ((forest.toState h).unionSpec x y).find? i) /\
      (forall i,
        (forest.union h x y).findRoot? i =
          ((forest.toState h).unionSpec x y).find? i) := by
  constructor
  · exact forest.union_invariant h x y
  · constructor
    · intro i
      exact forest.union_toState_find?_eq_unionSpec_find? h x y i
    · intro i
      exact forest.union_findRoot?_eq_unionSpec_find? h x y i

end ParentForest

/--
Public checkpoint for the parent-pointer forest layer.

The first conjunct is the refinement theorem: abstract `State.find?` over the
adapted state agrees with executable forest root search.  The remaining
conjuncts expose the bounded-depth/root totality and parent-bound facts that a
future union-by-rank or path-compression layer should preserve.
-/
theorem parentForestRefinement_profile
    (forest : ParentForest) (h : forest.Invariant) :
    (forall x, (forest.toState h).find? x = forest.findRoot? x) /\
      (forall {x : Nat}, forest.valid x ->
        exists r, forest.findRoot? x = some r /\ forest.valid r /\
          forest.IsRoot r) /\
      (forall {x parent : Nat}, forest.parent? x = some parent ->
        parent < forest.size) := by
  constructor
  · intro x
    exact forest.toState_find?_eq_findRoot? h x
  · constructor
    · intro x hx
      exact forest.findRoot?_total_of_valid h hx
    · intro x parent hparent
      exact h.parent_lt hparent


end Forest

end UnionFind

end VerifiedDS
