import RMQ.Core.UnionFind

/-!
# Parent-pointer forests for union-find

This module adds the first concrete representation layer below the abstract
`UnionFind.State` partition specification.  A `ParentForest` stores parent
pointers in a finite list, `findRoot?` follows those pointers with a bounded
fuel budget, and `ParentForest.Invariant` packages the root/bounded-depth facts
needed to adapt the forest back to the abstract representative state.
-/

namespace RMQ

namespace UnionFind

namespace Forest

/-- A finite parent-pointer forest.  Node `x` is represented by
`parents.get? x`; roots are self-parent pointers. -/
structure ParentForest where
  parents : List Nat

namespace ParentForest

def size (forest : ParentForest) : Nat :=
  forest.parents.length

abbrev valid (forest : ParentForest) (x : Nat) : Prop :=
  x < forest.size

def parent? (forest : ParentForest) (x : Nat) : Option Nat :=
  forest.parents[x]?

def IsRoot (forest : ParentForest) (x : Nat) : Prop :=
  forest.parent? x = some x

theorem valid_of_parent?_eq_some
    (forest : ParentForest) {x parent : Nat}
    (hparent : forest.parent? x = some parent) :
    forest.valid x := by
  by_cases hx : forest.valid x
  · exact hx
  · have hle : forest.parents.length <= x := by
      exact Nat.le_of_not_gt hx
    have hnone : forest.parent? x = none := by
      simpa [parent?] using
        (List.getElem?_eq_none hle :
          forest.parents[x]? = none)
    rw [hnone] at hparent
    cases hparent

theorem exists_parent?_of_valid
    (forest : ParentForest) {x : Nat}
    (hx : forest.valid x) :
    exists parent, forest.parent? x = some parent := by
  refine ⟨forest.parents[x], ?_⟩
  simp [parent?, List.getElem?_eq_getElem (l := forest.parents) hx]

/-- Follow parent pointers with explicit fuel. -/
def findRootFuel? (forest : ParentForest) : Nat -> Nat -> Option Nat
  | 0, _ => none
  | fuel + 1, x =>
      match forest.parent? x with
      | none => none
      | some parent =>
          if parent = x then
            some x
          else
            forest.findRootFuel? fuel parent

def maxSearchFuel (forest : ParentForest) : Nat :=
  forest.size + 1

/-- Executable root query for the forest representation.  Invalid nodes return
`none`; valid nodes are searched with a bounded fuel budget. -/
def findRoot? (forest : ParentForest) (x : Nat) : Option Nat :=
  if _hx : forest.valid x then
    forest.findRootFuel? forest.maxSearchFuel x
  else
    none

/-- `r` is the bounded root reached from `x` within `fuel` parent steps. -/
def ReachesRootWithin
    (forest : ParentForest) (fuel x r : Nat) : Prop :=
  forest.findRootFuel? fuel x = some r /\
    forest.valid r /\ forest.IsRoot r

/-- Every valid node reaches a valid self-parent root within the standard
`size + 1` fuel budget. -/
def BoundedDepth (forest : ParentForest) : Prop :=
  forall {x : Nat}, forest.valid x ->
    exists r, forest.ReachesRootWithin forest.maxSearchFuel x r

/--
Representation invariant for the first forest layer.

`parent_lt` keeps every stored parent pointer inside the finite node set, while
`bounded_depth` gives the totality certificate for `findRoot?` on valid nodes.
-/
structure Invariant (forest : ParentForest) : Prop where
  parent_lt :
    forall {x parent : Nat}, forest.parent? x = some parent ->
      parent < forest.size
  bounded_depth : forest.BoundedDepth

theorem findRoot?_eq_none_of_invalid
    (forest : ParentForest) {x : Nat}
    (hx : Not (forest.valid x)) :
    forest.findRoot? x = none := by
  simp [findRoot?, hx]

theorem findRoot?_eq_findRootFuel?_of_valid
    (forest : ParentForest) {x : Nat}
    (hx : forest.valid x) :
    forest.findRoot? x =
      forest.findRootFuel? forest.maxSearchFuel x := by
  simp [findRoot?, hx]

theorem findRoot?_total_of_valid
    (forest : ParentForest) (h : forest.Invariant) {x : Nat}
    (hx : forest.valid x) :
    exists r, forest.findRoot? x = some r /\ forest.valid r /\
      forest.IsRoot r := by
  rcases h.bounded_depth hx with ⟨r, hfind, hrvalid, hroot⟩
  refine ⟨r, ?_, hrvalid, hroot⟩
  simpa [findRoot?, hx] using hfind

theorem findRoot?_some_valid
    (forest : ParentForest) (h : forest.Invariant) {x r : Nat}
    (hfind : forest.findRoot? x = some r) :
    forest.valid r := by
  by_cases hx : forest.valid x
  · rcases forest.findRoot?_total_of_valid h hx with
      ⟨root, hrootFind, hrootValid, _hroot⟩
    rw [hfind] at hrootFind
    cases hrootFind
    exact hrootValid
  · simp [findRoot?, hx] at hfind

theorem findRoot?_some_root
    (forest : ParentForest) (h : forest.Invariant) {x r : Nat}
    (hfind : forest.findRoot? x = some r) :
    forest.IsRoot r := by
  by_cases hx : forest.valid x
  · rcases forest.findRoot?_total_of_valid h hx with
      ⟨root, hrootFind, _hrootValid, hroot⟩
    rw [hfind] at hrootFind
    cases hrootFind
    exact hroot
  · simp [findRoot?, hx] at hfind

theorem valid_of_findRoot?_eq_some
    (forest : ParentForest) {x r : Nat}
    (hfind : forest.findRoot? x = some r) :
    forest.valid x := by
  by_cases hx : forest.valid x
  · exact hx
  · simp [findRoot?, hx] at hfind

theorem invalid_of_findRoot?_eq_none
    (forest : ParentForest) (h : forest.Invariant) {x : Nat}
    (hfind : forest.findRoot? x = none) :
    Not (forest.valid x) := by
  intro hx
  rcases forest.findRoot?_total_of_valid h hx with
    ⟨root, hrootFind, _hrootValid, _hroot⟩
  rw [hfind] at hrootFind
  cases hrootFind

/-- Representative chosen by the concrete forest.  The fallback is unreachable
for valid nodes under `Invariant`, but keeps the function total on `Nat`. -/
def representative
    (forest : ParentForest) (_h : forest.Invariant) (x : Nat) : Nat :=
  (forest.findRoot? x).getD x

theorem representative_eq_of_findRoot?
    (forest : ParentForest) (h : forest.Invariant) {x r : Nat}
    (hfind : forest.findRoot? x = some r) :
    forest.representative h x = r := by
  simp [representative, hfind]

/-- Adapt an invariant parent-pointer forest to the abstract partition state. -/
def toState (forest : ParentForest) (h : forest.Invariant) : State where
  size := forest.size
  repr := forest.representative h
  repr_lt := by
    intro x hx
    rcases forest.findRoot?_total_of_valid h hx with
      ⟨root, hrootFind, hrootValid, _hroot⟩
    simpa [representative, hrootFind] using hrootValid

@[simp] theorem toState_size
    (forest : ParentForest) (h : forest.Invariant) :
    (forest.toState h).size = forest.size := by
  rfl

theorem toState_valid_iff
    (forest : ParentForest) (h : forest.Invariant) (x : Nat) :
    (forest.toState h).valid x <-> forest.valid x := by
  rfl

theorem toState_repr_eq_of_findRoot?
    (forest : ParentForest) (h : forest.Invariant) {x r : Nat}
    (hfind : forest.findRoot? x = some r) :
    (forest.toState h).repr x = r := by
  simpa [toState] using forest.representative_eq_of_findRoot? h hfind

theorem toState_find?_eq_findRoot?
    (forest : ParentForest) (h : forest.Invariant) (x : Nat) :
    (forest.toState h).find? x = forest.findRoot? x := by
  by_cases hx : forest.valid x
  · rcases forest.findRoot?_total_of_valid h hx with
      ⟨root, hrootFind, _hrootValid, _hroot⟩
    simp [State.find?, toState, representative, hx, hrootFind]
  · simp [State.find?, toState, findRoot?, hx]

theorem findRoot?_refines_State_find?
    (forest : ParentForest) (h : forest.Invariant) (x : Nat) :
    forest.findRoot? x = (forest.toState h).find? x := by
  exact (forest.toState_find?_eq_findRoot? h x).symm

theorem toState_samePartition_of_invariants
    (forest : ParentForest) (hleft hright : forest.Invariant) :
    State.SamePartition (forest.toState hleft) (forest.toState hright) := by
  apply State.samePartition_of_find?_eq
  intro i
  rw [forest.toState_find?_eq_findRoot? hleft i]

theorem findRootFuel?_eq_some_of_root
    (forest : ParentForest) {fuel x : Nat}
    (hfuel : 0 < fuel) (hroot : forest.IsRoot x) :
    forest.findRootFuel? fuel x = some x := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      unfold IsRoot at hroot
      simp [findRootFuel?, hroot]

theorem findRoot?_eq_some_of_root
    (forest : ParentForest) {x : Nat}
    (hx : forest.valid x) (hroot : forest.IsRoot x) :
    forest.findRoot? x = some x := by
  have hfuel : 0 < forest.maxSearchFuel := by
    simp [maxSearchFuel]
  simpa [findRoot?, hx] using
    forest.findRootFuel?_eq_some_of_root hfuel hroot

theorem toState_repr_idempotent
    (forest : ParentForest) (h : forest.Invariant) {x : Nat}
    (hx : (forest.toState h).valid x) :
    (forest.toState h).repr ((forest.toState h).repr x) =
      (forest.toState h).repr x := by
  have hxForest : forest.valid x := by
    simpa [toState] using hx
  rcases forest.findRoot?_total_of_valid h hxForest with
    ⟨root, hfind, hrootValid, hroot⟩
  have hreprx :
      (forest.toState h).repr x = root :=
    forest.toState_repr_eq_of_findRoot? h hfind
  have hrootFind : forest.findRoot? root = some root :=
    forest.findRoot?_eq_some_of_root hrootValid hroot
  have hreprRoot :
      (forest.toState h).repr root = root :=
    forest.toState_repr_eq_of_findRoot? h hrootFind
  rw [hreprx]
  exact hreprRoot

/--
Strengthened invariant for root-link proofs.  The extra `strict_depth` field
records that every valid node reaches a root with one unit of fuel left; after
linking one root below another, the ordinary `Invariant` fuel budget still
suffices.
-/
structure LinkableInvariant (forest : ParentForest) extends Invariant forest where
  strict_depth :
    forall {x : Nat}, forest.valid x ->
      exists r, forest.findRootFuel? forest.size x = some r /\
        forest.valid r /\ forest.IsRoot r

theorem findRootFuel?_succ_eq_some_of_eq_some
    (forest : ParentForest) {fuel x r : Nat}
    (hfind : forest.findRootFuel? fuel x = some r) :
    forest.findRootFuel? (fuel + 1) x = some r := by
  induction fuel generalizing x with
  | zero =>
      simp [findRootFuel?] at hfind
  | succ fuel ih =>
      unfold findRootFuel? at hfind ⊢
      cases hparent : forest.parent? x with
      | none =>
          simp [hparent] at hfind
      | some parent =>
          by_cases hsame : parent = x
          · simp [hparent, hsame] at hfind ⊢
            exact hfind
          · simp [hparent, hsame] at hfind ⊢
            exact ih hfind

theorem findRootFuel?_eq_some_of_le
    (forest : ParentForest) {small large x r : Nat}
    (hfind : forest.findRootFuel? small x = some r)
    (hle : small <= large) :
    forest.findRootFuel? large x = some r := by
  induction hle with
  | refl =>
      exact hfind
  | @step large hle ih =>
      exact forest.findRootFuel?_succ_eq_some_of_eq_some ih

theorem findRootFuel?_eq_some_unique
    (forest : ParentForest) :
    forall {fuelLeft fuelRight x rootLeft rootRight : Nat},
      forest.findRootFuel? fuelLeft x = some rootLeft ->
      forest.findRootFuel? fuelRight x = some rootRight ->
      rootLeft = rootRight := by
  intro fuelLeft
  induction fuelLeft with
  | zero =>
      intro fuelRight x rootLeft rootRight hleft _hright
      simp [findRootFuel?] at hleft
  | succ fuelLeft ih =>
      intro fuelRight x rootLeft rootRight hleft hright
      cases fuelRight with
      | zero =>
          simp [findRootFuel?] at hright
      | succ fuelRight =>
          unfold findRootFuel? at hleft hright
          cases hparent : forest.parent? x with
          | none =>
              simp [hparent] at hleft
          | some parent =>
              by_cases hsame : parent = x
              · simp [hparent, hsame] at hleft hright
                cases hleft
                cases hright
                rfl
              · simp [hparent, hsame] at hleft hright
                exact ih hleft hright

theorem findRoot?_eq_some_of_strict_depth
    (forest : ParentForest) (_h : forest.LinkableInvariant) {x r : Nat}
    (hx : forest.valid x)
    (hfind : forest.findRootFuel? forest.size x = some r) :
    forest.findRoot? x = some r := by
  have hsucc :=
    forest.findRootFuel?_succ_eq_some_of_eq_some hfind
  simpa [findRoot?, maxSearchFuel, hx] using hsucc

/--
Proof-only rank certificate for parent forests.

Every non-root parent edge must strictly increase `rank`, and all valid ranks
are bounded by the forest size. This gives a well-founded path fact strong
enough to rebuild `LinkableInvariant` after rank-respecting root links.
-/
structure RankInvariant (forest : ParentForest) (rank : Nat -> Nat)
    extends Invariant forest where
  rank_lt_size :
    forall {x : Nat}, forest.valid x -> rank x < forest.size
  parent_rank_lt :
    forall {x parent : Nat}, forest.parent? x = some parent ->
      parent ≠ x -> rank x < rank parent

/--
Proof-only rank-size certificate for the first union-by-rank boundary.

The extra field is the theorem-shaped projection of the future component-size
argument: two distinct equal-rank root components leave enough ambient node
budget to bump one of the roots without violating `rank_lt_size`.
-/
structure RankSizeInvariant (forest : ParentForest) (rank : Nat -> Nat)
    extends RankInvariant forest rank where
  equal_rank_root_bump_lt :
    forall {rootX rootY : Nat},
      forest.valid rootX -> forest.valid rootY ->
      forest.IsRoot rootX -> forest.IsRoot rootY ->
      rootY ≠ rootX -> rank rootX = rank rootY ->
      rank rootX + 1 < forest.size

/--
Proof-only component-cardinality checkpoint for preserving `RankSizeInvariant`.

The extra field is the local cardinality consequence needed after merging two
equal-rank components: if two distinct roots have rank `k` and a third
distinct root already has rank `k + 1`, then the finite forest has enough room
for the merged root's bumped rank to coexist with that third component.
-/
structure RankComponentInvariant
    (forest : ParentForest) (rank : Nat -> Nat)
    extends RankSizeInvariant forest rank where
  equal_pair_next_rank_bump_lt :
    forall {rootX rootY rootZ : Nat},
      forest.valid rootX -> forest.valid rootY -> forest.valid rootZ ->
      forest.IsRoot rootX -> forest.IsRoot rootY -> forest.IsRoot rootZ ->
      rootY ≠ rootX -> rootZ ≠ rootX -> rootZ ≠ rootY ->
      rank rootX = rank rootY -> rank rootZ = rank rootX + 1 ->
      rank rootX + 2 < forest.size

/-- Sum an executable root-mass map over a finite list of roots. -/
def rootMassSum (mass : Nat -> Nat) : List Nat -> Nat
  | [] => 0
  | root :: roots => mass root + rootMassSum mass roots

/--
Executable root-mass accounting.

`rootMassInvariant` deliberately quantifies over arbitrary duplicate-free root
lists rather than over fixed pairs/triples. This is the finite-list version of
the disjoint component-size argument needed to avoid the fixed-arity
obstruction hit by `RankComponentInvariant`.
-/
structure RootMassInvariant
    (forest : ParentForest) (rank mass : Nat -> Nat)
    extends RankInvariant forest rank where
  root_mass_pos :
    forall {root : Nat}, forest.valid root -> forest.IsRoot root ->
      0 < mass root
  rank_lt_mass :
    forall {root : Nat}, forest.valid root -> forest.IsRoot root ->
      rank root < mass root
  rootMassSum_le_size :
    forall {roots : List Nat}, roots.Nodup ->
      (forall {root : Nat}, root ∈ roots ->
        forest.valid root /\ forest.IsRoot root) ->
      rootMassSum mass roots <= forest.size

/--
Stronger union-by-rank component-size accounting.

For every valid root, the executable mass of that component is at least
`2 ^ rank root`. This is the first exponential-size fact needed before a
classical logarithmic rank bound or Tarjan-style potential can be stated.
-/
structure RankPowerMassInvariant
    (forest : ParentForest) (rank mass : Nat -> Nat)
    extends RootMassInvariant forest rank mass where
  rank_power_le_mass :
    forall {root : Nat}, forest.valid root -> forest.IsRoot root ->
      2 ^ rank root <= mass root

theorem RootMassInvariant.root_mass_le_size
    {forest : ParentForest} {rank mass : Nat -> Nat}
    (h : forest.RootMassInvariant rank mass)
    {root : Nat} (hvalid : forest.valid root) (hroot : forest.IsRoot root) :
    mass root <= forest.size := by
  have hnodup : [root].Nodup := by
    simp
  have hroots :
      forall {oldRoot : Nat}, oldRoot ∈ [root] ->
        forest.valid oldRoot /\ forest.IsRoot oldRoot := by
    intro oldRoot hmem
    simp at hmem
    subst oldRoot
    exact ⟨hvalid, hroot⟩
  have hsum := h.rootMassSum_le_size hnodup hroots
  simpa [rootMassSum] using hsum

theorem RankPowerMassInvariant.rank_power_le_size
    {forest : ParentForest} {rank mass : Nat -> Nat}
    (h : forest.RankPowerMassInvariant rank mass)
    {root : Nat} (hvalid : forest.valid root) (hroot : forest.IsRoot root) :
    2 ^ rank root <= forest.size := by
  exact Nat.le_trans
    (h.rank_power_le_mass hvalid hroot)
    (h.toRootMassInvariant.root_mass_le_size hvalid hroot)

theorem RankPowerMassInvariant.rank_le_log2_mass
    {forest : ParentForest} {rank mass : Nat -> Nat}
    (h : forest.RankPowerMassInvariant rank mass)
    {root : Nat} (hvalid : forest.valid root) (hroot : forest.IsRoot root) :
    rank root <= Nat.log2 (mass root) := by
  have hmassPos := h.root_mass_pos hvalid hroot
  have hmassNe : mass root ≠ 0 := by
    omega
  exact (Nat.le_log2 hmassNe).mpr
    (h.rank_power_le_mass hvalid hroot)

theorem RankPowerMassInvariant.rank_le_log2_size
    {forest : ParentForest} {rank mass : Nat -> Nat}
    (h : forest.RankPowerMassInvariant rank mass)
    {root : Nat} (hvalid : forest.valid root) (hroot : forest.IsRoot root) :
    rank root <= Nat.log2 forest.size := by
  have hsizeNe : forest.size ≠ 0 := by
    omega
  exact (Nat.le_log2 hsizeNe).mpr
    (h.rank_power_le_size hvalid hroot)

theorem RankSizeInvariant.bump_lt_of_findRoot?
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankSizeInvariant rank)
    {x y rootX rootY : Nat}
    (hxFind : forest.findRoot? x = some rootX)
    (hyFind : forest.findRoot? y = some rootY)
    (hne : rootY ≠ rootX)
    (hrankEq : rank rootX = rank rootY) :
    rank rootX + 1 < forest.size := by
  exact h.equal_rank_root_bump_lt
    (forest.findRoot?_some_valid h.toInvariant hxFind)
    (forest.findRoot?_some_valid h.toInvariant hyFind)
    (forest.findRoot?_some_root h.toInvariant hxFind)
    (forest.findRoot?_some_root h.toInvariant hyFind)
    hne hrankEq

theorem findRootFuel?_ranked_aux
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank) :
    forall budget : Nat,
      (forall smaller : Nat, smaller < budget ->
        forall {x : Nat}, forest.valid x ->
          forest.size - rank x = smaller ->
            exists r, forest.findRootFuel? smaller x = some r /\
              forest.valid r /\ forest.IsRoot r) ->
      forall {x : Nat}, forest.valid x ->
        forest.size - rank x = budget ->
          exists r, forest.findRootFuel? budget x = some r /\
            forest.valid r /\ forest.IsRoot r := by
  intro budget ih x hx hbudget
  have hbudget_pos : 0 < budget := by
    have hrank := h.rank_lt_size hx
    omega
  cases budget with
  | zero =>
      omega
  | succ fuel =>
      rcases forest.exists_parent?_of_valid hx with ⟨parent, hparent⟩
      by_cases hsame : parent = x
      · refine ⟨x, ?_, hx, ?_⟩
        · simp [findRootFuel?, hparent, hsame]
        · simpa [IsRoot, hsame] using hparent
      · have hparentValid : forest.valid parent := h.parent_lt hparent
        have hrankStep : rank x < rank parent :=
          h.parent_rank_lt hparent hsame
        have hparentBudgetLt :
            forest.size - rank parent < fuel + 1 := by
          have hxrank := h.rank_lt_size hx
          have hprank := h.rank_lt_size hparentValid
          omega
        rcases ih (forest.size - rank parent) hparentBudgetLt
            hparentValid rfl with ⟨root, hfindParent, hrootValid, hroot⟩
        have hparentBudgetLeFuel :
            forest.size - rank parent <= fuel := by
          omega
        have hfindParentFuel :
            forest.findRootFuel? fuel parent = some root :=
          forest.findRootFuel?_eq_some_of_le hfindParent
            hparentBudgetLeFuel
        refine ⟨root, ?_, hrootValid, hroot⟩
        simp [findRootFuel?, hparent, hsame, hfindParentFuel]

theorem findRootFuel?_ranked
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank) {x : Nat}
    (hx : forest.valid x) :
    exists r, forest.findRootFuel? (forest.size - rank x) x = some r /\
      forest.valid r /\ forest.IsRoot r := by
  let motive : Nat -> Prop := fun budget =>
    forall {x : Nat}, forest.valid x ->
      forest.size - rank x = budget ->
        exists r, forest.findRootFuel? budget x = some r /\
          forest.valid r /\ forest.IsRoot r
  have hmain : motive (forest.size - rank x) :=
    Nat.strongRecOn (motive := motive) (forest.size - rank x)
      (fun budget ih =>
        forest.findRootFuel?_ranked_aux rank h budget ih)
  exact hmain hx rfl

theorem findRootFuel?_rank_lt_of_ne
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank) :
    forall {fuel x root : Nat},
      forest.findRootFuel? fuel x = some root ->
      x ≠ root -> rank x < rank root := by
  intro fuel
  induction fuel with
  | zero =>
      intro x root hfind _hne
      simp [findRootFuel?] at hfind
  | succ fuel ih =>
      intro x root hfind hne
      unfold findRootFuel? at hfind
      cases hparent : forest.parent? x with
      | none =>
          simp [hparent] at hfind
      | some parent =>
          by_cases hsame : parent = x
          · simp [hparent, hsame] at hfind
            cases hfind
            exact False.elim (hne rfl)
          · simp [hparent, hsame] at hfind
            have hxParentRank : rank x < rank parent :=
              h.parent_rank_lt hparent hsame
            by_cases hparentRoot : parent = root
            · subst hparentRoot
              exact hxParentRank
            · have hparentRootRank : rank parent < rank root :=
                ih hfind hparentRoot
              omega

theorem findRoot?_rank_lt_of_ne
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank)
    {x root : Nat}
    (hfind : forest.findRoot? x = some root)
    (hne : x ≠ root) :
    rank x < rank root := by
  have hx : forest.valid x :=
    forest.valid_of_findRoot?_eq_some hfind
  have hfuel :
      forest.findRootFuel? forest.maxSearchFuel x = some root := by
    simpa [findRoot?, hx] using hfind
  exact forest.findRootFuel?_rank_lt_of_ne rank h hfuel hne

/-- Bare rank-recursion helper used to build fresh `RankInvariant` witnesses
after parent-pointer rewrites. -/
theorem findRootFuel?_ranked_aux_of_parent_rank
    (forest : ParentForest) (rank : Nat -> Nat)
    (hparent_lt :
      forall {x parent : Nat}, forest.parent? x = some parent ->
        parent < forest.size)
    (hrank_lt_size :
      forall {x : Nat}, forest.valid x -> rank x < forest.size)
    (hparent_rank_lt :
      forall {x parent : Nat}, forest.parent? x = some parent ->
        parent ≠ x -> rank x < rank parent) :
    forall budget : Nat,
      (forall smaller : Nat, smaller < budget ->
        forall {x : Nat}, forest.valid x ->
          forest.size - rank x = smaller ->
            exists r, forest.findRootFuel? smaller x = some r /\
              forest.valid r /\ forest.IsRoot r) ->
      forall {x : Nat}, forest.valid x ->
        forest.size - rank x = budget ->
          exists r, forest.findRootFuel? budget x = some r /\
            forest.valid r /\ forest.IsRoot r := by
  intro budget ih x hx hbudget
  have hbudget_pos : 0 < budget := by
    have hrank := hrank_lt_size hx
    omega
  cases budget with
  | zero =>
      omega
  | succ fuel =>
      rcases forest.exists_parent?_of_valid hx with ⟨parent, hparent⟩
      by_cases hsame : parent = x
      · refine ⟨x, ?_, hx, ?_⟩
        · simp [findRootFuel?, hparent, hsame]
        · simpa [IsRoot, hsame] using hparent
      · have hparentValid : forest.valid parent := hparent_lt hparent
        have hrankStep : rank x < rank parent :=
          hparent_rank_lt hparent hsame
        have hparentBudgetLt :
            forest.size - rank parent < fuel + 1 := by
          have hxrank := hrank_lt_size hx
          have hprank := hrank_lt_size hparentValid
          omega
        rcases ih (forest.size - rank parent) hparentBudgetLt
            hparentValid rfl with ⟨root, hfindParent, hrootValid, hroot⟩
        have hparentBudgetLeFuel :
            forest.size - rank parent <= fuel := by
          omega
        have hfindParentFuel :
            forest.findRootFuel? fuel parent = some root :=
          forest.findRootFuel?_eq_some_of_le hfindParent
            hparentBudgetLeFuel
        refine ⟨root, ?_, hrootValid, hroot⟩
        simp [findRootFuel?, hparent, hsame, hfindParentFuel]

theorem findRootFuel?_ranked_of_parent_rank
    (forest : ParentForest) (rank : Nat -> Nat)
    (hparent_lt :
      forall {x parent : Nat}, forest.parent? x = some parent ->
        parent < forest.size)
    (hrank_lt_size :
      forall {x : Nat}, forest.valid x -> rank x < forest.size)
    (hparent_rank_lt :
      forall {x parent : Nat}, forest.parent? x = some parent ->
        parent ≠ x -> rank x < rank parent)
    {x : Nat} (hx : forest.valid x) :
    exists r, forest.findRootFuel? (forest.size - rank x) x = some r /\
      forest.valid r /\ forest.IsRoot r := by
  let motive : Nat -> Prop := fun budget =>
    forall {x : Nat}, forest.valid x ->
      forest.size - rank x = budget ->
        exists r, forest.findRootFuel? budget x = some r /\
          forest.valid r /\ forest.IsRoot r
  have hmain : motive (forest.size - rank x) :=
    Nat.strongRecOn (motive := motive) (forest.size - rank x)
      (fun budget ih =>
        forest.findRootFuel?_ranked_aux_of_parent_rank rank
          hparent_lt hrank_lt_size hparent_rank_lt budget ih)
  exact hmain hx rfl

theorem rankInvariant_of_parent_rank
    (forest : ParentForest) (rank : Nat -> Nat)
    (hparent_lt :
      forall {x parent : Nat}, forest.parent? x = some parent ->
        parent < forest.size)
    (hrank_lt_size :
      forall {x : Nat}, forest.valid x -> rank x < forest.size)
    (hparent_rank_lt :
      forall {x parent : Nat}, forest.parent? x = some parent ->
        parent ≠ x -> rank x < rank parent) :
    forest.RankInvariant rank where
  toInvariant := by
    refine ⟨hparent_lt, ?_⟩
    intro x hx
    rcases forest.findRootFuel?_ranked_of_parent_rank rank
        hparent_lt hrank_lt_size hparent_rank_lt hx with
      ⟨root, hfind, hrootValid, hroot⟩
    have hbudgetLe : forest.size - rank x <= forest.maxSearchFuel := by
      simp [maxSearchFuel]
      omega
    refine ⟨root, ?_, hrootValid, hroot⟩
    exact forest.findRootFuel?_eq_some_of_le hfind hbudgetLe
  rank_lt_size := hrank_lt_size
  parent_rank_lt := hparent_rank_lt

theorem rankInvariant_linkable
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank) :
    forest.LinkableInvariant where
  toInvariant := h.toInvariant
  strict_depth := by
    intro x hx
    rcases forest.findRootFuel?_ranked rank h hx with
      ⟨root, hfind, hrootValid, hroot⟩
    have hbudgetLe : forest.size - rank x <= forest.size := by
      omega
    refine ⟨root, ?_, hrootValid, hroot⟩
    exact forest.findRootFuel?_eq_some_of_le hfind hbudgetLe

/-- Override one root pointer.  Semantically this changes only `fromRoot`'s
parent to `toRoot`; all other valid parent cells keep their old value. -/
def rootLink (forest : ParentForest) (fromRoot toRoot : Nat) :
    ParentForest where
  parents :=
    (List.range forest.size).map fun i =>
      if i = fromRoot then toRoot else (forest.parent? i).getD i

/-- Redirect one node's parent to a known root.  This is the local rewrite used
by the first path-compression `find`: unlike `rootLink`, the rewritten node
need not itself be a root, so the represented partition should not change. -/
def compressNode (forest : ParentForest) (node root : Nat) :
    ParentForest :=
  forest.rootLink node root

def bumpRank (rank : Nat -> Nat) (root : Nat) : Nat -> Nat :=
  fun i => if i = root then rank i + 1 else rank i

def rootMassAfterLink
    (mass : Nat -> Nat) (fromRoot toRoot : Nat) : Nat -> Nat :=
  fun i =>
    if i = toRoot then
      mass toRoot + mass fromRoot
    else if i = fromRoot then
      0
    else
      mass i

def rankedRootLink
    (forest : ParentForest) (rank : Nat -> Nat)
    (rootX rootY : Nat) : ParentForest :=
  if rank rootX < rank rootY then
    forest.rootLink rootX rootY
  else
    forest.rootLink rootY rootX

def rankAfterRootLinkByRank
    (rank : Nat -> Nat) (rootX rootY : Nat) : Nat -> Nat :=
  if rank rootX < rank rootY then
    rank
  else if rank rootY < rank rootX then
    rank
  else
    bumpRank rank rootX

def rootMassAfterRootLinkByRank
    (rank mass : Nat -> Nat) (rootX rootY : Nat) : Nat -> Nat :=
  if rank rootX < rank rootY then
    rootMassAfterLink mass rootX rootY
  else
    rootMassAfterLink mass rootY rootX

def unionByRank
    (forest : ParentForest) (rank : Nat -> Nat) (x y : Nat) :
    ParentForest :=
  match forest.findRoot? x, forest.findRoot? y with
  | some rootX, some rootY =>
      if rootY = rootX then
        forest
      else
        forest.rankedRootLink rank rootX rootY
  | _, _ => forest

def rankAfterUnionByRank
    (forest : ParentForest) (rank : Nat -> Nat) (x y : Nat) :
    Nat -> Nat :=
  match forest.findRoot? x, forest.findRoot? y with
  | some rootX, some rootY =>
      if rootY = rootX then
        rank
      else
        rankAfterRootLinkByRank rank rootX rootY
  | _, _ => rank

def rootMassAfterUnionByRank
    (forest : ParentForest) (rank mass : Nat -> Nat) (x y : Nat) :
    Nat -> Nat :=
  match forest.findRoot? x, forest.findRoot? y with
  | some rootX, some rootY =>
      if rootY = rootX then
        mass
      else
        rootMassAfterRootLinkByRank rank mass rootX rootY
  | _, _ => mass

@[simp] theorem rootLink_size
    (forest : ParentForest) (fromRoot toRoot : Nat) :
    (forest.rootLink fromRoot toRoot).size = forest.size := by
  simp [rootLink, size]

@[simp] theorem rankedRootLink_size
    (forest : ParentForest) (rank : Nat -> Nat) (rootX rootY : Nat) :
    (forest.rankedRootLink rank rootX rootY).size = forest.size := by
  unfold rankedRootLink
  split <;> simp

@[simp] theorem unionByRank_size
    (forest : ParentForest) (rank : Nat -> Nat) (x y : Nat) :
    (forest.unionByRank rank x y).size = forest.size := by
  unfold unionByRank
  cases hx : forest.findRoot? x with
  | none =>
      simp
  | some rootX =>
      cases hy : forest.findRoot? y with
      | none =>
          simp
      | some rootY =>
          by_cases hsame : rootY = rootX
          · simp [hsame]
          · simp [hsame]

theorem rootMassSum_afterLink_eq_of_not_mem
    (mass : Nat -> Nat) {fromRoot toRoot : Nat} :
    forall {roots : List Nat},
      fromRoot ∉ roots -> toRoot ∉ roots ->
        rootMassSum (rootMassAfterLink mass fromRoot toRoot) roots =
          rootMassSum mass roots
  | [], _hfrom, _hto => rfl
  | root :: roots, hfrom, hto => by
      have hroot_from : root ≠ fromRoot := by
        intro h
        exact hfrom (by simp [h])
      have hroots_from : fromRoot ∉ roots := by
        intro hmem
        exact hfrom (by simp [hmem])
      have hroot_to : root ≠ toRoot := by
        intro h
        exact hto (by simp [h])
      have hroots_to : toRoot ∉ roots := by
        intro hmem
        exact hto (by simp [hmem])
      have htail :=
        rootMassSum_afterLink_eq_of_not_mem mass
          (roots := roots) hroots_from hroots_to
      simp [rootMassSum, rootMassAfterLink, hroot_to, hroot_from, htail]

theorem rootMassSum_afterLink_eq_add_of_mem_to
    (mass : Nat -> Nat) {fromRoot toRoot : Nat} :
    forall {roots : List Nat}, roots.Nodup ->
      fromRoot ∉ roots -> toRoot ∈ roots ->
        rootMassSum (rootMassAfterLink mass fromRoot toRoot) roots =
          mass fromRoot + rootMassSum mass roots
  | [], _hnodup, _hfrom, hto => by
      simp at hto
  | root :: roots, hnodup, hfrom, hto => by
      have hnodup_cons := hnodup
      simp at hnodup_cons
      rcases hnodup_cons with ⟨hroot_not_mem, hnodup_tail⟩
      have hroot_not_mem : root ∉ roots := by
        exact hroot_not_mem
      have hnodup_tail : roots.Nodup := hnodup_tail
      have hroot_from : root ≠ fromRoot := by
        intro h
        exact hfrom (by simp [h])
      have hroots_from : fromRoot ∉ roots := by
        intro hmem
        exact hfrom (by simp [hmem])
      by_cases hroot_to : root = toRoot
      · subst hroot_to
        have hto_not_tail : root ∉ roots := hroot_not_mem
        have htail :=
          rootMassSum_afterLink_eq_of_not_mem mass
            (roots := roots) hroots_from hto_not_tail
        simp [rootMassSum, rootMassAfterLink, htail]
        omega
      · have hto_tail : toRoot ∈ roots := by
          have hcases : toRoot = root ∨ toRoot ∈ roots := by
            simpa using hto
          cases hcases with
          | inl hhead =>
              exact False.elim (hroot_to hhead.symm)
          | inr htail =>
              exact htail
        have htail :=
          rootMassSum_afterLink_eq_add_of_mem_to mass
            (roots := roots) hnodup_tail hroots_from hto_tail
        simp [rootMassSum, rootMassAfterLink, hroot_to, hroot_from, htail]
        omega

theorem rootMassSum_one_eq_length :
    forall roots : List Nat, rootMassSum (fun _ => 1) roots = roots.length
  | [] => rfl
  | _ :: roots => by
      simp [rootMassSum, rootMassSum_one_eq_length roots]
      omega

theorem nodup_length_le_of_forall_lt :
    forall (n : Nat) (roots : List Nat), roots.Nodup ->
      (forall {root : Nat}, root ∈ roots -> root < n) ->
      roots.length <= n
  | 0, roots, _hnodup, hbound => by
      cases roots with
      | nil =>
          simp
      | cons root roots =>
          have hlt : root < 0 := hbound (by simp)
          omega
  | n + 1, roots, hnodup, hbound => by
      by_cases hnmem : n ∈ roots
      · have hboundedErase :
            forall {root : Nat}, root ∈ roots.erase n -> root < n := by
          intro root hmem
          have hrootMem : root ∈ roots := List.mem_of_mem_erase hmem
          have hltSucc : root < n + 1 := hbound hrootMem
          have hne : root ≠ n := by
            intro hEq
            have hnNotMem : n ∉ roots.erase n :=
              hnodup.not_mem_erase
            exact hnNotMem (by simpa [hEq] using hmem)
          omega
        have hlenErase :=
          nodup_length_le_of_forall_lt n (roots.erase n)
            (hnodup.erase n) hboundedErase
        have hlenEq :
            (roots.erase n).length = roots.length - 1 :=
          List.length_erase_of_mem hnmem
        omega
      · have hbounded :
            forall {root : Nat}, root ∈ roots -> root < n := by
          intro root hmem
          have hltSucc : root < n + 1 := hbound hmem
          by_cases hroot : root = n
          · subst hroot
            exact False.elim (hnmem hmem)
          · omega
        have hlen :=
          nodup_length_le_of_forall_lt n roots hnodup hbounded
        omega

theorem RootMassInvariant.toRankSizeInvariant
    {forest : ParentForest} {rank mass : Nat -> Nat}
    (h : forest.RootMassInvariant rank mass) :
    forest.RankSizeInvariant rank where
  toRankInvariant := h.toRankInvariant
  equal_rank_root_bump_lt := by
    intro rootX rootY hxValid hyValid hrootX hrootY hne hrankEq
    have hxy : rootX ≠ rootY := by
      intro hEq
      exact hne hEq.symm
    have hnodup : [rootX, rootY].Nodup := by
      simp [hxy]
    have hroots :
        forall {root : Nat}, root ∈ [rootX, rootY] ->
          forest.valid root /\ forest.IsRoot root := by
      intro root hmem
      simp at hmem
      rcases hmem with hroot | hroot
      · subst hroot
        exact ⟨hxValid, hrootX⟩
      · subst hroot
        exact ⟨hyValid, hrootY⟩
    have hsum := h.rootMassSum_le_size hnodup hroots
    have hxMass := h.rank_lt_mass hxValid hrootX
    have hyPos := h.root_mass_pos hyValid hrootY
    simp [rootMassSum] at hsum
    omega

theorem RootMassInvariant.toRankComponentInvariant
    {forest : ParentForest} {rank mass : Nat -> Nat}
    (h : forest.RootMassInvariant rank mass) :
    forest.RankComponentInvariant rank where
  toRankSizeInvariant := h.toRankSizeInvariant
  equal_pair_next_rank_bump_lt := by
    intro rootX rootY rootZ hxValid hyValid hzValid
      hrootX hrootY hrootZ hneYX hneZX hneZY hrankEq hnext
    have hxy : rootX ≠ rootY := by
      intro hEq
      exact hneYX hEq.symm
    have hxz : rootX ≠ rootZ := by
      intro hEq
      exact hneZX hEq.symm
    have hyz : rootY ≠ rootZ := by
      intro hEq
      exact hneZY hEq.symm
    have hnodup : [rootX, rootY, rootZ].Nodup := by
      simp [hxy, hxz, hyz]
    have hroots :
        forall {root : Nat}, root ∈ [rootX, rootY, rootZ] ->
          forest.valid root /\ forest.IsRoot root := by
      intro root hmem
      simp at hmem
      rcases hmem with hroot | hroot | hroot
      · subst hroot
        exact ⟨hxValid, hrootX⟩
      · subst hroot
        exact ⟨hyValid, hrootY⟩
      · subst hroot
        exact ⟨hzValid, hrootZ⟩
    have hsum := h.rootMassSum_le_size hnodup hroots
    have hxMass := h.rank_lt_mass hxValid hrootX
    have hyMass := h.rank_lt_mass hyValid hrootY
    have hzMass := h.rank_lt_mass hzValid hrootZ
    simp [rootMassSum] at hsum
    omega

theorem rootLink_parent?_eq_some_of_valid
    (forest : ParentForest) {fromRoot toRoot i : Nat}
    (hi : forest.valid i) :
    (forest.rootLink fromRoot toRoot).parent? i =
      some (if i = fromRoot then toRoot else (forest.parent? i).getD i) := by
  have hrange : (List.range forest.size)[i]? = some i :=
    List.getElem?_range hi
  simp [rootLink, parent?, hrange]

theorem rootLink_parent?_eq_toRoot
    (forest : ParentForest) {fromRoot toRoot : Nat}
    (hfrom : forest.valid fromRoot) :
    (forest.rootLink fromRoot toRoot).parent? fromRoot = some toRoot := by
  simpa using
    forest.rootLink_parent?_eq_some_of_valid
      (fromRoot := fromRoot) (toRoot := toRoot) hfrom

theorem rootLink_parent?_eq_old_of_ne
    (forest : ParentForest) {fromRoot toRoot i parent : Nat}
    (hi : forest.valid i) (hne : i ≠ fromRoot)
    (hparent : forest.parent? i = some parent) :
    (forest.rootLink fromRoot toRoot).parent? i = some parent := by
  have hlink :=
    forest.rootLink_parent?_eq_some_of_valid
      (fromRoot := fromRoot) (toRoot := toRoot) hi
  simpa [hne, hparent] using hlink

theorem rootLink_isRoot_of_ne
    (forest : ParentForest) {fromRoot toRoot r : Nat}
    (hr : forest.valid r) (hne : r ≠ fromRoot)
    (hroot : forest.IsRoot r) :
    (forest.rootLink fromRoot toRoot).IsRoot r := by
  exact forest.rootLink_parent?_eq_old_of_ne
    (fromRoot := fromRoot) (toRoot := toRoot) hr hne hroot

@[simp] theorem compressNode_size
    (forest : ParentForest) (node root : Nat) :
    (forest.compressNode node root).size = forest.size := by
  simp [compressNode]

theorem compressNode_parent?_eq_root
    (forest : ParentForest) {node root : Nat}
    (hnode : forest.valid node) :
    (forest.compressNode node root).parent? node = some root := by
  simpa [compressNode] using
    forest.rootLink_parent?_eq_toRoot
      (fromRoot := node) (toRoot := root) hnode

theorem compressNode_parent?_eq_old_of_ne
    (forest : ParentForest) {node root i parent : Nat}
    (hi : forest.valid i) (hne : i ≠ node)
    (hparent : forest.parent? i = some parent) :
    (forest.compressNode node root).parent? i = some parent := by
  simpa [compressNode] using
    forest.rootLink_parent?_eq_old_of_ne
      (fromRoot := node) (toRoot := root) hi hne hparent

theorem compressNode_isRoot_of_old_root
    (forest : ParentForest) {node root : Nat}
    (hrootValid : forest.valid root) (hroot : forest.IsRoot root) :
    (forest.compressNode node root).IsRoot root := by
  by_cases hrootNode : root = node
  · subst hrootNode
    exact forest.compressNode_parent?_eq_root hrootValid
  · simpa [compressNode] using
      forest.rootLink_isRoot_of_ne
        (fromRoot := node) (toRoot := root) hrootValid hrootNode hroot

theorem old_isRoot_of_compressNode_isRoot
    (forest : ParentForest) {node root r : Nat}
    (hrootOld : forest.IsRoot root)
    (hr : (forest.compressNode node root).valid r)
    (hrootNew : (forest.compressNode node root).IsRoot r) :
    forest.valid r /\ forest.IsRoot r := by
  have hrOld : forest.valid r := by
    simpa [compressNode_size] using hr
  by_cases hrNode : r = node
  · subst hrNode
    have hnewParent :
        (forest.compressNode r root).parent? r = some root :=
      forest.compressNode_parent?_eq_root hrOld
    have hrootEq : root = r := by
      have hrootNewEq :
          (forest.compressNode r root).parent? r = some r := by
        simpa [IsRoot] using hrootNew
      rw [hnewParent] at hrootNewEq
      cases hrootNewEq
      rfl
    subst hrootEq
    exact ⟨hrOld, hrootOld⟩
  · rcases forest.exists_parent?_of_valid hrOld with ⟨oldParent, hparent⟩
    have hnewParent :
        (forest.compressNode node root).parent? r = some oldParent :=
      forest.compressNode_parent?_eq_old_of_ne hrOld hrNode hparent
    have hrootNewEq :
        (forest.compressNode node root).parent? r = some r := by
      simpa [IsRoot] using hrootNew
    rw [hnewParent] at hrootNewEq
    cases hrootNewEq
    exact ⟨hrOld, hparent⟩

theorem old_isRoot_of_rootLink_isRoot
    (forest : ParentForest) {fromRoot toRoot r : Nat}
    (hr : (forest.rootLink fromRoot toRoot).valid r)
    (hne : fromRoot ≠ toRoot)
    (hroot : (forest.rootLink fromRoot toRoot).IsRoot r) :
    forest.valid r /\ forest.IsRoot r /\ r ≠ fromRoot := by
  have hrOld : forest.valid r := by
    simpa [rootLink_size] using hr
  have hlink :=
    forest.rootLink_parent?_eq_some_of_valid
      (fromRoot := fromRoot) (toRoot := toRoot) hrOld
  have hrootEq :
      (forest.rootLink fromRoot toRoot).parent? r = some r := by
    simpa [IsRoot] using hroot
  by_cases hrFrom : r = fromRoot
  · rw [hlink] at hrootEq
    simp [hrFrom] at hrootEq
    cases hrootEq
    exact False.elim (hne rfl)
  · cases hOld : forest.parent? r with
    | none =>
        rcases forest.exists_parent?_of_valid hrOld with ⟨parent, hparent⟩
        rw [hOld] at hparent
        cases hparent
    | some oldParent =>
        rw [hlink] at hrootEq
        simp [hrFrom, hOld] at hrootEq
        cases hrootEq
        exact ⟨hrOld, hOld, hrFrom⟩

theorem compressNode_rankInvariant
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank)
    {node root : Nat}
    (hnodeValid : forest.valid node)
    (hrootValid : forest.valid root)
    (hrank : node ≠ root -> rank node < rank root) :
    (forest.compressNode node root).RankInvariant rank :=
  ParentForest.rankInvariant_of_parent_rank
    (forest.compressNode node root) rank
    (by
      intro i parent hparent
      change (forest.rootLink node root).parent? i = some parent at hparent
      by_cases hi : forest.valid i
      · have hlink :=
          forest.rootLink_parent?_eq_some_of_valid
            (fromRoot := node) (toRoot := root) hi
        by_cases hinode : i = node
        · subst hinode
          rw [hlink] at hparent
          simp at hparent
          cases hparent
          simpa [compressNode_size] using hrootValid
        · rcases hOld : forest.parent? i with _ | oldParent
          · rw [hlink] at hparent
            simp [hinode, hOld] at hparent
            cases hparent
            simpa [compressNode_size] using hi
          · rw [hlink] at hparent
            simp [hinode, hOld] at hparent
            cases hparent
            simpa [compressNode_size] using h.parent_lt hOld
      · have hle :
          ((forest.compressNode node root).parents).length <= i := by
          simpa [compressNode, rootLink, size] using Nat.le_of_not_gt hi
        have hnone :
            (forest.compressNode node root).parent? i = none := by
          simpa [parent?] using
            (List.getElem?_eq_none hle :
              (forest.compressNode node root).parents[i]? = none)
        have hnoneRootLink :
            (forest.rootLink node root).parent? i = none := by
          simpa [compressNode] using hnone
        rw [hnoneRootLink] at hparent
        cases hparent)
    (by
      intro i hi
      have hiOld : forest.valid i := by
        simpa [compressNode_size] using hi
      simpa [compressNode_size] using h.rank_lt_size hiOld)
    (by
      intro i parent hparent hneParent
      change (forest.rootLink node root).parent? i = some parent at hparent
      have hiNew : (forest.compressNode node root).valid i :=
        (forest.compressNode node root).valid_of_parent?_eq_some (by
          simpa [compressNode] using hparent)
      have hiOld : forest.valid i := by
        simpa [compressNode_size] using hiNew
      have hlink :=
        forest.rootLink_parent?_eq_some_of_valid
          (fromRoot := node) (toRoot := root) hiOld
      by_cases hinode : i = node
      · subst hinode
        rw [hlink] at hparent
        simp at hparent
        cases hparent
        exact hrank (by intro hEq; exact hneParent hEq.symm)
      · rcases hOld : forest.parent? i with _ | oldParent
        · rw [hlink] at hparent
          simp [hinode, hOld] at hparent
          cases hparent
          exact False.elim (hneParent rfl)
        · rw [hlink] at hparent
          simp [hinode, hOld] at hparent
          cases hparent
          exact h.parent_rank_lt hOld hneParent)

theorem compressNode_rootMassInvariant
    (forest : ParentForest) (rank mass : Nat -> Nat)
    (h : forest.RootMassInvariant rank mass)
    {node root : Nat}
    (hnodeValid : forest.valid node)
    (hrootValid : forest.valid root)
    (hroot : forest.IsRoot root)
    (hrank : node ≠ root -> rank node < rank root) :
    (forest.compressNode node root).RootMassInvariant rank mass where
  toRankInvariant :=
    forest.compressNode_rankInvariant rank h.toRankInvariant
      hnodeValid hrootValid hrank
  root_mass_pos := by
    intro r hvalidNew hrootNew
    rcases forest.old_isRoot_of_compressNode_isRoot hroot
        hvalidNew hrootNew with ⟨hvalidOld, hrootOld⟩
    exact h.root_mass_pos hvalidOld hrootOld
  rank_lt_mass := by
    intro r hvalidNew hrootNew
    rcases forest.old_isRoot_of_compressNode_isRoot hroot
        hvalidNew hrootNew with ⟨hvalidOld, hrootOld⟩
    exact h.rank_lt_mass hvalidOld hrootOld
  rootMassSum_le_size := by
    intro roots hnodup hrootsNew
    have hrootsOld :
        forall {root : Nat}, root ∈ roots ->
          forest.valid root /\ forest.IsRoot root := by
      intro oldRoot hmem
      exact forest.old_isRoot_of_compressNode_isRoot hroot
        (hrootsNew hmem).1 (hrootsNew hmem).2
    have hold := h.rootMassSum_le_size hnodup hrootsOld
    simpa [compressNode_size] using hold

theorem compressNode_rankPowerMassInvariant
    (forest : ParentForest) (rank mass : Nat -> Nat)
    (h : forest.RankPowerMassInvariant rank mass)
    {node root : Nat}
    (hnodeValid : forest.valid node)
    (hrootValid : forest.valid root)
    (hroot : forest.IsRoot root)
    (hrank : node ≠ root -> rank node < rank root) :
    (forest.compressNode node root).RankPowerMassInvariant rank mass where
  toRootMassInvariant :=
    forest.compressNode_rootMassInvariant rank mass h.toRootMassInvariant
      hnodeValid hrootValid hroot hrank
  rank_power_le_mass := by
    intro oldRoot hvalidNew hrootNew
    rcases forest.old_isRoot_of_compressNode_isRoot hroot
        hvalidNew hrootNew with ⟨hvalidOld, hrootOld⟩
    exact h.rank_power_le_mass hvalidOld hrootOld

theorem compressNode_findRootFuel?_eq_old_of_findRoot?
    (forest : ParentForest) (h : forest.Invariant)
    {node root fuel x r : Nat}
    (hnodeRoot : forest.findRoot? node = some root)
    (hfind : forest.findRootFuel? fuel x = some r) :
    (forest.compressNode node root).findRootFuel? (fuel + 1) x =
      some r := by
  have hnodeValid : forest.valid node :=
    forest.valid_of_findRoot?_eq_some hnodeRoot
  have hrootValid : forest.valid root :=
    forest.findRoot?_some_valid h hnodeRoot
  have hrootOld : forest.IsRoot root :=
    forest.findRoot?_some_root h hnodeRoot
  have hrootNew :
      (forest.compressNode node root).IsRoot root :=
    forest.compressNode_isRoot_of_old_root hrootValid hrootOld
  have hnodeRootFuel :
      forest.findRootFuel? forest.maxSearchFuel node = some root := by
    simpa [findRoot?, hnodeValid] using hnodeRoot
  induction fuel generalizing x r with
  | zero =>
      simp [findRootFuel?] at hfind
  | succ fuel ih =>
      have hfindOrig := hfind
      unfold findRootFuel? at hfind
      cases hparent : forest.parent? x with
      | none =>
          simp [hparent] at hfind
      | some parent =>
          by_cases hsame : parent = x
          · simp [hparent, hsame] at hfind
            cases hfind
            by_cases hxnode : x = node
            · have hxRootFuel :
                  forest.findRootFuel? forest.maxSearchFuel x =
                    some root := by
                simpa [hxnode] using hnodeRootFuel
              have hxEqRoot : x = root :=
                forest.findRootFuel?_eq_some_unique
                  hfindOrig hxRootFuel
              have hnewParent :
                  (forest.compressNode node root).parent? x =
                    some root :=
                by simpa [hxnode] using
                  forest.compressNode_parent?_eq_root
                    (node := node) (root := root) hnodeValid
              have hnewParentX :
                  (forest.compressNode node x).parent? x = some x := by
                simpa [hxEqRoot] using hnewParent
              have htarget :
                  (forest.compressNode node x).findRootFuel?
                    ((fuel + 1) + 1) x = some x := by
                simp [findRootFuel?, hnewParentX]
              simpa [hxEqRoot] using htarget
            · have hxValid : forest.valid x :=
                forest.valid_of_parent?_eq_some hparent
              have hnewParent :
                  (forest.compressNode node root).parent? x =
                    some parent :=
                forest.compressNode_parent?_eq_old_of_ne
                  hxValid hxnode hparent
              simp [findRootFuel?, hnewParent, hsame]
          · simp [hparent, hsame] at hfind
            by_cases hxnode : x = node
            · have hxRootFuel :
                  forest.findRootFuel? forest.maxSearchFuel x =
                    some root := by
                simpa [hxnode] using hnodeRootFuel
              have hrEq : r = root :=
                forest.findRootFuel?_eq_some_unique
                  hfindOrig hxRootFuel
              have hnewParent :
                  (forest.compressNode node root).parent? x =
                    some root :=
                by simpa [hxnode] using
                  forest.compressNode_parent?_eq_root
                    (node := node) (root := root) hnodeValid
              have hrootFindNew :
                  (forest.compressNode node root).findRootFuel?
                    (fuel + 1) root = some root :=
                (forest.compressNode node root).findRootFuel?_eq_some_of_root
                  (Nat.succ_pos fuel) hrootNew
              have htarget :
                  (forest.compressNode node root).findRootFuel?
                    ((fuel + 1) + 1) x = some root := by
                by_cases hrootX : root = x
                · have hnewParentX :
                      (forest.compressNode node x).parent? x = some x := by
                    simpa [hrootX] using hnewParent
                  have htargetX :
                      (forest.compressNode node x).findRootFuel?
                        ((fuel + 1) + 1) x = some x := by
                    simp [findRootFuel?, hnewParentX]
                  simpa [hrootX] using htargetX
                · unfold findRootFuel?
                  rw [hnewParent]
                  simp [hrootX]
                  exact hrootFindNew
              simpa [hrEq] using htarget
            · have hxValid : forest.valid x :=
                forest.valid_of_parent?_eq_some hparent
              have hnewParent :
                  (forest.compressNode node root).parent? x =
                    some parent :=
                forest.compressNode_parent?_eq_old_of_ne
                  hxValid hxnode hparent
              have hrec :
                  (forest.compressNode node root).findRootFuel?
                    (fuel + 1) parent = some r :=
                ih hfind
              unfold findRootFuel?
              simp [hnewParent, hsame]
              exact hrec

theorem compressNode_findRoot?_eq_of_findRoot?
    (forest : ParentForest) (h : forest.LinkableInvariant)
    {node root : Nat}
    (hnodeRoot : forest.findRoot? node = some root) (i : Nat) :
    (forest.compressNode node root).findRoot? i = forest.findRoot? i := by
  by_cases hi : forest.valid i
  · rcases h.strict_depth hi with ⟨oldRoot, hfind, _hrootValid, _hroot⟩
    have holdFind :
        forest.findRoot? i = some oldRoot :=
      forest.findRoot?_eq_some_of_strict_depth h hi hfind
    have hnewFuel :
        (forest.compressNode node root).findRootFuel?
            ((forest.compressNode node root).maxSearchFuel) i =
          some oldRoot := by
      have hstep :=
        forest.compressNode_findRootFuel?_eq_old_of_findRoot?
          h.toInvariant hnodeRoot hfind
      simpa [maxSearchFuel, compressNode_size] using hstep
    have hiNew : (forest.compressNode node root).valid i := by
      simpa [compressNode_size] using hi
    have hnewFind :
        (forest.compressNode node root).findRoot? i = some oldRoot := by
      rw [(forest.compressNode node root).findRoot?_eq_findRootFuel?_of_valid
        hiNew]
      exact hnewFuel
    rw [hnewFind, holdFind]
  · have hiNew : Not ((forest.compressNode node root).valid i) := by
      simpa [compressNode_size] using hi
    rw [(forest.compressNode node root).findRoot?_eq_none_of_invalid hiNew]
    rw [forest.findRoot?_eq_none_of_invalid hi]

theorem compressNode_samePartition_of_findRoot?
    (forest : ParentForest) (h : forest.LinkableInvariant)
    {node root : Nat}
    (hnodeRoot : forest.findRoot? node = some root)
    (hcompressed : (forest.compressNode node root).Invariant) :
    State.SamePartition
      ((forest.compressNode node root).toState hcompressed)
      (forest.toState h.toInvariant) := by
  apply State.samePartition_of_find?_eq
  intro i
  rw [(forest.compressNode node root).toState_find?_eq_findRoot?
    hcompressed i]
  rw [forest.toState_find?_eq_findRoot? h.toInvariant i]
  exact forest.compressNode_findRoot?_eq_of_findRoot? h hnodeRoot i

theorem compressNode_rootMassInvariant_refinement_profile
    (forest : ParentForest) (rank mass : Nat -> Nat)
    (h : forest.RootMassInvariant rank mass)
    {node root : Nat}
    (hnodeRoot : forest.findRoot? node = some root)
    (hrank : node ≠ root -> rank node < rank root) :
    (forest.compressNode node root).RootMassInvariant rank mass /\
      State.SamePartition
        ((forest.compressNode node root).toState
          (forest.compressNode_rootMassInvariant rank mass h
            (forest.valid_of_findRoot?_eq_some hnodeRoot)
            (forest.findRoot?_some_valid h.toInvariant hnodeRoot)
            (forest.findRoot?_some_root h.toInvariant hnodeRoot)
            hrank).toInvariant)
        (forest.toState h.toInvariant) := by
  have hlink : forest.LinkableInvariant :=
    forest.rankInvariant_linkable rank h.toRankInvariant
  let hcompressed :=
    forest.compressNode_rootMassInvariant rank mass h
      (forest.valid_of_findRoot?_eq_some hnodeRoot)
      (forest.findRoot?_some_valid h.toInvariant hnodeRoot)
      (forest.findRoot?_some_root h.toInvariant hnodeRoot)
      hrank
  exact ⟨hcompressed,
    forest.compressNode_samePartition_of_findRoot?
      hlink hnodeRoot hcompressed.toInvariant⟩

theorem rootLink_findRootFuel?_eq_toRoot_of_eq_fromRoot
    (forest : ParentForest) {fromRoot toRoot fuel x : Nat}
    (hfromValid : forest.valid fromRoot)
    (htoValid : forest.valid toRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hne : fromRoot ≠ toRoot)
    (hfind : forest.findRootFuel? fuel x = some fromRoot) :
    (forest.rootLink fromRoot toRoot).findRootFuel? (fuel + 1) x =
      some toRoot := by
  induction fuel generalizing x with
  | zero =>
      simp [findRootFuel?] at hfind
  | succ fuel ih =>
      unfold findRootFuel? at hfind
      cases hparent : forest.parent? x with
      | none =>
          simp [hparent] at hfind
      | some parent =>
          by_cases hsame : parent = x
          · simp [hparent, hsame] at hfind
            cases hfind
            have hnewParent :
                (forest.rootLink fromRoot toRoot).parent? fromRoot =
                  some toRoot :=
              forest.rootLink_parent?_eq_toRoot hfromValid
            have htoRootNew :
                (forest.rootLink fromRoot toRoot).IsRoot toRoot :=
              forest.rootLink_isRoot_of_ne htoValid
                (by intro h; exact hne h.symm) htoRoot
            have hto_ne_from : toRoot ≠ fromRoot := by
              intro h
              exact hne h.symm
            unfold IsRoot at htoRootNew
            simp [findRootFuel?, hnewParent, hto_ne_from, htoRootNew]
          · simp [hparent, hsame] at hfind
            have hx_ne_from : x ≠ fromRoot := by
              intro hx
              subst hx
              rw [hfromRoot] at hparent
              cases hparent
              exact hsame rfl
            have hxValid : forest.valid x := by
              exact forest.valid_of_parent?_eq_some hparent
            have hnewParent :
                (forest.rootLink fromRoot toRoot).parent? x =
                  some parent :=
              forest.rootLink_parent?_eq_old_of_ne hxValid hx_ne_from hparent
            simp [findRootFuel?, hnewParent, hsame]
            exact ih hfind

theorem rootLink_findRootFuel?_eq_same_of_ne_fromRoot
    (forest : ParentForest) {fromRoot toRoot fuel x r : Nat}
    (hfromRoot : forest.IsRoot fromRoot)
    (hr_ne : r ≠ fromRoot)
    (hfind : forest.findRootFuel? fuel x = some r) :
    (forest.rootLink fromRoot toRoot).findRootFuel? fuel x = some r := by
  induction fuel generalizing x with
  | zero =>
      simp [findRootFuel?] at hfind
  | succ fuel ih =>
      unfold findRootFuel? at hfind
      cases hparent : forest.parent? x with
      | none =>
          simp [hparent] at hfind
      | some parent =>
          by_cases hsame : parent = x
          · simp [hparent, hsame] at hfind
            cases hfind
            have hx_ne_from : r ≠ fromRoot := by
              intro hx
              subst hx
              exact hr_ne rfl
            have hxValid : forest.valid r := by
              exact forest.valid_of_parent?_eq_some hparent
            have hparentRoot : forest.parent? r = some r := by
              simpa [hsame] using hparent
            have hnewParent :
                (forest.rootLink fromRoot toRoot).parent? r = some r :=
              forest.rootLink_parent?_eq_old_of_ne hxValid hx_ne_from
                hparentRoot
            simp [findRootFuel?, hnewParent]
          · simp [hparent, hsame] at hfind
            have hx_ne_from : x ≠ fromRoot := by
              intro hx
              subst hx
              rw [hfromRoot] at hparent
              cases hparent
              exact hsame rfl
            have hxValid : forest.valid x := by
              exact forest.valid_of_parent?_eq_some hparent
            have hnewParent :
                (forest.rootLink fromRoot toRoot).parent? x =
                  some parent :=
              forest.rootLink_parent?_eq_old_of_ne hxValid hx_ne_from hparent
            simp [findRootFuel?, hnewParent, hsame]
            exact ih hfind

theorem rootLink_invariant
    (forest : ParentForest) (h : forest.LinkableInvariant)
    {fromRoot toRoot : Nat}
    (hfromValid : forest.valid fromRoot)
    (htoValid : forest.valid toRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hne : fromRoot ≠ toRoot) :
    (forest.rootLink fromRoot toRoot).Invariant where
  parent_lt := by
    intro i parent hparent
    by_cases hi : forest.valid i
    · have hlink :=
        forest.rootLink_parent?_eq_some_of_valid
          (fromRoot := fromRoot) (toRoot := toRoot) hi
      by_cases hieq : i = fromRoot
      · subst hieq
        rw [hlink] at hparent
        cases hparent
        simpa [rootLink_size] using htoValid
      · rcases hOld : forest.parent? i with _ | oldParent
        · simp [hieq, hOld] at hlink
          rw [hlink] at hparent
          cases hparent
          simpa [rootLink_size] using hi
        · simp [hieq, hOld] at hlink
          rw [hlink] at hparent
          cases hparent
          simpa [rootLink_size] using h.parent_lt hOld
    · have hle :
        ((forest.rootLink fromRoot toRoot).parents).length <= i := by
        simpa [rootLink, size] using Nat.le_of_not_gt hi
      have hnone : (forest.rootLink fromRoot toRoot).parent? i = none := by
        simpa [parent?] using
          (List.getElem?_eq_none hle :
            (forest.rootLink fromRoot toRoot).parents[i]? = none)
      rw [hnone] at hparent
      cases hparent
  bounded_depth := by
    intro i hiNew
    have hi : forest.valid i := by
      simpa [rootLink_size] using hiNew
    rcases h.strict_depth hi with ⟨oldRoot, hfind, hrootValid, hroot⟩
    by_cases hroot_eq : oldRoot = fromRoot
    · have hfindFrom :
          forest.findRootFuel? forest.size i = some fromRoot := by
        simpa [hroot_eq] using hfind
      have hnewFind :
          (forest.rootLink fromRoot toRoot).findRootFuel?
              (forest.rootLink fromRoot toRoot).maxSearchFuel i =
            some toRoot := by
        have hstep :=
          forest.rootLink_findRootFuel?_eq_toRoot_of_eq_fromRoot
            hfromValid htoValid hfromRoot htoRoot hne hfindFrom
        simpa [maxSearchFuel, rootLink_size] using hstep
      have htoRootNew :
          (forest.rootLink fromRoot toRoot).IsRoot toRoot :=
        forest.rootLink_isRoot_of_ne htoValid
          (by intro hEq; exact hne hEq.symm) htoRoot
      refine ⟨toRoot, hnewFind, ?_, htoRootNew⟩
      simpa [rootLink_size] using htoValid
    · have hnewFindStrict :
          (forest.rootLink fromRoot toRoot).findRootFuel? forest.size i =
            some oldRoot :=
        forest.rootLink_findRootFuel?_eq_same_of_ne_fromRoot
          hfromRoot hroot_eq hfind
      have hnewFind :=
        ParentForest.findRootFuel?_succ_eq_some_of_eq_some
          (forest.rootLink fromRoot toRoot) hnewFindStrict
      have hrootNew :
          (forest.rootLink fromRoot toRoot).IsRoot oldRoot :=
        forest.rootLink_isRoot_of_ne hrootValid hroot_eq hroot
      refine ⟨oldRoot, ?_, ?_, hrootNew⟩
      · simpa [maxSearchFuel, rootLink_size] using hnewFind
      · simpa [rootLink_size] using hrootValid

theorem rootLink_rankInvariant_of_rank_lt
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank)
    {fromRoot toRoot : Nat}
    (hfromValid : forest.valid fromRoot)
    (htoValid : forest.valid toRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hne : fromRoot ≠ toRoot)
    (hrank : rank fromRoot < rank toRoot) :
    (forest.rootLink fromRoot toRoot).RankInvariant rank where
  toInvariant :=
    forest.rootLink_invariant
      (forest.rankInvariant_linkable rank h)
      hfromValid htoValid hfromRoot htoRoot hne
  rank_lt_size := by
    intro x hx
    have hxOld : forest.valid x := by
      simpa [rootLink_size] using hx
    simpa [rootLink_size] using h.rank_lt_size hxOld
  parent_rank_lt := by
    intro x parent hparent hparent_ne
    have hxNew : (forest.rootLink fromRoot toRoot).valid x :=
      (forest.rootLink fromRoot toRoot).valid_of_parent?_eq_some hparent
    have hxOld : forest.valid x := by
      simpa [rootLink_size] using hxNew
    have hlink :=
      forest.rootLink_parent?_eq_some_of_valid
        (fromRoot := fromRoot) (toRoot := toRoot) hxOld
    by_cases hxfrom : x = fromRoot
    ·
      rw [hlink] at hparent
      simp [hxfrom] at hparent
      cases hparent
      simpa [hxfrom] using hrank
    · cases hOld : forest.parent? x with
      | none =>
          rw [hlink] at hparent
          simp [hxfrom, hOld] at hparent
          cases hparent
          exact False.elim (hparent_ne rfl)
      | some oldParent =>
          rw [hlink] at hparent
          simp [hxfrom, hOld] at hparent
          rw [← hparent]
          apply h.parent_rank_lt hOld
          intro hOldEq
          exact hparent_ne (hparent.symm.trans hOldEq)

theorem rootLink_rankInvariant_of_rank_eq_bump
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank)
    {fromRoot toRoot : Nat}
    (hfromValid : forest.valid fromRoot)
    (htoValid : forest.valid toRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hne : fromRoot ≠ toRoot)
    (hrankEq : rank fromRoot = rank toRoot)
    (hbump : rank toRoot + 1 < forest.size) :
    (forest.rootLink fromRoot toRoot).RankInvariant
      (bumpRank rank toRoot) where
  toInvariant :=
    forest.rootLink_invariant
      (forest.rankInvariant_linkable rank h)
      hfromValid htoValid hfromRoot htoRoot hne
  rank_lt_size := by
    intro x hx
    have hxOld : forest.valid x := by
      simpa [rootLink_size] using hx
    by_cases hxto : x = toRoot
    · subst hxto
      simpa [bumpRank] using hbump
    · simp [bumpRank, hxto, h.rank_lt_size hxOld]
  parent_rank_lt := by
    intro x parent hparent hparent_ne
    have hxNew : (forest.rootLink fromRoot toRoot).valid x :=
      (forest.rootLink fromRoot toRoot).valid_of_parent?_eq_some hparent
    have hxOld : forest.valid x := by
      simpa [rootLink_size] using hxNew
    have hlink :=
      forest.rootLink_parent?_eq_some_of_valid
        (fromRoot := fromRoot) (toRoot := toRoot) hxOld
    by_cases hxfrom : x = fromRoot
    ·
      rw [hlink] at hparent
      simp [hxfrom] at hparent
      cases hparent
      have hx_ne_to : x ≠ toRoot := by
        intro hxto
        exact hne (hxfrom.symm.trans hxto)
      simp [bumpRank, hne, hrankEq, hxfrom]
    · cases hOld : forest.parent? x with
      | none =>
          rw [hlink] at hparent
          simp [hxfrom, hOld] at hparent
          cases hparent
          exact False.elim (hparent_ne rfl)
      | some oldParent =>
          rw [hlink] at hparent
          simp [hxfrom, hOld] at hparent
          have hOldRank : rank x < rank oldParent :=
            h.parent_rank_lt hOld (by
              intro hOldEq
              exact hparent_ne (hparent.symm.trans hOldEq))
          have hx_ne_to : x ≠ toRoot := by
            intro hxto
            subst hxto
            rw [htoRoot] at hOld
            cases hOld
            exact hparent_ne hparent.symm
          rw [← hparent]
          by_cases hp_to : oldParent = toRoot
          ·
            subst hp_to
            simp [bumpRank, hx_ne_to]
            omega
          · simpa [bumpRank, hx_ne_to, hp_to] using hOldRank

theorem rootLink_rankSizeInvariant_of_rank_lt
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankSizeInvariant rank)
    {fromRoot toRoot : Nat}
    (hfromValid : forest.valid fromRoot)
    (htoValid : forest.valid toRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hne : fromRoot ≠ toRoot)
    (hrank : rank fromRoot < rank toRoot) :
    (forest.rootLink fromRoot toRoot).RankSizeInvariant rank where
  toRankInvariant :=
    forest.rootLink_rankInvariant_of_rank_lt rank h.toRankInvariant
      hfromValid htoValid hfromRoot htoRoot hne hrank
  equal_rank_root_bump_lt := by
    intro rootX rootY hxNew hyNew hrootXNew hrootYNew hrootNe hrankEq
    rcases forest.old_isRoot_of_rootLink_isRoot hxNew hne hrootXNew with
      ⟨hxOld, hrootXOld, _hxNeFrom⟩
    rcases forest.old_isRoot_of_rootLink_isRoot hyNew hne hrootYNew with
      ⟨hyOld, hrootYOld, _hyNeFrom⟩
    simpa [rootLink_size] using
      h.equal_rank_root_bump_lt
        hxOld hyOld hrootXOld hrootYOld hrootNe hrankEq

theorem rootLink_rankSizeInvariant_of_rank_eq_bump
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankComponentInvariant rank)
    {fromRoot toRoot : Nat}
    (hfromValid : forest.valid fromRoot)
    (htoValid : forest.valid toRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hne : fromRoot ≠ toRoot)
    (hrankEq : rank fromRoot = rank toRoot) :
    (forest.rootLink fromRoot toRoot).RankSizeInvariant
      (bumpRank rank toRoot) where
  toRankInvariant :=
    forest.rootLink_rankInvariant_of_rank_eq_bump rank h.toRankInvariant
      hfromValid htoValid hfromRoot htoRoot hne hrankEq
      (h.equal_rank_root_bump_lt htoValid hfromValid
        htoRoot hfromRoot (by intro hEq; exact hne hEq)
        hrankEq.symm)
  equal_rank_root_bump_lt := by
    intro rootX rootY hxNew hyNew hrootXNew hrootYNew hrootNe hrankEqNew
    rcases forest.old_isRoot_of_rootLink_isRoot hxNew hne hrootXNew with
      ⟨hxOld, hrootXOld, hxNeFrom⟩
    rcases forest.old_isRoot_of_rootLink_isRoot hyNew hne hrootYNew with
      ⟨hyOld, hrootYOld, hyNeFrom⟩
    by_cases hxTo : rootX = toRoot
    · by_cases hyTo : rootY = toRoot
      · exact False.elim (hrootNe (hyTo.trans hxTo.symm))
      · have hyNeTo : rootY ≠ toRoot := hyTo
        have hnext : rank rootY = rank fromRoot + 1 := by
          have hnextTo : rank rootY = rank toRoot + 1 := by
            simpa [bumpRank, hxTo, hyNeTo] using hrankEqNew.symm
          omega
        have hroom :
            rank fromRoot + 2 < forest.size :=
          h.equal_pair_next_rank_bump_lt
            hfromValid htoValid hyOld hfromRoot htoRoot hrootYOld
            (by intro hEq; exact hne hEq.symm)
            hyNeFrom hyNeTo hrankEq hnext
        simp [rootLink_size, bumpRank, hxTo]
        omega
    · by_cases hyTo : rootY = toRoot
      · have hxNeTo : rootX ≠ toRoot := hxTo
        have hnext : rank rootX = rank fromRoot + 1 := by
          have hnextTo : rank rootX = rank toRoot + 1 := by
            simpa [bumpRank, hxNeTo, hyTo] using hrankEqNew
          omega
        have hroom :
            rank fromRoot + 2 < forest.size :=
          h.equal_pair_next_rank_bump_lt
            hfromValid htoValid hxOld hfromRoot htoRoot hrootXOld
            (by intro hEq; exact hne hEq.symm)
            hxNeFrom hxNeTo hrankEq hnext
        simp [rootLink_size, bumpRank, hxNeTo]
        omega
      · have hrankEqOld : rank rootX = rank rootY := by
          simpa [bumpRank, hxTo, hyTo] using hrankEqNew
        have hroom :=
          h.equal_rank_root_bump_lt
            hxOld hyOld hrootXOld hrootYOld hrootNe hrankEqOld
        simp [rootLink_size, bumpRank, hxTo]
        exact hroom

theorem rootLink_rootMassSum_le_size
    (forest : ParentForest) (rank mass : Nat -> Nat)
    (h : forest.RootMassInvariant rank mass)
    {fromRoot toRoot : Nat}
    (hfromValid : forest.valid fromRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (hne : fromRoot ≠ toRoot) :
    forall {roots : List Nat}, roots.Nodup ->
      (forall {root : Nat}, root ∈ roots ->
        (forest.rootLink fromRoot toRoot).valid root /\
          (forest.rootLink fromRoot toRoot).IsRoot root) ->
      rootMassSum (rootMassAfterLink mass fromRoot toRoot) roots <=
        (forest.rootLink fromRoot toRoot).size := by
  intro roots hnodup hrootsNew
  have hrootsOld :
      forall {root : Nat}, root ∈ roots ->
        forest.valid root /\ forest.IsRoot root := by
    intro root hmem
    rcases hrootsNew hmem with ⟨hvalidNew, hrootNew⟩
    rcases forest.old_isRoot_of_rootLink_isRoot hvalidNew hne hrootNew with
      ⟨hvalidOld, hrootOld, _hrootNeFrom⟩
    exact ⟨hvalidOld, hrootOld⟩
  have hfrom_not_mem : fromRoot ∉ roots := by
    intro hmem
    rcases hrootsNew hmem with ⟨hvalidNew, hrootNew⟩
    rcases forest.old_isRoot_of_rootLink_isRoot hvalidNew hne hrootNew with
      ⟨_hvalidOld, _hrootOld, hrootNeFrom⟩
    exact hrootNeFrom rfl
  by_cases hto_mem : toRoot ∈ roots
  · have hsumNew :=
      rootMassSum_afterLink_eq_add_of_mem_to mass
        (roots := roots) hnodup hfrom_not_mem hto_mem
    have hconsNodup : (fromRoot :: roots).Nodup := by
      simp [hfrom_not_mem, hnodup]
    have hconsRoots :
        forall {root : Nat}, root ∈ fromRoot :: roots ->
          forest.valid root /\ forest.IsRoot root := by
      intro root hmem
      have hcases : root = fromRoot ∨ root ∈ roots := by
        simpa using hmem
      cases hcases with
      | inl hroot =>
          subst hroot
          exact ⟨hfromValid, hfromRoot⟩
      | inr htail =>
          exact hrootsOld htail
    have hold := h.rootMassSum_le_size hconsNodup hconsRoots
    rw [hsumNew]
    simpa [rootMassSum, rootLink_size] using hold
  · have hsumNew :=
      rootMassSum_afterLink_eq_of_not_mem mass
        (roots := roots) hfrom_not_mem hto_mem
    have hold := h.rootMassSum_le_size hnodup hrootsOld
    rw [hsumNew]
    simpa [rootLink_size] using hold

theorem rootLink_rootMassInvariant_of_rank_lt
    (forest : ParentForest) (rank mass : Nat -> Nat)
    (h : forest.RootMassInvariant rank mass)
    {fromRoot toRoot : Nat}
    (hfromValid : forest.valid fromRoot)
    (htoValid : forest.valid toRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hne : fromRoot ≠ toRoot)
    (hrank : rank fromRoot < rank toRoot) :
    (forest.rootLink fromRoot toRoot).RootMassInvariant rank
      (rootMassAfterLink mass fromRoot toRoot) where
  toRankInvariant :=
    forest.rootLink_rankInvariant_of_rank_lt rank h.toRankInvariant
      hfromValid htoValid hfromRoot htoRoot hne hrank
  root_mass_pos := by
    intro root hvalidNew hrootNew
    rcases forest.old_isRoot_of_rootLink_isRoot hvalidNew hne hrootNew with
      ⟨hvalidOld, hrootOld, hrootNeFrom⟩
    by_cases hrootTo : root = toRoot
    · subst hrootTo
      have htoPos := h.root_mass_pos htoValid htoRoot
      have hfromPos := h.root_mass_pos hfromValid hfromRoot
      simp [rootMassAfterLink]
      omega
    · simpa [rootMassAfterLink, hrootTo, hrootNeFrom] using
        h.root_mass_pos hvalidOld hrootOld
  rank_lt_mass := by
    intro root hvalidNew hrootNew
    rcases forest.old_isRoot_of_rootLink_isRoot hvalidNew hne hrootNew with
      ⟨hvalidOld, hrootOld, hrootNeFrom⟩
    by_cases hrootTo : root = toRoot
    · subst hrootTo
      have htoMass := h.rank_lt_mass htoValid htoRoot
      have hfromPos := h.root_mass_pos hfromValid hfromRoot
      simp [rootMassAfterLink]
      omega
    · simpa [rootMassAfterLink, hrootTo, hrootNeFrom] using
        h.rank_lt_mass hvalidOld hrootOld
  rootMassSum_le_size := by
    intro roots hnodup hroots
    exact forest.rootLink_rootMassSum_le_size rank mass h
      hfromValid hfromRoot hne hnodup hroots

theorem rootLink_rootMassInvariant_of_rank_eq_bump
    (forest : ParentForest) (rank mass : Nat -> Nat)
    (h : forest.RootMassInvariant rank mass)
    {fromRoot toRoot : Nat}
    (hfromValid : forest.valid fromRoot)
    (htoValid : forest.valid toRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hne : fromRoot ≠ toRoot)
    (hrankEq : rank fromRoot = rank toRoot) :
    (forest.rootLink fromRoot toRoot).RootMassInvariant
      (bumpRank rank toRoot) (rootMassAfterLink mass fromRoot toRoot) where
  toRankInvariant :=
    forest.rootLink_rankInvariant_of_rank_eq_bump rank h.toRankInvariant
      hfromValid htoValid hfromRoot htoRoot hne hrankEq
      (h.toRankSizeInvariant.equal_rank_root_bump_lt
        htoValid hfromValid htoRoot hfromRoot
        (by intro hEq; exact hne hEq)
        hrankEq.symm)
  root_mass_pos := by
    intro root hvalidNew hrootNew
    rcases forest.old_isRoot_of_rootLink_isRoot hvalidNew hne hrootNew with
      ⟨hvalidOld, hrootOld, hrootNeFrom⟩
    by_cases hrootTo : root = toRoot
    · subst hrootTo
      have htoPos := h.root_mass_pos htoValid htoRoot
      have hfromPos := h.root_mass_pos hfromValid hfromRoot
      simp [rootMassAfterLink]
      omega
    · simpa [rootMassAfterLink, hrootTo, hrootNeFrom] using
        h.root_mass_pos hvalidOld hrootOld
  rank_lt_mass := by
    intro root hvalidNew hrootNew
    rcases forest.old_isRoot_of_rootLink_isRoot hvalidNew hne hrootNew with
      ⟨hvalidOld, hrootOld, hrootNeFrom⟩
    by_cases hrootTo : root = toRoot
    · subst hrootTo
      have htoMass := h.rank_lt_mass htoValid htoRoot
      have hfromPos := h.root_mass_pos hfromValid hfromRoot
      simp [bumpRank, rootMassAfterLink]
      omega
    · simpa [bumpRank, rootMassAfterLink, hrootTo, hrootNeFrom] using
        h.rank_lt_mass hvalidOld hrootOld
  rootMassSum_le_size := by
    intro roots hnodup hroots
    exact forest.rootLink_rootMassSum_le_size rank mass h
      hfromValid hfromRoot hne hnodup hroots

theorem rootLink_rankPowerMassInvariant_of_rank_lt
    (forest : ParentForest) (rank mass : Nat -> Nat)
    (h : forest.RankPowerMassInvariant rank mass)
    {fromRoot toRoot : Nat}
    (hfromValid : forest.valid fromRoot)
    (htoValid : forest.valid toRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hne : fromRoot ≠ toRoot)
    (hrank : rank fromRoot < rank toRoot) :
    (forest.rootLink fromRoot toRoot).RankPowerMassInvariant rank
      (rootMassAfterLink mass fromRoot toRoot) where
  toRootMassInvariant :=
    forest.rootLink_rootMassInvariant_of_rank_lt rank mass
      h.toRootMassInvariant hfromValid htoValid hfromRoot htoRoot hne hrank
  rank_power_le_mass := by
    intro root hvalidNew hrootNew
    rcases forest.old_isRoot_of_rootLink_isRoot hvalidNew hne hrootNew with
      ⟨hvalidOld, hrootOld, hrootNeFrom⟩
    by_cases hrootTo : root = toRoot
    · subst hrootTo
      have htoPow := h.rank_power_le_mass htoValid htoRoot
      simp [rootMassAfterLink]
      omega
    · simpa [rootMassAfterLink, hrootTo, hrootNeFrom] using
        h.rank_power_le_mass hvalidOld hrootOld

theorem rootLink_rankPowerMassInvariant_of_rank_eq_bump
    (forest : ParentForest) (rank mass : Nat -> Nat)
    (h : forest.RankPowerMassInvariant rank mass)
    {fromRoot toRoot : Nat}
    (hfromValid : forest.valid fromRoot)
    (htoValid : forest.valid toRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hne : fromRoot ≠ toRoot)
    (hrankEq : rank fromRoot = rank toRoot) :
    (forest.rootLink fromRoot toRoot).RankPowerMassInvariant
      (bumpRank rank toRoot) (rootMassAfterLink mass fromRoot toRoot) where
  toRootMassInvariant :=
    forest.rootLink_rootMassInvariant_of_rank_eq_bump rank mass
      h.toRootMassInvariant hfromValid htoValid hfromRoot htoRoot hne hrankEq
  rank_power_le_mass := by
    intro root hvalidNew hrootNew
    rcases forest.old_isRoot_of_rootLink_isRoot hvalidNew hne hrootNew with
      ⟨hvalidOld, hrootOld, hrootNeFrom⟩
    by_cases hrootTo : root = toRoot
    · subst toRoot
      have htoPow :
          2 ^ rank root <= mass root :=
        h.rank_power_le_mass htoValid htoRoot
      have hfromPow :
          2 ^ rank root <= mass fromRoot := by
        simpa [hrankEq] using
          h.rank_power_le_mass hfromValid hfromRoot
      have hpowSucc :
          2 ^ (rank root + 1) =
            2 ^ rank root + 2 ^ rank root := by
        rw [Nat.pow_succ]
        omega
      simp [bumpRank, rootMassAfterLink]
      rw [hpowSucc]
      omega
    · simpa [bumpRank, rootMassAfterLink, hrootTo, hrootNeFrom] using
        h.rank_power_le_mass hvalidOld hrootOld

theorem rootLink_linkable_of_rank_lt
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank)
    {fromRoot toRoot : Nat}
    (hfromValid : forest.valid fromRoot)
    (htoValid : forest.valid toRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hne : fromRoot ≠ toRoot)
    (hrank : rank fromRoot < rank toRoot) :
    (forest.rootLink fromRoot toRoot).LinkableInvariant :=
  (forest.rootLink fromRoot toRoot).rankInvariant_linkable rank
    (forest.rootLink_rankInvariant_of_rank_lt rank h
      hfromValid htoValid hfromRoot htoRoot hne hrank)

theorem rootLink_linkable_of_rank_eq_bump
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank)
    {fromRoot toRoot : Nat}
    (hfromValid : forest.valid fromRoot)
    (htoValid : forest.valid toRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hne : fromRoot ≠ toRoot)
    (hrankEq : rank fromRoot = rank toRoot)
    (hbump : rank toRoot + 1 < forest.size) :
    (forest.rootLink fromRoot toRoot).LinkableInvariant :=
  (forest.rootLink fromRoot toRoot).rankInvariant_linkable
    (bumpRank rank toRoot)
    (forest.rootLink_rankInvariant_of_rank_eq_bump rank h
      hfromValid htoValid hfromRoot htoRoot hne hrankEq hbump)

theorem rootLink_findRoot?_eq_toRoot_of_strict_eq_fromRoot
    (forest : ParentForest) {fromRoot toRoot x : Nat}
    (hfromValid : forest.valid fromRoot)
    (htoValid : forest.valid toRoot)
    (hfromRoot : forest.IsRoot fromRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hne : fromRoot ≠ toRoot)
    (hfind : forest.findRootFuel? forest.size x = some fromRoot)
    (hx : forest.valid x) :
    (forest.rootLink fromRoot toRoot).findRoot? x = some toRoot := by
  have hlinkFind :=
    forest.rootLink_findRootFuel?_eq_toRoot_of_eq_fromRoot
      hfromValid htoValid hfromRoot htoRoot hne hfind
  have hxNew : (forest.rootLink fromRoot toRoot).valid x := by
    simpa [rootLink_size] using hx
  have hxNat : x < forest.size := hx
  simpa [findRoot?, maxSearchFuel, rootLink_size, hxNat] using hlinkFind

theorem rootLink_findRoot?_eq_same_of_strict_ne_fromRoot
    (forest : ParentForest) {fromRoot toRoot x r : Nat}
    (hfromRoot : forest.IsRoot fromRoot)
    (hr_ne : r ≠ fromRoot)
    (hfind : forest.findRootFuel? forest.size x = some r)
    (hx : forest.valid x) :
    (forest.rootLink fromRoot toRoot).findRoot? x = some r := by
  have hlinkFindStrict :=
    forest.rootLink_findRootFuel?_eq_same_of_ne_fromRoot
      (toRoot := toRoot) hfromRoot hr_ne hfind
  have hlinkFind :=
    ParentForest.findRootFuel?_succ_eq_some_of_eq_some
      (forest.rootLink fromRoot toRoot) hlinkFindStrict
  have hxNew : (forest.rootLink fromRoot toRoot).valid x := by
    simpa [rootLink_size] using hx
  have hxNat : x < forest.size := hx
  simpa [findRoot?, maxSearchFuel, rootLink_size, hxNat] using hlinkFind

theorem rootLink_refines_unionSpec_find?
    (forest : ParentForest) (h : forest.LinkableInvariant)
    {x y rootX rootY : Nat}
    (hxFind : forest.findRoot? x = some rootX)
    (hyFind : forest.findRoot? y = some rootY)
    (hne : rootY ≠ rootX) :
    forall i,
      (forest.rootLink rootY rootX).findRoot? i =
        ((forest.toState h.toInvariant).unionSpec x y).find? i := by
  intro i
  let state := forest.toState h.toInvariant
  have hxValid : forest.valid x :=
    forest.valid_of_findRoot?_eq_some hxFind
  have hyValid : forest.valid y :=
    forest.valid_of_findRoot?_eq_some hyFind
  have hrootXValid : forest.valid rootX :=
    forest.findRoot?_some_valid h.toInvariant hxFind
  have hrootYValid : forest.valid rootY :=
    forest.findRoot?_some_valid h.toInvariant hyFind
  have hrootX : forest.IsRoot rootX :=
    forest.findRoot?_some_root h.toInvariant hxFind
  have hrootY : forest.IsRoot rootY :=
    forest.findRoot?_some_root h.toInvariant hyFind
  have hstateX : state.repr x = rootX := by
    simpa [state] using
      forest.toState_repr_eq_of_findRoot? h.toInvariant hxFind
  have hstateY : state.repr y = rootY := by
    simpa [state] using
      forest.toState_repr_eq_of_findRoot? h.toInvariant hyFind
  by_cases hi : forest.valid i
  · rcases h.strict_depth hi with
      ⟨oldRoot, hstrict, hOldRootValid, hOldRoot⟩
    have hiFind : forest.findRoot? i = some oldRoot :=
      forest.findRoot?_eq_some_of_strict_depth h hi hstrict
    have hstateI : state.repr i = oldRoot := by
      simpa [state] using
        forest.toState_repr_eq_of_findRoot? h.toInvariant hiFind
    by_cases hiy : oldRoot = rootY
    · have hstrictY :
          forest.findRootFuel? forest.size i = some rootY := by
        simpa [hiy] using hstrict
      have hleft :
          (forest.rootLink rootY rootX).findRoot? i = some rootX :=
        forest.rootLink_findRoot?_eq_toRoot_of_strict_eq_fromRoot
          hrootYValid hrootXValid hrootY hrootX hne hstrictY hi
      have hiState : state.valid i := by
        simpa [state] using hi
      have hxState : state.valid x := by
        simpa [state] using hxValid
      have hyState : state.valid y := by
        simpa [state] using hyValid
      have hxyState : state.valid x /\ state.valid y :=
        ⟨hxState, hyState⟩
      have hunionValid : (state.unionSpec x y).valid i := by
        simpa [State.unionSpec_valid_iff] using hiState
      have hright :=
        State.find?_eq_some_of_valid (state.unionSpec x y) hunionValid
      have hrepr :
          (state.unionSpec x y).repr i = rootX := by
        change State.mergeRepr state x y i = rootX
        have hsame : state.repr i = state.repr y := by
          rw [hstateI, hiy, hstateY]
        simp [State.mergeRepr, hxyState, hsame, hstateX]
      rw [hleft]
      rw [hright, hrepr]
    · have hleft :
          (forest.rootLink rootY rootX).findRoot? i = some oldRoot :=
        forest.rootLink_findRoot?_eq_same_of_strict_ne_fromRoot
          hrootY hiy hstrict hi
      have hiState : state.valid i := by
        simpa [state] using hi
      have hxState : state.valid x := by
        simpa [state] using hxValid
      have hyState : state.valid y := by
        simpa [state] using hyValid
      have hxyState : state.valid x /\ state.valid y :=
        ⟨hxState, hyState⟩
      have hunionValid : (state.unionSpec x y).valid i := by
        simpa [State.unionSpec_valid_iff] using hiState
      have hright :=
        State.find?_eq_some_of_valid (state.unionSpec x y) hunionValid
      have hneOldRootStateY : oldRoot ≠ state.repr y := by
        intro heq
        apply hiy
        rw [heq, hstateY]
      have hrepr :
          (state.unionSpec x y).repr i = oldRoot := by
        change State.mergeRepr state x y i = oldRoot
        simp [State.mergeRepr, hxyState, hstateI, hneOldRootStateY]
      rw [hleft]
      rw [hright, hrepr]
  · have hiNew : Not ((forest.rootLink rootY rootX).valid i) := by
      simpa [rootLink_size] using hi
    have hiState : Not (state.valid i) := by
      simpa [state] using hi
    have hunionInvalid : Not ((state.unionSpec x y).valid i) := by
      simpa [State.unionSpec_valid_iff] using hiState
    rw [(forest.rootLink rootY rootX).findRoot?_eq_none_of_invalid hiNew]
    exact (State.find?_eq_none_of_invalid (state.unionSpec x y)
      hunionInvalid).symm

theorem rootLink_refinement_profile
    (forest : ParentForest) (h : forest.LinkableInvariant)
    {x y rootX rootY : Nat}
    (hxFind : forest.findRoot? x = some rootX)
    (hyFind : forest.findRoot? y = some rootY)
    (hne : rootY ≠ rootX) :
    (forest.rootLink rootY rootX).Invariant /\
      (forall i,
        (forest.rootLink rootY rootX).findRoot? i =
          ((forest.toState h.toInvariant).unionSpec x y).find? i) := by
  have hrootXValid : forest.valid rootX :=
    forest.findRoot?_some_valid h.toInvariant hxFind
  have hrootYValid : forest.valid rootY :=
    forest.findRoot?_some_valid h.toInvariant hyFind
  have hrootX : forest.IsRoot rootX :=
    forest.findRoot?_some_root h.toInvariant hxFind
  have hrootY : forest.IsRoot rootY :=
    forest.findRoot?_some_root h.toInvariant hyFind
  exact ⟨
    forest.rootLink_invariant h hrootYValid hrootXValid hrootY hrootX hne,
    forest.rootLink_refines_unionSpec_find? h hxFind hyFind hne⟩

theorem rootLink_refines_unionSpec_samePartition
    (forest : ParentForest) (h : forest.LinkableInvariant)
    {x y rootX rootY : Nat}
    (hxFind : forest.findRoot? x = some rootX)
    (hyFind : forest.findRoot? y = some rootY)
    (hne : rootY ≠ rootX)
    (hlinked : (forest.rootLink rootY rootX).Invariant) :
    State.SamePartition
      ((forest.rootLink rootY rootX).toState hlinked)
      ((forest.toState h.toInvariant).unionSpec x y) := by
  apply State.samePartition_of_find?_eq
  intro i
  rw [(forest.rootLink rootY rootX).toState_find?_eq_findRoot?
    hlinked i]
  exact forest.rootLink_refines_unionSpec_find? h hxFind hyFind hne i

theorem rootLink_rank_lt_refinement_profile
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank)
    {x y rootX rootY : Nat}
    (hxFind : forest.findRoot? x = some rootX)
    (hyFind : forest.findRoot? y = some rootY)
    (hne : rootY ≠ rootX)
    (hrank : rank rootY < rank rootX) :
    (forest.rootLink rootY rootX).LinkableInvariant /\
      (forall i,
        (forest.rootLink rootY rootX).findRoot? i =
          ((forest.toState h.toInvariant).unionSpec x y).find? i) := by
  have hlink : forest.LinkableInvariant :=
    forest.rankInvariant_linkable rank h
  have hrootXValid : forest.valid rootX :=
    forest.findRoot?_some_valid h.toInvariant hxFind
  have hrootYValid : forest.valid rootY :=
    forest.findRoot?_some_valid h.toInvariant hyFind
  have hrootX : forest.IsRoot rootX :=
    forest.findRoot?_some_root h.toInvariant hxFind
  have hrootY : forest.IsRoot rootY :=
    forest.findRoot?_some_root h.toInvariant hyFind
  exact ⟨
    forest.rootLink_linkable_of_rank_lt rank h
      hrootYValid hrootXValid hrootY hrootX hne hrank,
    forest.rootLink_refines_unionSpec_find? hlink hxFind hyFind hne⟩

theorem rootLink_rank_eq_bump_refinement_profile
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank)
    {x y rootX rootY : Nat}
    (hxFind : forest.findRoot? x = some rootX)
    (hyFind : forest.findRoot? y = some rootY)
    (hne : rootY ≠ rootX)
    (hrankEq : rank rootY = rank rootX)
    (hbump : rank rootX + 1 < forest.size) :
    (forest.rootLink rootY rootX).LinkableInvariant /\
      (forest.rootLink rootY rootX).RankInvariant
        (bumpRank rank rootX) /\
      (forall i,
        (forest.rootLink rootY rootX).findRoot? i =
          ((forest.toState h.toInvariant).unionSpec x y).find? i) := by
  have hlink : forest.LinkableInvariant :=
    forest.rankInvariant_linkable rank h
  have hrootXValid : forest.valid rootX :=
    forest.findRoot?_some_valid h.toInvariant hxFind
  have hrootYValid : forest.valid rootY :=
    forest.findRoot?_some_valid h.toInvariant hyFind
  have hrootX : forest.IsRoot rootX :=
    forest.findRoot?_some_root h.toInvariant hxFind
  have hrootY : forest.IsRoot rootY :=
    forest.findRoot?_some_root h.toInvariant hyFind
  have hrankInv :
      (forest.rootLink rootY rootX).RankInvariant
        (bumpRank rank rootX) :=
    forest.rootLink_rankInvariant_of_rank_eq_bump rank h
      hrootYValid hrootXValid hrootY hrootX hne hrankEq hbump
  exact ⟨
    (forest.rootLink rootY rootX).rankInvariant_linkable
      (bumpRank rank rootX) hrankInv,
    hrankInv,
    forest.rootLink_refines_unionSpec_find? hlink hxFind hyFind hne⟩

theorem rankedRootLink_refinement_profile_of_bump
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank)
    {x y rootX rootY : Nat}
    (hxFind : forest.findRoot? x = some rootX)
    (hyFind : forest.findRoot? y = some rootY)
    (hne : rootY ≠ rootX)
    (hbump :
      rank rootX = rank rootY -> rank rootX + 1 < forest.size) :
    exists hlinked :
      (forest.rankedRootLink rank rootX rootY).LinkableInvariant,
        (forest.rankedRootLink rank rootX rootY).RankInvariant
          (rankAfterRootLinkByRank rank rootX rootY) /\
        State.SamePartition
          ((forest.rankedRootLink rank rootX rootY).toState
            hlinked.toInvariant)
          ((forest.toState h.toInvariant).unionSpec x y) := by
  have holdLink : forest.LinkableInvariant :=
    forest.rankInvariant_linkable rank h
  have hrootXValid : forest.valid rootX :=
    forest.findRoot?_some_valid h.toInvariant hxFind
  have hrootYValid : forest.valid rootY :=
    forest.findRoot?_some_valid h.toInvariant hyFind
  have hrootX : forest.IsRoot rootX :=
    forest.findRoot?_some_root h.toInvariant hxFind
  have hrootY : forest.IsRoot rootY :=
    forest.findRoot?_some_root h.toInvariant hyFind
  by_cases hxyRank : rank rootX < rank rootY
  · have hneXY : rootX ≠ rootY := by
      intro hEq
      exact hne hEq.symm
    have hrankInv :
        (forest.rootLink rootX rootY).RankInvariant rank :=
      forest.rootLink_rankInvariant_of_rank_lt rank h
        hrootXValid hrootYValid hrootX hrootY hneXY hxyRank
    have hlinked :
        (forest.rootLink rootX rootY).LinkableInvariant :=
      (forest.rootLink rootX rootY).rankInvariant_linkable rank hrankInv
    have hsameYX :
        State.SamePartition
          ((forest.rootLink rootX rootY).toState hlinked.toInvariant)
          ((forest.toState h.toInvariant).unionSpec y x) :=
      forest.rootLink_refines_unionSpec_samePartition holdLink
        hyFind hxFind hneXY hlinked.toInvariant
    have hsameXY :
        State.SamePartition
          ((forest.rootLink rootX rootY).toState hlinked.toInvariant)
          ((forest.toState h.toInvariant).unionSpec x y) :=
      State.samePartition_trans hsameYX
        (State.unionSpec_samePartition_comm
          (forest.toState h.toInvariant) y x)
    simp [rankedRootLink, rankAfterRootLinkByRank, hxyRank]
    exact ⟨hrankInv, hlinked, hsameXY⟩
  · by_cases hyxRank : rank rootY < rank rootX
    · have hrankInv :
          (forest.rootLink rootY rootX).RankInvariant rank :=
        forest.rootLink_rankInvariant_of_rank_lt rank h
          hrootYValid hrootXValid hrootY hrootX hne hyxRank
      have hlinked :
          (forest.rootLink rootY rootX).LinkableInvariant :=
        (forest.rootLink rootY rootX).rankInvariant_linkable rank hrankInv
      have hsame :
          State.SamePartition
            ((forest.rootLink rootY rootX).toState hlinked.toInvariant)
            ((forest.toState h.toInvariant).unionSpec x y) :=
        forest.rootLink_refines_unionSpec_samePartition holdLink
          hxFind hyFind hne hlinked.toInvariant
      simp [rankedRootLink, rankAfterRootLinkByRank, hxyRank, hyxRank]
      exact ⟨hrankInv, hlinked, hsame⟩
    · have hEqXY : rank rootX = rank rootY := by
        have hyxLe : rank rootX <= rank rootY :=
          Nat.le_of_not_gt hyxRank
        have hxyLe : rank rootY <= rank rootX :=
          Nat.le_of_not_gt hxyRank
        exact Nat.le_antisymm hyxLe hxyLe
      have hrankInv :
          (forest.rootLink rootY rootX).RankInvariant
            (bumpRank rank rootX) :=
        forest.rootLink_rankInvariant_of_rank_eq_bump rank h
          hrootYValid hrootXValid hrootY hrootX hne
          hEqXY.symm (hbump hEqXY)
      have hlinked :
          (forest.rootLink rootY rootX).LinkableInvariant :=
        (forest.rootLink rootY rootX).rankInvariant_linkable
          (bumpRank rank rootX) hrankInv
      have hsame :
          State.SamePartition
            ((forest.rootLink rootY rootX).toState hlinked.toInvariant)
            ((forest.toState h.toInvariant).unionSpec x y) :=
        forest.rootLink_refines_unionSpec_samePartition holdLink
          hxFind hyFind hne hlinked.toInvariant
      simp [rankedRootLink, rankAfterRootLinkByRank, hxyRank, hyxRank]
      exact ⟨hrankInv, hlinked, hsame⟩

theorem unionByRank_refinement_profile_of_bump
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankInvariant rank) (x y : Nat)
    (hbump :
      forall {rootX rootY : Nat},
        forest.findRoot? x = some rootX ->
        forest.findRoot? y = some rootY ->
        rootY ≠ rootX ->
        rank rootX = rank rootY ->
        rank rootX + 1 < forest.size) :
    (forest.unionByRank rank x y).RankInvariant
      (forest.rankAfterUnionByRank rank x y) /\
      exists hlinked :
        (forest.unionByRank rank x y).LinkableInvariant,
          State.SamePartition
            ((forest.unionByRank rank x y).toState hlinked.toInvariant)
            ((forest.toState h.toInvariant).unionSpec x y) := by
  have holdLink : forest.LinkableInvariant :=
    forest.rankInvariant_linkable rank h
  have hsameStates :
      State.SamePartition
        (forest.toState holdLink.toInvariant)
        (forest.toState h.toInvariant) :=
    forest.toState_samePartition_of_invariants
      holdLink.toInvariant h.toInvariant
  cases hxFind : forest.findRoot? x with
  | none =>
      have hxInvalidForest : Not (forest.valid x) :=
        forest.invalid_of_findRoot?_eq_none h.toInvariant hxFind
      let state := forest.toState h.toInvariant
      have hxInvalidState : Not (state.valid x) := by
        simpa [state] using hxInvalidForest
      have hnot : Not (state.valid x /\ state.valid y) := by
        intro hxy
        exact hxInvalidState hxy.1
      have hsameUnion :
          State.SamePartition state (state.unionSpec x y) :=
        State.unionSpec_samePartition_self_of_not_valid state hnot
      have hsame :
          State.SamePartition
            (forest.toState holdLink.toInvariant)
            ((forest.toState h.toInvariant).unionSpec x y) := by
        simpa [state] using
          State.samePartition_trans hsameStates hsameUnion
      simp [unionByRank, rankAfterUnionByRank, hxFind]
      exact ⟨h, holdLink, hsame⟩
  | some rootX =>
      cases hyFind : forest.findRoot? y with
      | none =>
          have hyInvalidForest : Not (forest.valid y) :=
            forest.invalid_of_findRoot?_eq_none h.toInvariant hyFind
          let state := forest.toState h.toInvariant
          have hyInvalidState : Not (state.valid y) := by
            simpa [state] using hyInvalidForest
          have hnot : Not (state.valid x /\ state.valid y) := by
            intro hxy
            exact hyInvalidState hxy.2
          have hsameUnion :
              State.SamePartition state (state.unionSpec x y) :=
            State.unionSpec_samePartition_self_of_not_valid state hnot
          have hsame :
              State.SamePartition
                (forest.toState holdLink.toInvariant)
                ((forest.toState h.toInvariant).unionSpec x y) := by
            simpa [state] using
              State.samePartition_trans hsameStates hsameUnion
          simp [unionByRank, rankAfterUnionByRank, hxFind, hyFind]
          exact ⟨h, holdLink, hsame⟩
      | some rootY =>
          by_cases hsameRoot : rootY = rootX
          · let state := forest.toState h.toInvariant
            have hxValidForest : forest.valid x :=
              forest.valid_of_findRoot?_eq_some hxFind
            have hyValidForest : forest.valid y :=
              forest.valid_of_findRoot?_eq_some hyFind
            have hxState : state.valid x := by
              simpa [state] using hxValidForest
            have hyState : state.valid y := by
              simpa [state] using hyValidForest
            have hreprX : state.repr x = rootX := by
              simpa [state] using
                forest.toState_repr_eq_of_findRoot?
                  h.toInvariant hxFind
            have hreprY : state.repr y = rootY := by
              simpa [state] using
                forest.toState_repr_eq_of_findRoot?
                  h.toInvariant hyFind
            have hsameRepr : state.repr x = state.repr y := by
              rw [hreprX, hreprY, hsameRoot]
            have hsameUnion :
                State.SamePartition state (state.unionSpec x y) :=
              State.unionSpec_samePartition_self_of_same state
                hxState hyState hsameRepr
            have hsame :
                State.SamePartition
                  (forest.toState holdLink.toInvariant)
                  ((forest.toState h.toInvariant).unionSpec x y) := by
              simpa [state] using
                State.samePartition_trans hsameStates hsameUnion
            simp [unionByRank, rankAfterUnionByRank, hxFind, hyFind,
              hsameRoot]
            exact ⟨h, holdLink, hsame⟩
          · rcases forest.rankedRootLink_refinement_profile_of_bump rank h
                hxFind hyFind hsameRoot
                (fun hEq => hbump hxFind hyFind hsameRoot hEq) with
              ⟨hlinked, hrankInv, hsame⟩
            simp [unionByRank, rankAfterUnionByRank, hxFind, hyFind,
              hsameRoot]
            exact ⟨hrankInv, hlinked, hsame⟩

theorem rankedRootLink_refinement_profile
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankSizeInvariant rank)
    {x y rootX rootY : Nat}
    (hxFind : forest.findRoot? x = some rootX)
    (hyFind : forest.findRoot? y = some rootY)
    (hne : rootY ≠ rootX) :
    exists hlinked :
      (forest.rankedRootLink rank rootX rootY).LinkableInvariant,
        (forest.rankedRootLink rank rootX rootY).RankInvariant
          (rankAfterRootLinkByRank rank rootX rootY) /\
        State.SamePartition
          ((forest.rankedRootLink rank rootX rootY).toState
            hlinked.toInvariant)
          ((forest.toState h.toInvariant).unionSpec x y) := by
  exact forest.rankedRootLink_refinement_profile_of_bump rank
    h.toRankInvariant hxFind hyFind hne
    (fun hrankEq =>
      RankSizeInvariant.bump_lt_of_findRoot? forest rank h
        hxFind hyFind hne hrankEq)

theorem unionByRank_refinement_profile
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankSizeInvariant rank) (x y : Nat) :
    (forest.unionByRank rank x y).RankInvariant
      (forest.rankAfterUnionByRank rank x y) /\
      exists hlinked :
        (forest.unionByRank rank x y).LinkableInvariant,
          State.SamePartition
            ((forest.unionByRank rank x y).toState hlinked.toInvariant)
            ((forest.toState h.toInvariant).unionSpec x y) := by
  exact forest.unionByRank_refinement_profile_of_bump rank
    h.toRankInvariant x y
    (fun hxFind hyFind hne hrankEq =>
      RankSizeInvariant.bump_lt_of_findRoot? forest rank h
        hxFind hyFind hne hrankEq)

theorem rankedRootLink_rankSizeInvariant_profile
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankComponentInvariant rank)
    {x y rootX rootY : Nat}
    (hxFind : forest.findRoot? x = some rootX)
    (hyFind : forest.findRoot? y = some rootY)
    (hne : rootY ≠ rootX) :
    exists hlinked :
      (forest.rankedRootLink rank rootX rootY).LinkableInvariant,
        (forest.rankedRootLink rank rootX rootY).RankSizeInvariant
          (rankAfterRootLinkByRank rank rootX rootY) /\
        State.SamePartition
          ((forest.rankedRootLink rank rootX rootY).toState
            hlinked.toInvariant)
          ((forest.toState h.toInvariant).unionSpec x y) := by
  rcases forest.rankedRootLink_refinement_profile rank
      h.toRankSizeInvariant hxFind hyFind hne with
    ⟨hlinked, _hrankInv, hsame⟩
  have hrootXValid : forest.valid rootX :=
    forest.findRoot?_some_valid h.toInvariant hxFind
  have hrootYValid : forest.valid rootY :=
    forest.findRoot?_some_valid h.toInvariant hyFind
  have hrootX : forest.IsRoot rootX :=
    forest.findRoot?_some_root h.toInvariant hxFind
  have hrootY : forest.IsRoot rootY :=
    forest.findRoot?_some_root h.toInvariant hyFind
  have hrankSize :
      (forest.rankedRootLink rank rootX rootY).RankSizeInvariant
        (rankAfterRootLinkByRank rank rootX rootY) := by
    by_cases hxyRank : rank rootX < rank rootY
    · have hneXY : rootX ≠ rootY := by
        intro hEq
        exact hne hEq.symm
      simpa [rankedRootLink, rankAfterRootLinkByRank, hxyRank] using
        forest.rootLink_rankSizeInvariant_of_rank_lt rank
          h.toRankSizeInvariant hrootXValid hrootYValid
          hrootX hrootY hneXY hxyRank
    · by_cases hyxRank : rank rootY < rank rootX
      · simpa [rankedRootLink, rankAfterRootLinkByRank, hxyRank, hyxRank] using
          forest.rootLink_rankSizeInvariant_of_rank_lt rank
            h.toRankSizeInvariant hrootYValid hrootXValid
            hrootY hrootX hne hyxRank
      · have hEqXY : rank rootX = rank rootY := by
          have hyxLe : rank rootX <= rank rootY :=
            Nat.le_of_not_gt hyxRank
          have hxyLe : rank rootY <= rank rootX :=
            Nat.le_of_not_gt hxyRank
          exact Nat.le_antisymm hyxLe hxyLe
        simpa [rankedRootLink, rankAfterRootLinkByRank, hxyRank, hyxRank] using
          forest.rootLink_rankSizeInvariant_of_rank_eq_bump rank h
            hrootYValid hrootXValid hrootY hrootX hne hEqXY.symm
  exact ⟨hlinked, hrankSize, hsame⟩

theorem unionByRank_rankSizeInvariant_profile
    (forest : ParentForest) (rank : Nat -> Nat)
    (h : forest.RankComponentInvariant rank) (x y : Nat) :
    (forest.unionByRank rank x y).RankSizeInvariant
      (forest.rankAfterUnionByRank rank x y) /\
      exists hlinked :
        (forest.unionByRank rank x y).LinkableInvariant,
          State.SamePartition
            ((forest.unionByRank rank x y).toState hlinked.toInvariant)
            ((forest.toState h.toInvariant).unionSpec x y) := by
  rcases forest.unionByRank_refinement_profile rank
      h.toRankSizeInvariant x y with
    ⟨_hrankInv, hlinked, hsame⟩
  have hrankSize :
      (forest.unionByRank rank x y).RankSizeInvariant
        (forest.rankAfterUnionByRank rank x y) := by
    cases hxFind : forest.findRoot? x with
    | none =>
        simp [unionByRank, rankAfterUnionByRank, hxFind]
        exact h.toRankSizeInvariant
    | some rootX =>
        cases hyFind : forest.findRoot? y with
        | none =>
            simp [unionByRank, rankAfterUnionByRank, hxFind, hyFind]
            exact h.toRankSizeInvariant
        | some rootY =>
            by_cases hsameRoot : rootY = rootX
            · simp [unionByRank, rankAfterUnionByRank, hxFind, hyFind,
                hsameRoot]
              exact h.toRankSizeInvariant
            · rcases forest.rankedRootLink_rankSizeInvariant_profile rank h
                  hxFind hyFind hsameRoot with
                ⟨_hlinkedRanked, hrankSizeRanked, _hsameRanked⟩
              simpa [unionByRank, rankAfterUnionByRank, hxFind, hyFind,
                hsameRoot] using hrankSizeRanked
  exact ⟨hrankSize, hlinked, hsame⟩

theorem rankedRootLink_rootMassInvariant_profile
    (forest : ParentForest) (rank mass : Nat -> Nat)
    (h : forest.RootMassInvariant rank mass)
    {x y rootX rootY : Nat}
    (hxFind : forest.findRoot? x = some rootX)
    (hyFind : forest.findRoot? y = some rootY)
    (hne : rootY ≠ rootX) :
    exists hlinked :
      (forest.rankedRootLink rank rootX rootY).LinkableInvariant,
        (forest.rankedRootLink rank rootX rootY).RootMassInvariant
          (rankAfterRootLinkByRank rank rootX rootY)
          (rootMassAfterRootLinkByRank rank mass rootX rootY) /\
        State.SamePartition
          ((forest.rankedRootLink rank rootX rootY).toState
            hlinked.toInvariant)
          ((forest.toState h.toInvariant).unionSpec x y) := by
  rcases forest.rankedRootLink_refinement_profile rank
      h.toRankSizeInvariant hxFind hyFind hne with
    ⟨hlinked, _hrankInv, hsame⟩
  have hrootXValid : forest.valid rootX :=
    forest.findRoot?_some_valid h.toInvariant hxFind
  have hrootYValid : forest.valid rootY :=
    forest.findRoot?_some_valid h.toInvariant hyFind
  have hrootX : forest.IsRoot rootX :=
    forest.findRoot?_some_root h.toInvariant hxFind
  have hrootY : forest.IsRoot rootY :=
    forest.findRoot?_some_root h.toInvariant hyFind
  have hrootMass :
      (forest.rankedRootLink rank rootX rootY).RootMassInvariant
        (rankAfterRootLinkByRank rank rootX rootY)
        (rootMassAfterRootLinkByRank rank mass rootX rootY) := by
    by_cases hxyRank : rank rootX < rank rootY
    · have hneXY : rootX ≠ rootY := by
        intro hEq
        exact hne hEq.symm
      simpa [rankedRootLink, rankAfterRootLinkByRank,
        rootMassAfterRootLinkByRank, hxyRank] using
        forest.rootLink_rootMassInvariant_of_rank_lt rank mass h
          hrootXValid hrootYValid hrootX hrootY hneXY hxyRank
    · by_cases hyxRank : rank rootY < rank rootX
      · simpa [rankedRootLink, rankAfterRootLinkByRank,
          rootMassAfterRootLinkByRank, hxyRank, hyxRank] using
          forest.rootLink_rootMassInvariant_of_rank_lt rank mass h
            hrootYValid hrootXValid hrootY hrootX hne hyxRank
      · have hEqXY : rank rootX = rank rootY := by
          have hyxLe : rank rootX <= rank rootY :=
            Nat.le_of_not_gt hyxRank
          have hxyLe : rank rootY <= rank rootX :=
            Nat.le_of_not_gt hxyRank
          exact Nat.le_antisymm hyxLe hxyLe
        simpa [rankedRootLink, rankAfterRootLinkByRank,
          rootMassAfterRootLinkByRank, hxyRank, hyxRank] using
          forest.rootLink_rootMassInvariant_of_rank_eq_bump rank mass h
            hrootYValid hrootXValid hrootY hrootX hne hEqXY.symm
  exact ⟨hlinked, hrootMass, hsame⟩

theorem unionByRank_rootMassInvariant_profile
    (forest : ParentForest) (rank mass : Nat -> Nat)
    (h : forest.RootMassInvariant rank mass) (x y : Nat) :
    (forest.unionByRank rank x y).RootMassInvariant
      (forest.rankAfterUnionByRank rank x y)
      (forest.rootMassAfterUnionByRank rank mass x y) /\
      exists hlinked :
        (forest.unionByRank rank x y).LinkableInvariant,
          State.SamePartition
            ((forest.unionByRank rank x y).toState hlinked.toInvariant)
            ((forest.toState h.toInvariant).unionSpec x y) := by
  rcases forest.unionByRank_refinement_profile rank
      h.toRankSizeInvariant x y with
    ⟨_hrankInv, hlinked, hsame⟩
  have hrootMass :
      (forest.unionByRank rank x y).RootMassInvariant
        (forest.rankAfterUnionByRank rank x y)
        (forest.rootMassAfterUnionByRank rank mass x y) := by
    cases hxFind : forest.findRoot? x with
    | none =>
        simp [unionByRank, rankAfterUnionByRank,
          rootMassAfterUnionByRank, hxFind]
        exact h
    | some rootX =>
        cases hyFind : forest.findRoot? y with
        | none =>
            simp [unionByRank, rankAfterUnionByRank,
              rootMassAfterUnionByRank, hxFind, hyFind]
            exact h
        | some rootY =>
            by_cases hsameRoot : rootY = rootX
            · simp [unionByRank, rankAfterUnionByRank,
                rootMassAfterUnionByRank, hxFind, hyFind, hsameRoot]
              exact h
            · rcases forest.rankedRootLink_rootMassInvariant_profile
                  rank mass h hxFind hyFind hsameRoot with
                ⟨_hlinkedRanked, hrootMassRanked, _hsameRanked⟩
              simpa [unionByRank, rankAfterUnionByRank,
                rootMassAfterUnionByRank, hxFind, hyFind, hsameRoot] using
                hrootMassRanked
  exact ⟨hrootMass, hlinked, hsame⟩

theorem rankedRootLink_rankPowerMassInvariant_profile
    (forest : ParentForest) (rank mass : Nat -> Nat)
    (h : forest.RankPowerMassInvariant rank mass)
    {x y rootX rootY : Nat}
    (hxFind : forest.findRoot? x = some rootX)
    (hyFind : forest.findRoot? y = some rootY)
    (hne : rootY ≠ rootX) :
    exists hlinked :
      (forest.rankedRootLink rank rootX rootY).LinkableInvariant,
        (forest.rankedRootLink rank rootX rootY).RankPowerMassInvariant
          (rankAfterRootLinkByRank rank rootX rootY)
          (rootMassAfterRootLinkByRank rank mass rootX rootY) /\
        State.SamePartition
          ((forest.rankedRootLink rank rootX rootY).toState
            hlinked.toInvariant)
          ((forest.toState h.toInvariant).unionSpec x y) := by
  rcases forest.rankedRootLink_refinement_profile rank
      h.toRankSizeInvariant hxFind hyFind hne with
    ⟨hlinked, _hrankInv, hsame⟩
  have hrootXValid : forest.valid rootX :=
    forest.findRoot?_some_valid h.toInvariant hxFind
  have hrootYValid : forest.valid rootY :=
    forest.findRoot?_some_valid h.toInvariant hyFind
  have hrootX : forest.IsRoot rootX :=
    forest.findRoot?_some_root h.toInvariant hxFind
  have hrootY : forest.IsRoot rootY :=
    forest.findRoot?_some_root h.toInvariant hyFind
  have hpower :
      (forest.rankedRootLink rank rootX rootY).RankPowerMassInvariant
        (rankAfterRootLinkByRank rank rootX rootY)
        (rootMassAfterRootLinkByRank rank mass rootX rootY) := by
    by_cases hxyRank : rank rootX < rank rootY
    · have hneXY : rootX ≠ rootY := by
        intro hEq
        exact hne hEq.symm
      simpa [rankedRootLink, rankAfterRootLinkByRank,
        rootMassAfterRootLinkByRank, hxyRank] using
        forest.rootLink_rankPowerMassInvariant_of_rank_lt rank mass h
          hrootXValid hrootYValid hrootX hrootY hneXY hxyRank
    · by_cases hyxRank : rank rootY < rank rootX
      · simpa [rankedRootLink, rankAfterRootLinkByRank,
          rootMassAfterRootLinkByRank, hxyRank, hyxRank] using
          forest.rootLink_rankPowerMassInvariant_of_rank_lt rank mass h
            hrootYValid hrootXValid hrootY hrootX hne hyxRank
      · have hEqXY : rank rootX = rank rootY := by
          have hyxLe : rank rootX <= rank rootY :=
            Nat.le_of_not_gt hyxRank
          have hxyLe : rank rootY <= rank rootX :=
            Nat.le_of_not_gt hxyRank
          exact Nat.le_antisymm hyxLe hxyLe
        simpa [rankedRootLink, rankAfterRootLinkByRank,
          rootMassAfterRootLinkByRank, hxyRank, hyxRank] using
          forest.rootLink_rankPowerMassInvariant_of_rank_eq_bump rank mass h
            hrootYValid hrootXValid hrootY hrootX hne hEqXY.symm
  exact ⟨hlinked, hpower, hsame⟩

theorem unionByRank_rankPowerMassInvariant_profile
    (forest : ParentForest) (rank mass : Nat -> Nat)
    (h : forest.RankPowerMassInvariant rank mass) (x y : Nat) :
    (forest.unionByRank rank x y).RankPowerMassInvariant
      (forest.rankAfterUnionByRank rank x y)
      (forest.rootMassAfterUnionByRank rank mass x y) /\
      exists hlinked :
        (forest.unionByRank rank x y).LinkableInvariant,
          State.SamePartition
            ((forest.unionByRank rank x y).toState hlinked.toInvariant)
            ((forest.toState h.toInvariant).unionSpec x y) := by
  rcases forest.unionByRank_refinement_profile rank
      h.toRankSizeInvariant x y with
    ⟨_hrankInv, hlinked, hsame⟩
  have hpower :
      (forest.unionByRank rank x y).RankPowerMassInvariant
        (forest.rankAfterUnionByRank rank x y)
        (forest.rootMassAfterUnionByRank rank mass x y) := by
    cases hxFind : forest.findRoot? x with
    | none =>
        simp [unionByRank, rankAfterUnionByRank,
          rootMassAfterUnionByRank, hxFind]
        exact h
    | some rootX =>
        cases hyFind : forest.findRoot? y with
        | none =>
            simp [unionByRank, rankAfterUnionByRank,
              rootMassAfterUnionByRank, hxFind, hyFind]
            exact h
        | some rootY =>
            by_cases hsameRoot : rootY = rootX
            · simp [unionByRank, rankAfterUnionByRank,
                rootMassAfterUnionByRank, hxFind, hyFind, hsameRoot]
              exact h
            · rcases forest.rankedRootLink_rankPowerMassInvariant_profile
                  rank mass h hxFind hyFind hsameRoot with
                ⟨_hlinkedRanked, hpowerRanked, _hsameRanked⟩
              simpa [unionByRank, rankAfterUnionByRank,
                rootMassAfterUnionByRank, hxFind, hyFind, hsameRoot] using
                hpowerRanked
  exact ⟨hpower, hlinked, hsame⟩

theorem rootLink_rankComponentInvariant_equal_bump_boundary_obstruction
    (forest : ParentForest) (rank : Nat -> Nat)
    {fromRoot toRoot nextRoot topRoot : Nat}
    (htoValid : forest.valid toRoot)
    (hnextValid : forest.valid nextRoot)
    (htopValid : forest.valid topRoot)
    (htoRoot : forest.IsRoot toRoot)
    (hnextRoot : forest.IsRoot nextRoot)
    (htopRoot : forest.IsRoot topRoot)
    (hne : fromRoot ≠ toRoot)
    (hnext_ne_to : nextRoot ≠ toRoot)
    (hnext_ne_from : nextRoot ≠ fromRoot)
    (htop_ne_to : topRoot ≠ toRoot)
    (htop_ne_from : topRoot ≠ fromRoot)
    (htop_ne_next : topRoot ≠ nextRoot)
    (hrankEq : rank fromRoot = rank toRoot)
    (hnextRank : rank nextRoot = rank fromRoot + 1)
    (htopRank : rank topRoot = rank fromRoot + 2)
    (hsizeBoundary : forest.size = rank fromRoot + 3) :
    Not ((forest.rootLink fromRoot toRoot).RankComponentInvariant
      (bumpRank rank toRoot)) := by
  intro hpost
  have htoNewValid :
      (forest.rootLink fromRoot toRoot).valid toRoot := by
    simpa [rootLink_size] using htoValid
  have hnextNewValid :
      (forest.rootLink fromRoot toRoot).valid nextRoot := by
    simpa [rootLink_size] using hnextValid
  have htopNewValid :
      (forest.rootLink fromRoot toRoot).valid topRoot := by
    simpa [rootLink_size] using htopValid
  have htoNewRoot :
      (forest.rootLink fromRoot toRoot).IsRoot toRoot :=
    forest.rootLink_isRoot_of_ne htoValid
      (by intro hEq; exact hne hEq.symm) htoRoot
  have hnextNewRoot :
      (forest.rootLink fromRoot toRoot).IsRoot nextRoot :=
    forest.rootLink_isRoot_of_ne hnextValid hnext_ne_from hnextRoot
  have htopNewRoot :
      (forest.rootLink fromRoot toRoot).IsRoot topRoot :=
    forest.rootLink_isRoot_of_ne htopValid htop_ne_from htopRoot
  have hnewEq :
      bumpRank rank toRoot toRoot = bumpRank rank toRoot nextRoot := by
    simp [bumpRank, hnext_ne_to, hrankEq, hnextRank]
  have htopNext :
      bumpRank rank toRoot topRoot =
        bumpRank rank toRoot toRoot + 1 := by
    simp [bumpRank, htop_ne_to, hrankEq, htopRank]
  have hroom :=
    hpost.equal_pair_next_rank_bump_lt
      htoNewValid hnextNewValid htopNewValid
      htoNewRoot hnextNewRoot htopNewRoot
      hnext_ne_to htop_ne_to htop_ne_next
      hnewEq htopNext
  simp [rootLink_size, bumpRank, hsizeBoundary, hrankEq] at hroom

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

def fullCompressionFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  (backend.fullCompressFindTrace x).length

def rankGapFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.state.forest.maxSearchFuel + 1
  | some root => backend.state.rank root - backend.state.rank x + 1

def logRankFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.state.forest.maxSearchFuel + 1
  | some _root => Nat.log2 backend.state.forest.size + 1

/--
Coarse rank bucket used by the first Tarjan-facing accounting checkpoint.

Bucket `b` contains ranks whose successor has binary logarithm `b`; equivalently
the bucket widths grow geometrically. This is not the inverse-Ackermann level
function yet, but it is the first explicit rank-bucket interface above the
plain log-rank bound.
-/
def rankBucket (rank : Nat) : Nat :=
  Nat.log2 (rank + 1)

def rankBucketWidth (bucket : Nat) : Nat :=
  2 ^ (bucket + 1)

def rankBucketFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.state.forest.maxSearchFuel + 1
  | some root => rankBucketWidth (rankBucket (backend.state.rank root))

def unionByRankCredit
    (_backend : NoCompressionRankedMassBackendState) (_x _y : Nat) : Nat :=
  1

def rankSizePotential
    (backend : NoCompressionRankedMassBackendState) : Nat :=
  backend.state.forest.size

def rankBucketPotential
    (backend : NoCompressionRankedMassBackendState) : Nat :=
  backend.state.forest.size * (Nat.log2 backend.state.forest.size + 1)

def nodeRootParentRankSlack
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) : Nat :=
  match backend.state.forest.parent? x with
  | none => 0
  | some parent => backend.state.rank root - backend.state.rank parent

def traceRootParentRankSlack
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeRootParentRankSlack root x +
        backend.traceRootParentRankSlack root xs

def nodeFindRootParentRankSlack
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => 0
  | some root => backend.nodeRootParentRankSlack root x

def rankSlackPotentialOver
    (backend : NoCompressionRankedMassBackendState) : List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeFindRootParentRankSlack x +
        backend.rankSlackPotentialOver xs

def rankSlackPotential
    (backend : NoCompressionRankedMassBackendState) : Nat :=
  backend.rankSlackPotentialOver (List.range backend.state.forest.size)

def rankSlackFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.state.forest.maxSearchFuel + 1
  | some _root => 2

def rankSlackUnionCredit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) : Nat :=
  rankSlackPotential ((backend.unionCosted x y).erase) -
    rankSlackPotential backend + 1

def rankSlackSizeUnionCredit
    (backend : NoCompressionRankedMassBackendState) (_x _y : Nat) : Nat :=
  rankBucketPotential backend + 1

theorem rankSlackPotentialOver_le_of_forall_mem
    (left right : NoCompressionRankedMassBackendState) :
    forall (xs : List Nat),
      (forall x, x ∈ xs ->
        left.nodeFindRootParentRankSlack x <=
          right.nodeFindRootParentRankSlack x) ->
      left.rankSlackPotentialOver xs <= right.rankSlackPotentialOver xs
  | [], _hle => by
      simp [rankSlackPotentialOver]
  | x :: xs, hle => by
      have hx :
          left.nodeFindRootParentRankSlack x <=
            right.nodeFindRootParentRankSlack x :=
        hle x (by simp)
      have hxs :
          forall y, y ∈ xs ->
            left.nodeFindRootParentRankSlack y <=
              right.nodeFindRootParentRankSlack y := by
        intro y hy
        exact hle y (by simp [hy])
      have htail :=
        rankSlackPotentialOver_le_of_forall_mem left right xs hxs
      simp [rankSlackPotentialOver]
      omega

theorem rankSlackPotentialOver_le_length_mul
    (backend : NoCompressionRankedMassBackendState) :
    forall (xs : List Nat) (bound : Nat),
      (forall x, x ∈ xs ->
        backend.nodeFindRootParentRankSlack x <= bound) ->
      backend.rankSlackPotentialOver xs <= xs.length * bound
  | [], bound, _hle => by
      simp [rankSlackPotentialOver]
  | x :: xs, bound, hle => by
      have hx :
          backend.nodeFindRootParentRankSlack x <= bound :=
        hle x (by simp)
      have hxs :
          forall y, y ∈ xs ->
            backend.nodeFindRootParentRankSlack y <= bound := by
        intro y hy
        exact hle y (by simp [hy])
      have htail :=
        rankSlackPotentialOver_le_length_mul backend xs bound hxs
      have hmul :
          (xs.length + 1) * bound = xs.length * bound + bound := by
        simpa [Nat.succ_eq_add_one] using Nat.succ_mul xs.length bound
      simp [rankSlackPotentialOver]
      calc
        backend.nodeFindRootParentRankSlack x +
            backend.rankSlackPotentialOver xs
            <= bound + xs.length * bound := Nat.add_le_add hx htail
        _ = xs.length * bound + bound := Nat.add_comm _ _
        _ = (xs.length + 1) * bound := hmul.symm

theorem rankSlackPotentialOver_add_single_le_of_forall_mem
    (left right : NoCompressionRankedMassBackendState) :
    forall (xs : List Nat) {x d : Nat},
      xs.Nodup ->
      x ∈ xs ->
      left.nodeFindRootParentRankSlack x + d <=
        right.nodeFindRootParentRankSlack x ->
      (forall y, y ∈ xs -> y ≠ x ->
        left.nodeFindRootParentRankSlack y <=
          right.nodeFindRootParentRankSlack y) ->
      left.rankSlackPotentialOver xs + d <= right.rankSlackPotentialOver xs
  | [], x, d, _hnodup, hmem, _hdrop, _hle => by
      simp at hmem
  | y :: ys, x, d, hnodup, hmem, hdrop, hle => by
      have hnodupCons := hnodup
      simp at hnodupCons
      rcases hnodupCons with ⟨hyNotMem, hnodupTail⟩
      by_cases hyx : y = x
      · subst x
        have htailLe :
            left.rankSlackPotentialOver ys <=
              right.rankSlackPotentialOver ys := by
          apply rankSlackPotentialOver_le_of_forall_mem
          intro z hz
          have hzy : z ≠ y := by
            intro hzx
            exact hyNotMem (by simpa [hzx] using hz)
          exact hle z (by simp [hz]) hzy
        simp [rankSlackPotentialOver]
        omega
      · have hxTail : x ∈ ys := by
          have hcases : x = y ∨ x ∈ ys := by
            simpa using hmem
          cases hcases with
          | inl hxy =>
              exact False.elim (hyx hxy.symm)
          | inr htail =>
              exact htail
        have hhead :
            left.nodeFindRootParentRankSlack y <=
              right.nodeFindRootParentRankSlack y :=
          hle y (by simp) hyx
        have htail :
            left.rankSlackPotentialOver ys + d <=
              right.rankSlackPotentialOver ys :=
          rankSlackPotentialOver_add_single_le_of_forall_mem
            left right ys hnodupTail hxTail hdrop (by
              intro z hz hzx
              exact hle z (by simp [hz]) hzx)
        simp [rankSlackPotentialOver]
        omega

theorem rankSlackPotential_le_rankBucketPotential
    (backend : NoCompressionRankedMassBackendState) :
    rankSlackPotential backend <= rankBucketPotential backend := by
  unfold rankSlackPotential rankBucketPotential
  have hnode :
      forall x, x ∈ List.range backend.state.forest.size ->
        backend.nodeFindRootParentRankSlack x <=
          Nat.log2 backend.state.forest.size + 1 := by
    intro x _hx
    cases hfind : backend.state.forest.findRoot? x with
    | none =>
        simp [nodeFindRootParentRankSlack, hfind]
    | some root =>
        have hrootRank :
            backend.state.rank root <= Nat.log2 backend.state.forest.size :=
          backend.findRoot?_root_rank_le_log2_size hfind
        cases hparent : backend.state.forest.parent? x with
        | none =>
            simp [nodeFindRootParentRankSlack, nodeRootParentRankSlack,
              hfind, hparent]
        | some parent =>
            have hsub :
                backend.state.rank root - backend.state.rank parent <=
                  backend.state.rank root := Nat.sub_le _ _
            simp [nodeFindRootParentRankSlack, nodeRootParentRankSlack,
              hfind, hparent]
            omega
  have hsum :=
    backend.rankSlackPotentialOver_le_length_mul
      (List.range backend.state.forest.size)
      (Nat.log2 backend.state.forest.size + 1) hnode
  simpa using hsum

theorem compressFindCosted_nodeFindRootParentRankSlack_eq_zero_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    ((backend.compressFindCosted x).erase.1).nodeFindRootParentRankSlack x =
      0 := by
  have hfindEq :
      ((backend.compressFindCosted x).erase.1).state.forest.findRoot? x =
        some root := by
    rw [backend.compressFindCosted_findRoot?_eq x x]
    exact hfind
  have hparent :
      ((backend.compressFindCosted x).erase.1).state.forest.parent? x =
        some root :=
    backend.compressFindCosted_parent?_eq_root_of_findRoot? hfind
  have hrankEq :
      ((backend.compressFindCosted x).erase.1).state.rank =
        backend.state.rank :=
    backend.compressFindCosted_rank_eq x
  simp [nodeFindRootParentRankSlack, nodeRootParentRankSlack, hfindEq,
    hparent]

theorem compressFindCosted_nodeFindRootParentRankSlack_le_of_ne
    (backend : NoCompressionRankedMassBackendState)
    {x y : Nat}
    (hne : y ≠ x) :
    ((backend.compressFindCosted x).erase.1).nodeFindRootParentRankSlack y <=
      backend.nodeFindRootParentRankSlack y := by
  cases hyfind : backend.state.forest.findRoot? y with
  | none =>
      have hfindEq :
          ((backend.compressFindCosted x).erase.1).state.forest.findRoot? y =
            none := by
        rw [backend.compressFindCosted_findRoot?_eq x y]
        exact hyfind
      simp [nodeFindRootParentRankSlack, hfindEq, hyfind]
  | some yroot =>
      have hfindEq :
          ((backend.compressFindCosted x).erase.1).state.forest.findRoot? y =
            some yroot := by
        rw [backend.compressFindCosted_findRoot?_eq x y]
        exact hyfind
      have hrankEq :
          ((backend.compressFindCosted x).erase.1).state.rank =
            backend.state.rank :=
        backend.compressFindCosted_rank_eq x
      cases hparent : backend.state.forest.parent? y with
      | none =>
          have hyvalid :
              backend.state.forest.valid y :=
            backend.state.forest.valid_of_findRoot?_eq_some hyfind
          rcases backend.state.forest.exists_parent?_of_valid hyvalid with
            ⟨parent, hparentSome⟩
          rw [hparent] at hparentSome
          cases hparentSome
      | some parent =>
          have hparentNew :
              ((backend.compressFindCosted x).erase.1).state.forest.parent? y =
                some parent :=
            backend.compressFindCosted_parent?_eq_old_of_ne hne hparent
          have hparentRankLe :
              backend.state.rank parent <= backend.state.rank yroot := by
            by_cases hparentY : parent = y
            · subst hparentY
              exact backend.rank_le_root_rank_of_findRoot? hyfind
            · have hparentFind :
                  backend.state.forest.findRoot? parent = some yroot :=
                backend.findRoot?_parent_eq_of_parent?_ne
                  hparent hparentY hyfind
              exact backend.rank_le_root_rank_of_findRoot? hparentFind
          simp [nodeFindRootParentRankSlack, nodeRootParentRankSlack,
            hfindEq, hyfind, hparent, hparentNew]
          rw [hrankEq]
          omega

theorem rankSlackPotential_compressFindCosted_add_nodeRootParentRankSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    rankSlackPotential ((backend.compressFindCosted x).erase.1) +
        backend.nodeRootParentRankSlack root x <=
      rankSlackPotential backend := by
  let final := (backend.compressFindCosted x).erase.1
  unfold rankSlackPotential
  have hsize : final.state.forest.size = backend.state.forest.size := by
    simpa [final] using backend.compressFindCosted_forest_size_eq x
  rw [hsize]
  apply rankSlackPotentialOver_add_single_le_of_forall_mem
  · exact List.nodup_range
  · exact List.mem_range.mpr
      (backend.state.forest.valid_of_findRoot?_eq_some hfind)
  · change final.nodeFindRootParentRankSlack x +
        backend.nodeRootParentRankSlack root x <=
        backend.nodeFindRootParentRankSlack x
    have hzero :
        final.nodeFindRootParentRankSlack x = 0 := by
      simpa [final] using
        backend.compressFindCosted_nodeFindRootParentRankSlack_eq_zero_of_findRoot?
          hfind
    rw [hzero]
    simp [nodeFindRootParentRankSlack, hfind]
  · intro y _hymem hyx
    change final.nodeFindRootParentRankSlack y <=
      backend.nodeFindRootParentRankSlack y
    simpa [final] using
      backend.compressFindCosted_nodeFindRootParentRankSlack_le_of_ne hyx

theorem compressPathFindFuelTrace_rank_le_of_mem_of_findRoot?
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root y : Nat},
      backend.state.forest.findRoot? x = some root ->
      y ∈ backend.compressPathFindFuelTrace fuel x ->
      backend.state.rank x <= backend.state.rank y
  | 0, x, root, y, _hfind, hmem => by
      have hyx : y = x := by
        simpa [compressPathFindFuelTrace] using hmem
      subst y
      omega
  | fuel + 1, x, root, y, hfind, hmem => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          have hyx : y = x := by
            simpa [compressPathFindFuelTrace, hparent] using hmem
          subst y
          omega
      | some parent =>
          by_cases hsame : parent = x
          · have hyx : y = x := by
              simpa [compressPathFindFuelTrace, hparent, hsame] using hmem
            subst y
            omega
          · have hmemCases :
                y = x ∨
                  y ∈ backend.compressPathFindFuelTrace fuel parent := by
              simpa [compressPathFindFuelTrace, hparent, hsame] using hmem
            rcases hmemCases with hyx | htailMem
            · subst y
              omega
            · have hparentFind :
                  backend.state.forest.findRoot? parent = some root :=
                backend.findRoot?_parent_eq_of_parent?_ne
                  hparent hsame hfind
              have htailRank :
                  backend.state.rank parent <= backend.state.rank y :=
                compressPathFindFuelTrace_rank_le_of_mem_of_findRoot?
                  backend fuel hparentFind htailMem
              have hparentRank :
                  backend.state.rank x < backend.state.rank parent :=
                backend.inv.toRankInvariant.parent_rank_lt hparent hsame
              omega

theorem not_mem_parent_compressPathFindFuelTrace_of_parent?_ne
    (backend : NoCompressionRankedMassBackendState)
    (fuel : Nat) {x parent root : Nat}
    (hparent : backend.state.forest.parent? x = some parent)
    (hne : parent ≠ x)
    (hparentFind : backend.state.forest.findRoot? parent = some root) :
    x ∉ backend.compressPathFindFuelTrace fuel parent := by
  intro hmem
  have htailRank :
      backend.state.rank parent <= backend.state.rank x :=
    backend.compressPathFindFuelTrace_rank_le_of_mem_of_findRoot?
      fuel hparentFind hmem
  have hparentRank :
      backend.state.rank x < backend.state.rank parent :=
    backend.inv.toRankInvariant.parent_rank_lt hparent hne
  omega

theorem compressPathFindFuelCosted_nodeRootParentRankSlack_eq_old_of_not_mem_trace
    (backend : NoCompressionRankedMassBackendState)
    (fuel : Nat) {x y parent root : Nat}
    (hnot : y ∉ backend.compressPathFindFuelTrace fuel x)
    (hparent : backend.state.forest.parent? y = some parent) :
    ((backend.compressPathFindFuelCosted fuel x).erase.1).nodeRootParentRankSlack
      root y =
      backend.nodeRootParentRankSlack root y := by
  have hparentNew :
      ((backend.compressPathFindFuelCosted fuel x).erase.1).state.forest.parent?
        y =
        some parent :=
    backend.compressPathFindFuelCosted_parent?_eq_old_of_not_mem_trace
      fuel hnot hparent
  have hrankEq :
      ((backend.compressPathFindFuelCosted fuel x).erase.1).state.rank =
        backend.state.rank :=
    backend.compressPathFindFuelCosted_rank_eq fuel x
  simp [nodeRootParentRankSlack, hparentNew, hparent]
  rw [hrankEq]

theorem compressPathFindFuelCosted_rankSlackPotential_add_traceRootParentRankSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root : Nat},
      backend.state.forest.findRoot? x = some root ->
      rankSlackPotential ((backend.compressPathFindFuelCosted fuel x).erase.1) +
          backend.traceRootParentRankSlack root
            (backend.compressPathFindFuelTrace fuel x) <=
        rankSlackPotential backend
  | 0, x, root, hfind => by
      simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
        traceRootParentRankSlack] using
        backend.rankSlackPotential_compressFindCosted_add_nodeRootParentRankSlack_le_of_findRoot?
          hfind
  | fuel + 1, x, root, hfind => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
            traceRootParentRankSlack, hparent] using
            backend.rankSlackPotential_compressFindCosted_add_nodeRootParentRankSlack_le_of_findRoot?
              hfind
      | some parent =>
          by_cases hsame : parent = x
          · simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
              traceRootParentRankSlack, hparent, hsame] using
              backend.rankSlackPotential_compressFindCosted_add_nodeRootParentRankSlack_le_of_findRoot?
                hfind
          · have hparentFind :
                backend.state.forest.findRoot? parent = some root :=
              backend.findRoot?_parent_eq_of_parent?_ne
                hparent hsame hfind
            let tail :=
              (backend.compressPathFindFuelCosted fuel parent).erase.1
            have htailDrop :
                rankSlackPotential tail +
                    backend.traceRootParentRankSlack root
                      (backend.compressPathFindFuelTrace fuel parent) <=
                  rankSlackPotential backend := by
              simpa [tail] using
                compressPathFindFuelCosted_rankSlackPotential_add_traceRootParentRankSlack_le_of_findRoot?
                  backend fuel hparentFind
            have htailFindX :
                tail.state.forest.findRoot? x = some root := by
              rw [show tail.state.forest.findRoot? x =
                    backend.state.forest.findRoot? x by
                simpa [tail] using
                  backend.compressPathFindFuelCosted_findRoot?_eq
                    fuel parent x]
              exact hfind
            have hxNotTail :
                x ∉ backend.compressPathFindFuelTrace fuel parent :=
              backend.not_mem_parent_compressPathFindFuelTrace_of_parent?_ne
                fuel hparent hsame hparentFind
            have hxSlack :
                tail.nodeRootParentRankSlack root x =
                  backend.nodeRootParentRankSlack root x := by
              simpa [tail] using
                backend.compressPathFindFuelCosted_nodeRootParentRankSlack_eq_old_of_not_mem_trace
                  fuel hxNotTail hparent
            have hstep :
                rankSlackPotential ((tail.compressFindCosted x).erase.1) +
                    tail.nodeRootParentRankSlack root x <=
                  rankSlackPotential tail :=
              tail.rankSlackPotential_compressFindCosted_add_nodeRootParentRankSlack_le_of_findRoot?
                htailFindX
            rw [hxSlack] at hstep
            have hcombine :
                rankSlackPotential ((tail.compressFindCosted x).erase.1) +
                    backend.nodeRootParentRankSlack root x +
                    backend.traceRootParentRankSlack root
                      (backend.compressPathFindFuelTrace fuel parent) <=
                  rankSlackPotential backend := by
              omega
            simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
              traceRootParentRankSlack, hparent, hsame, tail, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using hcombine

theorem rankSlackPotential_fullCompressFindCosted_add_traceRootParentRankSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) +
        backend.traceRootParentRankSlack root (backend.fullCompressFindTrace x) <=
      rankSlackPotential backend := by
  simpa [fullCompressFindCosted, fullCompressFindTrace] using
    backend.compressPathFindFuelCosted_rankSlackPotential_add_traceRootParentRankSlack_le_of_findRoot?
      backend.state.forest.maxSearchFuel hfind

theorem fullCompressFindCosted_eq_self_of_findRoot?_none
    (backend : NoCompressionRankedMassBackendState)
    {x : Nat}
    (hfind : backend.state.forest.findRoot? x = none) :
    (backend.fullCompressFindCosted x).erase.1 = backend := by
  have hinvalid :
      ¬ backend.state.forest.valid x :=
    backend.state.forest.invalid_of_findRoot?_eq_none
      backend.inv.toInvariant hfind
  have hparent : backend.state.forest.parent? x = none := by
    cases hparent : backend.state.forest.parent? x with
    | none => rfl
    | some parent =>
        have hx : backend.state.forest.valid x :=
          backend.state.forest.valid_of_parent?_eq_some hparent
        exact False.elim (hinvalid hx)
  cases hfuel : backend.state.forest.maxSearchFuel with
  | zero =>
      unfold fullCompressFindCosted
      rw [hfuel]
      simp [compressPathFindFuelCosted,
        compressFindCosted, backend.compressFindResult_none x hfind]
  | succ fuel =>
      unfold fullCompressFindCosted
      rw [hfuel]
      simp [compressPathFindFuelCosted, hparent,
        compressFindCosted, backend.compressFindResult_none x hfind]

theorem rankSlackPotential_fullCompressFindCosted_eq_of_findRoot?_none
    (backend : NoCompressionRankedMassBackendState)
    {x : Nat}
    (hfind : backend.state.forest.findRoot? x = none) :
    rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) =
      rankSlackPotential backend := by
  rw [backend.fullCompressFindCosted_eq_self_of_findRoot?_none hfind]

theorem rank_succ_le_rankBucketWidth (rank : Nat) :
    rank + 1 <= rankBucketWidth (rankBucket rank) := by
  have hlt : rank + 1 < 2 ^ (Nat.log2 (rank + 1) + 1) :=
    Nat.lt_log2_self (n := rank + 1)
  exact Nat.le_of_lt (by
    simpa [rankBucket, rankBucketWidth] using hlt)

theorem fullCompressFindCosted_cost_le_rankGapFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost <=
      backend.rankGapFindCredit x := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      have hcost := backend.fullCompressFindCosted_cost_le x
      simpa [rankGapFindCredit, hfind] using hcost
  | some root =>
      have hcostEq := backend.fullCompressFindCosted_cost_eq_trace_length x
      have htrace :=
        backend.fullCompressFindTrace_length_le_rank_gap_of_findRoot? hfind
      rw [hcostEq]
      simpa [rankGapFindCredit, hfind] using htrace

theorem rankGapFindCredit_le_logRankFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    backend.rankGapFindCredit x <= backend.logRankFindCredit x := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp [rankGapFindCredit, logRankFindCredit, hfind]
  | some root =>
      have hroot :=
        backend.findRoot?_root_rank_le_log2_size hfind
      have hsub :
          backend.state.rank root - backend.state.rank x <=
            backend.state.rank root := Nat.sub_le _ _
      simp [rankGapFindCredit, logRankFindCredit, hfind]
      omega

theorem fullCompressFindCosted_cost_le_logRankFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost <=
      backend.logRankFindCredit x := by
  exact Nat.le_trans
    (backend.fullCompressFindCosted_cost_le_rankGapFindCredit x)
    (backend.rankGapFindCredit_le_logRankFindCredit x)

theorem rankGapFindCredit_le_rankBucketFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    backend.rankGapFindCredit x <= backend.rankBucketFindCredit x := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp [rankGapFindCredit, rankBucketFindCredit, hfind]
  | some root =>
      have hbucket :=
        rank_succ_le_rankBucketWidth (backend.state.rank root)
      have hsub :
          backend.state.rank root - backend.state.rank x <=
            backend.state.rank root := Nat.sub_le _ _
      simp [rankGapFindCredit, rankBucketFindCredit, hfind]
      omega

theorem fullCompressFindTrace_length_le_rankBucketWidth_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    (backend.fullCompressFindTrace x).length <=
      rankBucketWidth (rankBucket (backend.state.rank root)) := by
  have hgap :=
    backend.fullCompressFindTrace_length_le_rank_gap_of_findRoot? hfind
  have hbucket :=
    rank_succ_le_rankBucketWidth (backend.state.rank root)
  have hsub :
      backend.state.rank root - backend.state.rank x <=
        backend.state.rank root := Nat.sub_le _ _
  omega

theorem compressPathFindFuelTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root : Nat},
      backend.state.forest.findRoot? x = some root ->
      (backend.compressPathFindFuelTrace fuel x).length <=
        backend.traceRootParentRankSlack root
          (backend.compressPathFindFuelTrace fuel x) + 2
  | 0, x, root, _hfind => by
      simp [compressPathFindFuelTrace, traceRootParentRankSlack]
  | fuel + 1, x, root, hfind => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simp [compressPathFindFuelTrace, traceRootParentRankSlack, hparent]
      | some parent =>
          by_cases hsame : parent = x
          · simp [compressPathFindFuelTrace, traceRootParentRankSlack,
              nodeRootParentRankSlack, hparent, hsame]
          · have hparentFind :
                backend.state.forest.findRoot? parent = some root :=
              backend.findRoot?_parent_eq_of_parent?_ne hparent hsame hfind
            by_cases hparentRoot : parent = root
            · have hroot :
                  backend.state.forest.IsRoot root :=
                backend.state.forest.findRoot?_some_root
                  backend.inv.toInvariant hfind
              have htail :
                  backend.compressPathFindFuelTrace fuel root = [root] :=
                backend.compressPathFindFuelTrace_eq_singleton_of_root
                  fuel hroot
              have hrootNeX : root ≠ x := by
                intro hrootX
                exact hsame (hparentRoot.trans hrootX)
              simp [compressPathFindFuelTrace, traceRootParentRankSlack,
                nodeRootParentRankSlack, hparent, hparentRoot, htail,
                hrootNeX]
            · have htail :=
                compressPathFindFuelTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
                  backend fuel hparentFind
              have hparentRank :
                  backend.state.rank parent < backend.state.rank root :=
                backend.state.forest.findRoot?_rank_lt_of_ne
                  backend.state.rank backend.inv.toRankInvariant
                  hparentFind hparentRoot
              have hslack :
                  1 <= backend.nodeRootParentRankSlack root x := by
                simp [nodeRootParentRankSlack, hparent]
                omega
              simp [compressPathFindFuelTrace, traceRootParentRankSlack,
                hparent, hsame]
              omega

theorem fullCompressFindTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    (backend.fullCompressFindTrace x).length <=
      backend.traceRootParentRankSlack root
        (backend.fullCompressFindTrace x) + 2 := by
  simpa [fullCompressFindTrace] using
    backend.compressPathFindFuelTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
      backend.state.forest.maxSearchFuel hfind

theorem fullCompressFindCosted_nodeRootParentRankSlack_eq_zero_of_trace_mem
    (backend : NoCompressionRankedMassBackendState)
    {x root y : Nat}
    (hfind : backend.state.forest.findRoot? x = some root)
    (hmem : y ∈ backend.fullCompressFindTrace x) :
    ((backend.fullCompressFindCosted x).erase.1).nodeRootParentRankSlack
      root y = 0 := by
  have hparent :=
    backend.fullCompressFindCosted_trace_parent?_eq_root_of_findRoot?
      hfind hmem
  simp [nodeRootParentRankSlack, hparent]

theorem traceRootParentRankSlack_eq_zero_of_forall
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    forall (trace : List Nat),
      (forall y, y ∈ trace -> backend.nodeRootParentRankSlack root y = 0) ->
        backend.traceRootParentRankSlack root trace = 0
  | [], _h => by
      simp [traceRootParentRankSlack]
  | y :: ys, h => by
      have hy : backend.nodeRootParentRankSlack root y = 0 := by
        exact h y (by simp)
      have hys :
          forall z, z ∈ ys ->
            backend.nodeRootParentRankSlack root z = 0 := by
        intro z hz
        exact h z (by simp [hz])
      have htail :=
        traceRootParentRankSlack_eq_zero_of_forall backend root ys hys
      simp [traceRootParentRankSlack, hy, htail]

theorem fullCompressFindCosted_traceRootParentRankSlack_eq_zero_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    ((backend.fullCompressFindCosted x).erase.1).traceRootParentRankSlack
      root (backend.fullCompressFindTrace x) = 0 := by
  apply traceRootParentRankSlack_eq_zero_of_forall
  intro y hmem
  exact
    backend.fullCompressFindCosted_nodeRootParentRankSlack_eq_zero_of_trace_mem
      hfind hmem

theorem fullCompressFindCosted_cost_add_traceRootParentRankSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    (backend.fullCompressFindCosted x).cost +
        ((backend.fullCompressFindCosted x).erase.1).traceRootParentRankSlack
          root (backend.fullCompressFindTrace x) <=
      2 + backend.traceRootParentRankSlack root
        (backend.fullCompressFindTrace x) := by
  have hcost := backend.fullCompressFindCosted_cost_eq_trace_length x
  have hlen :=
    backend.fullCompressFindTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
      hfind
  have hzero :=
    backend.fullCompressFindCosted_traceRootParentRankSlack_eq_zero_of_findRoot?
      hfind
  rw [hcost, hzero]
  omega

theorem fullCompressFindCosted_cost_add_rankSlackPotential_le_two_add_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    (backend.fullCompressFindCosted x).cost +
        rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) <=
      2 + rankSlackPotential backend := by
  have hlocal :=
    backend.fullCompressFindCosted_cost_add_traceRootParentRankSlack_le_of_findRoot?
      hfind
  have hdrop :=
    backend.rankSlackPotential_fullCompressFindCosted_add_traceRootParentRankSlack_le_of_findRoot?
      hfind
  omega

theorem fullCompressFindCosted_cost_add_rankSlackPotential_le_rankSlackFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost +
        rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.rankSlackFindCredit x + rankSlackPotential backend := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      have hcost := backend.fullCompressFindCosted_cost_le x
      have hpot :=
        backend.rankSlackPotential_fullCompressFindCosted_eq_of_findRoot?_none
          hfind
      simp [rankSlackFindCredit, hfind]
      rw [hpot]
      omega
  | some root =>
      have hbound :=
        backend.fullCompressFindCosted_cost_add_rankSlackPotential_le_two_add_of_findRoot?
          hfind
      simpa [rankSlackFindCredit, hfind] using hbound

theorem fullCompressFindCosted_nodeFindRootParentRankSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root y : Nat}
    (hfind : backend.state.forest.findRoot? x = some root)
    (hy : backend.state.forest.valid y) :
    ((backend.fullCompressFindCosted x).erase.1).nodeFindRootParentRankSlack
      y <= backend.nodeFindRootParentRankSlack y := by
  let final := (backend.fullCompressFindCosted x).erase.1
  have hfindEq :
      final.state.forest.findRoot? y =
      backend.state.forest.findRoot? y := by
    simpa [final] using backend.fullCompressFindCosted_findRoot?_eq x y
  have hrankEq : final.state.rank = backend.state.rank := by
    simpa [final] using backend.fullCompressFindCosted_rank_eq x
  change final.nodeFindRootParentRankSlack y <=
    backend.nodeFindRootParentRankSlack y
  by_cases hmem : y ∈ backend.fullCompressFindTrace x
  · have hyFind :
        backend.state.forest.findRoot? y = some root :=
      backend.fullCompressFindTrace_mem_findRoot?_eq_of_findRoot?
        hfind hmem
    have hzero :
        final.nodeRootParentRankSlack root y = 0 := by
      simpa [final] using
        backend.fullCompressFindCosted_nodeRootParentRankSlack_eq_zero_of_trace_mem
          hfind hmem
    simp [nodeFindRootParentRankSlack, hfindEq, hyFind, hzero]
  · rcases backend.state.forest.exists_parent?_of_valid hy with
      ⟨parent, hparent⟩
    have hparentFinal :
        final.state.forest.parent? y = some parent := by
      simpa [final] using
        backend.fullCompressFindCosted_parent?_eq_old_of_not_mem_trace
          hmem hparent
    cases hyFind : backend.state.forest.findRoot? y with
    | none =>
        simp [nodeFindRootParentRankSlack, hfindEq, hyFind]
    | some yroot =>
        have hparentRankLe :
            backend.state.rank parent <= backend.state.rank yroot := by
          by_cases hparentY : parent = y
          · subst hparentY
            exact backend.rank_le_root_rank_of_findRoot? hyFind
          · have hparentFind :
                backend.state.forest.findRoot? parent = some yroot :=
              backend.findRoot?_parent_eq_of_parent?_ne
                hparent hparentY hyFind
            exact backend.rank_le_root_rank_of_findRoot? hparentFind
        simp [nodeFindRootParentRankSlack, nodeRootParentRankSlack,
          hfindEq, hyFind, hparent, hparentFinal]
        rw [hrankEq]
        omega

theorem rankSlackPotential_fullCompressFindCosted_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) <=
      rankSlackPotential backend := by
  let final := (backend.fullCompressFindCosted x).erase.1
  unfold rankSlackPotential
  have hsize : final.state.forest.size = backend.state.forest.size := by
    simpa [final] using backend.fullCompressFindCosted_forest_size_eq x
  rw [hsize]
  apply rankSlackPotentialOver_le_of_forall_mem
  intro y hyMem
  have hy : backend.state.forest.valid y := by
    exact List.mem_range.mp hyMem
  simpa [final] using
    backend.fullCompressFindCosted_nodeFindRootParentRankSlack_le_of_findRoot?
      hfind hy

theorem fullCompressionRankSlackCheckpoint_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      ((backend.fullCompressFindCosted x).erase.1).state.rank =
        backend.state.rank) /\
      (forall (backend : NoCompressionRankedMassBackendState)
        {x root : Nat},
        backend.state.forest.findRoot? x = some root ->
        (backend.fullCompressFindTrace x).length <=
          backend.traceRootParentRankSlack root
            (backend.fullCompressFindTrace x) + 2) /\
      (forall (backend : NoCompressionRankedMassBackendState)
        {x root : Nat},
        backend.state.forest.findRoot? x = some root ->
        ((backend.fullCompressFindCosted x).erase.1).traceRootParentRankSlack
          root (backend.fullCompressFindTrace x) = 0) /\
      (forall (backend : NoCompressionRankedMassBackendState)
        {x root : Nat},
        backend.state.forest.findRoot? x = some root ->
        (backend.fullCompressFindCosted x).cost +
            ((backend.fullCompressFindCosted x).erase.1).traceRootParentRankSlack
              root (backend.fullCompressFindTrace x) <=
          2 + backend.traceRootParentRankSlack root
            (backend.fullCompressFindTrace x)) /\
      (forall (backend : NoCompressionRankedMassBackendState)
        {x root : Nat},
        backend.state.forest.findRoot? x = some root ->
        rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) <=
          rankSlackPotential backend) := by
  constructor
  · intro backend x
    exact backend.fullCompressFindCosted_rank_eq x
  · constructor
    · intro backend x root hfind
      exact
        backend.fullCompressFindTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
          hfind
    · constructor
      · intro backend x root hfind
        exact
          backend.fullCompressFindCosted_traceRootParentRankSlack_eq_zero_of_findRoot?
            hfind
      · constructor
        · intro backend x root hfind
          exact
            backend.fullCompressFindCosted_cost_add_traceRootParentRankSlack_le_of_findRoot?
              hfind
        · intro backend x root hfind
          exact
            backend.rankSlackPotential_fullCompressFindCosted_le_of_findRoot?
              hfind

theorem fullCompressFindCosted_cost_le_rankBucketFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost <=
      backend.rankBucketFindCredit x := by
  exact Nat.le_trans
    (backend.fullCompressFindCosted_cost_le_rankGapFindCredit x)
    (backend.rankGapFindCredit_le_rankBucketFindCredit x)

theorem rankSizePotential_fullCompressFindCosted_eq
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    rankSizePotential ((backend.fullCompressFindCosted x).erase.1) =
      rankSizePotential backend := by
  simpa [rankSizePotential] using
    backend.fullCompressFindCosted_forest_size_eq x

theorem rankSizePotential_unionCosted_eq
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    rankSizePotential ((backend.unionCosted x y).erase) =
      rankSizePotential backend := by
  simp [rankSizePotential, unionCosted, unionResult,
    NoCompressionRankedMassForest.unionCosted]

theorem rankBucketPotential_fullCompressFindCosted_eq
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    rankBucketPotential ((backend.fullCompressFindCosted x).erase.1) =
      rankBucketPotential backend := by
  unfold rankBucketPotential
  rw [backend.fullCompressFindCosted_forest_size_eq x]

theorem rankBucketPotential_unionCosted_eq
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    rankBucketPotential ((backend.unionCosted x y).erase) =
      rankBucketPotential backend := by
  simp [rankBucketPotential, unionCosted, unionResult,
    NoCompressionRankedMassForest.unionCosted]

theorem rankSlackPotential_unionCosted_le_rankBucketPotential
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    rankSlackPotential ((backend.unionCosted x y).erase) <=
      rankBucketPotential backend := by
  have hle :=
    rankSlackPotential_le_rankBucketPotential ((backend.unionCosted x y).erase)
  have hbucket := backend.rankBucketPotential_unionCosted_eq x y
  rwa [hbucket] at hle

theorem unionCosted_cost_add_rankSlackPotential_le_rankSlackSizeUnionCredit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.unionCosted x y).cost +
        rankSlackPotential ((backend.unionCosted x y).erase) <=
      backend.rankSlackSizeUnionCredit x y + rankSlackPotential backend := by
  have hcost : (backend.unionCosted x y).cost = 1 := by
    rfl
  have hpot := backend.rankSlackPotential_unionCosted_le_rankBucketPotential x y
  rw [hcost]
  unfold rankSlackSizeUnionCredit
  omega

/--
Potential-method scaffold for the current representation backend.

The potential is intentionally zero and the compressed-find credit is the
actual executable trace length.  This is not Tarjan's amortized bound; it is the
checked boundary a future nonzero potential can strengthen.
-/
def fullCompressionRepresentationAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      representationZeroPotential
      fullCompressionFindCredit
      unionByRankCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
      representationZeroPotential fullCompressionFindCredit
    simp [fullCompressionRepresentationBackend,
      fullCompressFindCosted_cost_eq_trace_length]
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
      representationZeroPotential unionByRankCredit
    simp [fullCompressionRepresentationBackend, unionCosted]

theorem fullCompressionRepresentationAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionRepresentationAmortizedBackend.findCosted backend x)
        (representationZeroPotential backend)
        (representationZeroPotential
          ((fullCompressionRepresentationAmortizedBackend.findCosted backend x).erase.1))
        (fullCompressionFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionRepresentationAmortizedBackend.unionCosted backend x y)
          (representationZeroPotential backend)
          (representationZeroPotential
            (fullCompressionRepresentationAmortizedBackend.unionCosted
              backend x y).erase)
          (unionByRankCredit backend x y)) := by
  constructor
  · exact fullCompressionRepresentationAmortizedBackend.find_amortized
  · exact fullCompressionRepresentationAmortizedBackend.union_amortized

/--
First nonzero-potential checkpoint for full compression.

The potential is the current finite forest size, and the find credit is the
rank gap from the queried node to its returned root (falling back to the fuel
bound for invalid nodes).  The potential is coarse and does not yet encode
Tarjan's rank buckets, but the find credit is no longer the executed trace
length: it is discharged by the rank-gap trace theorem.
-/
def fullCompressionRankGapAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      rankSizePotential
      rankGapFindCredit
      unionByRankCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    have hcost := backend.fullCompressFindCosted_cost_le_rankGapFindCredit x
    have hpot := backend.rankSizePotential_fullCompressFindCosted_eq x
    change (backend.fullCompressFindCosted x).cost +
        rankSizePotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.rankGapFindCredit x + rankSizePotential backend
    rw [hpot]
    omega
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    have hpot := backend.rankSizePotential_unionCosted_eq x y
    change (backend.unionCosted x y).cost +
        rankSizePotential ((backend.unionCosted x y).erase) <=
      backend.unionByRankCredit x y + rankSizePotential backend
    rw [hpot]
    simp [unionByRankCredit]

theorem fullCompressionRankGapAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionRankGapAmortizedBackend.findCosted backend x)
        (rankSizePotential backend)
        (rankSizePotential
          ((fullCompressionRankGapAmortizedBackend.findCosted backend x).erase.1))
        (rankGapFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionRankGapAmortizedBackend.unionCosted backend x y)
          (rankSizePotential backend)
          (rankSizePotential
            (fullCompressionRankGapAmortizedBackend.unionCosted backend x y).erase)
          (unionByRankCredit backend x y)) := by
  constructor
  · exact fullCompressionRankGapAmortizedBackend.find_amortized
  · exact fullCompressionRankGapAmortizedBackend.union_amortized

/--
Log-rank credit checkpoint for full compression.

For successful finds, the credit is now bounded by `log2 forest.size + 1`
instead of the returned root's concrete rank gap. Invalid queries retain the
same fuel fallback as the rank-gap credit.
-/
def fullCompressionLogRankAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      rankSizePotential
      logRankFindCredit
      unionByRankCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    have hcost := backend.fullCompressFindCosted_cost_le_logRankFindCredit x
    have hpot := backend.rankSizePotential_fullCompressFindCosted_eq x
    change (backend.fullCompressFindCosted x).cost +
        rankSizePotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.logRankFindCredit x + rankSizePotential backend
    rw [hpot]
    omega
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    have hpot := backend.rankSizePotential_unionCosted_eq x y
    change (backend.unionCosted x y).cost +
        rankSizePotential ((backend.unionCosted x y).erase) <=
      backend.unionByRankCredit x y + rankSizePotential backend
    rw [hpot]
    simp [unionByRankCredit]

theorem fullCompressionLogRankAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionLogRankAmortizedBackend.findCosted backend x)
        (rankSizePotential backend)
        (rankSizePotential
          ((fullCompressionLogRankAmortizedBackend.findCosted backend x).erase.1))
        (logRankFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionLogRankAmortizedBackend.unionCosted backend x y)
          (rankSizePotential backend)
          (rankSizePotential
            (fullCompressionLogRankAmortizedBackend.unionCosted backend x y).erase)
          (unionByRankCredit backend x y)) := by
  constructor
  · exact fullCompressionLogRankAmortizedBackend.find_amortized
  · exact fullCompressionLogRankAmortizedBackend.union_amortized

/--
First explicit rank-bucket amortized checkpoint for full compression.

The successful-find credit is the geometric width of the returned root's rank
bucket. This is coarser than the log-rank checkpoint and still not Tarjan's
inverse-Ackermann analysis, but it exposes the bucket schedule and proves that
bucket width can pay the existing rank-gap trace bound.
-/
def fullCompressionRankBucketAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      rankBucketPotential
      rankBucketFindCredit
      unionByRankCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    have hcost := backend.fullCompressFindCosted_cost_le_rankBucketFindCredit x
    have hpot := backend.rankBucketPotential_fullCompressFindCosted_eq x
    change (backend.fullCompressFindCosted x).cost +
        rankBucketPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.rankBucketFindCredit x + rankBucketPotential backend
    rw [hpot]
    omega
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    have hpot := backend.rankBucketPotential_unionCosted_eq x y
    change (backend.unionCosted x y).cost +
        rankBucketPotential ((backend.unionCosted x y).erase) <=
      backend.unionByRankCredit x y + rankBucketPotential backend
    rw [hpot]
    simp [unionByRankCredit]

theorem fullCompressionRankBucketAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionRankBucketAmortizedBackend.findCosted backend x)
        (rankBucketPotential backend)
        (rankBucketPotential
          ((fullCompressionRankBucketAmortizedBackend.findCosted backend x).erase.1))
        (rankBucketFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionRankBucketAmortizedBackend.unionCosted backend x y)
          (rankBucketPotential backend)
          (rankBucketPotential
            (fullCompressionRankBucketAmortizedBackend.unionCosted backend x y).erase)
          (unionByRankCredit backend x y)) := by
  constructor
  · exact fullCompressionRankBucketAmortizedBackend.find_amortized
  · exact fullCompressionRankBucketAmortizedBackend.union_amortized

/--
Rank-slack potential checkpoint for full compression.

Successful finds are paid with constant credit `2`: the aggregate
`rankSlackPotential` drops by enough to cover the trace-root parent slack, and
the local trace theorem converts that slack into the actual trace cost. Invalid
queries retain the fuel fallback. Union uses an explicit potential-delta credit
because this checkpoint is about compression paying for find, not yet about a
Tarjan-tight union/find combined schedule.
-/
def fullCompressionRankSlackAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      rankSlackPotential
      rankSlackFindCredit
      rankSlackUnionCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.fullCompressFindCosted x).cost +
        rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.rankSlackFindCredit x + rankSlackPotential backend
    exact backend.fullCompressFindCosted_cost_add_rankSlackPotential_le_rankSlackFindCredit x
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    let before := rankSlackPotential backend
    let after := rankSlackPotential ((backend.unionCosted x y).erase)
    change (backend.unionCosted x y).cost + after <=
      backend.rankSlackUnionCredit x y + before
    have hcost : (backend.unionCosted x y).cost = 1 := by
      rfl
    rw [hcost]
    unfold rankSlackUnionCredit
    change 1 + after <= (after - before + 1) + before
    by_cases hle : before <= after
    · have hcancel : after - before + before = after :=
        Nat.sub_add_cancel hle
      omega
    · have hle' : after <= before := by
        omega
      have hzero : after - before = 0 :=
        Nat.sub_eq_zero_of_le hle'
      omega

theorem fullCompressionRankSlackAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionRankSlackAmortizedBackend.findCosted backend x)
        (rankSlackPotential backend)
        (rankSlackPotential
          ((fullCompressionRankSlackAmortizedBackend.findCosted backend x).erase.1))
        (rankSlackFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionRankSlackAmortizedBackend.unionCosted backend x y)
          (rankSlackPotential backend)
          (rankSlackPotential
            (fullCompressionRankSlackAmortizedBackend.unionCosted backend x y).erase)
          (rankSlackUnionCredit backend x y)) := by
  constructor
  · exact fullCompressionRankSlackAmortizedBackend.find_amortized
  · exact fullCompressionRankSlackAmortizedBackend.union_amortized

/--
Rank-slack checkpoint with a non-delta union credit.

This keeps the constant successful-find credit from
`fullCompressionRankSlackAmortizedBackend`, but replaces the union credit
`potential_after - potential_before + 1` with the explicit size-log bound
`rankBucketPotential backend + 1`.  The bound is intentionally coarse; its job
is to remove the answer-shaped delta credit before the later Tarjan potential is
designed.
-/
def fullCompressionRankSlackSizeUnionAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      rankSlackPotential
      rankSlackFindCredit
      rankSlackSizeUnionCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.fullCompressFindCosted x).cost +
        rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.rankSlackFindCredit x + rankSlackPotential backend
    exact
      backend.fullCompressFindCosted_cost_add_rankSlackPotential_le_rankSlackFindCredit x
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.unionCosted x y).cost +
        rankSlackPotential ((backend.unionCosted x y).erase) <=
      backend.rankSlackSizeUnionCredit x y + rankSlackPotential backend
    exact
      backend.unionCosted_cost_add_rankSlackPotential_le_rankSlackSizeUnionCredit
        x y

theorem fullCompressionRankSlackSizeUnionAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionRankSlackSizeUnionAmortizedBackend.findCosted backend x)
        (rankSlackPotential backend)
        (rankSlackPotential
          ((fullCompressionRankSlackSizeUnionAmortizedBackend.findCosted
            backend x).erase.1))
        (rankSlackFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionRankSlackSizeUnionAmortizedBackend.unionCosted
            backend x y)
          (rankSlackPotential backend)
          (rankSlackPotential
            (fullCompressionRankSlackSizeUnionAmortizedBackend.unionCosted
              backend x y).erase)
          (rankSlackSizeUnionCredit backend x y)) := by
  constructor
  · exact fullCompressionRankSlackSizeUnionAmortizedBackend.find_amortized
  · exact fullCompressionRankSlackSizeUnionAmortizedBackend.union_amortized

theorem profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      (backend.findCosted x).cost = 1 /\
        (backend.findCosted x).erase.2 =
          backend.abstractState.find? x /\
        State.SamePartition
          (abstractState (backend.findCosted x).erase.1)
          backend.abstractState) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
        (backend.compressFindCosted x).cost = 1 /\
          (backend.compressFindCosted x).erase.2 =
            backend.abstractState.find? x /\
          State.SamePartition
            (abstractState (backend.compressFindCosted x).erase.1)
            backend.abstractState) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
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
            backend.abstractState) /\
      (forall (backend : NoCompressionRankedMassBackendState)
        {x root y : Nat},
        backend.state.forest.findRoot? x = some root ->
        y ∈ backend.fullCompressFindTrace x ->
        ((backend.fullCompressFindCosted x).erase.1).state.forest.parent? y =
          some root) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        (backend.unionCosted x y).cost = 1 /\
          State.SamePartition
            (abstractState (backend.unionCosted x y).erase)
            (backend.abstractState.unionSpec x y)) /\
      (forall (backend : NoCompressionRankedMassBackendState)
        (ops : List (Nat × Nat)),
        (backend.unionManyCosted ops).cost = ops.length /\
          State.SamePartition
            (abstractState (backend.unionManyCosted ops).erase)
            (backend.abstractState.unionSpecMany ops)) := by
  constructor
  · intro backend x
    exact findCosted_refinement_profile backend x
  · constructor
    · intro backend x
      exact compressFindCosted_refinement_profile backend x
    · constructor
      · intro backend x
        exact fullCompressFindCosted_refinement_profile backend x
      · constructor
        · intro backend x root y hfind hmem
          exact backend.fullCompressFindCosted_trace_parent?_eq_root_of_findRoot?
            hfind hmem
        · constructor
          · intro backend x y
            exact unionCosted_refinement_profile backend x y
          · intro backend ops
            exact unionManyCosted_refinement_profile backend ops

end NoCompressionRankedMassBackendState

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

end RMQ
