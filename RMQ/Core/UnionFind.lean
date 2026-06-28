import RMQ.Core.Amortized

/-!
# Union-find specification surface

This is the first non-succinct data-structure spoke.  It is intentionally a
specification and accounting layer, not yet a path-compression implementation:
states expose a representative function over a finite index set, `find` is
allowed to return an updated state, and amortized bounds are phrased through
the reusable potential-method inequality from `RMQ.Core.Amortized`.
-/

namespace RMQ

namespace UnionFind

/--
A proof-facing union-find partition state over indices `< size`.

The representative function is only semantically meaningful on valid indices;
`repr_lt` ensures valid representatives stay in range.
-/
structure State where
  size : Nat
  repr : Nat -> Nat
  repr_lt : forall {x : Nat}, x < size -> repr x < size

namespace State

abbrev valid (state : State) (x : Nat) : Prop :=
  x < state.size

def find? (state : State) (x : Nat) : Option Nat :=
  if _hx : state.valid x then
    some (state.repr x)
  else
    none

def Same (state : State) (x y : Nat) : Prop :=
  state.valid x /\ state.valid y /\ state.repr x = state.repr y

def SamePartition (left right : State) : Prop :=
  forall x y, left.Same x y <-> right.Same x y

def same? (state : State) (x y : Nat) : Option Bool :=
  match state.find? x, state.find? y with
  | some rx, some ry => some (decide (rx = ry))
  | _, _ => none

theorem find?_eq_some_of_valid
    (state : State) {x : Nat} (hx : state.valid x) :
    state.find? x = some (state.repr x) := by
  simp [find?, hx]

theorem find?_eq_none_of_invalid
    (state : State) {x : Nat} (hx : ¬ state.valid x) :
    state.find? x = none := by
  simp [find?, hx]

theorem find?_some_lt
    (state : State) {x rep : Nat}
    (hfind : state.find? x = some rep) :
    rep < state.size := by
  unfold find? at hfind
  by_cases hx : state.valid x
  · simp [hx] at hfind
    cases hfind
    exact state.repr_lt hx
  · simp [hx] at hfind

theorem valid_of_find?_eq_some
    (state : State) {x rep : Nat}
    (hfind : state.find? x = some rep) :
    state.valid x := by
  unfold find? at hfind
  by_cases hx : state.valid x
  · exact hx
  · simp [hx] at hfind

theorem repr_eq_of_find?_eq_some
    (state : State) {x rep : Nat}
    (hfind : state.find? x = some rep) :
    state.repr x = rep := by
  unfold find? at hfind
  by_cases hx : state.valid x
  · simp [hx] at hfind
    exact hfind
  · simp [hx] at hfind

theorem samePartition_refl (state : State) :
    state.SamePartition state := by
  intro x y
  rfl

theorem samePartition_symm {left right : State}
    (h : left.SamePartition right) :
    right.SamePartition left := by
  intro x y
  exact (h x y).symm

theorem samePartition_trans {left mid right : State}
    (hleft : left.SamePartition mid)
    (hright : mid.SamePartition right) :
    left.SamePartition right := by
  intro x y
  exact (hleft x y).trans (hright x y)

theorem samePartition_of_find?_eq
    {left right : State}
    (hfind : forall i, left.find? i = right.find? i) :
    left.SamePartition right := by
  intro x y
  constructor
  · intro hsame
    rcases hsame with ⟨hx, hy, hrepr⟩
    have hxFindLeft := left.find?_eq_some_of_valid hx
    have hyFindLeft := left.find?_eq_some_of_valid hy
    have hxFindRight : right.find? x = some (left.repr x) := by
      rw [← hfind x]
      exact hxFindLeft
    have hyFindRight : right.find? y = some (left.repr y) := by
      rw [← hfind y]
      exact hyFindLeft
    exact ⟨
      right.valid_of_find?_eq_some hxFindRight,
      right.valid_of_find?_eq_some hyFindRight,
      (right.repr_eq_of_find?_eq_some hxFindRight).trans
        (hrepr.trans
          (right.repr_eq_of_find?_eq_some hyFindRight).symm)⟩
  · intro hsame
    rcases hsame with ⟨hx, hy, hrepr⟩
    have hxFindRight := right.find?_eq_some_of_valid hx
    have hyFindRight := right.find?_eq_some_of_valid hy
    have hxFindLeft : left.find? x = some (right.repr x) := by
      rw [hfind x]
      exact hxFindRight
    have hyFindLeft : left.find? y = some (right.repr y) := by
      rw [hfind y]
      exact hyFindRight
    exact ⟨
      left.valid_of_find?_eq_some hxFindLeft,
      left.valid_of_find?_eq_some hyFindLeft,
      (left.repr_eq_of_find?_eq_some hxFindLeft).trans
        (hrepr.trans
          (left.repr_eq_of_find?_eq_some hyFindLeft).symm)⟩

theorem same_refl
    (state : State) {x : Nat} (hx : state.valid x) :
    state.Same x x := by
  exact ⟨hx, hx, rfl⟩

theorem same_symm
    (state : State) {x y : Nat}
    (h : state.Same x y) :
    state.Same y x := by
  exact ⟨h.2.1, h.1, h.2.2.symm⟩

theorem same_trans
    (state : State) {x y z : Nat}
    (hxy : state.Same x y) (hyz : state.Same y z) :
    state.Same x z := by
  exact ⟨hxy.1, hyz.2.1, hxy.2.2.trans hyz.2.2⟩

theorem same?_eq_some_of_valid
    (state : State) {x y : Nat}
    (hx : state.valid x) (hy : state.valid y) :
    state.same? x y =
      some (decide (state.repr x = state.repr y)) := by
  simp [same?, find?, hx, hy]

theorem same?_eq_none_left_of_invalid
    (state : State) {x y : Nat}
    (hx : ¬ state.valid x) :
    state.same? x y = none := by
  simp [same?, find?, hx]

theorem same?_eq_none_right_of_invalid
    (state : State) {x y : Nat}
    (hy : ¬ state.valid y) :
    state.same? x y = none := by
  by_cases hx : state.valid x
  · simp [same?, find?, hx, hy]
  · simp [same?, find?, hx]

def mergeRepr (state : State) (x y i : Nat) : Nat :=
  if _hxy : state.valid x /\ state.valid y then
    if state.repr i = state.repr y then
      state.repr x
    else
      state.repr i
  else
    state.repr i

/--
Pure reference union: invalid endpoints are a no-op; valid endpoints merge the
component of `y` into the representative of `x`.
-/
def unionSpec (state : State) (x y : Nat) : State where
  size := state.size
  repr := mergeRepr state x y
  repr_lt := by
    intro i hi
    unfold mergeRepr
    by_cases hxy : state.valid x /\ state.valid y
    · by_cases hsame : state.repr i = state.repr y
      · simp [hxy, hsame, state.repr_lt hxy.1]
      · simp [hxy, hsame, state.repr_lt hi]
    · simp [hxy, state.repr_lt hi]

@[simp] theorem unionSpec_size
    (state : State) (x y : Nat) :
    (state.unionSpec x y).size = state.size := by
  rfl

theorem unionSpec_valid_iff
    (state : State) (x y i : Nat) :
    (state.unionSpec x y).valid i <-> state.valid i := by
  rfl

theorem unionSpec_same_of_valid
    (state : State) {x y : Nat}
    (hx : state.valid x) (hy : state.valid y) :
    (state.unionSpec x y).Same x y := by
  unfold Same valid unionSpec
  constructor
  · exact hx
  · constructor
    · exact hy
    · change mergeRepr state x y x = mergeRepr state x y y
      have hxy : state.valid x /\ state.valid y := ⟨hx, hy⟩
      simp [mergeRepr, hxy]

theorem unionSpec_same_iff
    (state : State) (x y a b : Nat) :
    (state.unionSpec x y).Same a b <->
      state.Same a b \/
        (state.valid x /\ state.valid y /\
          ((state.Same a x /\ state.Same b y) \/
            (state.Same a y /\ state.Same b x))) := by
  by_cases hxy : state.valid x /\ state.valid y
  · rcases hxy with ⟨hx, hy⟩
    by_cases ha : state.valid a
    · by_cases hb : state.valid b
      · unfold Same unionSpec mergeRepr
        simp [valid, hx, hy, ha, hb]
        by_cases hay : state.repr a = state.repr y
        · by_cases hby : state.repr b = state.repr y
          · simp [hay, hby]
          · by_cases hbx : state.repr b = state.repr x
            · simp [hay, hbx]
            · constructor
              · intro hEq
                have hxbr : state.repr x = state.repr b := by
                  simpa [hay, hby] using hEq
                exact False.elim (hbx hxbr.symm)
              · intro hEq
                have hybr : state.repr y = state.repr b := by
                  simpa [hay, hby, hbx, eq_comm] using hEq
                exact False.elim (hby hybr.symm)
        · by_cases hby : state.repr b = state.repr y
          · by_cases hax : state.repr a = state.repr x
            · simp [hby, hax]
            · simp [hay, hby, hax]
          · simp [hay, hby]
      · unfold Same unionSpec mergeRepr
        simp [valid, hx, hy, ha, hb]
    · unfold Same unionSpec mergeRepr
      simp [valid, hx, hy, ha]
  · constructor
    · intro hsame
      exact Or.inl (by
        simpa [Same, unionSpec, mergeRepr, hxy] using hsame)
    · intro hsame
      rcases hsame with hsame | hmerge
      · simpa [Same, unionSpec, mergeRepr, hxy] using hsame
      · exact False.elim (hxy ⟨hmerge.1, hmerge.2.1⟩)

theorem samePartition_unionSpec
    {left right : State} (h : left.SamePartition right)
    (x y : Nat) :
    (left.unionSpec x y).SamePartition (right.unionSpec x y) := by
  intro a b
  rw [left.unionSpec_same_iff x y a b,
    right.unionSpec_same_iff x y a b]
  have hxx := h x x
  have hyy := h y y
  have hxValid : left.valid x <-> right.valid x := by
    constructor
    · intro hx
      exact (hxx.mp ⟨hx, hx, rfl⟩).1
    · intro hx
      exact (hxx.mpr ⟨hx, hx, rfl⟩).1
  have hyValid : left.valid y <-> right.valid y := by
    constructor
    · intro hy
      exact (hyy.mp ⟨hy, hy, rfl⟩).1
    · intro hy
      exact (hyy.mpr ⟨hy, hy, rfl⟩).1
  constructor
  · intro hsame
    rcases hsame with hsame | hmerge
    · exact Or.inl ((h a b).mp hsame)
    · rcases hmerge with ⟨hx, hy, hcases⟩
      refine Or.inr ⟨hxValid.mp hx, hyValid.mp hy, ?_⟩
      rcases hcases with hxyCases | hyxCases
      · exact Or.inl ⟨(h a x).mp hxyCases.1, (h b y).mp hxyCases.2⟩
      · exact Or.inr ⟨(h a y).mp hyxCases.1, (h b x).mp hyxCases.2⟩
  · intro hsame
    rcases hsame with hsame | hmerge
    · exact Or.inl ((h a b).mpr hsame)
    · rcases hmerge with ⟨hx, hy, hcases⟩
      refine Or.inr ⟨hxValid.mpr hx, hyValid.mpr hy, ?_⟩
      rcases hcases with hxyCases | hyxCases
      · exact Or.inl ⟨(h a x).mpr hxyCases.1, (h b y).mpr hxyCases.2⟩
      · exact Or.inr ⟨(h a y).mpr hyxCases.1, (h b x).mpr hyxCases.2⟩

theorem unionSpec_samePartition_self_of_not_valid
    (state : State) {x y : Nat}
    (hxy : Not (state.valid x /\ state.valid y)) :
    state.SamePartition (state.unionSpec x y) := by
  intro a b
  unfold Same unionSpec mergeRepr
  simp [hxy]

theorem unionSpec_samePartition_self_of_same
    (state : State) {x y : Nat}
    (hx : state.valid x) (hy : state.valid y)
    (hsame : state.repr x = state.repr y) :
    state.SamePartition (state.unionSpec x y) := by
  have hxy : state.valid x /\ state.valid y := ⟨hx, hy⟩
  apply State.samePartition_of_find?_eq
  intro i
  by_cases hi : state.valid i
  · have hleft := state.find?_eq_some_of_valid hi
    have hright :=
      (state.unionSpec x y).find?_eq_some_of_valid
        (by simpa [unionSpec_valid_iff] using hi)
    have hrepr : state.repr i = mergeRepr state x y i := by
      unfold mergeRepr
      by_cases hiy : state.repr i = state.repr y
      · simp [hxy, hiy, hsame]
      · simp [hxy, hiy]
    rw [hleft, hright]
    simpa [unionSpec] using congrArg some hrepr
  · have hleft := state.find?_eq_none_of_invalid hi
    have hright :=
      (state.unionSpec x y).find?_eq_none_of_invalid
        (by simpa [unionSpec_valid_iff] using hi)
    rw [hleft, hright]

theorem unionSpec_samePartition_comm
    (state : State) (x y : Nat) :
    (state.unionSpec x y).SamePartition (state.unionSpec y x) := by
  intro a b
  unfold Same unionSpec mergeRepr
  by_cases hxy : state.valid x /\ state.valid y
  · have hyx : state.valid y /\ state.valid x := ⟨hxy.2, hxy.1⟩
    by_cases hreprXY : state.repr x = state.repr y
    · simp [hxy, hreprXY]
    · constructor
      · intro hsame
        rcases hsame with ⟨ha, hb, hrepr⟩
        refine ⟨ha, hb, ?_⟩
        by_cases hay : state.repr a = state.repr y
        · by_cases hby : state.repr b = state.repr y
          · simp [hxy, hay, hby]
          · have hbx : state.repr b = state.repr x := by
              simpa [hxy, hay, hby] using hrepr.symm
            have hax_ne : state.repr a ≠ state.repr x := by
              intro hax
              exact hreprXY (hax.symm.trans hay)
            simpa [hyx, hax_ne, hbx] using hay
        · by_cases hby : state.repr b = state.repr y
          · have hax : state.repr a = state.repr x := by
              simpa [hxy, hay, hby] using hrepr
            have hbx_ne : state.repr b ≠ state.repr x := by
              intro hbx
              exact hreprXY (hbx.symm.trans hby)
            simpa [hyx, hax, hbx_ne] using hby.symm
          · have hab : state.repr a = state.repr b := by
              simpa [hxy, hay, hby] using hrepr
            by_cases hax : state.repr a = state.repr x
            · have hbx : state.repr b = state.repr x := hab.symm.trans hax
              simp [hyx, hbx, hab]
            · have hbx : state.repr b ≠ state.repr x := by
                intro hbx
                exact hax (hab.trans hbx)
              simp [hyx, hbx, hab]
      · intro hsame
        rcases hsame with ⟨ha, hb, hrepr⟩
        refine ⟨ha, hb, ?_⟩
        by_cases hax : state.repr a = state.repr x
        · by_cases hbx : state.repr b = state.repr x
          · simp [hxy, hax, hbx]
          · have hby : state.repr b = state.repr y := by
              simpa [hyx, hax, hbx] using hrepr.symm
            have hay_ne : state.repr a ≠ state.repr y := by
              intro hay
              exact hreprXY (hax.symm.trans hay)
            simpa [hxy, hay_ne, hby] using hax
        · by_cases hbx : state.repr b = state.repr x
          · have hay : state.repr a = state.repr y := by
              simpa [hyx, hax, hbx] using hrepr
            have hby_ne : state.repr b ≠ state.repr y := by
              intro hby
              exact hreprXY (hbx.symm.trans hby)
            simpa [hxy, hay, hby_ne] using hbx.symm
          · have hab : state.repr a = state.repr b := by
              simpa [hyx, hax, hbx] using hrepr
            by_cases hay : state.repr a = state.repr y
            · have hby : state.repr b = state.repr y := hab.symm.trans hay
              simp [hxy, hby, hab]
            · have hby : state.repr b ≠ state.repr y := by
                intro hby
                exact hay (hab.trans hby)
              simp [hxy, hby, hab]
  · have hyx : Not (state.valid y /\ state.valid x) := by
      intro hyx
      exact hxy ⟨hyx.2, hyx.1⟩
    simp [hxy, hyx]

def unionSpecMany (state : State) : List (Nat × Nat) -> State
  | [] => state
  | (x, y) :: ops => (state.unionSpec x y).unionSpecMany ops

@[simp] theorem unionSpecMany_nil (state : State) :
    state.unionSpecMany [] = state := by
  rfl

@[simp] theorem unionSpecMany_cons
    (state : State) (x y : Nat) (ops : List (Nat × Nat)) :
    state.unionSpecMany ((x, y) :: ops) =
      (state.unionSpec x y).unionSpecMany ops := by
  rfl

theorem samePartition_unionSpecMany
    {left right : State} (h : left.SamePartition right) :
    forall ops : List (Nat × Nat),
      (left.unionSpecMany ops).SamePartition
        (right.unionSpecMany ops)
  | [] => by
      simpa using h
  | (x, y) :: ops => by
      exact samePartition_unionSpecMany
        (samePartition_unionSpec h x y) ops

end State

/-- Costed reference find: one modeled read, no state mutation. -/
def findSpecCosted (state : State) (x : Nat) :
    Costed (State × Option Nat) :=
  Costed.tickValue 1 (state, state.find? x)

/-- Costed reference union: one modeled update, using `State.unionSpec`. -/
def unionSpecCosted (state : State) (x y : Nat) : Costed State :=
  Costed.tickValue 1 (state.unionSpec x y)

@[simp] theorem findSpecCosted_cost
    (state : State) (x : Nat) :
    (findSpecCosted state x).cost = 1 := by
  rfl

@[simp] theorem findSpecCosted_erase
    (state : State) (x : Nat) :
    (findSpecCosted state x).erase = (state, state.find? x) := by
  rfl

@[simp] theorem unionSpecCosted_cost
    (state : State) (x y : Nat) :
    (unionSpecCosted state x y).cost = 1 := by
  rfl

@[simp] theorem unionSpecCosted_erase
    (state : State) (x y : Nat) :
    (unionSpecCosted state x y).erase = state.unionSpec x y := by
  rfl

/--
Backend surface for future implementations.  `find` may compress paths and
return a new state, but it must preserve the represented partition.
-/
structure Backend where
  findCosted : State -> Nat -> Costed (State × Option Nat)
  unionCosted : State -> Nat -> Nat -> Costed State
  find_exact :
    forall state x, (findCosted state x).erase.2 = state.find? x
  find_preserves_same :
    forall state x a b,
      ((findCosted state x).erase.1).Same a b <-> state.Same a b
  union_exact :
    forall state x y, (unionCosted state x y).erase = state.unionSpec x y

/--
Representation-backed backend boundary.

Unlike `Backend`, the executable representation state may carry parent
pointers, ranks, component masses, potentials, or other implementation data.
`abstractState` is the partition observed by the specification layer.
-/
structure RepresentationBackend (Rep : Type) where
  abstractState : Rep -> State
  findCosted : Rep -> Nat -> Costed (Rep × Option Nat)
  unionCosted : Rep -> Nat -> Nat -> Costed Rep
  find_exact :
    forall rep x,
      (findCosted rep x).erase.2 = (abstractState rep).find? x
  find_refines :
    forall rep x,
      State.SamePartition
        (abstractState (findCosted rep x).erase.1)
        (abstractState rep)
  union_refines :
    forall rep x y,
      State.SamePartition
        (abstractState (unionCosted rep x y).erase)
        ((abstractState rep).unionSpec x y)

def representationZeroPotential {Rep : Type} (_rep : Rep) : Nat :=
  0

/--
Potential-method obligations for representation-backed backends.

Credits are allowed to depend on the current representation state and query
arguments.  This is the honest intermediate boundary for the current forest
implementation, whose compressed find has a bounded-depth credit before the
future Tarjan potential collapses the amortized credit to a small uniform
function.
-/
structure RepresentationAmortizedBackend
    (Rep : Type) (potential : Rep -> Nat)
    (findCredit : Rep -> Nat -> Nat)
    (unionCredit : Rep -> Nat -> Nat -> Nat)
    extends RepresentationBackend Rep where
  find_amortized :
    forall rep x,
      Amortized.CostedBound (findCosted rep x)
        (potential rep)
        (potential (findCosted rep x).erase.1)
        (findCredit rep x)
  union_amortized :
    forall rep x y,
      Amortized.CostedBound (unionCosted rep x y)
        (potential rep)
        (potential (unionCosted rep x y).erase)
        (unionCredit rep x y)

def referenceBackend : Backend where
  findCosted := findSpecCosted
  unionCosted := unionSpecCosted
  find_exact := by
    intro state x
    rfl
  find_preserves_same := by
    intro state x a b
    rfl
  union_exact := by
    intro state x y
    rfl

def zeroPotential (_state : State) : Nat :=
  0

structure AmortizedBackend
    (potential : State -> Nat) (findCredit unionCredit : Nat)
    extends Backend where
  find_amortized :
    forall state x,
      Amortized.CostedBound (findCosted state x)
        (potential state)
        (potential (findCosted state x).erase.1)
        findCredit
  union_amortized :
    forall state x y,
      Amortized.CostedBound (unionCosted state x y)
        (potential state)
        (potential (unionCosted state x y).erase)
        unionCredit

def referenceAmortizedBackend :
    AmortizedBackend zeroPotential 1 1 where
  toBackend := referenceBackend
  find_amortized := by
    intro state x
    unfold Amortized.CostedBound Amortized.Bound zeroPotential
    simp [referenceBackend, findSpecCosted]
  union_amortized := by
    intro state x y
    unfold Amortized.CostedBound Amortized.Bound zeroPotential
    simp [referenceBackend, unionSpecCosted]

theorem referenceBackend_profile :
    (forall state x,
      (referenceBackend.findCosted state x).cost = 1 /\
        (referenceBackend.findCosted state x).erase =
          (state, state.find? x)) /\
      (forall state x y,
        (referenceBackend.unionCosted state x y).cost = 1 /\
          (referenceBackend.unionCosted state x y).erase =
            state.unionSpec x y) /\
      (forall state x a b,
        ((referenceBackend.findCosted state x).erase.1).Same a b <->
          state.Same a b) := by
  constructor
  · intro state x
    exact ⟨rfl, rfl⟩
  · constructor
    · intro state x y
      exact ⟨rfl, rfl⟩
    · intro state x a b
      rfl

theorem referenceAmortizedBackend_profile :
    (forall state x,
      Amortized.CostedBound
        (referenceAmortizedBackend.findCosted state x)
        (zeroPotential state)
        (zeroPotential (referenceAmortizedBackend.findCosted state x).erase.1)
        1) /\
      (forall state x y,
        Amortized.CostedBound
          (referenceAmortizedBackend.unionCosted state x y)
          (zeroPotential state)
          (zeroPotential
            (referenceAmortizedBackend.unionCosted state x y).erase)
          1) := by
  constructor
  · exact referenceAmortizedBackend.find_amortized
  · exact referenceAmortizedBackend.union_amortized

end UnionFind

end RMQ
