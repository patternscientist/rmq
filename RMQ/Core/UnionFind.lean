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
