import RMQ.Core.Cost

/-!
# Tiny traced RAM substrate

This module gives a small operational substrate for future cost refinements.
Unlike the older model-level wrappers, a program carries a trace of primitive
operations and its step count is derived from the trace length.
-/

namespace RMQ

namespace RAM

/-- Primitive operations counted by the tiny RAM trace model. -/
inductive Op where
  | branch
  | read
  | write
  | compare
  | alloc
  | wordRank
  | wordSelect
deriving Repr, DecidableEq

/--
A traced execution: a value plus the primitive operations used to get it.

The constructor is private so executable clients build programs through the
combinators and typed primitives in this module, not by pairing an arbitrary
value with an arbitrary trace.
-/
structure Exec (a : Type u) where
  private mk ::
  value : a
  trace : List Op
deriving Repr, DecidableEq

namespace Exec

/-- Operational step count, derived from the trace. -/
def steps (x : Exec a) : Nat :=
  x.trace.length

/-- Zero-step return of an already computed value. -/
def pure (x : a) : Exec a where
  value := x
  trace := []

/-- Sequential composition concatenates operation traces. -/
def bind (x : Exec a) (f : a -> Exec b) : Exec b :=
  let y := f x.value
  { value := y.value, trace := x.trace ++ y.trace }

/-- Internal one-step primitive boundary. Public users get typed primitives. -/
private def primitive (op : Op) (x : a) : Exec a where
  value := x
  trace := [op]

/--
Forget the trace shape into the existing `Costed` carrier.  The cost is the
derived operational step count, not a separate handwritten cost function.
-/
def toCosted (x : Exec a) : Costed a where
  value := x.value
  cost := x.steps

@[simp] theorem steps_pure (x : a) :
    (pure x).steps = 0 := by
  rfl

@[simp] theorem value_pure (x : a) :
    (pure x).value = x := by
  rfl

@[simp] private theorem steps_primitive (op : Op) (x : a) :
    (primitive op x).steps = 1 := by
  rfl

@[simp] private theorem value_primitive (op : Op) (x : a) :
    (primitive op x).value = x := by
  rfl

@[simp] theorem value_bind (x : Exec a) (f : a -> Exec b) :
    (bind x f).value = (f x.value).value := by
  rfl

@[simp] theorem steps_bind (x : Exec a) (f : a -> Exec b) :
    (bind x f).steps = x.steps + (f x.value).steps := by
  simp [steps, bind]

@[simp] theorem toCosted_value (x : Exec a) :
    x.toCosted.value = x.value := by
  rfl

@[simp] theorem toCosted_cost_eq_steps (x : Exec a) :
    x.toCosted.cost = x.steps := by
  rfl

theorem toCosted_run_eq_value_steps (x : Exec a) :
    x.toCosted.run = (x.value, x.steps) := by
  rfl

end Exec

/-- Count one branch/validity decision. -/
def branch (b : Bool) : Exec Bool :=
  Exec.primitive Op.branch b

/-- Count one indexed array read. -/
def readArray? (xs : Array a) (i : Nat) : Exec (Option a) :=
  Exec.primitive Op.read (xs[i]?)

/-- Count one total indexed array write. Out-of-bounds writes leave the array unchanged. -/
def writeArray? (xs : Array a) (i : Nat) (x : a) : Exec (Array a) :=
  Exec.primitive Op.write (xs.setIfInBounds i x)

/-- Count one integer less-than comparison. -/
def compareLtInt (a b : Int) : Exec Bool :=
  Exec.primitive Op.compare (decide (a < b))

/-- Count one array materialization/allocation step. -/
def allocArray (xs : Array a) : Exec (Array a) :=
  Exec.primitive Op.alloc xs

/-- Count one array append/push step. -/
def pushArray (xs : Array a) (x : a) : Exec (Array a) :=
  Exec.primitive Op.alloc (xs.push x)

/-- Reference value of a word-level rank-prefix primitive over a Boolean word. -/
def boolRankPrefix (target : Bool) : List Bool -> Nat -> Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | bit :: rest, limit + 1 =>
      (if bit = target then 1 else 0) + boolRankPrefix target rest limit

/-- Reference value of a word-level select primitive over a Boolean word. -/
def boolSelectFrom
    (target : Bool) : List Bool -> Nat -> Nat -> Option Nat
  | [], _base, _occurrence => none
  | bit :: rest, base, occurrence =>
      if bit = target then
        if occurrence = 0 then
          some base
        else
          boolSelectFrom target rest (base + 1) (occurrence - 1)
      else
        boolSelectFrom target rest (base + 1) occurrence

/-- Select the zero-based `occurrence`-th `target` bit in one word. -/
def boolSelectInWord
    (target : Bool) (word : List Bool) (occurrence : Nat) : Option Nat :=
  boolSelectFrom target word 0 occurrence

/--
Count one broadword rank-prefix primitive.

This is intentionally a word-level primitive, not a whole-bitvector rank
operation.  A faithful succinct rank/select structure still has to prove that
the queried word was obtained by counted indexed access from the packed payload
and that its auxiliary samples are read from counted directories.
-/
def rankBoolWordPrefix (target : Bool) (word : List Bool) (limit : Nat) :
    Exec Nat :=
  Exec.primitive Op.wordRank (boolRankPrefix target word limit)

/-- Count one broadword select primitive inside a Boolean word. -/
def selectBoolWord (target : Bool) (word : List Bool) (occurrence : Nat) :
    Exec (Option Nat) :=
  Exec.primitive Op.wordSelect (boolSelectInWord target word occurrence)

@[simp] theorem branch_value (b : Bool) :
    (branch b).value = b := by
  rfl

@[simp] theorem branch_steps (b : Bool) :
    (branch b).steps = 1 := by
  rfl

@[simp] theorem readArray?_value (xs : Array a) (i : Nat) :
    (readArray? xs i).value = xs[i]? := by
  rfl

@[simp] theorem readArray?_steps (xs : Array a) (i : Nat) :
    (readArray? xs i).steps = 1 := by
  rfl

@[simp] theorem writeArray?_value (xs : Array a) (i : Nat) (x : a) :
    (writeArray? xs i x).value = xs.setIfInBounds i x := by
  rfl

@[simp] theorem writeArray?_steps (xs : Array a) (i : Nat) (x : a) :
    (writeArray? xs i x).steps = 1 := by
  rfl

@[simp] theorem compareLtInt_value (a b : Int) :
    (compareLtInt a b).value = decide (a < b) := by
  rfl

@[simp] theorem compareLtInt_steps (a b : Int) :
    (compareLtInt a b).steps = 1 := by
  rfl

@[simp] theorem allocArray_value (xs : Array a) :
    (allocArray xs).value = xs := by
  rfl

@[simp] theorem allocArray_steps (xs : Array a) :
    (allocArray xs).steps = 1 := by
  rfl

@[simp] theorem pushArray_value (xs : Array a) (x : a) :
    (pushArray xs x).value = xs.push x := by
  rfl

@[simp] theorem pushArray_steps (xs : Array a) (x : a) :
    (pushArray xs x).steps = 1 := by
  rfl

@[simp] theorem rankBoolWordPrefix_value
    (target : Bool) (word : List Bool) (limit : Nat) :
    (rankBoolWordPrefix target word limit).value =
      boolRankPrefix target word limit := by
  rfl

@[simp] theorem rankBoolWordPrefix_steps
    (target : Bool) (word : List Bool) (limit : Nat) :
    (rankBoolWordPrefix target word limit).steps = 1 := by
  rfl

@[simp] theorem selectBoolWord_value
    (target : Bool) (word : List Bool) (occurrence : Nat) :
    (selectBoolWord target word occurrence).value =
      boolSelectInWord target word occurrence := by
  rfl

@[simp] theorem selectBoolWord_steps
    (target : Bool) (word : List Bool) (occurrence : Nat) :
    (selectBoolWord target word occurrence).steps = 1 := by
  rfl

theorem branch_run (b : Bool) :
    (branch b).toCosted.run = (b, 1) := by
  rfl

theorem readArray?_run (xs : Array a) (i : Nat) :
    (readArray? xs i).toCosted.run = (xs[i]?, 1) := by
  rfl

theorem writeArray?_run (xs : Array a) (i : Nat) (x : a) :
    (writeArray? xs i x).toCosted.run =
      (xs.setIfInBounds i x, 1) := by
  rfl

theorem compareLtInt_run (a b : Int) :
    (compareLtInt a b).toCosted.run = (decide (a < b), 1) := by
  rfl

theorem allocArray_run (xs : Array a) :
    (allocArray xs).toCosted.run = (xs, 1) := by
  rfl

theorem pushArray_run (xs : Array a) (x : a) :
    (pushArray xs x).toCosted.run = (xs.push x, 1) := by
  rfl

theorem rankBoolWordPrefix_run
    (target : Bool) (word : List Bool) (limit : Nat) :
    (rankBoolWordPrefix target word limit).toCosted.run =
      (boolRankPrefix target word limit, 1) := by
  rfl

theorem selectBoolWord_run
    (target : Bool) (word : List Bool) (occurrence : Nat) :
    (selectBoolWord target word occurrence).toCosted.run =
      (boolSelectInWord target word occurrence, 1) := by
  rfl

/-- Counted left-to-right copy of a list into an existing Array accumulator. -/
def pushListToArray : List a -> Array a -> Exec (Array a)
  | [], acc => Exec.pure acc
  | x :: xs, acc =>
      Exec.bind (pushArray acc x) fun acc' =>
        pushListToArray xs acc'

theorem pushListToArray_value_toList
    (xs : List a) (acc : Array a) :
    (pushListToArray xs acc).value.toList = acc.toList ++ xs := by
  induction xs generalizing acc with
  | nil =>
      simp [pushListToArray]
  | cons x xs ih =>
      simp [pushListToArray, Exec.bind, ih, List.append_assoc]

theorem pushListToArray_steps
    (xs : List a) (acc : Array a) :
    (pushListToArray xs acc).steps = xs.length := by
  induction xs generalizing acc with
  | nil =>
      simp [pushListToArray]
  | cons x xs ih =>
      simp [pushListToArray, Exec.steps_bind, ih]
      omega

/-- Counted Array materialization from a List: one allocation plus one push per element. -/
def arrayOfList (xs : List a) : Exec (Array a) :=
  Exec.bind (allocArray #[]) fun acc =>
    pushListToArray xs acc

theorem arrayOfList_value_toList (xs : List a) :
    (arrayOfList xs).value.toList = xs := by
  unfold arrayOfList
  simp [Exec.bind, pushListToArray_value_toList]

theorem arrayOfList_steps (xs : List a) :
    (arrayOfList xs).steps = xs.length + 1 := by
  unfold arrayOfList
  simp [Exec.steps_bind, pushListToArray_steps, Nat.add_comm]

theorem arrayOfList_refines_with_steps (xs : List a) :
    (arrayOfList xs).value.toList = xs ∧
      (arrayOfList xs).steps = xs.length + 1 := by
  exact ⟨arrayOfList_value_toList xs, arrayOfList_steps xs⟩

theorem arrayOfList_run (xs : List a) :
    (arrayOfList xs).toCosted.run =
      ((arrayOfList xs).value, xs.length + 1) := by
  rw [Exec.toCosted_run_eq_value_steps, arrayOfList_steps]

end RAM

end RMQ
