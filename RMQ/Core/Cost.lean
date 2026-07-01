import Std

/-!
# Lightweight cost accounting

This module introduces a tiny Mathlib-free cost carrier for later algorithmic
cost proofs. It deliberately separates the value story from the cost story:
`erase` forgets costs, while `run` exposes both the value and accumulated cost.
-/

namespace RMQ

/-- A pure value paired with a natural-number cost. -/
structure Costed (a : Type u) where
  value : a
  cost : Nat
deriving Repr, DecidableEq

namespace Costed

theorem ext {x y : Costed a}
    (hvalue : x.value = y.value) (hcost : x.cost = y.cost) :
    x = y := by
  cases x with
  | mk xv xc =>
      cases y with
      | mk yv yc =>
          simp at hvalue hcost
          subst yv
          subst yc
          rfl

/-- Forget the cost annotation. -/
def erase (x : Costed a) : a :=
  x.value

/-- Expose both the value and accumulated cost. -/
def run (x : Costed a) : Prod a Nat :=
  (x.value, x.cost)

/-- A zero-cost value. -/
def pure (x : a) : Costed a where
  value := x
  cost := 0

/-- Sequential composition adds costs. -/
def bind (x : Costed a) (f : a -> Costed b) : Costed b :=
  let y := f x.value
  { value := y.value, cost := x.cost + y.cost }

/-- Add `n` units of cost and return `Unit`. -/
def tick (n : Nat := 1) : Costed Unit where
  value := ()
  cost := n

/-- Charge `n` units of cost to a specific value. -/
def tickValue (n : Nat) (x : a) : Costed a where
  value := x
  cost := n

/-- Map a pure function over a costed value without changing its cost. -/
def map (f : a -> b) (x : Costed a) : Costed b :=
  bind x (fun y => pure (f y))

@[simp] theorem erase_mk (x : a) (n : Nat) :
    erase ({ value := x, cost := n } : Costed a) = x := by
  rfl

@[simp] theorem run_mk (x : a) (n : Nat) :
    run ({ value := x, cost := n } : Costed a) = (x, n) := by
  rfl

@[simp] theorem value_pure (x : a) :
    (pure x).value = x := by
  rfl

@[simp] theorem cost_pure (x : a) :
    (pure x).cost = 0 := by
  rfl

@[simp] theorem erase_pure (x : a) :
    erase (pure x) = x := by
  rfl

@[simp] theorem run_pure (x : a) :
    run (pure x) = (x, 0) := by
  rfl

@[simp] theorem value_bind (x : Costed a) (f : a -> Costed b) :
    (bind x f).value = (f x.value).value := by
  rfl

@[simp] theorem cost_bind (x : Costed a) (f : a -> Costed b) :
    (bind x f).cost = x.cost + (f x.value).cost := by
  rfl

@[simp] theorem erase_bind (x : Costed a) (f : a -> Costed b) :
    erase (bind x f) = erase (f (erase x)) := by
  rfl

@[simp] theorem run_bind (x : Costed a) (f : a -> Costed b) :
    run (bind x f) =
      ((f x.value).value, x.cost + (f x.value).cost) := by
  rfl

@[simp] theorem value_tick (n : Nat) :
    (tick n).value = () := by
  rfl

@[simp] theorem cost_tick (n : Nat) :
    (tick n).cost = n := by
  rfl

@[simp] theorem erase_tick (n : Nat) :
    erase (tick n) = () := by
  rfl

@[simp] theorem run_tick (n : Nat) :
    run (tick n) = ((), n) := by
  rfl

@[simp] theorem value_tickValue (n : Nat) (x : a) :
    (tickValue n x).value = x := by
  rfl

@[simp] theorem cost_tickValue (n : Nat) (x : a) :
    (tickValue n x).cost = n := by
  rfl

@[simp] theorem erase_tickValue (n : Nat) (x : a) :
    erase (tickValue n x) = x := by
  rfl

@[simp] theorem run_tickValue (n : Nat) (x : a) :
    run (tickValue n x) = (x, n) := by
  rfl

@[simp] theorem pure_bind (x : a) (f : a -> Costed b) :
    bind (pure x) f = f x := by
  cases h : f x with
  | mk y c =>
      simp [bind, pure, h]

@[simp] theorem bind_pure (x : Costed a) :
    bind x pure = x := by
  cases x
  rfl

theorem bind_assoc
    (x : Costed a) (f : a -> Costed b) (g : b -> Costed c) :
    bind (bind x f) g = bind x (fun y => bind (f y) g) := by
  cases x with
  | mk xv xc =>
      cases f xv with
      | mk yv yc =>
          cases g yv with
          | mk zv zc =>
              simp [bind, Nat.add_assoc]

theorem cost_bind_assoc
    (x : Costed a) (f : a -> Costed b) (g : b -> Costed c) :
    (bind (bind x f) g).cost =
      x.cost + (f x.value).cost + (g (f x.value).value).cost := by
  simp [Nat.add_assoc]

theorem tick_bind_cost (n : Nat) (f : Unit -> Costed a) :
    (bind (tick n) f).cost = n + (f ()).cost := by
  rfl

theorem bind_tick_cost (x : Costed a) (n : Nat) :
    (bind x (fun _ => tick n)).cost = x.cost + n := by
  rfl

theorem tickValue_eq_tick_bind_pure (n : Nat) (x : a) :
    tickValue n x = bind (tick n) (fun _ => pure x) := by
  rfl

@[simp] theorem map_value (f : a -> b) (x : Costed a) :
    (map f x).value = f x.value := by
  rfl

@[simp] theorem map_cost (f : a -> b) (x : Costed a) :
    (map f x).cost = x.cost := by
  cases x
  rfl

@[simp] theorem erase_map (f : a -> b) (x : Costed a) :
    erase (map f x) = f (erase x) := by
  rfl

end Costed

end RMQ
