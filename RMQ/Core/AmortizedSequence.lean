import RMQ.Core.Amortized

/-!
# Amortized sequence accounting (potential-method telescoping)

`RMQ.Core.Amortized` provides the per-operation potential-method obligation

```
Amortized.Bound actual before after credit := actual + after <= credit + before
```

and a two-step `compose`. This module telescopes a *whole sequence* of such
obligations threaded through a potential: the total actual work over the sequence
is bounded by the total charged credit plus the initial potential. This is the
harness an amortized-complexity headline actually needs — e.g. "a sequence of `m`
union-find operations costs at most `(total credit) + Phi_initial`" — rather than
a single per-operation inequality that might not compose.

It is data-structure agnostic: a concrete structure supplies a potential and a
per-operation `Bound`, and `runBound` / `totalActual_le` deliver the sequence
bound.
-/

namespace RMQ

namespace Amortized

/--
One amortized step record: the actual work done, the potential immediately after
the step, and the credit charged for it. The potential *before* the step is
threaded externally (by `RunBound` / `finalPotential`), so a `List Step` is a run
whose intermediate potentials are pinned by the `after` fields.
-/
structure Step where
  actual : Nat
  after  : Nat
  credit : Nat
deriving Repr, DecidableEq

namespace Step

/-- Total actual work over a run. -/
def totalActual : List Step -> Nat
  | [] => 0
  | s :: rest => s.actual + totalActual rest

/-- Total charged credit over a run. -/
def totalCredit : List Step -> Nat
  | [] => 0
  | s :: rest => s.credit + totalCredit rest

@[simp] theorem totalActual_nil : totalActual [] = 0 := rfl
@[simp] theorem totalActual_cons (s : Step) (rest : List Step) :
    totalActual (s :: rest) = s.actual + totalActual rest := rfl
@[simp] theorem totalCredit_nil : totalCredit [] = 0 := rfl
@[simp] theorem totalCredit_cons (s : Step) (rest : List Step) :
    totalCredit (s :: rest) = s.credit + totalCredit rest := rfl

end Step

/-- The potential after running `steps` starting from potential `before`. -/
def finalPotential (before : Nat) : List Step -> Nat
  | [] => before
  | s :: rest => finalPotential s.after rest

@[simp] theorem finalPotential_nil (before : Nat) :
    finalPotential before [] = before := rfl
@[simp] theorem finalPotential_cons (before : Nat) (s : Step) (rest : List Step) :
    finalPotential before (s :: rest) = finalPotential s.after rest := rfl

/--
A *valid run* from initial potential `before`: each step's local potential-method
`Bound` holds against the potential threaded through the previous `after` fields.
-/
def RunBound (before : Nat) : List Step -> Prop
  | [] => True
  | s :: rest => Bound s.actual before s.after s.credit /\ RunBound s.after rest

@[simp] theorem runBound_nil (before : Nat) : RunBound before [] := trivial
@[simp] theorem runBound_cons (before : Nat) (s : Step) (rest : List Step) :
    RunBound before (s :: rest) <->
      (Bound s.actual before s.after s.credit /\ RunBound s.after rest) :=
  Iff.rfl

/--
Telescoped potential-method bound: total actual work plus the final potential is
covered by total credit plus the initial potential. This is the exact
generalization of `Amortized.compose` from two steps to a whole sequence.
-/
theorem runBound (steps : List Step) (before : Nat)
    (h : RunBound before steps) :
    Step.totalActual steps + finalPotential before steps
      <= Step.totalCredit steps + before := by
  induction steps generalizing before with
  | nil => simp
  | cons s rest ih =>
      rcases h with ⟨hstep, hrest⟩
      have hb : s.actual + s.after <= s.credit + before := hstep
      have ihb := ih s.after hrest
      simp only [Step.totalActual_cons, Step.totalCredit_cons,
        finalPotential_cons]
      omega

/--
Headline amortized bound: the total actual work over a valid run is at most the
total charged credit plus the initial potential (the final potential is `>= 0`
and is dropped). Instantiating `credit` with a uniform per-operation bound `c`
gives `totalActual <= (#operations) * c + Phi_initial`.
-/
theorem totalActual_le (steps : List Step) (before : Nat)
    (h : RunBound before steps) :
    Step.totalActual steps <= Step.totalCredit steps + before := by
  have hrun := runBound steps before h
  omega

/-- Total credit over a run is at most `(#steps) * c` when each step charges at most `c`. -/
theorem Step.totalCredit_le_length_mul (steps : List Step) (c : Nat)
    (hcredit : forall s, s ∈ steps -> s.credit <= c) :
    totalCredit steps <= steps.length * c := by
  induction steps with
  | nil => simp
  | cons s rest ih =>
      have hs : s.credit <= c := hcredit s (List.mem_cons.mpr (Or.inl rfl))
      have hrest : forall t, t ∈ rest -> t.credit <= c :=
        fun t ht => hcredit t (List.mem_cons.mpr (Or.inr ht))
      have hih := ih hrest
      simp only [totalCredit_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/--
Uniform-credit corollary: if every step charges at most `c` credit, the whole
run costs at most `steps.length * c + Phi_initial`.
-/
theorem totalActual_le_length_mul
    (steps : List Step) (before c : Nat)
    (h : RunBound before steps)
    (hcredit : forall s, s ∈ steps -> s.credit <= c) :
    Step.totalActual steps <= steps.length * c + before := by
  have hbase := totalActual_le steps before h
  have hcred := Step.totalCredit_le_length_mul steps c hcredit
  omega

end Amortized

end RMQ
