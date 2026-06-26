import RMQ.Core.Cost

/-!
# Amortized accounting

This module is the first reusable potential-method layer for non-succinct data
structures.  It deliberately stays small: an amortized step is an inequality
relating actual cost, potential before/after, and charged credit.  Concrete
structures such as union-find can later instantiate the potential function and
compose these inequalities.
-/

namespace RMQ

namespace Amortized

/--
`Bound actual before after credit` is the standard potential-method local
obligation: actual work plus final potential is paid for by charged credit plus
initial potential.
-/
def Bound (actual before after credit : Nat) : Prop :=
  actual + after <= credit + before

theorem actual_le_credit_plus_before
    {actual before after credit : Nat}
    (h : Bound actual before after credit) :
    actual <= credit + before := by
  unfold Bound at h
  omega

theorem zero (potential : Nat) :
    Bound 0 potential potential 0 := by
  unfold Bound
  omega

theorem of_actual_le
    {actual before after credit : Nat}
    (hactual : actual <= credit)
    (hpotential : after <= before) :
    Bound actual before after credit := by
  unfold Bound
  omega

theorem compose
    {actual1 actual2 potential0 potential1 potential2 credit1 credit2 : Nat}
    (h1 : Bound actual1 potential0 potential1 credit1)
    (h2 : Bound actual2 potential1 potential2 credit2) :
    Bound (actual1 + actual2) potential0 potential2 (credit1 + credit2) := by
  unfold Bound at h1 h2 ⊢
  omega

/-- Costed form of `Bound`. -/
def CostedBound (x : Costed α) (before after credit : Nat) : Prop :=
  Bound x.cost before after credit

theorem costed_actual_le_credit_plus_before
    {x : Costed α} {before after credit : Nat}
    (h : CostedBound x before after credit) :
    x.cost <= credit + before :=
  actual_le_credit_plus_before h

theorem costed_pure (x : α) (potential : Nat) :
    CostedBound (Costed.pure x) potential potential 0 := by
  unfold CostedBound
  simpa using zero potential

theorem costed_tickValue
    (n : Nat) (x : α) (potential : Nat) :
    CostedBound (Costed.tickValue n x) potential potential n := by
  unfold CostedBound Bound
  simp

theorem costed_bind
    {x : Costed α} {f : α -> Costed β}
    {potential0 potential1 potential2 credit1 credit2 : Nat}
    (h1 : CostedBound x potential0 potential1 credit1)
    (h2 : CostedBound (f x.value) potential1 potential2 credit2) :
    CostedBound (Costed.bind x f)
      potential0 potential2 (credit1 + credit2) := by
  unfold CostedBound
  simpa [Costed.cost_bind] using compose h1 h2

end Amortized

end RMQ
