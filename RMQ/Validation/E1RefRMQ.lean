/-!
# The independent reference RMQ, in a module of its own

REQ-E1-08's anti-vacuity column requires that the reference implementation
"must not import the machine or succinct modules' answers (independence
audit: it may share only `List Int` and basic prelude)".

`refRMQ` satisfied that FUNCTIONALLY from the day it was written -- it calls
neither the machine nor the succinct route -- but it was DEFINED inside
`RMQ/Validation/E1MachineValidate.lean`, which imports nine machine modules.
On the clause's literal wording that failed, and the matrix recorded it as
gap (b) of REQ-E1-08.  This module is the repair: it is the reference and
nothing else, and it has **no `import` lines at all**, so its entire ambient
context is Lean's own `Init` -- the "basic prelude" the clause allows.

The independence is therefore STRUCTURAL rather than argued.  A later edit
that reached for a machine or route constant from here would not merely be
poor style; it would fail to elaborate, because the constant is not in
scope.  That is the property the clause is asking for, and it is now
enforced by the module system instead of by reviewer attention.

## Why the namespace does not match the module path

The declarations below sit in `RMQ.Validation.E1MachineValidate`, not in a
namespace named after this file.  That is deliberate and load-bearing:
`refRMQ`'s fully-qualified name is cited by the acceptance matrix, and the
campaign's standing rule forbids renaming a frozen public identity.  Keeping
the namespace keeps `RMQ.Validation.E1MachineValidate.refRMQ` spelled exactly
as it was before the move, so this is a change of FILE only -- no identity,
no call site, and no citation moves with it.
-/

namespace RMQ.Validation.E1MachineValidate

/-! ## 1. The independent reference implementation

Written from the specification of half-open leftmost RMQ.  Nothing in this
section mentions the machine, the route, or any repository construction. -/

/-- Half-open leftmost range minimum over `xs` on `[lo, hi)`.

Specification, restated: the result is `some i` where `lo ≤ i < hi`,
`xs[i]` is minimal over the window, and no `j < i` in the window attains
that minimum; the result is `none` exactly when the window is empty
(`hi ≤ lo`) or reaches past the end of `xs` (`xs.length < hi`).

The fold replaces the incumbent only on a STRICTLY smaller value, which is
what makes the answer the LEFTMOST minimiser rather than an arbitrary
one. -/
def refRMQ (xs : List Int) (lo hi : Nat) : Option Nat :=
  if hi ≤ lo then none
  else if xs.length < hi then none
  else
    ((List.range (hi - lo)).map (fun k => lo + k)).foldl
      (fun best i =>
        match best with
        | none => some i
        | some b =>
            match xs[i]?, xs[b]? with
            | some v, some bv => if v < bv then some i else some b
            | _, _ => best)
      none

/-! ## 2. The two guard clauses, PROVED rather than executed

The harness already checks the reference's positive content by execution
(`expectationSelfConsistent`, which brute-forces leftmost-minimality against
every other window index).  What it cannot check by execution is a clause
that quantifies over ALL inputs, and the specification's two `none` clauses
are exactly that shape.

They are proved here rather than in the harness for the same reason the
definition lives here: a theorem that elaborates in a module with no imports
is itself evidence that the reference needs nothing beyond the prelude.  A
reference whose properties could only be established with the machine in
scope would not be independent of it in any useful sense. -/

/-- An empty or reversed window has no minimiser. -/
theorem refRMQ_eq_none_of_hi_le_lo (xs : List Int) (lo hi : Nat)
    (h : hi ≤ lo) : refRMQ xs lo hi = none := by
  unfold refRMQ
  rw [if_pos h]

/-- A window reaching past the end of the list has no minimiser.

Both branches are spelled with an explicit `if_pos`/`if_neg` rather than
`split`, and the reason is worth recording.  `split` also proves this, but it
proves it by using `h` to discharge the branch where `¬(xs.length < hi)` --
so the hypothesis is consumed by the SPLIT and the remaining goals both read
`none = none`, at which point a trailing `simp [h]` reports `h` as an unused
simp argument.  Written that way the theorem looks like it does not depend on
its hypothesis.  It does: with `h` deleted from the statement the proof fails
on exactly that third branch, the goal retaining the `foldl`.  The explicit
form below keeps the dependence visible at the point where it is used. -/
theorem refRMQ_eq_none_of_length_lt (xs : List Int) (lo hi : Nat)
    (h : xs.length < hi) : refRMQ xs lo hi = none := by
  unfold refRMQ
  by_cases hle : hi ≤ lo
  · rw [if_pos hle]
  · rw [if_neg hle, if_pos h]

end RMQ.Validation.E1MachineValidate
