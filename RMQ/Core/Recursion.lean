import RMQ.Core.Spec

/-!
# Mathlib-free well-founded recursion helpers

This module isolates the self-referential recursion pattern needed for
recursive hybrid RMQ constructions. Recursive calls are available only on
strictly shorter input lists, measured by `List.length`.
-/

namespace RMQ

/--
Well-founded recursion over lists ordered by length.

The step receives a recursive hypothesis for any strictly shorter list. This is
the ergonomic form we want for recursive RMQ constructions: a summary problem
can call back into the same construction once its length shrink proof is known.
-/
def lengthRec
    {motive : List Int -> Sort u}
    (step : (xs : List Int) ->
      ((ys : List Int) -> ys.length < xs.length -> motive ys) -> motive xs)
    (xs : List Int) : motive xs :=
  step xs (fun ys _h => lengthRec step ys)
termination_by xs.length
decreasing_by
  assumption

/-- Number of full `b`-sized blocks in a list of length `n`. -/
def compressedLength (n b : Nat) : Nat :=
  n / b

theorem compressedLength_lt_self
    {n b : Nat} (hn : 0 < n) (hb : 1 < b) :
    compressedLength n b < n := by
  unfold compressedLength
  exact Nat.div_lt_self hn hb

/--
For nontrivial inputs, the public hybrid block size is strictly larger than
one. This is the small arithmetic fact that makes recursive compression shrink.
-/
theorem publicBlockSize_gt_one_of_length_gt_one
    {xs : List Int} (hlarge : 1 < xs.length) :
    1 < Nat.log2 xs.length + 1 := by
  have hne : xs.length ≠ 0 := by omega
  have htwo_le : 2 ^ 1 <= xs.length := by
    simp
    omega
  have hlog : 1 <= Nat.log2 xs.length := by
    exact (Nat.le_log2 hne).2 htwo_le
  omega

theorem publicCompressedLength_lt_self
    {xs : List Int} (hlarge : 1 < xs.length) :
    compressedLength xs.length (Nat.log2 xs.length + 1) < xs.length := by
  have hpos : 0 < xs.length := by omega
  have hb := publicBlockSize_gt_one_of_length_gt_one (xs := xs) hlarge
  exact compressedLength_lt_self hpos hb

/--
A summary-shape abstraction for self-recursive constructions.

An implementation supplies a summary list plus a proof that large inputs map to
strictly smaller summary inputs. The values in the summary may be block minima,
cartesian-tree signatures, or any future compressed RMQ representation.
-/
structure SummaryShape where
  summary : List Int -> List Int
  shrink : forall {xs : List Int}, 1 < xs.length -> (summary xs).length < xs.length

/--
Generic self-recursive construction over a shrinking summary shape.

`small` handles inputs of length at most one. `large` handles all larger inputs
and receives the recursively constructed result for the summary problem.
-/
def recurseOnSummary
    (shape : SummaryShape)
    {motive : List Int -> Sort u}
    (small : (xs : List Int) -> xs.length <= 1 -> motive xs)
    (large : (xs : List Int) -> (hlarge : 1 < xs.length) ->
      motive (shape.summary xs) -> motive xs)
    (xs : List Int) : motive xs :=
  lengthRec
    (fun xs rec =>
      if hsmall : xs.length <= 1 then
        small xs hsmall
      else
        let hlarge : 1 < xs.length := by omega
        large xs hlarge (rec (shape.summary xs) (shape.shrink hlarge)))
    xs

theorem recurseOnSummary_of_small
    (shape : SummaryShape)
    {motive : List Int -> Sort u}
    (small : (xs : List Int) -> xs.length <= 1 -> motive xs)
    (large : (xs : List Int) -> (hlarge : 1 < xs.length) ->
      motive (shape.summary xs) -> motive xs)
    {xs : List Int}
    (hsmall : xs.length <= 1) :
    recurseOnSummary shape small large xs = small xs hsmall := by
  conv =>
    lhs
    unfold recurseOnSummary
    rw [lengthRec]
  simp [hsmall]

theorem recurseOnSummary_of_large
    (shape : SummaryShape)
    {motive : List Int -> Sort u}
    (small : (xs : List Int) -> xs.length <= 1 -> motive xs)
    (large : (xs : List Int) -> (hlarge : 1 < xs.length) ->
      motive (shape.summary xs) -> motive xs)
    {xs : List Int}
    (hlarge : 1 < xs.length) :
    recurseOnSummary shape small large xs =
      large xs hlarge (recurseOnSummary shape small large (shape.summary xs)) := by
  conv =>
    lhs
    unfold recurseOnSummary
    rw [lengthRec]
  conv =>
    rhs
    unfold recurseOnSummary
  have hnot_small : Not (xs.length <= 1) := by omega
  simp [hnot_small]

/--
The public hybrid block-size summary shape, currently tracking only the
compressed problem size. The summary values are placeholders; later hybrid
layers can replace them with actual block-minimum values while reusing the same
shrink proof.
-/
def publicBlockSummaryShape : SummaryShape where
  summary := fun xs =>
    List.replicate (compressedLength xs.length (Nat.log2 xs.length + 1)) 0
  shrink := by
    intro xs hlarge
    simp [compressedLength]
    exact publicCompressedLength_lt_self (xs := xs) hlarge

/--
A tiny executable witness that the self-recursive shape is accepted by Lean's
well-founded recursion checker. It counts how many recursive summary layers are
formed before the input length reaches at most one.
-/
def publicSummaryDepth (xs : List Int) : Nat :=
  recurseOnSummary publicBlockSummaryShape
    (motive := fun _ => Nat)
    (fun _ _ => 0)
    (fun _ _ depth => depth + 1)
    xs

example : publicSummaryDepth ([] : List Int) = 0 := by native_decide
example : publicSummaryDepth [1] = 0 := by native_decide
example : publicSummaryDepth [1, 2, 3, 4, 5] = 1 := by native_decide

end RMQ
