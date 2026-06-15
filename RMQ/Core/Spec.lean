import Std

/-!
# Core RMQ specification

This module contains the canonical value-correctness contract used by the RMQ
library: valid queries are nonempty half-open windows, and successful answers
return the leftmost index attaining the minimum value in that window.
-/

namespace RMQ

/-- A valid RMQ query is a nonempty half-open range inside the list. -/
abbrev ValidRange (xs : List Int) (left right : Nat) : Prop :=
  left < right /\ right <= xs.length

/-- Prefer index `i` exactly when it has a strictly smaller value than `best`. -/
def betterIndex (xs : List Int) (best i : Nat) : Nat :=
  match xs[best]?, xs[i]? with
  | some bestVal, some iVal => if iVal < bestVal then i else best
  | none, some _ => i
  | _, _ => best

/-- Option-level argmin combination. `none` represents an absent subrange. -/
def combineIndex (xs : List Int) : Option Nat -> Option Nat -> Option Nat
  | none, other => other
  | other, none => other
  | some i, some j => some (betterIndex xs i j)

/--
`LeftmostArgMin xs left right idx` says `idx` is the leftmost position attaining
the minimum value in the valid half-open range `[left, right)`.
-/
def LeftmostArgMin (xs : List Int) (left right idx : Nat) : Prop :=
  left < right /\ right <= xs.length /\
    left <= idx /\ idx < right /\
      exists v, xs[idx]? = some v /\
        (forall j w, left <= j -> j < right -> xs[j]? = some w -> v <= w) /\
        (forall j w, left <= j -> j < idx -> xs[j]? = some w -> v < w)

/-- A leftmost-argmin witness implies the query range is valid. -/
theorem LeftmostArgMin.valid {xs : List Int} {left right idx : Nat}
    (h : LeftmostArgMin xs left right idx) :
    ValidRange xs left right :=
  ⟨h.1, h.2.1⟩

/-- Leftmost argmin witnesses are unique. -/
theorem leftmostArgMin_unique (xs : List Int) (left right : Nat) :
    forall i j,
      LeftmostArgMin xs left right i ->
        LeftmostArgMin xs left right j -> i = j := by
  intro i j hi hj
  rcases hi with ⟨_hli, _hri, hleft_i, hright_i, vi, hget_i, hmin_i, hleftmost_i⟩
  rcases hj with ⟨_hlj, _hrj, hleft_j, hright_j, vj, hget_j, hmin_j, hleftmost_j⟩
  by_cases hij : i = j
  · exact hij
  · by_cases hlt : i < j
    · have hvj_lt_vi := hleftmost_j i vi hleft_i hlt hget_i
      have hvi_le_vj := hmin_i j vj hleft_j hright_j hget_j
      omega
    · have hji : j < i := by omega
      have hvi_lt_vj := hleftmost_i j vj hleft_j hji hget_j
      have hvj_le_vi := hmin_j i vi hleft_i hright_i hget_i
      omega

/--
If two exact argmin witnesses cover a larger range, `betterIndex` combines
them into the exact leftmost argmin for the larger range.
-/
theorem combineLeftmost
    {xs : List Int} {left r1 l2 right i j : Nat}
    (hA : LeftmostArgMin xs left r1 i)
    (hB : LeftmostArgMin xs l2 right j)
    (hA_sub : r1 <= right)
    (hB_sub : left <= l2)
    (hcover : forall t, left <= t -> t < right -> t < r1 \/ l2 <= t) :
    LeftmostArgMin xs left right (betterIndex xs i j) := by
  rcases hA with ⟨_hleft_r1, _hr1_len, hleft_i, hi_r1, vi, hi_get, hi_min,
    hi_leftmost⟩
  rcases hB with ⟨_hl2_right, hright_len, hl2_j, hj_right, vj, hj_get, hj_min,
    hj_leftmost⟩
  unfold betterIndex
  simp [hi_get, hj_get]
  by_cases hlt : vj < vi
  · simp [hlt]
    refine ⟨by omega, hright_len, by omega, hj_right, vj, hj_get, ?_, ?_⟩
    · intro t w ht_left ht_right hget
      rcases hcover t ht_left ht_right with htA | htB
      · have hvi_le := hi_min t w ht_left htA hget
        omega
      · exact hj_min t w htB ht_right hget
    · intro t w ht_left ht_j hget
      rcases hcover t ht_left (Nat.lt_trans ht_j hj_right) with htA | htB
      · have hvi_le := hi_min t w ht_left htA hget
        omega
      · exact hj_leftmost t w htB ht_j hget
  · simp [hlt]
    have hvi_le_vj : vi <= vj := by omega
    refine ⟨by omega, by omega, hleft_i, by omega, vi, hi_get, ?_, ?_⟩
    · intro t w ht_left ht_right hget
      rcases hcover t ht_left ht_right with htA | htB
      · exact hi_min t w ht_left htA hget
      · have hvj_le := hj_min t w htB ht_right hget
        omega
    · intro t w ht_left ht_i hget
      exact hi_leftmost t w ht_left ht_i hget

/--
`CandidateExact xs left right candidate` connects an optional candidate to an
interval: `some idx` carries an exact leftmost argmin witness, while `none`
is allowed exactly for an empty interval.
-/
def CandidateExact
    (xs : List Int) (left right : Nat) (candidate : Option Nat) : Prop :=
  (candidate = none /\ left = right) \/
    exists idx, candidate = some idx /\ LeftmostArgMin xs left right idx

theorem candidateExact_none {xs : List Int} {left right : Nat}
    (h : left = right) :
    CandidateExact xs left right none := by
  exact Or.inl ⟨rfl, h⟩

theorem candidateExact_some {xs : List Int} {left right idx : Nat}
    (h : LeftmostArgMin xs left right idx) :
    CandidateExact xs left right (some idx) := by
  exact Or.inr ⟨idx, rfl, h⟩

theorem CandidateExact.exists_of_nonempty
    {xs : List Int} {left right : Nat} {candidate : Option Nat}
    (h : CandidateExact xs left right candidate)
    (hne : left < right) :
    exists idx, candidate = some idx /\ LeftmostArgMin xs left right idx := by
  rcases h with ⟨_hnone, hempty⟩ | hsome
  · omega
  · exact hsome

/-- Adjacent exact optional candidates compose through `combineIndex`. -/
theorem candidateExact_combineAdjacent
    {xs : List Int} {left middle right : Nat}
    {leftCandidate rightCandidate : Option Nat}
    (hLeft : CandidateExact xs left middle leftCandidate)
    (hRight : CandidateExact xs middle right rightCandidate) :
    CandidateExact xs left right
      (combineIndex xs leftCandidate rightCandidate) := by
  rcases hLeft with ⟨hlNone, hleft_empty⟩ | ⟨li, hlSome, hlarg⟩
  · rcases hRight with ⟨hrNone, hright_empty⟩ | ⟨ri, hrSome, hrarg⟩
    · exact Or.inl ⟨by simp [combineIndex, hlNone, hrNone], by omega⟩
    · refine Or.inr ⟨ri, ?_, ?_⟩
      · simp [combineIndex, hlNone, hrSome]
      · simpa [hleft_empty] using hrarg
  · rcases hRight with ⟨hrNone, hright_empty⟩ | ⟨ri, hrSome, hrarg⟩
    · refine Or.inr ⟨li, ?_, ?_⟩
      · simp [combineIndex, hlSome, hrNone]
      · simpa [hright_empty] using hlarg
    · refine Or.inr ⟨betterIndex xs li ri, ?_, ?_⟩
      · simp [combineIndex, hlSome, hrSome]
      · have hcover :
            forall t, left <= t -> t < right ->
              t < middle \/ middle <= t := by
          intro t _ht_left _ht_right
          by_cases ht : t < middle
          · exact Or.inl ht
          · exact Or.inr (by omega)
        have hA_sub : middle <= right := Nat.le_of_lt hrarg.1
        have hB_sub : left <= middle := Nat.le_of_lt hlarg.1
        exact combineLeftmost hlarg hrarg hA_sub hB_sub hcover

/-- Three adjacent exact optional candidates compose associatively in query order. -/
theorem candidateExact_combineThree
    {xs : List Int} {left middle right end_ : Nat}
    {leftCandidate middleCandidate rightCandidate : Option Nat}
    (hLeft : CandidateExact xs left middle leftCandidate)
    (hMiddle : CandidateExact xs middle right middleCandidate)
    (hRight : CandidateExact xs right end_ rightCandidate) :
    CandidateExact xs left end_
      (combineIndex xs (combineIndex xs leftCandidate middleCandidate)
        rightCandidate) := by
  exact candidateExact_combineAdjacent
    (candidateExact_combineAdjacent hLeft hMiddle) hRight

/--
Combine the three candidate pieces used by hybrid RMQ schedules.

The left boundary piece is nonempty and exact. The middle and right pieces may
be absent, but only when their corresponding interval is empty.
-/
theorem combineHybridLeftmost
    {xs : List Int} {left leftEnd middleEnd right li : Nat}
    {middleCandidate rightCandidate : Option Nat}
    (hLeft : LeftmostArgMin xs left leftEnd li)
    (hMiddle : CandidateExact xs leftEnd middleEnd middleCandidate)
    (hRight : CandidateExact xs middleEnd right rightCandidate)
    (hLeftMiddle : leftEnd <= middleEnd)
    (hMiddleRight : middleEnd <= right) :
    exists idx,
      combineIndex xs (combineIndex xs (some li) middleCandidate) rightCandidate =
        some idx /\
      LeftmostArgMin xs left right idx := by
  have hCombined :
      CandidateExact xs left right
        (combineIndex xs (combineIndex xs (some li) middleCandidate)
          rightCandidate) :=
    candidateExact_combineThree
      (candidateExact_some hLeft) hMiddle hRight
  have hleft_lt_leftEnd : left < leftEnd := hLeft.1
  have hne : left < right := by omega
  exact hCombined.exists_of_nonempty hne

end RMQ
