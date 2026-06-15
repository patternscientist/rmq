import RMQ.Core.Spec

/-!
# Window scan kernel

This module factors the left-to-right scan used by linear RMQ and by later
boundary-window implementations. The main theorem proves that scanning a valid
window returns the exact `LeftmostArgMin` witness.
-/

namespace RMQ

/-- Indices scanned after the initial left endpoint for a window of length `len`. -/
def windowTailIndices (start : Nat) : Nat -> List Nat
  | 0 => []
  | 1 => []
  | len + 2 => windowTailIndices start (len + 1) ++ [start + len + 1]

/-- Linear-scan kernel for a half-open window starting at `start` with length `len`. -/
def scanWindow (xs : List Int) (start : Nat) : Nat -> Nat
  | 0 => start
  | 1 => start
  | len + 2 => betterIndex xs (scanWindow xs start (len + 1)) (start + len + 1)

private theorem get?_some_of_lt (xs : List Int) {i : Nat} (h : i < xs.length) :
    xs[i]? = some (xs[i]'h) := by
  simp

/-- A singleton valid window has its only index as the leftmost argmin. -/
theorem singleton_leftmostArgMin
    (xs : List Int) (start : Nat) (hstart : start < xs.length) :
    LeftmostArgMin xs start (start + 1) start := by
  refine ⟨by omega, by omega, by omega, by omega, xs[start]'hstart,
    get?_some_of_lt xs hstart, ?_, ?_⟩
  · intro j w hleft hright hget
    have hj : j = start := by omega
    subst j
    have hw : w = xs[start]'hstart := by
      exact (Option.some.inj (by simpa [get?_some_of_lt xs hstart] using hget)).symm
    simp [hw]
  · intro j _ hleft hlt _
    omega

/-- Extending an exact window by one right endpoint preserves leftmost argmin. -/
theorem extend_leftmostArgMin
    (xs : List Int) {left right best : Nat}
    (hbest : LeftmostArgMin xs left right best)
    (hright : right < xs.length) :
    LeftmostArgMin xs left (right + 1) (betterIndex xs best right) := by
  rcases hbest with ⟨hlr, hr_len, hl_best, hbest_right, bestVal,
    hbest_get, hbest_min, hbest_leftmost⟩
  let rightVal := xs[right]'hright
  have hright_get : xs[right]? = some rightVal := get?_some_of_lt xs hright
  unfold betterIndex
  simp [hbest_get, hright_get]
  by_cases hlt : rightVal < bestVal
  · simp [hlt]
    refine ⟨by omega, by omega, by omega, by omega, rightVal, hright_get, ?_, ?_⟩
    · intro j w hj_left hj_right hget
      by_cases hj_eq : j = right
      · subst j
        have hw : w = rightVal := by
          exact (Option.some.inj (by simpa [hright_get] using hget)).symm
        simp [hw]
      · have hj_old : j < right := by omega
        have hbest_le := hbest_min j w hj_left hj_old hget
        omega
    · intro j w hj_left hj_lt hget
      have hj_old : j < right := by omega
      have hbest_le := hbest_min j w hj_left hj_old hget
      omega
  · simp [hlt]
    have hbest_le_right : bestVal <= rightVal := by omega
    refine ⟨by omega, by omega, hl_best, by omega, bestVal, hbest_get, ?_, ?_⟩
    · intro j w hj_left hj_right hget
      by_cases hj_eq : j = right
      · subst j
        have hw : w = rightVal := by
          exact (Option.some.inj (by simpa [hright_get] using hget)).symm
        simpa [hw] using hbest_le_right
      · have hj_old : j < right := by omega
        exact hbest_min j w hj_left hj_old hget
    · intro j w hj_left hj_lt hget
      exact hbest_leftmost j w hj_left hj_lt hget

/-- Scanning a bounded nonempty window returns its exact leftmost argmin. -/
theorem scanWindow_leftmost
    (xs : List Int) (start len : Nat)
    (hlen : 0 < len) (hbound : start + len <= xs.length) :
    LeftmostArgMin xs start (start + len) (scanWindow xs start len) := by
  induction len with
  | zero =>
      omega
  | succ len ih =>
      cases len with
      | zero =>
          have hstart : start < xs.length := by omega
          simpa [scanWindow] using singleton_leftmostArgMin xs start hstart
      | succ len =>
          have hprefix_pos : 0 < Nat.succ len := by omega
          have hprefix_bound : start + Nat.succ len <= xs.length := by omega
          have hprefix := ih hprefix_pos hprefix_bound
          have hright_lt : start + Nat.succ len < xs.length := by omega
          have hext := extend_leftmostArgMin xs hprefix hright_lt
          simpa [scanWindow, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hext

end RMQ
