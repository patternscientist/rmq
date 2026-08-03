import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
EG-CP-F01, part J: REFINED `n`-only budgets for the two content-dependent
select components.

Why this matters.  The existing budgets are `o(n)` but their crossovers are
astronomically far out:

  longSuperRelativeTableOverhead n     = n / ell n + 1          (~ n/4 at n=512)
  sparseExceptionRelativeTableOverhead n = 512 * (n / ell n) + 512
                                                                (= 129 * n at n=512)

Padding to the second one would cost 66048 bits inside a 1024-bit structure.
But parts G and I prove both tables are EMPTY in closed, `n`-decidable regimes.
Folding those regimes into the budget gives a still-`n`-only budget that is
exactly ZERO at every reachable size.
-/

namespace SdkJ

open RMQ
open RMQ.Cartesian
open RMQ.GenericSelect

/-! ## Re-derive the two emptiness facts (self-contained) -/

theorem superSpan_le_length
    (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hslot : superSlot < superSlotCount bits target) :
    superSpan bits target superSlot <= bits.length := by
  have hgap := superSpan_le_next_gap bits target hslot
  have hnext :
      position bits target
        (superBaseOccurrence bits.length (superSlot + 1)) <= bits.length :=
    position_le_length bits target _
  omega

theorem longRank_zero
    (bits : List Bool) (target : Bool)
    (hsmall : bits.length <= superLongSpan bits.length) :
    forall m, m <= superSlotCount bits target ->
      RMQ.Succinct.rankPrefix true (longSuperFlagBits bits target) m = 0 := by
  intro m
  induction m with
  | zero => intro _; simp [RMQ.Succinct.rankPrefix]
  | succ m ih =>
      intro hm
      have hslot : m < superSlotCount bits target := by omega
      have hget := longSuperFlagBits_get? bits target hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true) (bits := longSuperFlagBits bits target)
          (n := m) hget
      have hfalse : superIsLong bits target m = false := by
        unfold superIsLong
        have hspan := superSpan_le_length bits target hslot
        simp
        omega
      rw [hrank, ih (by omega), hfalse]
      simp

theorem sparseRank_zero
    (bits : List Bool) (target : Bool)
    (hstride : localStride bits.length = 1) :
    forall m, m <= localSlotCount bits target ->
      RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target) m = 0 := by
  intro m
  induction m with
  | zero => intro _; simp [RMQ.Succinct.rankPrefix]
  | succ m ih =>
      intro hm
      have hslot : m < localSlotCount bits target := by omega
      have hget := sparseExceptionFlagBits_get? bits target hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true) (bits := sparseExceptionFlagBits bits target)
          (n := m) hget
      have hspan : shortSuperLocalSpan bits target m <= 1 := by
        have hend :
            shortSuperLocalEndOccurrence bits target m <=
              localBaseOccurrence bits.length m + 1 := by
          unfold shortSuperLocalEndOccurrence
          rw [hstride]
          exact Nat.min_le_left _ _
        have hmono :
            position bits target
                (shortSuperLocalEndOccurrence bits target m - 1) <=
              position bits target (localBaseOccurrence bits.length m) :=
          position_mono bits target (by omega)
        show
          position bits target
              (shortSuperLocalEndOccurrence bits target m - 1) + 1 -
            position bits target (localBaseOccurrence bits.length m) <= 1
        omega
      have hfalse : localIsSparseException bits target m = false := by
        unfold localIsSparseException
        have hword : 0 < wordBits bits.length := wordBits_pos bits.length
        simp
        intro _
        omega
      rw [hrank, ih (by omega), hfalse]
      simp

/-! ## The refined budgets -/

/-- Refined `n`-only budget for the long-super relative region. -/
def refinedLongBudget (n : Nat) : Nat :=
  if n <= superLongSpan n then 0 else longSuperRelativeTableOverhead n

/-- Refined `n`-only budget for the sparse-exception relative region. -/
def refinedSparseBudget (n : Nat) : Nat :=
  if localStride n = 1 then 0 else sparseExceptionRelativeTableOverhead n

/-- The refined long budget is still an unconditional upper bound. -/
theorem long_le_refined (bits : List Bool) (target : Bool) :
    (longSuperRelativeTable bits target).payload.length <=
      refinedLongBudget bits.length := by
  unfold refinedLongBudget
  by_cases hsmall : bits.length <= superLongSpan bits.length
  · rw [if_pos hsmall, longSuperRelativeTable_payload_length,
      longRank_zero bits target hsmall (superSlotCount bits target)
        (Nat.le_refl _)]
    simp
  · rw [if_neg hsmall]
    exact longSuperRelativeTable_payload_le_overhead bits target

/-- The refined sparse budget is still an unconditional upper bound. -/
theorem sparse_le_refined (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeTable bits target).payload.length <=
      refinedSparseBudget bits.length := by
  unfold refinedSparseBudget
  by_cases hstride : localStride bits.length = 1
  · rw [if_pos hstride, sparseExceptionRelativeTable_payload_expanded_length,
      sparseRank_zero bits target hstride (localSlotCount bits target)
        (Nat.le_refl _)]
    simp
  · rw [if_neg hstride]
    exact sparseExceptionRelativeTable_payload_le_overhead bits target

/-- Both refined budgets are pointwise below the originals, hence still `o(n)`. -/
theorem refined_le_original (n : Nat) :
    refinedLongBudget n <= longSuperRelativeTableOverhead n /\
      refinedSparseBudget n <= sparseExceptionRelativeTableOverhead n := by
  constructor
  · unfold refinedLongBudget
    by_cases h : n <= superLongSpan n
    · rw [if_pos h]; exact Nat.zero_le _
    · rw [if_neg h]; exact Nat.le_refl _
  · unfold refinedSparseBudget
    by_cases h : localStride n = 1
    · rw [if_pos h]; exact Nat.zero_le _
    · rw [if_neg h]; exact Nat.le_refl _

theorem refined_littleO :
    SuccinctSpace.LittleOLinear refinedLongBudget /\
      SuccinctSpace.LittleOLinear refinedSparseBudget := by
  constructor
  · intro scale hscale
    obtain ⟨th, hth⟩ := longSuperRelativeTableOverhead_littleO scale hscale
    refine ⟨th, fun n hn => ?_⟩
    exact Nat.le_trans
      (Nat.mul_le_mul_left scale (refined_le_original n).1) (hth n hn)
  · intro scale hscale
    obtain ⟨th, hth⟩ := sparseExceptionRelativeTableOverhead_littleO scale hscale
    refine ⟨th, fun n hn => ?_⟩
    exact Nat.le_trans
      (Nat.mul_le_mul_left scale (refined_le_original n).2) (hth n hn)

/-! ## Executed: the refined budgets are ZERO at every reachable size -/

#eval (List.range 16).map (fun k =>
  let n := 2 ^ (k + 1)
  (n, refinedLongBudget n, refinedSparseBudget n,
    longSuperRelativeTableOverhead n, sparseExceptionRelativeTableOverhead n))

#print axioms long_le_refined
#print axioms sparse_le_refined
#print axioms refined_littleO

end SdkJ
