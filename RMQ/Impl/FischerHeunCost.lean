import RMQ.Core.CostKernels

/-!
# Fischer-Heun microtable cost profile

This module packages the two exact finite facts that drive the Fischer-Heun
microtable story:

* raw shape lookup follows one decision path, so its cost is at most
  `blockSize + 1`;
* a block of size `blockSize` ranges over exactly `shapeCount blockSize`
  Cartesian signatures;
* the Catalan envelope `shapeCount b <= 4^b` turns the exact count into a
  square-root table-budget corollary when `4*b <= log2 n`.

The corollary is stated without introducing a separate square-root function:
`rawShapeTableCount b * rawShapeTableCount b <= n`.
-/

namespace RMQ

namespace FischerHeun

/-- Unit-cost bound for one raw local microtable lookup. -/
def rawLookupCostBound (blockSize : Nat) : Nat :=
  blockSize + 1

/-- Number of distinct shape-indexed local tables for this block size. -/
def rawShapeTableCount (blockSize : Nat) : Nat :=
  (Cartesian.shapeUniverse blockSize).length

/-- Number of local half-open query slots if each shape table is materialized. -/
def localQuerySlotBudget (blockSize : Nat) : Nat :=
  blockSize * (blockSize + 1) / 2

/-- Total slots in the exact shape-indexed microtable universe. -/
def rawMicrotableSlotBudget (blockSize : Nat) : Nat :=
  rawShapeTableCount blockSize * localQuerySlotBudget blockSize

/-- Standard Catalan-envelope target used by the Fischer-Heun table-count proof. -/
def shapeCountEnvelope (blockSize : Nat) : Nat :=
  4 ^ blockSize

theorem rawShapeTableCount_eq_shapeCount (blockSize : Nat) :
    rawShapeTableCount blockSize = Cartesian.shapeCount blockSize := by
  simp [rawShapeTableCount, Cartesian.shapeUniverse_length]

theorem rawMicrotableSlotBudget_eq_shapeCount_mul
    (blockSize : Nat) :
    rawMicrotableSlotBudget blockSize =
      Cartesian.shapeCount blockSize * localQuerySlotBudget blockSize := by
  simp [rawMicrotableSlotBudget, rawShapeTableCount_eq_shapeCount]

theorem rawLookupCosted_cost_le_bound
    (xs : List Int) (start blockSize left right : Nat) :
    (Cartesian.rawMicrotableLookupCosted xs start blockSize left right).cost <=
      rawLookupCostBound blockSize := by
  simpa [rawLookupCostBound] using
    Cartesian.rawMicrotableLookupCosted_cost_le
      xs start blockSize left right

/--
Combined cost/count certificate for the raw shape microtable profile.

This is the exact finite form of the Fischer-Heun microtable premise: lookup is
linear in block size, and the number of shape tables is `shapeCount blockSize`.
-/
theorem rawMicrotable_cost_count_profile
    (xs : List Int) (start blockSize left right : Nat) :
    (Cartesian.rawMicrotableLookupCosted xs start blockSize left right).cost <=
        rawLookupCostBound blockSize /\
      rawShapeTableCount blockSize = Cartesian.shapeCount blockSize := by
  exact ⟨rawLookupCosted_cost_le_bound xs start blockSize left right,
    rawShapeTableCount_eq_shapeCount blockSize⟩

theorem rawShapeTableCount_le_envelope
    (blockSize : Nat)
    (hcat : Cartesian.shapeCount blockSize <= shapeCountEnvelope blockSize) :
    rawShapeTableCount blockSize <= shapeCountEnvelope blockSize := by
  simpa [rawShapeTableCount_eq_shapeCount] using hcat

theorem rawShapeTableCount_le_shapeCountEnvelope (blockSize : Nat) :
    rawShapeTableCount blockSize <= shapeCountEnvelope blockSize := by
  exact rawShapeTableCount_le_envelope blockSize
    (by
      simpa [shapeCountEnvelope] using
        Cartesian.shapeCount_le_four_pow blockSize)

/--
Squared form of the eventual `O(sqrt n)` table-count corollary.

Once the Catalan envelope `shapeCount b <= 4^b` and the block-size choice
`(4^b)^2 <= n` are supplied, the number of shape tables fits a square-root
budget, stated without introducing a separate square-root function.
-/
theorem rawShapeTableCount_square_le_of_envelope_square
    {blockSize n : Nat}
    (hcat : Cartesian.shapeCount blockSize <= shapeCountEnvelope blockSize)
    (hbudget : shapeCountEnvelope blockSize * shapeCountEnvelope blockSize <= n) :
    rawShapeTableCount blockSize * rawShapeTableCount blockSize <= n := by
  have htable := rawShapeTableCount_le_envelope blockSize hcat
  exact Nat.le_trans (Nat.mul_le_mul htable htable) hbudget

/--
Fischer-Heun square-root table-count corollary, stated without introducing a
separate square-root function: if the block-size choice makes the Catalan
envelope square fit under `n`, then the exact raw shape-table count does too.
-/
theorem rawShapeTableCount_square_le_of_envelope_budget
    {blockSize n : Nat}
    (hbudget :
      shapeCountEnvelope blockSize * shapeCountEnvelope blockSize <= n) :
    rawShapeTableCount blockSize * rawShapeTableCount blockSize <= n := by
  exact rawShapeTableCount_square_le_of_envelope_square
    (blockSize := blockSize) (n := n)
    (by
      simpa [shapeCountEnvelope] using
        Cartesian.shapeCount_le_four_pow blockSize)
    hbudget

theorem shapeCountEnvelope_eq_two_pow_two_mul (blockSize : Nat) :
    shapeCountEnvelope blockSize = 2 ^ (2 * blockSize) := by
  simp [shapeCountEnvelope]
  calc
    4 ^ blockSize = (2 ^ 2) ^ blockSize := by
      simp
    _ = 2 ^ (2 * blockSize) := by
      rw [← Nat.pow_mul]

theorem shapeCountEnvelope_square_eq_two_pow_four_mul
    (blockSize : Nat) :
    shapeCountEnvelope blockSize * shapeCountEnvelope blockSize =
      2 ^ (4 * blockSize) := by
  rw [shapeCountEnvelope_eq_two_pow_two_mul, ← Nat.pow_add]
  congr
  omega

theorem shapeCountEnvelope_square_le_of_four_mul_le_log2
    {blockSize n : Nat}
    (hn : 0 < n) (hlog : 4 * blockSize <= Nat.log2 n) :
    shapeCountEnvelope blockSize * shapeCountEnvelope blockSize <= n := by
  rw [shapeCountEnvelope_square_eq_two_pow_four_mul]
  have hmono : 2 ^ (4 * blockSize) <= 2 ^ Nat.log2 n := by
    exact Nat.pow_le_pow_right (by omega) hlog
  have hself : 2 ^ Nat.log2 n <= n := Nat.log2_self_le (by omega)
  exact Nat.le_trans hmono hself

/--
Base-2-log version of the square-root table-count corollary. Since
`shapeCount b <= 4^b`, the squared budget is discharged by
`4*b <= log2 n`.
-/
theorem rawShapeTableCount_square_le_of_four_mul_le_log2
    {blockSize n : Nat}
    (hn : 0 < n) (hlog : 4 * blockSize <= Nat.log2 n) :
    rawShapeTableCount blockSize * rawShapeTableCount blockSize <= n := by
  exact rawShapeTableCount_square_le_of_envelope_budget
    (shapeCountEnvelope_square_le_of_four_mul_le_log2
      (blockSize := blockSize) (n := n) hn hlog)

end FischerHeun

end RMQ
