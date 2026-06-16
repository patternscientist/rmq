import RMQ.Core.CostKernels

/-!
# Fischer-Heun microtable cost profile

This module packages the two exact finite facts that drive the Fischer-Heun
microtable story:

* raw shape lookup follows one decision path, so its cost is at most
  `blockSize + 1`;
* a block of size `blockSize` ranges over exactly `shapeCount blockSize`
  Cartesian signatures.

The usual `O(sqrt n)` preprocessing-table story is a later asymptotic corollary
after choosing `blockSize` around `(log n) / 2`; this module keeps the Mathlib-free
core at the exact finite-count level.
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

end FischerHeun

end RMQ
