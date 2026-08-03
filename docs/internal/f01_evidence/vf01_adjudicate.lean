/-
Coordinator adjudication scan for EG-CP-F01.
EXPLORATORY: `#eval` only, no theorems claimed.  Pure Nat mirrors of
`zkd_f01_k_decision.lean`'s `longSpanOfSize` / `localStrideOfSize` /
`paddedLongBits` / `paddedSparseBits`, restated standalone so this file
needs no import beyond core Nat.
-/

def mwb (n : Nat) : Nat := Nat.log2 n + 1

def longSpanOfSize (n : Nat) : Nat :=
  mwb (2 * n) * mwb (2 * n) * mwb (2 * n) * (Nat.log2 (mwb (2 * n)) + 1)

def localStrideOfSize (n : Nat) : Nat :=
  max 1 (mwb (2 * n) / ((Nat.log2 (mwb (2 * n)) + 1) * (Nat.log2 (mwb (2 * n)) + 1)))

def paddedLongBits (n : Nat) : Nat :=
  1 * (2 * n / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1)) + 1

def paddedSparseBits (n : Nat) : Nat :=
  512 * (2 * n / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1)) + 512

def refinedLongBudget (n : Nat) : Nat :=
  if 2 * n < longSpanOfSize n then 0 else paddedLongBits n

def refinedSparseBudget (n : Nat) : Nat :=
  if localStrideOfSize n = 1 then 0 else paddedSparseBits n

/-- First `n` in `[0, hi)` at which the refined long budget is nonzero. -/
def firstNonzeroLong (hi : Nat) : Option Nat :=
  (List.range hi).find? (fun n => refinedLongBudget n != 0)

/-- Every flip of `refinedLongBudget = 0` in `[0, hi)`: is it ever re-entered? -/
def longZeroFlips (hi : Nat) : List (Nat × Bool) :=
  ((List.range hi).filter (fun n =>
      n == 0 || ((refinedLongBudget n == 0) != (refinedLongBudget (n - 1) == 0)))).map
    (fun n => (n, refinedLongBudget n == 0))

#eval firstNonzeroLong 20000
#eval longZeroFlips 300000
#eval ((List.range 30).map (fun k => (k, refinedLongBudget (2 ^ k) == 0)))

/-- (n, 2n, refinedLong, refinedSparse, percent of 2n taken by refined padding) -/
def row (n : Nat) : Nat × Nat × Nat × Nat × Nat :=
  (n, 2 * n, refinedLongBudget n, refinedSparseBudget n,
    100 * (refinedLongBudget n + refinedSparseBudget n) / (2 * n + 1))

#eval [row 0, row 1, row 2, row 512, row 4096, row 5487, row 5488, row 5489,
       row 8192, row 65536, row 1000000]
#eval [row (2 ^ 20), row (2 ^ 30), row (2 ^ 40), row (2 ^ 60)]

/-- Unrefined comparison, for the record. -/
#eval [(1024, paddedLongBits 1024, paddedSparseBits 1024, 2 * 1024),
       ((2:Nat) ^ 30, paddedLongBits (2 ^ 30), paddedSparseBits (2 ^ 30), 2 * 2 ^ 30)]

/-- Does the local stride ever leave 1 below 2^128? -/
#eval ((List.range 130).filter (fun k => localStrideOfSize (2 ^ k) != 1)).take 5
