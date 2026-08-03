import RMQ.Core.SuccinctSelect.CloseSelect.BuiltRouting.SpanBudgets
import RMQ.Core.GenericSelect.RelativeTables

open RMQ
open RMQ.SuccinctSelect

/-! Adversarial check of the f02-scope padding recommendation.

The lane recommends padding the two content-dependent select regions up to
their existing `n`-only budgets so their lengths become `n`-derived and `K`
stays 1, arguing the space cost "is bounded by results that exist today"
(the two `LittleOLinear` proofs).  Both budgets are bit counts: the region
payloads are `List Bool` (`RMQ/Core/GenericSelect/SelectSource.lean:18`), and
the capstone counts `2 * n + overhead` bits
(`FlatPayload.lean:154-159`).  So the padded region size is directly
comparable with the `2 * n` data term.

Below: the two budgets, and their ratio to `2 * n`, at realistic sizes. -/

-- 1. The budgets are closed functions of `n` (no shape), unfolded:
--    sparse:  512 * (2n / (log2 (log2 (2n) + 1) + 1)) + 512
--    long:      1 * (2n / (log2 (log2 (2n) + 1) + 1)) + 1
example (n : Nat) :
    sparseExceptionRelativeTableOverhead n =
      512 * (2 * n / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1)) + 512 := rfl

example (n : Nat) :
    compactLongSuperRelativeTableOverhead n =
      1 * (2 * n / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1)) + 1 := rfl

-- 2. Small-size behavior, including n = 0 and n = 1.
#eval (List.range 4).map fun n =>
  (n, sparseExceptionRelativeTableOverhead n, compactLongSuperRelativeTableOverhead n)

-- 3. Budget vs the 2n data term at realistic sizes.
--    Tuple: (n, 2n, sparse budget, long budget, (sparse+long) / (2n)).
#eval [8192, 65536, 1000000, 10 ^ 9, 10 ^ 12, 10 ^ 18].map fun n =>
  let s := sparseExceptionRelativeTableOverhead n
  let l := compactLongSuperRelativeTableOverhead n
  (n, 2 * n, s, l, (s + l) / (2 * n))

-- 4. The divisor that drives the little-o.  For (sparse+long) to fall below
--    2n we need `log2 (log2 (2n) + 1) + 1 > 513`, i.e. log2 (2n) + 1 > 2^512.
#eval [8192, 1000000, 10 ^ 18, 2 ^ 64, 2 ^ 256].map fun n =>
  (Nat.log2 (Nat.log2 (2 * n) + 1) + 1)

-- 5. The two upper-bound theorems the padding relies on really are
--    unconditional in the shape (no regime, no positivity, no span side
--    condition).  Restated here with an explicit binder so the statement is
--    visible.
theorem av_sparse_budget_unconditional (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload.length <=
      sparseExceptionRelativeTableOverhead shape.size :=
  builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_overhead shape

theorem av_long_budget_unconditional (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length <=
      compactLongSuperRelativeTableOverhead shape.size :=
  compactLongSuperRelativeTable_payload_le_overhead shape

#print axioms av_sparse_budget_unconditional
#print axioms av_long_budget_unconditional
