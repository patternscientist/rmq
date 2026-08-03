import RMQ.Core.SuccinctFinal.RAM.ReviewerPhysical

namespace VfyCross
open RMQ RMQ.GenericSelect

def refinedLongBudget (m : Nat) : Nat :=
  if m <= superLongSpan m then 0 else longSuperRelativeTableOverhead m

def refinedSparseBudget (m : Nat) : Nat :=
  if localStride m = 1 then 0 else sparseExceptionRelativeTableOverhead m

/-- m is the BP bit length = 2n. -/
#eval (List.range 30).map (fun k =>
  let n := 2 ^ (k + 1)
  let m := 2 * n
  (k + 1, n, localStride m, decide (m <= superLongSpan m),
    refinedLongBudget m, refinedSparseBudget m))
end VfyCross
