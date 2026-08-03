import RMQ.Core.SuccinctFinal.RAM.ReviewerPhysical

namespace VfyLaneJ
open RMQ RMQ.GenericSelect

def refinedLongBudget (n : Nat) : Nat :=
  if n <= superLongSpan n then 0 else longSuperRelativeTableOverhead n

def refinedSparseBudget (n : Nat) : Nat :=
  if localStride n = 1 then 0 else sparseExceptionRelativeTableOverhead n

#eval (List.range 16).map (fun k =>
  let n := 2 ^ (k + 1)
  (n, refinedLongBudget n, refinedSparseBudget n,
    longSuperRelativeTableOverhead n, sparseExceptionRelativeTableOverhead n))
end VfyLaneJ
