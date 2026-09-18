import RMQ.Core.WordRAM.Packed.AllocationLowerBound

namespace RMQ.SuccinctFinal.PackedWordRAM.S03Diagnostic

open Cartesian

-- Q is exactly the existing S03 replacement field type, with every guard and
-- quantifier retained. This diagnostic does not mutate any producer or olean.
theorem canonicalBudgetSibling :
    ∀ n B, UniformAllocationBudget n B →
      shapeCount n ≤ 2 ^ (2 * n + allocationRho n + 1) - 1 := by
  intro n B budget
  exact packedAllocationOptimality_holds.canonicalCount n

-- P is the literal frozen checkO09 expected proposition. Rejection here is a
-- proof-elaboration diagnostic; the root still must replay the real S03 field.
theorem checkO09 :
    ∀ n B, UniformAllocationBudget n B → shapeCount n ≤ 2 ^ (B + 1) - 1 :=
  by with_reducible exact canonicalBudgetSibling

end RMQ.SuccinctFinal.PackedWordRAM.S03Diagnostic
