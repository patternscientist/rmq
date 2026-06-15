import RMQ.Impl.HybridBlock
import RMQ.Impl.RecursiveHybrid

/-!
# Backend equivalence theorems

These results compare implementations at the public RMQ contract boundary.
-/

namespace RMQ

/--
The sparse-middle hybrid and self-recursive hybrid public queries are
extensionally equal. The proof uses only the shared leftmost-argmin contract:
valid queries return the unique leftmost minimum, and invalid queries return
`none`.
-/
theorem hybridBlock_query_eq_recursiveHybrid_query
    (xs : List Int) (left right : Nat) :
    HybridBlock.query xs left right = RecursiveHybrid.query xs left right := by
  by_cases hValid : ValidRange xs left right
  · rcases HybridBlock.query_valid_exact xs left right hValid with
      ⟨idx, hHybrid, harg⟩
    have hRecursive : RecursiveHybrid.query xs left right = some idx :=
      RecursiveHybrid.query_complete harg
    rw [hHybrid, hRecursive]
  · have hHybrid : HybridBlock.query xs left right = none :=
      HybridBlock.invalid_none (xs := xs) (left := left) (right := right) hValid
    have hRecursive : RecursiveHybrid.query xs left right = none :=
      RecursiveHybrid.invalid_none (xs := xs) (left := left) (right := right)
        hValid
    rw [hHybrid, hRecursive]

theorem recursiveHybrid_query_eq_hybridBlock_query
    (xs : List Int) (left right : Nat) :
    RecursiveHybrid.query xs left right = HybridBlock.query xs left right :=
  (hybridBlock_query_eq_recursiveHybrid_query xs left right).symm

end RMQ
