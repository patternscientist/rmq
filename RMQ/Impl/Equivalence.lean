import RMQ.Impl.LinearScan
import RMQ.Impl.SparseTable
import RMQ.Impl.HybridBlock
import RMQ.Impl.RecursiveHybrid

/-!
# Backend equivalence theorems

These results compare implementations at the public RMQ contract boundary.
-/

namespace RMQ

/--
The linear-scan and sparse-table public queries are extensionally equal by the
generic backend contract.
-/
theorem linearScan_query_eq_sparseTable_query
    (xs : List Int) (left right : Nat) :
    LinearScan.query xs left right = SparseTable.query xs left right := by
  simpa [RMQBackend.queryBuilt, LinearScan.backend, SparseTable.backend,
    SparseTable.query]
    using RMQBackend.queryBuilt_eq (LinearScan.backend xs)
      (SparseTable.backend xs) left right

/--
The linear-scan and sparse-middle hybrid public queries are extensionally equal
by the generic backend contract.
-/
theorem linearScan_query_eq_hybridBlock_query
    (xs : List Int) (left right : Nat) :
    LinearScan.query xs left right = HybridBlock.query xs left right := by
  simpa [RMQBackend.queryBuilt, LinearScan.backend, HybridBlock.backend,
    HybridBlock.query]
    using RMQBackend.queryBuilt_eq (LinearScan.backend xs)
      (HybridBlock.backend xs) left right

/--
The linear-scan and self-recursive hybrid public queries are extensionally equal
by the generic backend contract.
-/
theorem linearScan_query_eq_recursiveHybrid_query
    (xs : List Int) (left right : Nat) :
    LinearScan.query xs left right = RecursiveHybrid.query xs left right := by
  simpa [RMQBackend.queryBuilt, LinearScan.backend, RecursiveHybrid.query]
    using RMQBackend.queryBuilt_eq (LinearScan.backend xs)
      (RecursiveHybrid.backend xs) left right

/--
The sparse-table and sparse-middle hybrid public queries are extensionally
equal by the generic backend contract.
-/
theorem sparseTable_query_eq_hybridBlock_query
    (xs : List Int) (left right : Nat) :
    SparseTable.query xs left right = HybridBlock.query xs left right := by
  simpa [RMQBackend.queryBuilt, SparseTable.backend, SparseTable.query,
    HybridBlock.backend, HybridBlock.query]
    using RMQBackend.queryBuilt_eq (SparseTable.backend xs)
      (HybridBlock.backend xs) left right

/--
The sparse-table and self-recursive hybrid public queries are extensionally
equal by the generic backend contract.
-/
theorem sparseTable_query_eq_recursiveHybrid_query
    (xs : List Int) (left right : Nat) :
    SparseTable.query xs left right = RecursiveHybrid.query xs left right := by
  simpa [RMQBackend.queryBuilt, SparseTable.backend, SparseTable.query,
    RecursiveHybrid.query]
    using RMQBackend.queryBuilt_eq (SparseTable.backend xs)
      (RecursiveHybrid.backend xs) left right

/--
The sparse-middle hybrid and self-recursive hybrid public queries are
extensionally equal by the generic backend contract.
-/
theorem hybridBlock_query_eq_recursiveHybrid_query
    (xs : List Int) (left right : Nat) :
    HybridBlock.query xs left right = RecursiveHybrid.query xs left right := by
  simpa [RMQBackend.queryBuilt, HybridBlock.backend, HybridBlock.query,
    RecursiveHybrid.query]
    using RMQBackend.queryBuilt_eq (HybridBlock.backend xs)
      (RecursiveHybrid.backend xs) left right

theorem recursiveHybrid_query_eq_hybridBlock_query
    (xs : List Int) (left right : Nat) :
    RecursiveHybrid.query xs left right = HybridBlock.query xs left right :=
  (hybridBlock_query_eq_recursiveHybrid_query xs left right).symm

end RMQ
