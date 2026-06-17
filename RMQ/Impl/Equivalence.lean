import RMQ.Core.Microtable
import RMQ.Impl.LinearScan
import RMQ.Impl.SparseTable
import RMQ.Impl.SparseTableMemoCost
import RMQ.Impl.HybridBlock
import RMQ.Impl.RecursiveHybrid
import RMQ.Impl.FischerHeun

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
The original overprovisioned sparse-table query and the cost-faithful memoized
log-row sparse-table query are extensionally equal.
-/
theorem sparseTable_query_eq_memoSparseTable_query
    (xs : List Int) (left right : Nat) :
    SparseTable.query xs left right = SparseTable.memoQuery xs left right :=
  (SparseTable.memoQuery_eq_query xs left right).symm

/--
The linear-scan and memoized sparse-table public queries are extensionally equal
by the verified sparse-table bridge.
-/
theorem linearScan_query_eq_memoSparseTable_query
    (xs : List Int) (left right : Nat) :
    LinearScan.query xs left right = SparseTable.memoQuery xs left right := by
  rw [linearScan_query_eq_sparseTable_query,
    sparseTable_query_eq_memoSparseTable_query]

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
The linear-scan and raw shape-microtable public queries are extensionally equal
by the generic backend contract.
-/
theorem linearScan_query_eq_microtableRaw_query
    (xs : List Int) (left right : Nat) :
    LinearScan.query xs left right =
      RMQBackend.queryBuilt (Cartesian.Microtable.rawBackend xs) left right := by
  simpa [RMQBackend.queryBuilt, LinearScan.backend, LinearScan.query]
    using RMQBackend.queryBuilt_eq (LinearScan.backend xs)
      (Cartesian.Microtable.rawBackend xs) left right

/--
The linear-scan and canonical Fischer-Heun public queries are extensionally
equal by the generic backend contract.
-/
theorem linearScan_query_eq_fischerHeun_query
    (xs : List Int) (left right : Nat) :
    LinearScan.query xs left right = FischerHeun.query xs left right := by
  simpa [RMQBackend.queryBuilt, LinearScan.backend, FischerHeun.backend,
    FischerHeun.backendWithBlockSize, FischerHeun.query]
    using RMQBackend.queryBuilt_eq (LinearScan.backend xs)
      (FischerHeun.backend xs) left right

/--
The linear-scan and all-input Fischer-Heun wrapper queries are extensionally
equal by the generic backend contract.
-/
theorem linearScan_query_eq_fischerHeun_allInputQuery
    (xs : List Int) (left right : Nat) :
    LinearScan.query xs left right = FischerHeun.allInputQuery xs left right := by
  simpa [RMQBackend.queryBuilt, LinearScan.backend,
    FischerHeun.allInputBackend]
    using RMQBackend.queryBuilt_eq (LinearScan.backend xs)
      (FischerHeun.allInputBackend xs) left right

/--
The canonical Fischer-Heun query and its all-input wrapper are extensionally
equal at the RMQ contract boundary.
-/
theorem fischerHeun_query_eq_allInputQuery
    (xs : List Int) (left right : Nat) :
    FischerHeun.query xs left right = FischerHeun.allInputQuery xs left right := by
  rw [(linearScan_query_eq_fischerHeun_query xs left right).symm,
    linearScan_query_eq_fischerHeun_allInputQuery]

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
The sparse-table and raw shape-microtable public queries are extensionally
equal by the generic backend contract.
-/
theorem sparseTable_query_eq_microtableRaw_query
    (xs : List Int) (left right : Nat) :
    SparseTable.query xs left right =
      RMQBackend.queryBuilt (Cartesian.Microtable.rawBackend xs) left right := by
  simpa [RMQBackend.queryBuilt, SparseTable.backend, SparseTable.query]
    using RMQBackend.queryBuilt_eq (SparseTable.backend xs)
      (Cartesian.Microtable.rawBackend xs) left right

/--
The sparse-table and canonical Fischer-Heun public queries are extensionally
equal by the generic backend contract.
-/
theorem sparseTable_query_eq_fischerHeun_query
    (xs : List Int) (left right : Nat) :
    SparseTable.query xs left right = FischerHeun.query xs left right := by
  simpa [RMQBackend.queryBuilt, SparseTable.backend, SparseTable.query,
    FischerHeun.backend, FischerHeun.backendWithBlockSize, FischerHeun.query]
    using RMQBackend.queryBuilt_eq (SparseTable.backend xs)
      (FischerHeun.backend xs) left right

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

/--
The self-recursive hybrid and canonical Fischer-Heun public queries are
extensionally equal by the generic backend contract.
-/
theorem recursiveHybrid_query_eq_fischerHeun_query
    (xs : List Int) (left right : Nat) :
    RecursiveHybrid.query xs left right = FischerHeun.query xs left right := by
  simpa [RMQBackend.queryBuilt, RecursiveHybrid.query,
    FischerHeun.backend, FischerHeun.backendWithBlockSize, FischerHeun.query]
    using RMQBackend.queryBuilt_eq (RecursiveHybrid.backend xs)
      (FischerHeun.backend xs) left right

theorem fischerHeun_query_eq_recursiveHybrid_query
    (xs : List Int) (left right : Nat) :
    FischerHeun.query xs left right = RecursiveHybrid.query xs left right :=
  (recursiveHybrid_query_eq_fischerHeun_query xs left right).symm

end RMQ
