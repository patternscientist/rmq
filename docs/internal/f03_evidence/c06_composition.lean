import RMQ.Core.SuccinctFinal.RAM.GeometryClosure

/-!
A10-F03-03 remediation probe.

The audit's finding: a shared *arbitrary whole store* is weaker than the frozen
model's "contents returned by prior probes", because sharing a total store does
not forbid dependence on addresses the execution never probes.

The composition partner already exists and predates the delta:
`RMQ.SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint`
(`RMQ/Core/SuccinctRMQClassic.lean:1298`), exported as the headline
`listIntSuccinctRMQQueryTraceResultWithStoreEqOfOrderedReadFootprint`
(`RMQ/Headlines/RMQ.lean:251`). Its docstring: agreement on the actual ordered
footprint determines "decoded result, cost, ordered trace, repeated reads, and
failed reads".

Chaining it with the delta's `queryTraceResultWithStore_size_only` should give
dependence on `(n, endpoints, replies at addresses actually probed)` -- the
row's model rather than a whole-store congruence.
-/

open RMQ

namespace C06Comp

/-- Two inputs of equal length, and two stores that agree only on the ordered
read footprint of the first, produce identical executions. -/
theorem queryTraceResultWithStore_length_and_footprint
    (xs ys : List Int) (storeA storeB : WordRAM.ReadStore) (l r : Nat)
    (hlen : xs.length = ys.length)
    (hagree : SuccinctClassic.storesAgreeOnOrderedReadFootprint xs storeA storeB l r) :
    SuccinctClassic.queryTraceResultWithStore xs storeA l r =
      SuccinctClassic.queryTraceResultWithStore ys storeB l r := by
  rw [SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint
        xs storeA storeB l r hagree]
  exact SuccinctFinal.GeometryClosure.queryTraceResultWithStore_size_only
    xs ys storeB l r hlen

/-- The footprint projection likewise. -/
theorem orderedReadFootprintWithStore_length_and_footprint
    (xs ys : List Int) (storeA storeB : WordRAM.ReadStore) (l r : Nat)
    (hlen : xs.length = ys.length)
    (hagree : SuccinctClassic.storesAgreeOnOrderedReadFootprint xs storeA storeB l r) :
    SuccinctClassic.orderedReadFootprintWithStore xs storeA l r =
      SuccinctClassic.orderedReadFootprintWithStore ys storeB l r := by
  unfold SuccinctClassic.orderedReadFootprintWithStore
  rw [queryTraceResultWithStore_length_and_footprint xs ys storeA storeB l r hlen hagree]

#print axioms queryTraceResultWithStore_length_and_footprint
#print axioms orderedReadFootprintWithStore_length_and_footprint

end C06Comp
