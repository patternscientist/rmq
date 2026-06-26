# Union-Find Frontier

Snapshot: 2026-06-26. This note records the first non-succinct data-structure
spoke.

## Import

Use the standalone import root:

```lean
import RMQUnionFind
```

Verification:

```powershell
lake build RMQUnionFind
lake env lean scripts/union_find_axiom_check.lean
```

## Public Surface

The initial surface is a specification and amortized-accounting layer:

```lean
RMQ.Amortized.Bound
RMQ.Amortized.compose
RMQ.UnionFind.State
RMQ.UnionFind.Backend
RMQ.UnionFind.AmortizedBackend
RMQ.UnionFind.referenceBackend_profile
RMQ.UnionFind.referenceAmortizedBackend_profile
```

`UnionFind.State` represents a finite partition by a representative function
over indices `< size`. `State.find?` is the exact reference representative
query, `State.unionSpec` is the exact reference merge operation, and
`State.Same` is the induced equivalence relation on valid indices.

`Backend` is shaped for future path-compression implementations: `find` returns
both an updated state and the representative answer, and must preserve the
represented partition. `AmortizedBackend` adds potential-method obligations for
`find` and `union`.

## What Is Not Claimed Yet

This is not yet Tarjan union-find, inverse-Ackermann analysis, mutable arrays,
or a path-compression/rank implementation. The current checked backend is a
constant-cost reference backend over the abstract partition state, included so
the exactness and amortized-accounting interfaces are non-vacuous.

## Next Theorem Targets

1. Add an array/list forest representation with parent pointers and a
   well-founded root predicate.
2. Prove that forest representatives refine `UnionFind.State`.
3. Implement union-by-rank without path compression and prove a logarithmic
   height/rank invariant.
4. Add path compression as a `find` that returns an updated state preserving
   `State.Same`.
5. Replace the zero-potential reference profile with the real potential needed
   for the classical amortized bound.
