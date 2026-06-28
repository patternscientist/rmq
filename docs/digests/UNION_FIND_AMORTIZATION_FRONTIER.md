# Union-Find Amortization Frontier Digest

Snapshot: 2026-06-28. This note digests the union-find spoke after the
rank-gap/log-rank amortization milestone. It also records the bucket/slack
frontier precisely: the current checked code prepares for Tarjan-style rank
buckets, but does not yet prove an inverse-Ackermann bound.

## What Changed Conceptually

The union-find spoke has moved past a pure specification. It now has a concrete
parent-pointer forest representation, union-by-rank invariants, executable
root-mass accounting, full path compression, and representation-level
amortized backends.

The current amortization story has three rungs:

1. Trace-length credit: pay for exactly the nodes visited by full compression.
2. Rank-gap credit: pay successful finds by the rank gap from the queried node
   to its root.
3. Log-rank credit: bound that rank gap by `Nat.log2 forest.size + 1` using
   the checked `2 ^ rank <= mass` invariant.

This is a real conceptual shift: the cost argument no longer just says "the
trace is as long as the trace." It starts paying from rank and component-size
facts. But it is still not Tarjan. The current potential is too coarse and
does not yet encode rank buckets whose credits decrease under compression.

## Plain English Story

Union-find maintains a partition of elements. The reference state is
`RMQ.UnionFind.State`; `State.find?` returns a representative, and
`State.unionSpec` merges two components. Concrete forests are allowed to choose
different representatives as long as they induce the same partition, so the
semantic boundary is `RMQ.UnionFind.State.SamePartition`.

The concrete representation is `RMQ.UnionFind.Forest.ParentForest`. A valid
forest has in-bounds parent pointers and a root reachable from every valid
node. The theorem `RMQ.UnionFind.Forest.parentForestRefinement_profile` says
the executable root search `ParentForest.findRoot?` agrees with the abstract
`State.find?`.

Union-by-rank needs more than parent pointers. The forest carries rank and
mass facts. `RankPowerMassInvariant` proves the classical size floor
`2 ^ rank root <= mass root`. That gives logarithmic rank bounds:
`RankPowerMassInvariant.rank_le_log2_mass` and
`RankPowerMassInvariant.rank_le_log2_size`.

Full compression is checked as a concrete operation. It follows the original
parent chain, rewrites every node in the discovered trace to the returned
root, and preserves the represented partition. The key representation theorem
is
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationBackend_profile`.

## Live Assumptions

- Costs are modeled with `Costed`, not measured Lean runtime.
- The forest is list-backed and proof-friendly. It is not a mutable-array
  implementation.
- Invariants such as `RootMassInvariant` and `RankPowerMassInvariant` are proof
  certificates unless a later representation split counts them as executable
  payload.
- Invalid `find` queries retain a fuel fallback. Successful finds get the
  rank-gap or log-rank credit.
- The current potential `rankSizePotential` is size-preserving and coarse. It
  does not yet model Tarjan bucket credits that decrease with compression.

## Theorem Anchors

```lean
#check RMQ.UnionFind.Forest.parentForestRefinement_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationBackend_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationAmortizedBackend_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankGapAmortizedBackend_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionLogRankAmortizedBackend_profile
```

The cost bridges behind the last two are:

- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_le_rankGapFindCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.rankGapFindCredit_le_logRankFindCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_le_logRankFindCredit`.

## Skeptical Grad Student Questions

**Is this Tarjan's inverse-Ackermann theorem?**

No. The current theorem is a log-rank amortized checkpoint. It is stronger than
trace-length accounting, but it does not yet use Tarjan buckets or prove an
inverse-Ackermann amortized bound.

**What does "bucket/slack frontier" mean here?**

It means the code has enough rank/mass/log-rank structure to state the next
bucketed potential, and it has representation slack for pointer rewrites, but
the bucket potential itself is still future work. The comment in
`fullCompressionRankGapAmortizedBackend` explicitly says the potential does not
yet encode Tarjan's rank buckets.

**Why not call the proof done after log-rank credit?**

Because log-rank is still too large for the classical union-find theorem. The
Tarjan result needs a subtler accounting where path compression spends and
releases credits across rank buckets.

**What should the next proof worker actually build?**

A bucketed potential over `RMQ.UnionFind.RepresentationAmortizedBackend`, with
find credit that is smaller than global log-rank credit and a proof that path
compression decreases or preserves the right bucket credits.

