# Union-Find Amortization Frontier Digest

Snapshot: 2026-06-28. Stable base is `main` at `c92c8af`. The Tarjan-level
potential statements in this note are branch-relative to the latest
`codex/union-find-tarjan-levels` worktree until that branch merges.

This note assumes no prior union-find background. Union-find maintains a
partition of elements. `find x` returns the representative of `x`'s set.
`union x y` merges two sets. A parent-pointer forest implements this by making
each node point upward toward a root representative. Path compression rewrites
the parent pointers seen during `find` so future finds are shorter.

## What Changed Conceptually

The stable union-find spoke already has a concrete parent-pointer forest,
union-by-rank invariants, executable root-mass accounting, full path
compression, and representation-level amortized backends.

The amortization ladder is now:

1. Trace-length credit: pay for exactly the nodes visited.
2. Rank-gap credit: pay successful finds by the rank gap to the root.
3. Log-rank credit: use `2 ^ rank <= mass` to bound root rank by
   `Nat.log2 forest.size + 1`.
4. Rank-bucket/rank-slack credit: prove compression drops a node-level slack
   potential enough to pay successful finds with constant credit, while union
   still uses a coarse size-log credit.
5. Branch-relative Tarjan-level scaffold: split a rank gap into cross-level
   work and residual within-level work.

The new branch-local conceptual move is the level/residual split. Cross-level
gaps are paid by `tarjanLevelPotential`; residual within-level slack remains
in the find credit. This is the shape of a Tarjan proof, but not the classical
bound yet.

## Plain English Story

The semantic boundary is `RMQ.UnionFind.State.SamePartition`: two concrete
forests may choose different representatives, but they are equivalent if they
induce the same partition on valid nodes. The forest refinement theorem
`RMQ.UnionFind.Forest.parentForestRefinement_profile` says executable
`ParentForest.findRoot?` agrees with abstract `State.find?`.

The stable compression theorem
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationBackend_profile`
checks that full compression follows the original parent chain, rewrites every
visited node to the returned root, and preserves the represented partition.

The stable rank-slack backend
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankSlackSizeUnionAmortizedBackend_profile`
pays successful full-compression find by a potential drop plus constant `2`.
Its union credit is still coarse:
`rankBucketPotential backend + 1`.

The branch-relative Tarjan-level scaffold adds these handles:

- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanLevelIter`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanRankLevel`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.nodeRootParentTarjanLevelGap`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.nodeRootParentTarjanResidualSlack`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanLevelPotential`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.traceRootParentRankSlack_le_tarjanLevelGap_add_residual`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanLevelPotential_fullCompressFindCosted_add_traceLevelGap_le_of_findRoot?`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_add_tarjanLevelPotential_le_tarjanLevelFindCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.unionCosted_cost_add_tarjanLevelPotential_le_tarjanLevelUnionCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionTarjanLevelAmortizedBackend_profile`.

In words: the proof defines levels of ranks by repeatedly taking logarithms.
For now the concrete level is fixed as
`tarjanRankLevel rank = tarjanLevelIter 2 rank`. A find trace may contain
edges that jump across these levels and edges that stay within a level. The
potential pays the cross-level jumps. The residual within-level part is still
charged explicitly.

## Live Assumptions

- Costs are modeled with `Costed`, not measured Lean runtime.
- The forest is list-backed and proof-friendly, not a mutable-array
  implementation.
- Rank, parent, and mass data are executable fields in the forest model.
  Invariants and potential-drop proofs are proof-only unless a later
  representation split counts them.
- Invalid `find` queries still retain a fuel fallback.
- `tarjanRankLevel` is currently a fixed two-iteration schedule, not an
  operation-sequence-dependent inverse-Ackermann phase.
- `tarjanLevelFindCredit` still contains
  `traceRootParentTarjanResidualSlack root trace + 2`.
- `tarjanLevelUnionCredit` is `tarjanLevelPotentialBound backend + 1`, a
  whole-forest credit, not a small uniform union credit.

## Skeptical Grad Student Questions

**Is this Tarjan's inverse-Ackermann theorem?**

No. It is a Tarjan-shaped potential interface. The proof separates cross-level
work from residual work, but it does not yet prove that the residual and union
credits are bounded by an inverse-Ackermann function over operation sequences.

**What did the scaffold buy?**

It moved from "pay by a coarse rank/bucket quantity" to "define levels and
prove compression drops a level potential." That is the structural ingredient
needed for Tarjan-style analysis.

**Where are the remaining large credits hiding?**

In `traceRootParentTarjanResidualSlack`, which is part of
`tarjanLevelFindCredit`, and in `tarjanLevelPotentialBound`, which defines
`tarjanLevelUnionCredit`. Those are explicit, not hidden; they are just not
yet the small classical credits.

**What should the next proof worker build?**

Generalize `tarjanRankLevel = tarjanLevelIter 2` to a phase schedule controlled
by operation count or rank universe, then prove residual find credit and union
credit bounds that assemble into an inverse-Ackermann-style amortized theorem.
