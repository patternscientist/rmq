# Union-Find Amortization Frontier Digest

Snapshot: 2026-06-28. This note digests the union-find spoke after the
rank-gap/log-rank amortization milestone, the first multilevel Tarjan-style
checkpoint, a clean-credit refinement, a phase-count checkpoint, and an
explicit level-index potential checkpoint. The checked code now has a reusable
level/residual potential interface, but does not yet prove an
inverse-Ackermann bound.

This note assumes no prior union-find background. Union-find maintains a
partition of elements. `find x` returns the representative of `x`'s set.
`union x y` merges two sets. A parent-pointer forest implements this by making
each node point upward toward a root representative. Path compression rewrites
the parent pointers seen during `find` so future finds are shorter.

## What Changed Conceptually

The stable union-find spoke already has a concrete parent-pointer forest,
union-by-rank invariants, executable root-mass accounting, full path
compression, and representation-level amortized backends.

The current amortization story has nine rungs:

1. Trace-length credit: pay for exactly the nodes visited by full compression.
2. Rank-gap credit: pay successful finds by the rank gap from the queried node
   to its root.
3. Log-rank credit: bound that rank gap by `Nat.log2 forest.size + 1` using
   the checked `2 ^ rank <= mass` invariant.
4. Rank-slack potential: full compression drops aggregate parent-to-root rank
   slack enough to pay successful finds with constant credit.
5. Tarjan-level potential: split each rank gap into a cross-level part and a
   residual within-level part; aggregate level potential pays cross-level
   jumps, and find credit pays only the residual plus constant `2`.
6. Tarjan-level clean credit: keep the level potential but remove the
   trace-dependent residual from the public successful-find credit, replacing
   it with a root-rank count bound; union is paid by a local level-potential
   delta instead of the whole level-potential bound.
7. Tarjan phase-count credit: add the residual rank-slack layer to the
   potential, then charge successful finds by the global iterated-log phase
   count plus constant `2`.
8. Tarjan level-index credit: replace that hidden full rank-slack layer with
   the explicit sum of cross-level potential plus raw within-level residual
   potential, and prove the combined drop pays trace rank slack.
9. Level-index obstruction: prove that when the level gap is a genuine sub-gap,
   defining residual as `rankSlack - levelGap` makes the additive level-index
   potential collapse back to ordinary rank slack.

This is a real conceptual shift: the cost argument no longer just says "the
trace is as long as the trace." It starts paying from rank and component-size
facts. But it is still not Tarjan. The current potential is too coarse and
does not yet encode the full operation-sequence-dependent phase schedule whose
credits collapse to inverse-Ackermann, but it now has the first checked
multilevel drop boundary.

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

The Tarjan-level and level-index scaffold adds these handles:

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
- Invariants such as `RootMassInvariant` and `RankPowerMassInvariant` are proof
  certificates unless a later representation split counts them as executable
  payload.
- Invalid `find` queries retain a fuel fallback. Successful finds can be paid
  by rank-gap/log-rank credit, constant rank-slack credit, or residual
  Tarjan-level credit depending on the checkpoint. The clean-credit
  Tarjan-level profile removes the explicit trace residual, but its successful
  find credit is still a root-rank count bound.
- `tarjanPhaseCountPotential` absorbs full rank slack plus the level potential.
  This gives a phase-count-shaped successful-find credit, but it is still
  powered by a coarse potential. The sharper `tarjanLevelIndexPotential`
  replaces that hidden full-rank-slack layer with explicit level plus residual
  accounting, but the residual is still raw within-level rank slack. The
  theorem
  `tarjanLevelIndexPotential_eq_rankSlackPotential_of_forall_gap_le` records
  the design obstruction: with a residual literally defined as
  `rankSlack - levelGap`, the additive potential is just rank slack whenever
  the level gap is a true sub-gap.
- `tarjanRankLevel` is currently the fixed phase `tarjanLevelIter 2`; the
  inverse-Ackermann theorem will need a phase schedule tied to operation counts
  or rank universe parameters.

## Theorem Anchors

```lean
#check RMQ.UnionFind.Forest.parentForestRefinement_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationBackend_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationAmortizedBackend_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankGapAmortizedBackend_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionLogRankAmortizedBackend_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankSlackAmortizedBackend_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankSlackSizeUnionAmortizedBackend_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionTarjanLevelAmortizedBackend_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionTarjanLevelCleanCreditAmortizedBackend_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionTarjanPhaseCountAmortizedBackend_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionTarjanLevelIndexAmortizedBackend_profile
```

The cost/drop bridges behind the amortized checkpoints include:

- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_le_rankGapFindCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.rankGapFindCredit_le_logRankFindCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_le_logRankFindCredit`.
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.rankSlackPotential_fullCompressFindCosted_add_traceRootParentRankSlack_le_of_findRoot?`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanLevelPotential_fullCompressFindCosted_add_traceLevelGap_le_of_findRoot?`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_add_tarjanLevelPotential_le_tarjanLevelFindCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.unionCosted_cost_add_tarjanLevelPotential_le_tarjanLevelUnionCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_add_tarjanLevelPotential_le_tarjanLevelRootRankFindCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.unionCosted_cost_add_tarjanLevelPotential_le_tarjanLevelDeltaUnionCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanLevelDeltaUnionCredit_le_tarjanLevelUnionCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_add_tarjanPhaseCountPotential_le_tarjanPhaseCountFindCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.unionCosted_cost_add_tarjanPhaseCountPotential_le_tarjanPhaseCountDeltaUnionCredit`.
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanResidualPotential_fullCompressFindCosted_add_traceResidualSlack_le_of_findRoot?`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanLevelIndexPotential_fullCompressFindCosted_add_traceRootParentRankSlack_le_of_findRoot?`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_add_tarjanLevelIndexPotential_le_tarjanLevelIndexFindCredit`.
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanLevelIndexPotential_eq_rankSlackPotential_of_forall_gap_le`.

## Skeptical Grad Student Questions

**Is this Tarjan's inverse-Ackermann theorem?**

No. It is a Tarjan-shaped potential interface. The proof separates cross-level
work from residual work, but it does not yet prove that the residual and union
credits are bounded by an inverse-Ackermann function over operation sequences.

**What did the scaffold buy?**

It means the code has enough rank/mass/log-rank structure to define checked
rank levels and split each parent-to-root rank gap. The level potential pays
for trace nodes that jump between levels; the residual credit records the
within-level work still not handled by a deeper phase schedule.
The clean-credit profile packages a trace-free public credit, but by falling
back to the returned root's rank it documents exactly where the alpha-style
phase schedule is still missing.
The phase-count profile removes that root-rank fallback from the public credit,
but pays for it by carrying the full rank-slack potential. The level-index
profile replaces that coarse hidden layer with an explicit residual-index
potential, so the next proof must compress that raw residual into a recursively
bucketed/Ackermann-indexed counter. The obstruction theorem now explains why:
the current residual-as-difference counter is algebraically rank slack again
under the natural sub-gap condition.

**Where are the remaining large credits hiding?**

In `traceRootParentTarjanResidualSlack`, which is part of
`tarjanLevelFindCredit`, and in `tarjanLevelPotentialBound`, which defines
`tarjanLevelUnionCredit`. Those are explicit, not hidden; they are just not
yet the small classical credits.

**What should the next proof worker actually build?**

Replace the raw residual component of `tarjanLevelIndexPotential` with a
recursively bucketed/Ackermann-indexed residual counter. The target should keep
the phase-count successful-find credit while making the residual index itself
alpha-shaped instead of carrying within-level rank slack verbatim, and should
avoid the collapse theorem for residual-as-difference accounting.

Generalize `tarjanRankLevel = tarjanLevelIter 2` to a phase schedule controlled
by operation count or rank universe, then prove residual find credit and union
credit bounds that assemble into an inverse-Ackermann-style amortized theorem.
