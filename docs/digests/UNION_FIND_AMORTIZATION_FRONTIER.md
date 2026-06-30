# Union-Find Amortization Frontier Digest

Snapshot: 2026-06-28. This note digests the union-find spoke after the
rank-gap/log-rank amortization milestone, the first multilevel Tarjan-style
checkpoint, a clean-credit refinement, a phase-count checkpoint, and an
explicit level-index potential checkpoint. The checked code now has a reusable
level/residual potential interface, but does not yet prove an
inverse-Ackermann bound.

## What Changed Conceptually

The union-find spoke has moved past a pure specification. It now has a concrete
parent-pointer forest representation, union-by-rank invariants, executable
root-mass accounting, full path compression, and representation-level
amortized backends.

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
- The architecture pass in `UNION_FIND_TARJAN_ARCHITECTURE.md` now makes the
  next boundary sequence-level. The first part has landed: `UFOp`,
  `State.runOpsSpec`, `RepresentationBackend.runOpsCosted`,
  `RepresentationBackend.runOpsCosted_refinement_profile`, and
  `RepresentationAmortizedBackend.runOpsCosted_amortized` provide the mixed
  operation runner and telescope theorem. Trace-event extraction has landed in
  `TarjanEvents.lean`, including a root-edge-aware strict classifier. The
  root-link/public-union caveat is now split explicitly by `chargedUnionCosted`,
  which charges two full-compression finds before the final rank-guided link.
  The event-record follow-up now carries old-parent/root rank snapshots for
  strict residual events, proves every record has strict rank progress, ties
  full-find records to the concrete parent rewrite, and exposes rank
  monotonicity across charged operation runs.
  A Mathlib-free Ackermann schedule and a sequence theorem bounding strict
  same-level residual events still need to land before the residual is consumed
  in an alpha-style profile.
- Delta credits are explicitly marked as scaffolding by the checked shared
  lemmas `RMQ.Amortized.deltaCredit` and
  `RMQ.Amortized.costed_deltaCredit`.

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
#check RMQ.UnionFind.RepresentationBackend.runOpsCosted_refinement_profile
#check RMQ.UnionFind.RepresentationAmortizedBackend.runOpsCosted_amortized
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runFullCompressionOpsCosted_refinement_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runFullCompressionTarjanLevelIndexAmortized_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.chargedUnionCosted_refinement_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.chargedUnionCosted_rank_le
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionOpsCosted_refinement_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionOpsCosted_rank_le
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionTarjanLevelIndexAmortized_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionEventCost_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionScheduledEventCost_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionStrictScheduledEventCost_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionFixedUniverse_profile
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionCost_le_strictScheduledResiduals_add_five_mul_length_of_valid
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindScheduleRootEdgeCount_le_two_of_findRoot?
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindScheduleStrictResidualCount_le_traceRootParentRankSlack_of_findRoot?
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_strictResidual_parent_rank_progress_of_trace_mem
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindScheduleStrictResidualNodes_length
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_strictResidual_parent_rank_progress_of_residual_node_mem
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionScheduleStrictResidualNodes_length
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindScheduleStrictResidualEvents_length
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindScheduleStrictResidualEvents_rankProgress
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindScheduleStrictResidualEvents_parent?_eq_root_of_mem
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindScheduleStrictResidualEvents_rootRank_eq_after_rank_of_mem
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionScheduleStrictResidualEvents_length
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionScheduleStrictResidualEvents_rankProgress
#check RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindStrictIteratedLogScheduleCrossCount_le_traceLevelGap_of_findRoot?
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
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionStrictScheduledEventCost_profile`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionCost_le_strictScheduledResiduals_add_five_mul_length_of_valid`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindScheduleRootEdgeCount_le_two_of_findRoot?`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindScheduleStrictResidualCount_le_traceRootParentRankSlack_of_findRoot?`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_strictResidual_parent_rank_progress_of_trace_mem`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindScheduleStrictResidualNodes_length`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_strictResidual_parent_rank_progress_of_residual_node_mem`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.runChargedFullCompressionScheduleStrictResidualNodes_length`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindStrictIteratedLogScheduleCrossCount_le_traceLevelGap_of_findRoot?`.

## Skeptical Grad Student Questions

**Is this Tarjan's inverse-Ackermann theorem?**

No. The current strongest theorem is a charged sequence/event checkpoint with a
root-edge-aware strict classifier. It proves that valid-node run cost reduces
to strict cross-level plus strict same-level residual events, with root-edge
and link work absorbed into linear overhead. It does not yet prove the
Ackermann/alpha bound on those strict residual events.

**What does "bucket/slack frontier" mean here?**

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

**Why not call the proof done after log-rank credit?**

Because log-rank is still too large for the classical union-find theorem. The
Tarjan result needs a subtler accounting where path compression spends and
releases credits across rank buckets.

**What should the next proof worker actually build?**

Replace the raw residual component of `tarjanLevelIndexPotential` with a
recursively bucketed/Ackermann-indexed residual counter, but do it over the
root-edge-aware mixed-operation sequence/event interface rather than as another
isolated one-step backend wrapper. The immediate consumer is
`runChargedFullCompressionCost_le_strictScheduledResiduals_add_five_mul_length_of_valid`:
bound the event-node list tracked by
`runChargedFullCompressionScheduleStrictResidualNodes_length` by an alpha-shaped
operation-sequence budget while avoiding the collapse theorem for
residual-as-difference accounting.
