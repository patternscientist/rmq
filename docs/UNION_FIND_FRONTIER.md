# Union-Find Frontier

Snapshot: 2026-06-27. This note records the first non-succinct data-structure
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

The current surface is a specification and amortized-accounting layer plus the
first concrete parent-pointer forest refinement checkpoint:

```lean
RMQ.Amortized.Bound
RMQ.Amortized.compose
RMQ.UnionFind.State
RMQ.UnionFind.Backend
RMQ.UnionFind.RepresentationBackend
RMQ.UnionFind.RepresentationAmortizedBackend
RMQ.UnionFind.AmortizedBackend
RMQ.UnionFind.State.SamePartition
RMQ.UnionFind.State.unionSpec_samePartition_comm
RMQ.UnionFind.State.unionSpecMany
RMQ.UnionFind.State.samePartition_unionSpecMany
RMQ.UnionFind.referenceBackend_profile
RMQ.UnionFind.referenceAmortizedBackend_profile
RMQ.UnionFind.Forest.ParentForest
RMQ.UnionFind.Forest.ParentForest.Invariant
RMQ.UnionFind.Forest.ParentForest.LinkableInvariant
RMQ.UnionFind.Forest.ParentForest.RankInvariant
RMQ.UnionFind.Forest.ParentForest.RankSizeInvariant
RMQ.UnionFind.Forest.ParentForest.RankComponentInvariant
RMQ.UnionFind.Forest.ParentForest.RootMassInvariant
RMQ.UnionFind.Forest.ParentForest.RankPowerMassInvariant
RMQ.UnionFind.Forest.ParentForest.rootMassSum_one_eq_length
RMQ.UnionFind.Forest.ParentForest.nodup_length_le_of_forall_lt
RMQ.UnionFind.Forest.ParentForest.rootMassAfterUnionByRank
RMQ.UnionFind.Forest.ParentForest.findRoot?
RMQ.UnionFind.Forest.ParentForest.toState
RMQ.UnionFind.Forest.ParentForest.toState_find?_eq_findRoot?
RMQ.UnionFind.Forest.parentForestRefinement_profile
RMQ.UnionFind.Forest.ParentForest.identity
RMQ.UnionFind.Forest.ParentForest.identity_invariant
RMQ.UnionFind.Forest.ParentForest.identity_linkable
RMQ.UnionFind.Forest.ParentForest.identity_rankInvariant
RMQ.UnionFind.Forest.ParentForest.identity_rankSizeInvariant
RMQ.UnionFind.Forest.ParentForest.identity_rankComponentInvariant
RMQ.UnionFind.Forest.ParentForest.identity_rootMassInvariant
RMQ.UnionFind.Forest.ParentForest.identity_profile
RMQ.UnionFind.Forest.ParentForest.union
RMQ.UnionFind.Forest.ParentForest.union_invariant
RMQ.UnionFind.Forest.ParentForest.union_profile
RMQ.UnionFind.Forest.ParentForest.rootLink
RMQ.UnionFind.Forest.ParentForest.rootLink_invariant
RMQ.UnionFind.Forest.ParentForest.rootLink_refinement_profile
RMQ.UnionFind.Forest.ParentForest.rootLink_rank_lt_refinement_profile
RMQ.UnionFind.Forest.ParentForest.rootLink_rank_eq_bump_refinement_profile
RMQ.UnionFind.Forest.ParentForest.rankedRootLink
RMQ.UnionFind.Forest.ParentForest.rankAfterRootLinkByRank
RMQ.UnionFind.Forest.ParentForest.rankedRootLink_refinement_profile
RMQ.UnionFind.Forest.ParentForest.rankedRootLink_rankSizeInvariant_profile
RMQ.UnionFind.Forest.ParentForest.unionByRank
RMQ.UnionFind.Forest.ParentForest.rankAfterUnionByRank
RMQ.UnionFind.Forest.ParentForest.unionByRank_refinement_profile
RMQ.UnionFind.Forest.ParentForest.unionByRank_rankSizeInvariant_profile
RMQ.UnionFind.Forest.ParentForest.RootMassInvariant.toRankSizeInvariant
RMQ.UnionFind.Forest.ParentForest.RootMassInvariant.toRankComponentInvariant
RMQ.UnionFind.Forest.ParentForest.RootMassInvariant.root_mass_le_size
RMQ.UnionFind.Forest.ParentForest.rankedRootLink_rootMassInvariant_profile
RMQ.UnionFind.Forest.ParentForest.unionByRank_rootMassInvariant_profile
RMQ.UnionFind.Forest.ParentForest.RankPowerMassInvariant.rank_power_le_size
RMQ.UnionFind.Forest.ParentForest.RankPowerMassInvariant.rank_le_log2_mass
RMQ.UnionFind.Forest.ParentForest.RankPowerMassInvariant.rank_le_log2_size
RMQ.UnionFind.Forest.ParentForest.identity_rankPowerMassInvariant
RMQ.UnionFind.Forest.ParentForest.rankedRootLink_rankPowerMassInvariant_profile
RMQ.UnionFind.Forest.ParentForest.unionByRank_rankPowerMassInvariant_profile
RMQ.UnionFind.Forest.ParentForest.findRoot?_rank_lt_of_ne
RMQ.UnionFind.Forest.ParentForest.compressNode
RMQ.UnionFind.Forest.ParentForest.compressNode_rankPowerMassInvariant
RMQ.UnionFind.Forest.ParentForest.compressNode_rootMassInvariant_refinement_profile
RMQ.UnionFind.Forest.ParentForest.rootLink_rankComponentInvariant_equal_bump_boundary_obstruction
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedForest
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedForest.findCosted
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedForest.unionCosted
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedForest.profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedForest.unionCosted_rankSizeInvariant_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.findCosted
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.unionCosted
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.identity
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.identity_rootMassInvariant
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.identity_rankPowerMassInvariant
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.identity_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.unionManyCosted
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.unionManyCosted_cost
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.unionManyCosted_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.unionManyCosted_rankPowerMass_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.identity_unionManyCosted_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.identity_unionManyCosted_rankPowerMass_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.unionManyCosted_samePartition_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.unionManyCosted_refinement_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.identity_unionManyCosted_refinement_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.unionCosted_rootMassInvariant_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest.unionCosted_rankPowerMassInvariant_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.abstractState
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.identity
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.findCosted
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.compressFindCosted
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.compressPathFindFuelCosted
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.compressPathFindFuelTrace
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindTrace
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.unionCosted
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.unionManyCosted
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.findCosted_refinement_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.compressFindCosted_parent?_eq_root_of_findRoot?
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.compressFindCosted_parent?_eq_old_of_ne
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.compressFindCosted_findRoot?_eq
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.compressFindCosted_refinement_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_le
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindTrace_length_le
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_eq_trace_length
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_findRoot?_eq
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_parent?_eq_root_of_findRoot?
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_trace_parent?_eq_root_of_findRoot?
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.rank_le_root_rank_of_findRoot?
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindTrace_length_le_rank_gap_of_findRoot?
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.findRoot?_rank_lt_rootMass
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.findRoot?_root_rank_le_log2_mass
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.findRoot?_root_rank_le_log2_size
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindTrace_length_le_rootMass_of_findRoot?
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindTrace_length_le_log2_size_of_findRoot?
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_refinement_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.unionCosted_refinement_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.unionManyCosted_refinement_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.identity_unionManyCosted_refinement_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationBackend
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationBackend_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionFindCredit
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.unionByRankCredit
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationAmortizedBackend
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationAmortizedBackend_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.rankGapFindCredit
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.logRankFindCredit
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.rankSizePotential
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_le_rankGapFindCredit
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.rankGapFindCredit_le_logRankFindCredit
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_le_logRankFindCredit
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.rankSizePotential_fullCompressFindCosted_eq
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.rankSizePotential_unionCosted_eq
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankGapAmortizedBackend
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankGapAmortizedBackend_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionLogRankAmortizedBackend
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionLogRankAmortizedBackend_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.profile
```

`UnionFind.State` represents a finite partition by a representative function
over indices `< size`. `State.find?` is the exact reference representative
query, `State.unionSpec` is the exact reference merge operation, and
`State.Same` is the induced equivalence relation on valid indices.
`State.SamePartition` is the representative-insensitive partition boundary:
two states can choose different concrete representatives while inducing the
same valid-node equivalence relation. `unionSpec_samePartition_comm` proves the
two abstract union orientations are equivalent at this boundary.
`State.unionSpecMany` folds a finite list of abstract union requests, and
`samePartition_unionSpecMany` proves that this fold respects the
representative-insensitive boundary.

`Backend` is shaped for implementations whose executable state is already the
abstract `State`: `find` returns both an updated state and the representative
answer, and must preserve the represented partition. `RepresentationBackend`
is the cleaner boundary for concrete representation states carrying parent
pointers, ranks, masses, or potentials; it exposes an `abstractState` adapter
and states find/union refinement through `State.SamePartition`.
`RepresentationAmortizedBackend` adds potential-method obligations to that
representation boundary with credits that may depend on the current
representation state and operation arguments. `AmortizedBackend` remains the
constant-credit potential surface for backends already expressed over
`UnionFind.State`.

`Forest.ParentForest` is a finite list-backed parent-pointer representation.
Roots are self-parent pointers, and `ParentForest.findRoot?` follows parent
pointers with an explicit `size + 1` fuel budget. `ParentForest.Invariant`
packages the parent-in-bounds and bounded-depth/root-totality facts needed to
adapt a forest to `UnionFind.State`; `parentForestRefinement_profile` proves the
adapted abstract `State.find?` agrees with executable forest root search.
`ParentForest.identity n` is the first concrete non-vacuous forest instance:
all nodes are singleton roots, `identity_invariant` proves the invariant,
`identity_rootMassInvariant` proves the singleton root-mass accounting instance,
and `identity_profile` packages its exact `findRoot?`/`State.find?` behavior
with the rank and mass base invariants.
`ParentForest.union` is the first concrete union refinement checkpoint: it
rebuilds a direct-parent forest from `(forest.toState h).unionSpec x y`, proves
the resulting forest satisfies `ParentForest.Invariant`, and proves its
`findRoot?`/adapted `State.find?` answers refine the abstract `State.unionSpec`.
`ParentForest.LinkableInvariant` strengthens `Invariant` with a strict
root-search witness, enough slack to reason about one root pointer changing.
`ParentForest.rootLink fromRoot toRoot` changes only the `fromRoot` parent cell;
`rootLink_refinement_profile` proves that, for distinct endpoint roots, this
one-pointer link preserves `Invariant` and refines `State.unionSpec`.
`ParentForest.RankInvariant` is the first proof-only rank certificate: every
non-root parent edge strictly increases rank, and valid ranks are bounded by
the forest size. `rankInvariant_linkable` derives `LinkableInvariant` from that
rank discipline. The rank-guided root-link profiles prove that a lower-rank
root can be linked below a higher-rank root while preserving
`LinkableInvariant`; the equal-rank case is also covered by bumping the
surviving root's proof rank. `ParentForest.RankSizeInvariant` is the first
theorem-shaped component-size/rank-size checkpoint: two distinct equal-rank
roots must leave enough finite-node budget to bump one root's rank. This
automatically discharges the equal-rank premise in the public
`rankedRootLink_refinement_profile` and `unionByRank_refinement_profile`.
`ParentForest.RankComponentInvariant` adds the next local component-cardinality
checkpoint: two roots of rank `k` plus a distinct root already at rank `k+1`
force enough room for the bumped rank `k+1` to coexist with that third root.
`rankedRootLink_rankSizeInvariant_profile` and
`unionByRank_rankSizeInvariant_profile` consume this accounting to preserve
`RankSizeInvariant` across the concrete rank-guided link/union step.
`rootLink_rankComponentInvariant_equal_bump_boundary_obstruction` records the
boundary case showing this three-root checkpoint is not self-preserving: after
an equal-rank bump, the bumped root can pair with an old next-rank root against
an old top-rank root exactly at the finite-size boundary. A stronger executable
component-size/counting invariant is needed for repeated preservation.
`ParentForest.RootMassInvariant` is that next accounting layer: it carries an
executable root-mass map and a duplicate-free finite-list budget theorem over
root lists. The reusable helper `nodup_length_le_of_forall_lt` proves that a
duplicate-free list of naturals bounded by `n` has length at most `n`, and
`rootMassSum_one_eq_length` computes singleton root mass. Together they give
`identity_rootMassInvariant`. `RootMassInvariant.toRankSizeInvariant` and
`RootMassInvariant.toRankComponentInvariant` recover the older proof-only
rank-size checkpoints from mass accounting, and
`rankedRootLink_rootMassInvariant_profile` /
`unionByRank_rootMassInvariant_profile` prove the executable rank and mass
updates are preserved across the no-compression union-by-rank step.
`ParentForest.RankPowerMassInvariant` strengthens this with the classical
union-by-rank component-size lower bound `2 ^ rank root <= mass root` for every
valid root. `identity_rankPowerMassInvariant`,
`rankedRootLink_rankPowerMassInvariant_profile`, and
`unionByRank_rankPowerMassInvariant_profile` prove the singleton base and
preservation across concrete rank-guided links/unions; the equal-rank bump case
is discharged by the mass-addition identity for the two old rank-`k` roots. The
logarithmic bridge is now explicit:
`RootMassInvariant.root_mass_le_size`,
`RankPowerMassInvariant.rank_power_le_size`,
`RankPowerMassInvariant.rank_le_log2_mass`, and
`RankPowerMassInvariant.rank_le_log2_size` turn component-size accounting into
root-rank bounds. Compression preserves the stronger invariant via
`compressNode_rankPowerMassInvariant`, so the representation-backed state now
carries the rank-power certificate internally rather than receiving it as a
separate proof-side premise.
`rankedRootLink` chooses the rank-compatible root orientation, and
`unionByRank` wraps the two endpoint root searches around that choice. Their
refinement profiles preserve `RankInvariant`, produce a `LinkableInvariant`
witness, and refine the abstract union through `State.SamePartition` rather
than fixed representative equality. `NoCompressionRankedForest` packages the
forest/rank pair with costed no-compression `find` and `union` operations;
`unionCosted_rankSizeInvariant_profile` connects the modeled union step back to
the rank-size preservation theorem. `NoCompressionRankedMassForest` additionally
threads the executable root-mass map through the same costed surface;
`unionCosted_rootMassInvariant_profile` is the repeatable backend-style
checkpoint for carrying the stronger accounting through successive unions.
`NoCompressionRankedMassForest.identity` packages the singleton forest as a
concrete mass-backed executable state, and `unionManyCosted` runs a finite list
of union requests with exact model cost equal to the list length.
`identity_unionManyCosted_rankPowerMass_profile` packages the concrete base
with repeated union-by-rank while preserving the exponential rank/mass fact.
`identity_unionManyCosted_profile` combines the concrete initial state with the
repeated-union carrier, proving the final erased state still satisfies
`RootMassInvariant`. The stronger
`identity_unionManyCosted_refinement_profile` also proves that the final forest
state refines the abstract `State.unionSpecMany` fold up to `SamePartition`.
`NoCompressionRankedMassBackendState` is the representation-state adapter over
that executable layer: it stores a `NoCompressionRankedMassForest` together
with its `RootMassInvariant`, exposes `abstractState` as the induced partition
state, and provides costed `find`, one-node-compressing `compressFind`,
full-path `fullCompressFind`, `union`, and finite `unionMany` operations.
`findRoot?_rank_lt_of_ne` proves
that a non-root node has strictly smaller rank than the root returned by
`findRoot?`, which discharges the rank premise for `compressNode`.
`compressNode_rootMassInvariant_refinement_profile` proves that redirecting a
queried node to its existing root preserves `RootMassInvariant` and the
abstract partition. `compressFindCosted_parent?_eq_root_of_findRoot?` records
the concrete rewrite performed by the backend find, and
`compressFindCosted_refinement_profile` proves the costed find still returns
`abstractState.find?` and preserves `State.SamePartition`. The union profiles
continue to prove invariant-carrying union steps that refine
`State.unionSpec`, and finite union sequences refine `State.unionSpecMany`
without requiring callers to pass the root-mass invariant separately.
`fullCompressFindCosted` follows the original parent chain with explicit fuel,
compresses each visited node on the way back through the one-node kernel, and
has a checked cost bound `<= maxSearchFuel + 1`. Its executable
`fullCompressFindTrace` records the parent-chain nodes visited under the same
fuel recursion, `fullCompressFindTrace_length_le` bounds that trace by the
search fuel, and `fullCompressFindCosted_cost_eq_trace_length` proves the
modeled cost is exactly the trace length.
`fullCompressFindCosted_findRoot?_eq` proves all executable representatives
are preserved exactly, `fullCompressFindCosted_parent?_eq_root_of_findRoot?`
records that the queried node is rewritten to the returned root on successful
finds, and
`fullCompressFindCosted_trace_parent?_eq_root_of_findRoot?` strengthens the
anti-vacuity checkpoint to every node in the discovered trace.
The rank/height/cardinality bridge is now explicit:
`fullCompressFindTrace_length_le_rank_gap_of_findRoot?` bounds a successful
trace by the rank gap to the returned root, `findRoot?_rank_lt_rootMass`
connects the root rank to executable component mass, and
`fullCompressFindTrace_length_le_rootMass_of_findRoot?` gives the resulting
component-cardinality bound on successful traces.
`fullCompressFindCosted_refinement_profile` packages the bounded cost, exact
answer, exact representative preservation, and `SamePartition` boundary.
`fullCompressionRepresentationBackend_profile` then instantiates
`RepresentationBackend` with full path compression for `find` and the existing
rank/mass union-by-rank operation for `union`.
`fullCompressionRepresentationAmortizedBackend_profile` instantiates
`RepresentationAmortizedBackend` with zero potential, exact trace-length
credit for full-compression `find`, and unit credit for union-by-rank. This is
only the baseline amortized scaffold. The next checkpoint,
`fullCompressionRankGapAmortizedBackend_profile`, uses the nonzero
`rankSizePotential` and replaces exact trace-length find credit with
`rankGapFindCredit`, discharged by
`fullCompressFindCosted_cost_le_rankGapFindCredit`. This is still not Tarjan:
the potential is coarse and size-preserving, but the credit has moved from the
executed trace list to a rank/height quantity. The follow-up checkpoint
`fullCompressionLogRankAmortizedBackend_profile` consumes the logarithmic rank
bound: successful finds use `logRankFindCredit`, bounded by
`Nat.log2 forest.size + 1`, while invalid queries retain the existing fuel
fallback. The bridge theorem is
`fullCompressFindCosted_cost_le_logRankFindCredit`, with the intermediate
`rankGapFindCredit_le_logRankFindCredit`.

## What Is Not Claimed Yet

This is not yet Tarjan union-find, inverse-Ackermann analysis, mutable arrays,
or a constant-credit amortized executable backend. The checked `Backend`
instance is still
the constant-cost reference backend over the abstract partition state, included
so the exactness and amortized-accounting interfaces are non-vacuous. The
forest layer now has a rank-aware parent-link operation, an abstract rank-size
fact that discharges the equal-rank bump premise, an executable root-mass
accounting layer that preserves the stronger invariant across no-compression
union-by-rank steps, plus one-node and full-parent-chain compression finds on
the representation-backed adapter. It also has trace-cost equality,
rank/root-mass/log-rank trace bounds, the stronger `2 ^ rank <= mass`
invariant, and nonzero-potential rank-gap/log-rank amortized checkpoints. The
current amortized theorems still have rank-gap or log-rank credit rather than a
uniform inverse-Ackermann-style credit.
The singleton identity forest now instantiates the root-mass invariant, the
mass-carrying no-compression layer has a concrete base state plus a finite
repeated-union carrier that refines the abstract folded union specification,
and `NoCompressionRankedMassBackendState` packages those pieces as a
representation-backed adapter. It is still not a literal `Backend` instance
because the current `Backend` surface is over abstract `UnionFind.State`,
while the mass forest state carries representation data and proof-relevant
invariants. It is now a literal `RepresentationBackend` instance through
`fullCompressionRepresentationBackend` and a literal
`RepresentationAmortizedBackend` instance through
`fullCompressionRepresentationAmortizedBackend`; the stronger
rank-gap and log-rank nonzero-potential checkpoints are
`fullCompressionRankGapAmortizedBackend` and
`fullCompressionLogRankAmortizedBackend`.

## Next Theorem Targets

1. Replace log-rank find credit with the first bucketed/Tarjan-style potential
   over the `RepresentationAmortizedBackend` boundary.
2. Split the current invariant-carrying backend state into executable payload
   fields versus proof-only certificates, so a future array-backed backend can
   share the same `RepresentationBackend` theorem shape.
3. Promote the log-rank and bucketed checkpoints from size-preserving potential
   scaffolds to a path-compression-aware potential that can decrease on
   compression rather than merely pay from a bounded credit term.
