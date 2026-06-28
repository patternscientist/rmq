import RMQ.Core.UnionFind.Forest

/-!
# Standalone union-find spoke

This import root exposes the first union-find specification and amortized
accounting surface plus the first parent-pointer forest refinement layer. It is
not yet Tarjan union-find or a mutable-array implementation: the public API
gives a finite partition state, exact costed reference `find`/`union`
operations, a backend interface where `find` may return an updated state, a
list-backed parent forest with bounded root search, and representation-backed
compression/rank-mass checkpoints future implementations can consume.

The current public profile theorems are
`RMQ.UnionFind.referenceBackend_profile`,
`RMQ.UnionFind.referenceAmortizedBackend_profile`, and
`RMQ.UnionFind.Forest.parentForestRefinement_profile`; the first concrete
singleton-component forest checkpoint is
`RMQ.UnionFind.Forest.ParentForest.identity_profile`, and the first concrete
union checkpoint is `RMQ.UnionFind.Forest.ParentForest.union_profile`.  The
root-link frontier is tracked by
`RMQ.UnionFind.Forest.ParentForest.rootLink_refinement_profile`; the first
rank-guided closure checkpoints are
`RMQ.UnionFind.Forest.ParentForest.rootLink_rank_lt_refinement_profile` and
`RMQ.UnionFind.Forest.ParentForest.rootLink_rank_eq_bump_refinement_profile`.
The representative-insensitive union-by-rank boundary is exposed by
`RMQ.UnionFind.State.SamePartition`,
`RMQ.UnionFind.Forest.ParentForest.rankedRootLink_refinement_profile`, and
`RMQ.UnionFind.Forest.ParentForest.unionByRank_refinement_profile`; its
equal-rank bump premise is discharged by the proof-only
`RMQ.UnionFind.Forest.ParentForest.RankSizeInvariant`.  Preservation across
one union-by-rank step is tracked by
`RMQ.UnionFind.Forest.ParentForest.RankComponentInvariant` and
`RMQ.UnionFind.Forest.ParentForest.unionByRank_rankSizeInvariant_profile`.
The executable root-mass accounting layer is tracked by
`RMQ.UnionFind.Forest.ParentForest.RootMassInvariant`,
`RMQ.UnionFind.Forest.ParentForest.identity_rootMassInvariant`,
`RMQ.UnionFind.Forest.ParentForest.unionByRank_rootMassInvariant_profile`, and
the mass-carrying no-compression costed forest surface
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassForest`, including
its concrete singleton init profile, finite repeated-union profile, and
`SamePartition` refinement to the abstract `State.unionSpecMany` fold.  The
representation-backed adapter surface is
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState`, whose
`findCosted`, one-node-compressing `compressFindCosted`, full-path
`fullCompressFindCosted`, `unionCosted`, and `unionManyCosted` profiles carry
the rank-power/root-mass certificate internally while exposing the induced
abstract `State` boundary.  `RMQ.UnionFind.RepresentationBackend` is the cleaner representation
boundary for non-`State` executable backends, and
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationBackend_profile`
instantiates it with full path compression for `find`.  The executable
`fullCompressFindTrace` plus
`fullCompressFindCosted_trace_parent?_eq_root_of_findRoot?` theorem record that
every node in the discovered trace, not just the query node, is rewritten to
the returned root after a successful full-compression find. The current
potential-method checkpoint is
`RMQ.UnionFind.RepresentationAmortizedBackend` instantiated by
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationAmortizedBackend_profile`;
it uses zero potential with exact trace-length credit for compressed find and
unit credit for union-by-rank. The rank/height/cardinality bridge is exposed by
`fullCompressFindCosted_cost_eq_trace_length`,
`fullCompressFindTrace_length_le_rank_gap_of_findRoot?`, and
`fullCompressFindTrace_length_le_rootMass_of_findRoot?`. The stronger
`RMQ.UnionFind.Forest.ParentForest.RankPowerMassInvariant` layer proves and
preserves the exponential component-size lower bound
`2 ^ rank root <= mass root`, and
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankGapAmortizedBackend_profile`
is the first nonzero-potential checkpoint: finite-size potential, rank-gap
find credit, and unit union credit. The logarithmic-rank follow-up is exposed by
`RMQ.UnionFind.Forest.ParentForest.RankPowerMassInvariant.rank_le_log2_mass`,
`RMQ.UnionFind.Forest.ParentForest.RankPowerMassInvariant.rank_le_log2_size`,
and
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionLogRankAmortizedBackend_profile`,
which replaces successful-find rank-gap credit with a global
`log2 forest.size + 1` credit while retaining the invalid-query fuel fallback.
The first explicit bucketed checkpoint is
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankBucketAmortizedBackend_profile`:
it defines logarithmic rank buckets, pays successful full-compression finds by
the returned root bucket's geometric width, and keeps the statement explicitly
pre-inverse-Ackermann. The local path-compression drop kernel is
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankSlackCheckpoint_profile`:
it preserves ranks through full compression, bounds a successful trace by
original parent-rank slack plus two, and proves the compressed final state
zeroes that slack on the visited trace. The theorem
`fullCompressFindCosted_cost_add_traceRootParentRankSlack_le_of_findRoot?`
packages the local potential-method inequality with constant credit `2`. The
checkpoint also exposes `rankSlackPotential`, proves successful full
compression drops that aggregate enough to pay the original trace slack via
`rankSlackPotential_fullCompressFindCosted_add_traceRootParentRankSlack_le_of_findRoot?`,
and packages the resulting constant-successful-find credit in
`fullCompressionRankSlackAmortizedBackend_profile`. Union in that checkpoint
uses explicit potential-delta credit. The follow-up
`fullCompressionRankSlackSizeUnionAmortizedBackend_profile` keeps the same
find credit but replaces that delta with the coarse non-oracular union credit
`rankBucketPotential backend + 1`, using
`rankSlackPotential_unionCosted_le_rankBucketPotential`. The multilevel
follow-up
`fullCompressionTarjanLevelAmortizedBackend_profile` introduces the executable
iterated-log schedule `tarjanLevelIter`, the concrete rank level
`tarjanRankLevel`, and a level potential that pays cross-level parent-to-root
rank gaps while `tarjanLevelFindCredit` charges only the residual rank slack
left within the current level plus constant `2`. Its union credit is bounded by
`tarjanLevelPotentialBound`, a level-specific whole-forest bound. This is still
not a Tarjan or inverse-Ackermann theorem. The clean-credit follow-up
`fullCompressionTarjanLevelCleanCreditAmortizedBackend_profile` keeps the same
level potential but replaces the trace-dependent successful-find credit with
`tarjanLevelRootRankFindCredit` and replaces the whole-forest union credit with
the local delta `tarjanLevelDeltaUnionCredit`, proved no larger than
`tarjanLevelUnionCredit`.
`fullCompressionTarjanPhaseCountAmortizedBackend_profile` then absorbs the
residual rank-slack layer into `tarjanPhaseCountPotential`, allowing
successful finds to use the trace-free phase-count credit
`tarjanPhaseCountFindCredit`. This is alpha-shaped but still not alpha-tight:
the potential includes full rank slack, and the phase schedule is a fixed
iterated-log collapse of the rank universe. The sharper
`fullCompressionTarjanLevelIndexAmortizedBackend_profile` replaces that hidden
full-rank-slack layer with the explicit sum `tarjanLevelIndexPotential =
tarjanLevelPotential + tarjanResidualPotential`; the new drop theorem
`tarjanLevelIndexPotential_fullCompressFindCosted_add_traceRootParentRankSlack_le_of_findRoot?`
shows successful full compression releases enough level-plus-index potential
to pay the original trace rank slack. This is closer to the Tarjan proof path,
but the index is still raw within-level rank slack, not an Ackermann-indexed
potential or final inverse-Ackermann theorem. The obstruction theorem
`tarjanLevelIndexPotential_eq_rankSlackPotential_of_forall_gap_le` explains
why this exact residual definition cannot be the final answer: when the level
gap is a true sub-gap, adding `levelGap` and `rankSlack - levelGap` collapses
back to ordinary rank slack.
-/
