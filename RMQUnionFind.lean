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
-/
