# Union-Find Tarjan Architecture Digest

Snapshot: 2026-06-29. This note records the architecture research pass for
moving the union-find spoke from the current forest-refinement/log-rank/rank
slack checkpoints toward a true Tarjan inverse-Ackermann theorem.

## Research Baseline

The checked RMQ branch already has the right algorithmic substrate:
`ParentForest`, bounded `findRoot?`, union-by-rank, root-mass/rank-power
accounting, full path compression, and representation-backed amortized
profiles. The strongest current Tarjan-facing checkpoint is
`fullCompressionTarjanLevelIndexAmortizedBackend_profile`, with the obstruction
`tarjanLevelIndexPotential_eq_rankSlackPotential_of_forall_gap_le`. The first
sequence-level checkpoint now adds `UFOp`, `State.runOpsSpec`,
`RepresentationBackend.runOpsCosted`,
`RepresentationBackend.runOpsCosted_refinement_profile`,
`RepresentationAmortizedBackend.runOpsCosted_amortized`, and
`NoCompressionRankedMassBackendState.runFullCompressionTarjanLevelIndexAmortized_profile`.
It also adds `chargedUnionCosted` and
`runChargedFullCompressionOpsCosted_refinement_profile`, which model public
union as two full-compression finds followed by the rank-guided link.
The event layer has since landed in `RMQ/Core/UnionFind/TarjanEvents.lean`.
Its root-edge-aware strict profile
`runChargedFullCompressionStrictScheduledEventCost_profile` decomposes a public
run into root/root-edge events, strict cross-level events, strict same-level
residual events, and rank-link events. The valid-operation reduction
`runChargedFullCompressionCost_le_strictScheduledResiduals_add_five_mul_length_of_valid`
absorbs root-edge and link events into linear overhead, leaving strict
cross/residual events as the non-linear target. The local bridges
`fullCompressFindScheduleStrictResidualCount_le_traceRootParentRankSlack_of_findRoot?`
and
`fullCompressFindStrictIteratedLogScheduleCrossCount_le_traceLevelGap_of_findRoot?`
show why this is the right boundary: direct root edges are no longer polluting
the residual bucket, strict residuals have positive rank slack, and the current
iterated-log cross events are already paid by the level-gap potential.
The bridge
`fullCompressFindCosted_strictResidual_parent_rank_progress_of_trace_mem`
adds the local sequence-counting hook: every strict residual trace event
rewrites that node to a strictly higher-rank parent.
The list theorem
`runChargedFullCompressionScheduleStrictResidualNodes_length` packages those
events as an explicit whole-run node stream whose length is exactly the strict
residual count.
The event-record layer now upgrades that node stream:
`runChargedFullCompressionScheduleStrictResidualEvents_length` keeps the exact
count, `runChargedFullCompressionScheduleStrictResidualEvents_rankProgress`
proves every event carries `oldParentRank < rootRank`, and
`fullCompressFindScheduleStrictResidualEvents_parent?_eq_root_of_mem` ties
full-find event records to the actual parent rewrite. The rank monotonicity
hooks `rank_le_rankAfterUnionByRank`, `chargedUnionCosted_rank_le`, and
`runChargedFullCompressionOpsCosted_rank_le` say that the underlying rank data
never decreases across union-by-rank or charged operation runs.

That obstruction is a design signal. It proves that splitting rank slack into
`levelGap + (rankSlack - levelGap)` does not create Tarjan accounting; under the
natural sub-gap condition it is extensionally the old rank-slack potential.
The next proof therefore needs a recursively indexed event counter, not another
algebraic residual. More sharply, it needs an ordered same-node theorem saying
that a later strict residual event starts from at least the previous event's
root rank, so same-bucket events can be packed by an Ackermann-indexed schedule.

The literature shape is sequence-level. Tarjan's classical result bounds a
sequence of `m` operations on `n` elements by an inverse-Ackermann term, while
path compression rewrites parent chains and union by rank/size controls rank
growth. Standard expositions split traversed edges into root edges, bucket or
level crossings, and same-bucket residual events; the hard part is proving the
same-bucket events are globally few across the whole operation sequence.

Sources checked during this pass:

- Tarjan, "Efficiency of a Good But Not Linear Set Union Algorithm",
  DOI: https://doi.org/10.1145/321879.321884
- Tarjan and van Leeuwen, "Worst-case Analysis of Set Union Algorithms",
  DOI: https://doi.org/10.1145/62.2160
- Seidel and Sharir, "Top-Down Analysis of Path Compression",
  DOI: https://doi.org/10.1137/S0097539703439088
- Secondary proof-outline cross-check:
  https://en.wikipedia.org/wiki/Disjoint-set_data_structure
- Local sibling audit:
  `C:\Users\poin\Documents\path-compression-digestion\formalization`

## Agent Red-Team Conclusions

Three read-only agents independently converged on the same architectural pivot.

1. `RepresentationAmortizedBackend` is still valuable, but it is a one-step
   local profile. The true Tarjan theorem needs a mixed-operation sequence
   theorem with explicit operation count, initial element count, total modeled
   cost, and telescoping potential/credit sums.
2. The current `unionCosted = 1` model is an honest root-link-style backend
   checkpoint, but it is not yet the classical public union operation unless
   union is decomposed into charged finds plus a link, or the theorem explicitly
   states a root-link primitive API.
3. The separate path-compression formalization is useful research material but
   not a drop-in RMQ dependency. Its alpha layer uses `noncomputable` least
   indices, and parts of its source model are certificate-heavy. RMQ should
   either define executable bounded alpha searches or first prove a
   parameterized-by-`k` sequence theorem.
4. Delta-style union credits are scaffolding. The checked theorem
   `RMQ.Amortized.deltaCredit` now records the generic fact that if credit may
   include the exact post-minus-pre potential delta, the potential obligation is
   automatic.
5. Mutable arrays are not necessary for the mathematical Tarjan theorem. The
   list-backed forest plus modeled `Costed` ticks is acceptable for the next
   theorem, provided the theorem is explicit about model cost rather than Lean
   runtime.

## Required Architecture

The next layer should be added beside `Forest.lean`, not by growing it.

Recommended module split:

- `RMQ/Core/UnionFind/Sequence.lean`
  now defines a mixed operation language, abstract and representation-backed
  runners, output/refinement conventions, and the first sequence telescope
  theorem. It intentionally proves representative-insensitive final-state
  refinement rather than raw representative-name equality for find outputs.
- `RMQ/Core/UnionFind/TarjanSchedule.lean`
  should define Mathlib-free rank thresholds, Ackermann-style rows, bounded
  least-index alpha functions or a parameterized `k` interface, and monotonicity
  lemmas.
- `RMQ/Core/UnionFind/TarjanEvents.lean`
  now extracts compression events from `fullCompressFindTrace`, classifies them
  first by the coarse schedule split and then by the stricter root-edge-aware
  split, proves root-edge work is linear for valid operation sequences, and
  proves strict iterated-log cross events are paid by the existing level-gap
  potential.
- `RMQ/Core/UnionFind/TarjanAnalysis.lean`
  should connect rank-threshold packing, event counts, schedule indices, and
  sequence telescoping into the first alpha-shaped theorem.

The executable state can remain `NoCompressionRankedMassBackendState` for now,
but proofs must keep payload fields separate from proof-only certificates such
as root-mass and rank-power invariants.

## Theorem Roadmap

The next crisp targets should land in this order.

1. Mathlib-free schedule:
   `tarjanAckermann`, `tarjanThreshold`, `tarjanAlphaBounded`, and monotonicity
   lemmas. If bounded alpha is too early, prove the same statement
   parameterized by a level `k`.
2. Strict residual-event bound:
   consume
   `runChargedFullCompressionCost_le_strictScheduledResiduals_add_five_mul_length_of_valid`
   by bounding
   `runChargedFullCompressionScheduleStrictResidualCount` with the new
   schedule, using
   `fullCompressFindCosted_strictResidual_parent_rank_progress_of_trace_mem`
   and `runChargedFullCompressionScheduleStrictResidualNodes_length` as the
   local progress and enumeration tickets. This is the live theorem gap; the
   old coarse residual bucket is no longer the target.
3. Rank-threshold packing:
   derive a `rankThresholdPacking` theorem from the existing
   `RankPowerMassInvariant`, rather than taking packing as an arbitrary
   certificate.
4. First real Tarjan-shaped profile:
   `fullCompressionTarjanSequenceParameterized_profile`, with credit depending
   on a fixed schedule level `k` and an explicit threshold condition.
5. Alpha bridge:
   `fullCompressionTarjanSequenceAlpha_profile`, replacing the parameterized
   `k` with executable `tarjanAlphaBounded m n`.

The older target, "replace `tarjanLevelIndexPotential` with a recursively
bucketed residual," remains necessary but should now be built against the
sequence/event interface rather than directly as another one-step backend
wrapper.

## Nonclaims

This architecture pass does not claim:

- Tarjan's inverse-Ackermann theorem is proved in RMQ.
- The root-edge-aware event profile by itself bounds strict same-level
  residual events by alpha.
- The current delta-credit union profiles are uniform amortized bounds.
- `unionCosted = 1` is already the classical public union API.
- The sibling path-compression formalization can be imported into RMQ as-is.
- Lean list runtime costs are the modeled operation costs.
- Mutable-array executable refinement is established.

## Skeptical Grad Student Question

If `RepresentationAmortizedBackend` already has potentials and credits, why
not just define an alpha-sized credit there?

Because alpha-sized credit is a theorem about a whole operation sequence. A
single-operation profile can always hide work in a state-dependent credit or a
post-minus-pre delta. The true Tarjan proof must show that, across the entire
run, every same-bucket residual traversal consumes a globally bounded index or
packing budget. That requires a runner, event extraction, and sequence
telescoping before the Ackermann counter can mean anything.
