# Proof Digestion Log

This document is the standing protocol for turning verified proof progress into
an explanation that a mathematically mature non-Lean audience can interrogate.
It is not a replacement for `lake build`, axiom checks, or theorem inventories.
It is the companion process that keeps the project from becoming merely true:
verified, but hard to teach, audit, or extend.

## Audience

The target reader is a Lean club or graduate CS/math audience: comfortable with
proofs and asymptotics, but not assumed to know Lean internals, monads, or the
project's local cost-model vocabulary.

## Running Protocol

After a spoke milestone lands, the spoke coordinator should add or update a
short explanation note containing the following required worker-report
questions:

- the theorem or construction that changed;
- what changed conceptually;
- what the completed work now means in plain English;
- what assumptions are live, especially payload bits, proof-only fields,
  charged reads, and compiled Lean execution nonclaims;
- what a skeptical grad student would ask next;
- the informal mathematical statement;
- the proof idea in ordinary language;
- the dependency path to the previous public surface;
- the live frontier after the milestone.

The main coordinator periodically folds those notes into this log and asks
read-only reviewers to attack the explanation from distinct perspectives:

- mathematically mature non-Lean reader;
- data-structures researcher;
- Lean/library maintainer;
- cost-model skeptic;
- public-facing/audience explainer.

An explanation is considered digested only when the reviewers can identify the
main idea, the theorem's actual scope, and the remaining nonclaims without
reading the full Lean proof.

## Current Global Story

The repository began as a formal RMQ proof-of-concept and now has three active
spokes:

- RMQ/LCA/succinct RMQ: exact RMQ correctness, Fischer-Heun-style construction
  layers, a BP-native `2*n + o(n)` constant-query profile under the documented
  RAM/indexed-access model, and matching Catalan-style lower-bound machinery.
- Rank/select: a standalone bitvector spec and public Jacobson/Clark
  `n + o(n)` constant-query profile, plus a compressed/FID fixed-weight family
  surface. The concrete sub-log/Packed-Clark constructor now has interpreted
  access/rank/select replays, store-backed trace packets, a target-independent
  global payload-store execution story for shared access plus rank false/true
  and select false/true, and an RMQ-style bounded trace-local event-width
  companion, now fused into one public compressed/FID capstone theorem. The
  remaining RMQ-level gap is stronger uniform machine-word/asymptotic width
  bounds.
- Union-find: a finite partition specification, costed reference operations,
  a parent-pointer forest refinement, union-by-rank/root-mass/rank-power
  invariants, full-compression find refinement, rank-gap/log-rank amortized
  checkpoints, explicit rank-bucket-width accounting, and a local/global
  rank-slack compression-drop kernel, and merged Tarjan-level, phase-count, and
  level-index potential checkpoints. These still leave residual/large-credit
  structure explicit; the Tarjan inverse-Ackermann theorem remains open.

## Current Digests

- [`digests/PROJECT_DIGESTION_2026_07_06.md`](digests/PROJECT_DIGESTION_2026_07_06.md):
  canonical current public state-significance-and-path-to-a-paper digest for
  `main` at
  `3f6f1e3`, for a mathematically mature non-DS audience. Covers the
  store-parametric whole-query capstone and the 2026-07-06 model-adequacy /
  footprint-containment / paper-surface landings; ranks the achievements; and
  gives the candid publishable-work gap analysis that led to the later
  fast-regime cost theorem, with the corrected `2^15`-readiness story.
  Includes a recorded adversarial review loop (Appendix A) whose fact-check
  round corrected an earlier `2^128`-gate mischaracterization in
  `docs/PUBLICATION_STRATEGY.md`.
- [`ADD_PROVENANCE.md`](ADD_PROVENANCE.md):
  public audit-driven-development provenance note. It explains the coordinator
  / specialist-worker distinction, theorem-shaped prompts, audit-of-audits
  synthesis, Goodhart failure modes, and transcript-evidence policy. It is
  process evidence, not a proof object or trust-base assumption.
- [`digests/DEEP_PROJECT_DIGESTION_2026_06_28.md`](digests/DEEP_PROJECT_DIGESTION_2026_06_28.md):
  historical deep Lean-club-facing project digestion, with first-contact
  definitions of RMQ, Cartesian shape, rank/select, balanced parentheses,
  modeled cost, payload accounting, compressed/FID, and union-find; includes a
  recorded adversarial classroom fixedpoint loop. Revised 2026-06-28 (Part I-IV
  structure): groundings now quote the primitives directly (`Spec.LeftmostArgMin`,
  `Costed`, the private-constructor `RAM.Exec` traced substrate, the `RMQBackend`
  contract, `binomialCount` as Pascal's recurrence, the union-find
  `tarjanLevelIndexPotential` collapse self-diagnostic), and a literature map
  (Bender-Farach-Colton, Jacobson, Munro-Raman, RRR, Fischer-Heun, Tarjan) was
  added so the routine/classical steps are recognizable as known results.
- [`digests/PROJECT_STATE_2026_06_28.md`](digests/PROJECT_STATE_2026_06_28.md):
  June 28 project-wide digest, including the merged rank/select log-chunk
  primary-budget/split-width route-directory work and the merged union-find
  Tarjan-level scaffold.
- [`digests/RMQ_PROOF_MAP.md`](digests/RMQ_PROOF_MAP.md): index and shared
  assumptions ledger for the digest layer.
- [`digests/COORDINATOR_COMPLETION_LOG.md`](digests/COORDINATOR_COMPLETION_LOG.md):
  time-stamped coordinator completion reports in the proof-digestion format.
- [`digests/RMQ_CAPSTONE.md`](digests/RMQ_CAPSTONE.md): classroom proof map
  for the stable RMQ capstone.
- [`digests/RANK_SELECT_FID_FRONTIER.md`](digests/RANK_SELECT_FID_FRONTIER.md):
  rank/select FID frontier after the access/rank/select chunk-route, narrow
  metadata, log-chunk primary-budget, and split-width table/RAM milestones.
- [`digests/RANK_SELECT_COMPRESSED_FID_2026_06_29.md`](digests/RANK_SELECT_COMPRESSED_FID_2026_06_29.md):
  first-contact explanation of the fixed-weight compressed/FID family capstone.
- [`digests/UNION_FIND_AMORTIZATION_FRONTIER.md`](digests/UNION_FIND_AMORTIZATION_FRONTIER.md):
  union-find amortization frontier around rank-gap, rank-bucket, rank-slack,
  Tarjan-level, phase-count, and level-index potential checkpoints.
- [`digests/UNION_FIND_TARJAN_ARCHITECTURE.md`](digests/UNION_FIND_TARJAN_ARCHITECTURE.md):
  sequence/event architecture plan for the remaining Tarjan amortization gap.

## Current Rank/Select Note

2026-06-29 update: the fixed-weight compressed/FID spoke now has a public
concrete capstone family surface.  `RMQ.RankSelect.compressedFIDFixedWeightFamily`
packages the concrete sub-log/Packed-Clark directory for every bitvector, and
`RMQ.RankSelect.compressedFIDFixedWeightFamilyProfile` states that the
enumerative fixed-weight primary payload plus the concrete auxiliary payload
fits `fixedWeightPayloadBudget bits + o(n)` and supports exact
access/rank/select with one modeled constant query bound.  Plain English: the
rank/select spoke now has its own compressed analogue of the succinct-RMQ
family story, scoped to fixed-weight/FID payload accounting.  The follow-up
interpreted theorem
`RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile` now replays
that same access/rank/select surface through the first-order `WordRAM` bridge
layer.  The first trace-level execution packets are now also present:
`RMQ.RankSelect.compressedFIDFixedWeightAccessTraceResult_execution_story`
builds a concrete access trace result with a four-segment access payload store,
and `RMQ.RankSelect.compressedFIDFixedWeightRankTraceResult_execution_story`
builds the analogous rank trace result with a six-segment rank payload store.
`RMQ.RankSelect.compressedFIDFixedWeightSelectTraceResult_execution_story`
now adds the select packet: it reads the charged packed-Clark route directory
and then performs the constant local fixed-weight block decode through
code/length/class/shared-decoder payload reads.  The combined theorem
`RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStore_execution_story`
relabels shared access plus rank false/true and select false/true into one
concrete payload store for each fixed `bits`.  The bounded companion
`RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStore_bounded_execution_story`
now adds the same style of finite trace-local event-width packet used by the
final RMQ bounded trace theorem: every payload-read segment/index and every
natural operand/result exposed by word-local rank/select primitives fits the
declared trace-local width.  Live assumptions: this is still the project's
modeled RAM/indexed-read cost layer, not compiled Lean execution speed, the earlier
target-indexed theorem remains as lower-level compatibility, and the width is
trace-local rather than an asymptotic machine-word-size theorem.  A skeptical
grad student should now ask whether the trace-local width can be replaced or
complemented by uniform machine-word side conditions, and whether the
rank/select global packet should be folded into an even larger RMQ-style trace
with a single closed controller.
The latest fused capstone
`RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStoreFusedProfile` packages
the compressed family theorem, interpreted replay theorem, target-independent
global-store theorem, and bounded global-store theorem into one public surface.
Plain English: the fixed-weight compressed/FID rank/select spoke now has a
single theorem to cite for payload budget, exact constant modeled queries,
WordRAM replay, one shared read store, and trace-local bounded events. The
remaining question is not whether the pieces coexist, but whether the
trace-local bound can be strengthened into a uniform machine-word discipline.

The fixed-weight compressed/FID spoke now separates four issues that were easy
to conflate. First, log-sized sentinel chunk decompositions have an `o(n)` block
count. Second, class/length metadata for those chunks is small only when stored
at a narrow `log log n`-style width; padding it to route width is formally
linear, so it cannot be hidden in the auxiliary term. Third, the per-block
fixed-weight primary codes now have the real enumerative bridge for sentinel
log chunks: the product of per-block fixed-weight universes fits under the
global fixed-weight universe, with one slack bit per block, and the log-chunk
block count is `o(n)`. The replacement charged route-directory/local-decoder
family now exists as a table/RAM envelope with a counted shared decoded-word
table read, and the log-chunk version consumes that primary budget. The live
construction question is therefore not a dense log-chunk decoder: that is ruled
out by `noFixedWeightLogChunkDenseDecoderLittleO`. The split-width table/RAM
profile now provides the needed route-vs-class/length width separation, so the
next positive design must instantiate that family with concrete route payloads
and a genuinely sublinear shared decoder payload.

## Current Union-Find Digestion Note

The bucket checkpoint should be read as a schedule interface, not as Tarjan's
analysis. The Lean theorem defines logarithmic rank buckets and proves that the
geometric width of the returned root's bucket pays the existing rank-gap bound
for a successful full-compression find. This is a useful bridge because future
potential definitions can refine "pay by whole bucket width" into "charge a
node-level bucket potential that decreases under compression." It does not yet
prove that compression has inverse-Ackermann amortized cost, and it does not
introduce mutable arrays or an imperative executable backend.

The rank-slack checkpoint is the first local version of that decrease. For a
successful full-compression find, it measures each visited node by the rank gap
between the returned root and that node's current parent, proves the trace
length is bounded by the sum of those local slacks plus two, and proves the
compressed final state sets all those visited-node slacks to zero. The local
potential-method inequality then pays the full trace cost by original trace
slack plus constant credit `2`. The checkpoint also defines a global sum of
each valid node's slack to its own root and now proves a successful
full-compression find decreases that aggregate enough to pay the original
visited-trace slack. The resulting representation-amortized checkpoint gives
successful compression constant find credit, with invalid queries falling back
to fuel and union using an explicit potential-delta credit. A follow-up
backend replaces that answer-shaped union credit with the coarse size-log bound
`rankBucketPotential backend + 1`, proved from
`rankSlackPotential_unionCosted_le_rankBucketPotential`. It still does not
derive Tarjan's inverse-Ackermann bound or a small uniform union credit.

The Tarjan-level checkpoint is the first multilevel version of this accounting.
It defines an executable iterated-log level schedule over ranks, splits every
parent-to-root rank gap into a cross-level part and a residual within-level
part, and proves full compression drops the aggregate cross-level potential
enough to pay the cross-level part of the visited trace. The backend profile
`fullCompressionTarjanLevelAmortizedBackend_profile` charges successful finds
only for the residual within-level slack plus constant `2`; union is bounded by
a level-specific whole-forest potential bound. This is a reusable
Tarjan-style interface, not the inverse-Ackermann theorem.
The clean-credit refinement
`fullCompressionTarjanLevelCleanCreditAmortizedBackend_profile` keeps the same
level potential but removes the explicit trace residual from successful-find
credit, replacing it with the returned root's rank plus one, and replaces the
whole-forest union credit with a local potential delta. This cleans up the
profile shape without claiming alpha-style amortization.
The next phase-count checkpoint
`fullCompressionTarjanPhaseCountAmortizedBackend_profile` absorbs the residual
rank slack into `tarjanPhaseCountPotential`, so successful-find credit is the
global iterated-log `tarjanPhaseCountBound + 2` rather than a trace or root-rank
quantity. This moves the public credit shape toward inverse-Ackermann analyses,
but the underlying potential is still too coarse because it contains the full
rank-slack layer.
The sharper level-index checkpoint
`fullCompressionTarjanLevelIndexAmortizedBackend_profile` replaces that hidden
full-rank-slack layer with
`tarjanLevelIndexPotential = tarjanLevelPotential + tarjanResidualPotential`.
Its aggregate drop theorem pays the original trace-root parent rank slack from
the combined cross-level and residual-index drops, while retaining the
phase-count-shaped public find credit. This is closer to the Tarjan proof path,
but still not the inverse-Ackermann theorem: the residual index is raw
within-level rank slack, not a recursively bucketed Ackermann counter.
The obstruction theorem
`tarjanLevelIndexPotential_eq_rankSlackPotential_of_forall_gap_le` records why
this exact design cannot simply be pushed to the true Tarjan theorem: whenever
the level gap is a real sub-gap, the additive level-plus-residual potential is
extensionally the old rank-slack potential. The next proof needs a genuinely
indexed residual counter, not `rankSlack - levelGap`.

The next residual-counter obstruction generalizes that caveat. The theorem
`subtractiveResidualIndexPotential_collapse_obstruction` says that any
node-local index bounded by rank slack collapses if the potential simply adds
the index to its complement `rankSlack - index` over the current finite node
universe. Conceptually, this rules out a broad family of "better split point"
designs: they may rename or refine the local index, but if the residual is
defined as the remaining rank slack, the sum is still exactly
`rankSlackPotential`. Plain English: to move toward Tarjan, the counter must
remember sequence/event/bucket structure, not just repartition each node's
current slack. The live assumption is that this obstruction applies to local
additive-complement potentials on one forest state; it does not rule out
ordered event streams, operation-count-indexed phases, or Ackermann buckets.
A skeptical grad student should ask for the next theorem that proves repeated
same-node residual events start above the previous event's target rank and can
therefore be packed by the new schedule.

The follow-up architecture pass is recorded in
`docs/digests/UNION_FIND_TARJAN_ARCHITECTURE.md`. The code has now moved the
Tarjan target from isolated one-step backend wrappers to mixed operation
sequences and event accounting. `RMQ.UnionFind.UFOp`,
`RMQ.UnionFind.RepresentationBackend.runOpsCosted_refinement_profile`, and
`RMQ.UnionFind.RepresentationAmortizedBackend.runOpsCosted_amortized` provide a
generic `find`/`union` run surface and telescope one-step credits over a run.
`chargedUnionCosted` models public union as two full-compression finds followed
by a rank-guided link, and the strict event scorecard reduces valid-run cost to
strict cross-level and strict same-level residual events plus linear overhead.
The event-record layer records old-parent/root rank snapshots, proves
`oldParentRank < rootRank`, connects full-find records to the concrete parent
rewrite, and proves charged operation runs never decrease ranks. In plain
English: the project can now talk about the exact residual compression events
Tarjan's proof must count, rather than only aggregate rank slack on one forest
state. The skeptical question is now sharper: can the same node's later
residual events be ordered by the previous event's root rank and packed by a
Mathlib-free Ackermann/alpha schedule?

## Current RMQ Word-RAM Note

2026-06-30 update: the succinct RMQ capstone now has an additive interpreted
headline,
`RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryInterpreted`. Conceptually,
the public `2*n + o(n)`, constant-query RMQ theorem is no longer only a
composition of disciplined `Costed` callbacks: the final query is replayed
through Word-RAM bridge layers for the generic sparse-exception close-select
leaf, the compact close/LCA seed path, and the final answer-rank leaf, and is
proved equal to the existing final costed query.

Plain English: the theorem still says the same thing about RMQ answers, payload
space, and modeled query cost, but the path that computes the answer now has a
checked first-order read/word-operation layer underneath its critical payload
reads. This separates the counted payload from proof-only certificates more
sharply and removes the main oracle-shaped concern from the public succinct RMQ
surface.

Live assumptions remain model assumptions, not compiled Lean execution claims. The theorem
uses the standard word-RAM interpretation of charged payload reads and word
operations; it is not a statement about Lean's compiled `List` performance, and
it is not yet a single closed AST for every branch in the final query. The
standalone compressed/FID rank-select spoke has now been replayed through the
same bridge layer. A skeptical grad student should next ask whether later flat
whole-query program presentations, for RMQ or rank/select, would buy clarity
without changing the theorem's mathematical content.

2026-07-01 update: the RMQ whole-query controller now has a leaf-trace
checkpoint,
`RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryLeafTrace`. Conceptually, the
closed controller no longer immediately erases its operational story to the
plain `Costed` carrier. It evaluates to an explicit domain-leaf trace recording
the select-close, compact close/LCA, and answer-rank leaves it called, together
with their modeled costs, and then proves that projecting this trace result
back to `Costed` is exactly the existing whole-query interpreted capstone.

Plain English: this is one rung closer to a flat machine account of the query.
We can now point to the whole-query control program, its leaf trace, and the
same `2*n + o(n)`, constant-query theorem in one theorem chain. The live
assumption is that the trace events are still domain leaves, not one shared
payload-store `WordRAM.TraceEvent` stream. A skeptical grad student should next
ask which of those leaf events should be inlined first into a unified store
trace, and whether that inlining changes any public theorem beyond making the
execution model flatter.

2026-07-01 update: the next rung has landed as
`RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTrace`. Conceptually, the
final closed query controller now emits one `WordRAM.TraceEvent` stream. The
close-select part, answer-rank part, and compact-close rank-seed reads are real
payload/register traces. The bounded local BP decoders, endpoint-fringe
decoders, and relative-rmM interior query are still explicit charged decoder
leaves. Plain English: the public RMQ capstone now has one machine-shaped trace
carrier for the whole query, and more of that stream is payload-derived than
before, but close navigation is not yet fully replayed from payload tables. A
skeptical grad student should now ask for the exact theorem that replaces each
remaining decoder leaf by payload-read events.

2026-07-01 update: the large-regime companion has landed as
`RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTraceLargeRegime`.
Conceptually, this does not change the `2*n + o(n)`, constant-query theorem
shape; it strengthens the execution story under the explicit size premise
`2^128 <= shape.size`. In that regime, the compact close/LCA part of the final
query no longer treats local BP decoding, endpoint fringes, or the relative-rmM
interior query as the same all-size charged fallback boundary. Those pieces are
replayed through structural `WordRAM.TraceEvent` traces and consumed by the
final BP-native RMQ profile. Plain English: for the large canonical regime, the
query trace is now much closer to "read these payload words and run these word
operations" instead of "call this trusted close-navigation black box." The live
assumption is still the word-RAM model itself, plus the fact that the current
large-regime theorem is not the all-input fallback theorem. A skeptical grad
student should next ask for the global store/provenance theorem tying all
events in the combined stream to one concrete payload store.

2026-07-01 follow-up: that global store/provenance theorem has landed as
`RMQ.Headlines.succinctRMQGlobalPayloadStoreExecutionStory`, backed by
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_execution_story`.
Conceptually, the large-regime final succinct RMQ query is now answered from
one globally segmented payload store: the query cost is the projection of a
single `WordRAM.TraceEvent` stream, every event is either a payload read or a
bounded word primitive, and every payload read is checked against the concrete
store assembled from the BP code, select/rank payloads, and compact close/LCA
tables. Plain English: the trace is no longer merely a list of plausible
component calls; in the large regime, each information-bearing read has an
address in the declared payload. Live assumptions remain the word-RAM model,
the explicit `2^128 <= shape.size` premise for this strongest theorem, and the
separation between model cost and compiled Lean execution. A skeptical grad student should
now ask how much of this store-backed execution-story pattern can be reused for
rank/select, BP tree navigation, and eventually a more general machine model.

2026-07-02 update: the store-backed execution story is now total, not just
large-regime. The public alias
`RMQ.Headlines.succinctRMQGlobalPayloadStoreExecutionStory` now points to
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story`,
which has no `2^128 <= shape.size` premise. The large-regime theorem is kept as
`RMQ.Headlines.succinctRMQLargeRegimeGlobalPayloadStoreExecutionStory`.
Conceptually, every actual payload read in the final query is checked against
one concrete global store for all input sizes. Tiny/inactive close-navigation
fallback work is still present, but it is represented as explicitly counted
word-primitive trace events rather than as hidden payload reads. A skeptical
grad student should now ask whether those fallback primitives should be
replaced by a small-table structural replay too, or whether the current
explicit primitive boundary is the right public model boundary.

2026-07-02 follow-up: the succinct RMQ capstone now has a direct ordinary-list
front door,
`RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery`, backed by
`SuccinctClassic.listInt_two_n_plus_o_constant_query_profile`. Conceptually,
the construction-heavy theorem still lives over Cartesian shapes, but the
public theorem now starts with `xs : List Int`: build the counted BP-native
payload for `Cartesian.shape xs`, prove its length is `2 * xs.length + o(n)`,
and prove valid half-open queries return the same leftmost-minimum index that a
direct scan of `xs` returns. The key bridge is not handwaving: the
shape-only local query `CartesianShape.queryOffset?` is exact both for `xs` and
for the canonical representative of `Cartesian.shape xs`, so the representative
answer is transported back to the original list. A skeptical grad student
should now ask whether future public theorem surfaces should lead with the
ordinary object-level API first and put the shape/encoding universe theorem as
the proof engine behind it.

2026-07-02 WordRAM hardening update: the first-order WordRAM/register layer now
separates three things that were previously mostly documented as modeling
discipline. Payload reads have address-provenance theorems: a read event's
segment/index pair comes from the first-order program syntax under the current
register file, not from a proof callback. Register and address values have an
explicit `FitsInBits`/`AddressFitsInBits` vocabulary, and `NatExpr.NoOverflow`
states the policy for arithmetic: expressions evaluate as mathematical `Nat`,
with machine-word safety proved as a side condition rather than silently
wrapping. Finally, trace events are classified as payload reads or word-local
primitives, while register lookup, arithmetic, and branching are zero-cost
control and do not appear as information-bearing events. Plain English: the
model still is not a full CPU, but it is now much harder to hide an unbounded
address computation or an uncharged proof-driven read inside the query trace. A
skeptical grad student should next ask for these bounded-address side
conditions to be consumed by the public whole-query RMQ and standalone
rank/select execution-story theorems, not merely available as local lemmas.

2026-07-02 bounded final-trace update: the public all-size RMQ execution story
now consumes a bounded event-width theorem, not just the global store theorem.
`RMQ.Headlines.succinctRMQGlobalPayloadStoreBoundedExecutionStory` is backed by
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story`.
It packages the existing global-store result together with a finite
trace-local bit width and proves that every payload-read address and every
natural operand/result exposed by word primitives fits that width. The
large-regime companion has the same bounded packet under its explicit size
premise. Separately, `WordRAM.TraceResult.costOnlyTrace_syntheticCostOnlyPrimitive`
names the exact fallback marker used when an old `Costed` component is lifted
to a trace. Plain English: fallback work is no longer just "some primitive
events"; it is a fixed payload-free marker, and the later no-synthetic theorem
proves that this marker is absent from the final all-size RMQ trace. Live
assumptions: the bound is trace-local and conservative, not a tight asymptotic
word-size claim for every component. A skeptical grad student should ask
whether the trace-local width can be pushed down to component-level
machine-word side conditions and then reused by rank/select and BP navigation.

2026-07-03 flat-payload no-synthetic update: the final all-size RMQ global
trace now has a concrete flat-payload backing theorem,
`RMQ.Headlines.succinctRMQFlatPayloadStoreNoSyntheticExecutionStory`, backed by
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story`.
The layout object is query-independent and splits the execution payload into BP
code, final rank/access payload, sparse-exception select payload, padding,
and compact close/LCA payload; the finite-small same-block table is no longer a
public flat-payload appendix. The theorem packages the flat read store, source
and component offsets for successful reads, bounded trace-local event data, and
the proof that no event is the dedicated synthetic cost-only marker. Plain
English: the final trace no longer merely agrees with "some global store"; its
reads are formally tied back to concrete payload slices while the old synthetic
fallback marker is absent from the all-size final trace.
Live assumptions: word primitives still remain explicit trace events, padding
is layout-only rather than a meaningful read source, and the BP-code segment
read by final rank is an alias into the already-counted BP-code slice, not a
new counted copy. A skeptical grad student should next ask whether the
trace-local width can be pushed down to component-level machine-word
side-conditions and then reused by rank/select and BP navigation.

2026-07-04 structural relative-rmM interior repair: the non-Ready relative-rmM
interior is no longer a legacy range-min witness table in the public
all-size trace/store/flat-payload story. The old Ready predicate remains
intentionally non-total:
`SuccinctClose.concreteBPRelativeRmmInteriorReady_not_all` records the
empty-shape obstruction. The public route gets around that obstruction
structurally: Ready shapes use the compact two-level directory, active
non-Ready shapes use a bounded summary scan over the canonical relative
min/max/arg table, and inactive shapes use a pure-none interior trace because
there is no block obligation. `SuccinctClose.concreteBPRelativeRmmInteriorReady_of_size_ge_readyThreshold`
is now only a sufficient Ready theorem; the same-block finite-small close
table is retired from the public flat-payload story and segment 28 is a dead
compatibility slot. Plain English: the all-size flat-payload theorem still
proves every actual successful read is counted and backed, but segments for the
old interior witness table and the retired same-block slot have no successful
reads in that public trace. A skeptical grad student should ask whether the
active non-Ready bounded summary scan should eventually be replaced by a
smaller direct BP-code micro-scan.

2026-07-04 zero-block same-block structural repair: the final all-size
close/LCA trace no longer treats the zero-block same-block case as an
untraced value oracle. The new
`SuccinctClose.ConcreteCompactBPCloseLCADirectory.zeroBlockSameBlockCloseStructuralTraceResult`
reads the counted chunked BP-code payload, computes the same prefix-min close
candidate as the costed local BP specification, and is consumed by the public
global/flat execution story. Plain English: every successful read in the final
trace is still backed by counted flat payload, and the zero-block same-block
case now contributes ordinary BP-code reads rather than disappearing into a
pure branch. Live assumptions: this is a simple whole-BP-code scan for the
tiny/inactive zero-block case, bounded by the existing readiness threshold, not
a tight micro-scan. A skeptical grad student should ask whether the structural
zero-block scan can be shrunk to the exact query window while preserving the
same all-size theorem surface.

2026-07-04 all-size structural route polish: the replacement for a false
total-Ready theorem is now named directly by
`SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorAllSizeStructuralRoute_total`.
It states that the actual all-size interior trace takes exactly one of three
routes: Ready two-level replay, active non-Ready bounded summary scan, or
inactive pure-none. `SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadLegacyInteriorSegmentStatus`
records that legacy interior slots 26 and 27 remain as compatibility names but
are not counted flat payload, and
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead`
is now a public successful-read exclusion anchor. The two-sided RMQ capstone
also has the explicit lower-clause anchor
`SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_lower_bound`,
and `RMQExamples.Concrete` now instantiates `SuccinctClassic.buildPayload_length`,
`SuccinctClassic.queryCosted_exact`, and
`SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory` on `[3, 1, 4, 1, 5]`.
Plain English: the public story now has theorem names for the structural
all-size route, for the precise slots-26-and-27 successful-read exclusion, and for the
lower side of the two-sided capstone. Live assumption: this proves no
successful reads to legacy slots 26 and 27, not the stronger syntactic absence of failed
read events. A skeptical grad student should ask whether those legacy slots can
be deleted entirely after the remaining compatibility lemmas are retired.

2026-07-03 rank/select no-synthetic global-store update: the standalone
compressed/FID rank/select spoke now has
`RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile`,
backed by
`RankSelect.compressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile`.
The theorem keeps the compressed `n + o(n)` family profile, interpreted replay,
one target-independent global payload store, read-store agreement, and
trace-local bounds, and adds that successful trace reads are certified against
the concrete access, rank-target, or select-target component store they came
from. It also proves no synthetic cost-only trace events occur on the
compressed/FID access/rank/select traces. Plain English: the rank/select spoke
now meets the same execution-story hygiene bar as the RMQ capstone: the trace
reads real relabeled payload components and does not hide work in cost-only
markers. Live assumptions: the width theorem is still trace-local, the backing
certificate is at the trace-event/component-store boundary rather than a new
flat byte-offset layout, and word-rank/word-select remain explicit primitive
events. A skeptical grad student should next ask whether this component-backed
global store can be flattened into one counted offset manifest and whether the
trace-local bounds can be replaced by uniform machine-word side conditions.

## Current Paper-Path Note

2026-07-06 digestion pass: the project-wide digest was refreshed as
`digests/PROJECT_DIGESTION_2026_07_06.md` after the store-parametric
whole-query capstone (2026-07-04/05) and the model-adequacy, footprint
containment, paper-surface, and artifact-reproducibility landings
(2026-07-06). Two corrections worth recording at log level. First, the fast
compact-interior path is proved applicable for all `shape.size >= 2^15`
(`concreteBPRelativeRmmInteriorReady_of_size_ge_readyThreshold`); earlier
strategy prose that described the clean path as gated on `2^128` was too
pessimistic and has been corrected — the `2^128` premise survives only in
derived compatibility lemmas. Second, the whole-query footprint is a set of
segments with agreement required at every address inside them, and the new
containment theorem proves all emitted reads stay inside it, so exactness and
the cost bound transfer to any footprint-agreeing supplied store. The former
publishable-work proof gap was the public query-cost bound: `196727` is a
conservative cross-regime sum with sub-threshold scan caps. The integrated
fast-regime theorem now states the smaller bound explicitly:
`SuccinctFinal.concreteBPNativeSuccinctRMQFastRegimeQueryCost = 118` under the
real `2^15` readiness threshold. A skeptical grad student should now ask for
paper/artifact packaging, external novelty calibration, and tighter
machine-word side conditions, not another existence proof for the regime split.

2026-07-07 publication/provenance alignment pass: the publication branch treats
`digests/PROJECT_DIGESTION_2026_07_06.md` as the canonical current public
digest. The coordinator checkout's local
`digests/PROJECT_DIGESTION_2026_07_CURRENT.md` and `ADD_PROVENANCE.md` were
read as branch-local evidence, but this branch keeps only one current public
digest to avoid competing "current state" documents. The new public
`ADD_PROVENANCE.md` records transcript exports as local provenance evidence,
not as committed proof artifacts. Publication wording was tightened: priority
language now waits for a referee-grade novelty search; interpreter-generated
trace claims are scoped to checked constructors and provenance theorems; and
`RAM.Exec` is described as the private-constructor traced substrate, while
first-order/register syntax belongs to `WordRAM.Program` / register programs.

2026-07-08 R2 clean all-size cost pass: the public all-size RMQ cost surface now
has a branch-sensitive theorem,
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_routeSplit`,
plus the fixed corollary
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_cleanAllSize`
and checked equality
`SuccinctFinal.concreteBPNativeSuccinctRMQCleanAllSizeQueryCost_eq = 65585`.
Conceptually, the old `196727` theorem was true but paid for mutually
exclusive routes at once: the zero-block BP-code scan and the interior fallback
scan were added even though a close/LCA query dispatches to only one route.
The new theorem keeps Ready at `118`, active non-Ready at `568`, inactive
non-Ready at `88`, and leaves the zero-block structural scan as the all-size
maximum. Plain English: the public theorem now says "pay for the route you
actually take," with a smaller fixed all-size maximum for paper use. Live
assumption: exact all-size `118` is still false for this construction unless
the zero-block same-block structural replay is replaced by a smaller counted
route. A skeptical grad student should next ask whether the zero-block scan can
be replaced without adding an uncounted answer table or proof-only answer
field.

2026-07-09 R3 zero-block scan tightening: the public route-split theorem now
uses `SuccinctClose.concreteCompactBPCloseZeroBlockRouteScanCost = 4096` for
the zero-block same-block close/LCA leg, backed by
`SuccinctClose.zeroBlockSameBlockCloseCosted_cost_le_routeScanCost_of_blockSize_zero`.
The clean fixed all-size RMQ query equality is now
`SuccinctFinal.concreteBPNativeSuccinctRMQCleanAllSizeQueryCost_eq = 4144`.
Conceptually, the zero-block trace did not change: it still scans counted
chunked BP-code payload words. The proof stopped discarding the machine-word
divisor and uses `shape.size < 2^15` plus
`machineWordBits shape.bpCode.length` to cap the chunk count by `4096`.
Plain English: no new answer table or oracle was added; the same honest scan
now has the tight small-regime word-count bound consumed by the public theorem.
Live assumption: the zero-block branch still scans the full BP-code chunk list,
so exact all-size `118` remains false. A skeptical grad student should next ask
for a charged zero-block interval navigator, or for a theorem showing the
current BP-code-only trace cannot beat the full chunk scan.

## Digestion Tasks

1. Turn the RMQ capstone into a two-page lecture-style proof map:
   lower bound, upper bound, payload model, query model, and nonclaims.
2. Turn the rank/select frontier into a glossary of fixed-weight codes, RRR/FID
   local blocks, route tables, charged reads, the proved log-chunk primary
   budget, split-width table/RAM profile, and the remaining concrete family
   instantiation.
3. Turn the union-find spoke into a sequence of ordinary data-structure
   invariants: parent forest, representative refinement, rank discipline,
   root-mass accounting, path compression, Tarjan-level potentials, and the
   remaining residual/large-credit gap to Tarjan.
4. Maintain a short "assumptions ledger" that can be read aloud before a talk,
   review, or onboarding session: what is model-level, what is executable, what
   is proof-only, and what is not claimed.
