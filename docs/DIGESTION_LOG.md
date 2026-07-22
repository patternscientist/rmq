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

## U2 Acceptance Digest (2026-07-14)

U2 is accepted at exact target
`4f7ec8be47ecd65b2859a3784fadeab48a629e4e` after coordinator reconstruction
and the fresh blind A04 audit. The accepted route uses one public
`SuccinctClassic.buildPayload`, one exact physical-word representation of that
payload, one supplied-store evaluator with ordered positional reads, and one
occurrence-preserving provenance relation. The same objects reach final model
adequacy, the ordinary `List Int` theorem, `RMQ.Headlines.RMQ`, and `RMQPaper`.

In plain English, the public space theorem and the executable model now talk
about the same represented data. Every successful read is backed by that data;
failed and repeated reads remain in the execution-derived footprint; every
emitted read has an indexed producer receipt; and every counted source has a
successful witness in some valid top-level query. One input-derived word width
bounds the whole physical machine, and the current all-size modeled cap is the
checked transitional constant `328`.

The live boundary remains explicit: modeled ticks are not Lean wall-clock time,
symbolic reachability witnesses are proof-only, and global source liveness does
not mean every query reads every source. A04 found no proof or architecture
defect. Its sole P3 finding was stale comment text describing synthetic
fallback; integration corrected that prose. The next skeptical question is U3:
derive the cleanest explained all-size constant while preserving the accepted
single-payload, supplied-store, footprint, and provenance chain.

## W19 Global-Liveness / Query-Provenance Composition Digest (2026-07-13)

The W19 occurrence and symbolic witness proofs did not change. The repaired
public composition changes what is quantified where. For one current valid
query, indexed provenance follows each actual trace position through the exact
program instruction, folded pre-state, invocation parameters, component-local
position, and trace embedding. Separately, the reviewer-manifest theorem says
each counted source and named shared-BP consumer has some successful valid
whole-query witness. It does not say the current query reads every source.

The split was selected because the source-liveness predicate existentially
chooses its own list and valid query; adding unrelated current-query parameters
and an unused validity premise did not strengthen it and suggested a false
universal liveness claim. The paper theorem now consumes one non-parameterized
manifest packet and keeps trace adequacy and occurrence provenance inside the
current-query validity domain. Native validation still imports only the genuine
`SuccinctRMQClassic` runtime path; proof-only long/sparse witness modules remain
outside executable closure.

The live assumptions are unchanged: modeled WordRAM cost is not compiled Lean
runtime, payload bits remain distinct from proof-only witness data, and `328`
is the checked transitional canonical bound. No current canonical execution
theorem has a `2^128` activation premise. W19's proof-only sparse-local
nonvacuity witness does use symbolic `N = 2^128`; that size is not a route,
payload, cost, runtime, or paper-theorem premise.

A skeptical graduate student should next ask whether the paper statement makes
the two quantifier scopes visually unavoidable, and whether an import guard can
prevent future executables from importing the proof-only witness seam. U3 is
not opened by this repair.

## Current Digests

- [`digests/PROJECT_DIGESTION_CURRENT.md`](digests/PROJECT_DIGESTION_CURRENT.md):
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
`RMQ.Headlines.succinctRMQLegacy196727InterpretedTwoNPlusOConstantQuery`.
Conceptually,
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
`RMQ.Headlines.succinctRMQLegacy196727LeafTraceTwoNPlusOConstantQuery`.
Conceptually, the
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
`RMQ.Headlines.succinctRMQLegacy196727WordTraceTwoNPlusOConstantQuery`.
Conceptually, the
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
`RMQ.Headlines.succinctRMQLegacy196727LargeRegimeWordTraceTwoNPlusOConstantQuery`.
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
`RMQ.Headlines.succinctRMQCompatibilityLargeRegimeGlobalPayloadStoreExecutionStory`.
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

2026-07-10 U2 composed range-store closure: the canonical
`SuccinctClose.canonicalRelativeRmmInteriorDirectory` still instantiates one
all-size two-level hierarchy from `RelativeRmm.canonicalLayout`, but its
reviewer-facing execution and payload trace now come from one physical store.
`canonicalRelativeRmmInteriorComponentStore` concatenates the rechunked
baseline, min-relative, max-relative, arg-offset, local-offset, and global-block
tables in directory-payload order. The corresponding offset record identifies
each segment and the canonical dead address. Its flattening theorem says those
machine words decode exactly to the counted summary/local/global payload.

`canonicalRelativeRmmInteriorRangeMinCostedWithStore` threads one supplied
flat word array through every summary, local, and global read. The decoded
candidates are built only from returned indexed words. Its physical footprint
is an ordered list--including repeated and failed addresses--obtained by
projecting addresses from that same execution's read log. Therefore the
footprint length is definitionally the modeled cost, and the directory's
`payloadWordsRead` field is the successful-word projection of the execution,
not an independently generated witness. Agreement on the first store's actual
footprint determines the full execution, including adaptive later addresses;
consequently it determines result, cost, and the recorded footprint.

On the canonical component store, every successful read address is in range,
the returned word is backed by the counted payload, and its length is at most
the modeled machine width. The capstone
`canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current` connects the
composed execution to the earlier canonical range query. Thus the existing
unconditional exactness theorem and the 240 physical-read bound transfer to
the supplied-store path. `canonicalRelativeRmmInteriorDirectory_profile_allSize`
now includes a `CanonicalRelativeRmmInteriorStoreProfile` packaging flattening,
execution agreement, footprint determinacy, backing, word bounds, footprint
recording, and cost/footprint equality. The earlier generic
`FixedWidthNatTable` machine adapter evidence remains because this composed
execution is now its concrete downstream consumer.

Plain English: U2 now has one counted machine store and one query whose reads
both determine its answer and generate its footprint; there is no second
public directory abstraction with a decorative trace. Live assumptions are
the model-level `Costed` convention that one indexed word read costs one tick,
the proved fixed-width chunk codec, and valid positive range premises for
semantic exactness; a compiled Lean runtime bound is not claimed. CompactReady is
used only for checked legacy agreement. Final close/LCA dispatch, the
zero-block route, and public final-query constants are unchanged. A skeptical
grad student should next ask for this component store and its offsets to become
a segment of the global flat close/LCA store, with the final consumer using
this exact footprint instead of the three-way legacy interior route.
## 2026-07-11 U2 Canonical Reviewer Route Closure

The canonical range store is now consumed all the way through cross-block
close, `lcaClose`, the globally segmented whole-query trace, the supplied-store
replay, model adequacy, and the ordinary `List Int` surface. Segment `20`
serves the six-table concatenated component. Its local address is translated by
`concreteBPNativeSuccinctRMQCanonicalInteriorWordOffset`, and
`concreteBPNativeSuccinctRMQCanonicalInteriorPhysicalAddress` states the
physical reviewer-store address.

The result is not computed semantically and replayed afterward. Endpoint
fringes and the middle candidate are constructed from charged reads; the
canonical interior execution itself generates the ordered dynamic footprint.
Agreement on those addresses determines the adaptive execution, result, trace,
and cost. Successful reads are backed by the counted canonical reviewer payload,
and returned words and translated addresses satisfy the reviewer-native word
bound.

The previous trace-local width was replaced on the reviewer path by
`concreteBPNativeSuccinctRMQCanonicalReviewerWordBits`, derived from input
operands and addressable counted machine words. Empty, singleton, size-two, and
symbolic readiness-boundary cases are checked in the kernel. The all-size
canonical trace is exact, and the honest transitional cost is the named sum
`328`; no decorative reads preserve the obsolete `118` or route-split
story.

Plain English: every input size now follows the same positive canonical
geometry, reads the same counted component representation, and reaches the
paper-facing answer through those reads. Live assumptions remain the explicit
WordRAM read-cost model and mathematical `Nat` arithmetic with proved fit
conditions; there is no compiled-runtime claim. A skeptical graduate student
should next ask U3 to simplify the checked `328` decomposition into the final
paper constant, not whether the old zero-block route is still hiding underneath.

## Current Paper-Path Note

2026-07-06 digestion pass: the project-wide digest was refreshed as
the digest now named `digests/PROJECT_DIGESTION_CURRENT.md` after the store-parametric
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
the digest now named `digests/PROJECT_DIGESTION_CURRENT.md` as the canonical current public
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

## 2026-07-12 W15 Whole-Machine U2 Worker Candidate (Superseded)

The W16 audit found that the earlier uniform-directory milestone still joined
space and execution facts about different objects: the public payload remained
the old list while the canonical interior was an appended sibling, and the
physical theorem covered only segment `20`. W15 replaced that split with one
live public payload and one pre-execution physical word list. The physical list
erases exactly to `SuccinctClassic.buildPayload`, and physical replay refines
the whole logical query with result, modeled cost, ordered trace, failures, and
footprint preserved.

Conceptually, the query is now store-parametric on what it actually reads.
The ordered logical footprint retains repetitions and failed reads; agreement
there determines the complete supplied `TraceResult`. Successful physical reads
are positional reads from the same counted list. A capacity of
`400000 * (n + 1)` bounds the physical representation, and the derived reviewer
word width is at most `20 * (log2 (n + 2) + 1)`. That one width covers stored
and returned words, live/dead/sentinel addresses, segment encodings, and charged
primitive operands/results.

Plain English: there is no longer a counted payload on one side and a more
convenient executable sibling on the other. The answer, trace, and `328` cost
come from reads of the one represented payload. The claims remain about the
formal Word-RAM/model cost, not compiled Lean time or hardware. U3 still owns a
tighter explained constant; M1 may repackage the adequacy facts; neither may be
used to supply missing U2 truth. A skeptical grad student should next ask the
coordinator to reconstruct the frozen matrix at the exact commit and commission
a fresh blind audit. Until then this is worker-candidate evidence, not U2
acceptance.

## 2026-07-13 W17 Genuine Physical Execution Correction

The coordinator rejected W15 because its reviewer-facing physical result was
constructed by mapping an already-computed logical value and trace. Exact
physical-word erasure and the underlying supplied-store proofs were real
progress, but that capstone did not itself compute the answer from a supplied
flat physical store. W17 replaces it with
`concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore`: the
existing supplied-store evaluator runs behind
`concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter`, which performs
checked logical-to-physical address translation and actually reads the caller's
flat store. Canonical flat execution refines logical execution while preserving
decoded result, modeled cost, ordered successes and failures, repeated reads,
and the execution-derived footprint. Agreement on the first execution's
consumed physical footprint determines the entire execution; disagreement at a
consumed address provably changes it.

The same correction makes storage provenance structural rather than
route-descriptive. One exhaustive typed 20-source universe includes canonical
close, proves counted source iff reviewer-live source, gives injective/exclusive
physical regions and complete logical-segment coverage, maps emitted reads to
listed regions, records named consumers with BP code explicitly shared, and
keeps legacy duplicate close/interior storage behind compatibility surfaces.
The list-facing API now has one validity boundary, so empty, reversed, and
out-of-bounds ranges return `none` through canonical, supplied-store, trace,
costed, and reviewer-physical surfaces.

The approved space amendment is also explicit: the public theorem states
`buildPayload.length <= 2*n + overhead n` with `overhead = o(n)`. Exact erasure
of physical words to `buildPayload` remains proved, and no padding is introduced
to manufacture equality. The canonical modeled cap is the uniform `328`; Ready
`118`, route-split `4144`, zero-block, and `196727` remain compatibility/history.

Plain English: changing a physical word that the machine consumes can now
change its execution, which is the missing evidence that the payload is not
decorative. Live assumptions remain the explicit WordRAM cost model,
query-independent reviewer width, and kernel-checked translation/store
theorems; this is not compiled Lean or hardware timing. A skeptical graduate
student should next reconstruct every frozen or formally amended acceptance row
at the pushed exact commit and verify that both remote workflows are green.
Until that coordinator-only step, W17 is corrected worker evidence, not an
accepted U2 declaration.

## 2026-07-13 W17 Semantic Nonvacuity Correction

The follow-up audit found that three individually true-looking surfaces did not
yet compose into the advertised semantics. `ReviewerSource.Live` was `True`,
the public story mixed guarded list execution with unconditional raw adequacy,
and the corruption theorem compared aggregate trace records rather than the
returned answer. The revised acceptance contract adds
`INV-SEMANTIC-NONVACUITY` and reopens those rows explicitly.

Operational liveness now starts from the logical segment/source map and a
`ReviewerReadLeaf` classification tied to the constructors of the actual
closed whole-query program. Every emitted read resolves to a counted/live
source, its segment-derived leaf, a concrete program instruction, and the
expanded `evalGlobalWordTrace` branch. Conversely, every counted source reaches
one of those evaluator branches; the one BP-code source carries checked
segment-0 and segment-19 shared dependencies. Adding a dead candidate, removing
any used source, and forging a consumer label fail three separate checked
properties. In plain English, the payload list cannot prove its own liveness.

The public List story now describes one execution per input. A `ValidRange`
premise is required to extract raw shape-level adequacy. On an invalid input,
the same story instead proves `none` for logical and physical results, empty
logical/physical traces and footprint, zero modeled cost, and the same guarded
result for every supplied flat store. Empty, reversed, and out-of-bounds cases
exercise that packet independently.

Answer provenance is now stated at `.value`. The flat physical result is
definitionally the result of the existing supplied-store evaluator after the
address adapter, and differing translated evaluator values transfer to
differing flat-physical values. A valid singleton query supplies the concrete
nontrivial witness: physical address seven is consumed, removing it changes the
returned answer from `some 0` to `none`, and a trace-preserving mutant that
ignores the supplied return value remains incorrectly at `some 0`. This does
not claim every consumed word is decisive for every query.

Live assumptions remain the closed whole-query program, checked segment and
physical-address maps, the explicit WordRAM cost model, and the public
half-open validity contract. A skeptical graduate student should next inspect
the exact theorem types in the amended matrix and rerun each mutation against
the pushed commit; aggregate record inequality or a hand-written label should
not be accepted as a substitute for these projection and evaluator links.

## 2026-07-13 W18 Producer-Level Reviewer Provenance

The coordinator's W17 audit found a deeper gap than a missing label.  The
emitted-read theorem first classified the event's segment with a functional
segment-to-leaf map and then selected any instruction in the closed program
having that category.  It did not retain the event in that instruction's
actual trace, and it evaluated the category witness at an arbitrary state.
This was especially wrong for later LCA and rank instructions, whose input
registers are created by earlier program steps.  It also hid that segments
`17`--`19` can be read inside LCA as well as by final rank.

W18 introduces `WholeQueryProgram.ProducesEvent`.  Its recursive proof follows
the same `TraceResult.bind` decomposition as program evaluation: a head event
is tied to the current instruction/current state, while a tail event advances
to the value produced by the head instruction.  The relation exposes a prefix
whose actual fold value is exactly the producer's pre-state.  From there,
`ReviewerSource.ProducedReadBy` and `ReviewerProducerReadPath` keep one event
connected to its physical source/region, logical segment, producer leaf, and
concrete select/rank/LCA component trace.  The relational path intentionally
supports multiple producer families for one segment.

Reverse liveness is now constructive: every counted source has an actual
possible attempted read in a concrete component call.  Shared BP is stronger
still: select, rank, and canonical-close each exhibit one event that is both a
BP-source read and a path in that consumer.  The counterfactual adds fresh
segment `21` with the plausible existing `.canonicalClose` label.  It fails
because every real instruction trace proves its read segment is below `21`,
not because a new `Live` predicate was set to `False`.

Plain English: an emitted memory event now comes with a receipt naming the
instruction that made it, the machine state that instruction actually saw,
and the represented payload source it read.  Counted storage is justified by
at least one real callable read path, but the theorem does not claim every
query exercises every source.  The accepted physical store, answer dependency,
invalid-range behavior, `2n + o(n)` payload bound, logarithmic reviewer width,
and modeled cost `328` are unchanged.

Live assumptions are the repository's explicit WordRAM trace/cost semantics,
the concrete closed whole-query program, the checked source/physical-address
maps, and the existing component evaluators.  This is not a compiled-runtime
or hardware-timing statement.  A skeptical graduate student should next ask
whether component-level may-read witnesses ought eventually to be strengthened
to top-level query-reachability witnesses for every source.  That would be a
strictly stronger theorem; it is not needed for the present may-read ownership
contract and should not be confused with the false claim that every query
reads every source.

## 2026-07-13 W19 Occurrence-Level Producer Provenance

W19 replaces the load-bearing W18 event-value membership with an indexed
interpreter decomposition. A receipt begins at `globalTrace[globalPos]?`,
identifies the exact instruction position in the closed program, proves that
instruction's pre-state is the fold of the preceding prefix, retains the same
component-local position, and records
`globalPos = prefixTrace.length + localPos`. `ReviewerReadInvocation` keeps the
actual select index, rank position, or pair of close positions computed by the
instruction. Equal event values therefore do not merge: a checked singleton
regression has identical successful read events at global positions `0` and
`12`, and the generic theorem returns a separate receipt for each position.

Reverse provenance now ends at top level. Every counted source is successfully
read by some actual closed whole-query execution under `ValidRange`; small
witnesses cover sources 1--11 and 20, a symbolic long-super construction covers
12--15, and a symbolic sparse-local construction covers 16--19. The latter two
prove their large arithmetic in Lean rather than treating the reachability
scout's calculations as evidence. Select, rank, and canonical-close shared-BP
consumers also retain their exact leaf in successful closed-valid witnesses.

Positive claim `P` is a successful `some word` instance of
`ReviewerProducerClaim.HasClosedValidOccurrence`. Mutation claim `Q` permits
any `word?` instance of that same relation. They are intentionally not
definitionally equal, and
`ReviewerProducerClaim.hasOperationalProducer_of_successful` checks `P -> Q`.
Fresh segment `21` fails `Q` itself. This removes the W18 mismatch between
component may-read acceptance and stronger arbitrary-state rejection.

The symbolic reachability proofs live in a proof-only final semantic-
provenance adequacy extension and a proof-only `List Int` projection module.
The paper and headline roots import that extension, while the executable
validator and cost harness continue to import the genuine
`SuccinctRMQClassic` execution core. This separation was forced by a checked
native regression: linking the large symbolic witnesses into both executable
roots caused a Windows stack overflow, whereas the exact-base harness passed;
after the proof/runtime split, both W19 executables pass unchanged.

Plain English: every emitted read has a positional receipt for the invocation
that really made it, and every piece of counted storage can be seen succeeding
in a real valid public query. Two identical reads at different moments remain
two obligations. The physical evaluator, one public payload, invalid-range
semantics, logarithmic reviewer width, no-synthetic trace, and checked `328`
bound did not change; U3 was not started.

Live assumptions remain the explicit WordRAM trace/cost semantics, concrete
closed whole-query program, source/address maps, component evaluators, and the
ordinary half-open `ValidRange` contract. The theorem is not a compiled-runtime
claim and does not say every query reads every source. A skeptical graduate
student should next reconstruct the symbolic long/sparse witness arithmetic
and verify that no compatibility may-read or event-value theorem is needed by
the paper main theorem. Coordinator acceptance and the blind exact-commit audit
remain separate from this worker candidate.

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

## 2026-07-14 W21 Principled All-Size Charged-Trace Cost

U3 derives `76` from the accepted U2 execution rather than preserving its
transitional `328` sum. The exact component expression is
`2*select13 + (2*rank4 + 2*endpointFringe4 + interior30) + rank4`. Direct
sparse-exception select costs at most 13 events; two-level rank costs four;
each endpoint fringe costs four. The remaining work was the interior.

The old interior proof treated every fixed-width logical cell as up to eight
physical words, so a summary cost 32, a span 40, two spans 80, and the
six-span route 240. The new proof reads the actual canonical widths. General
relative fields cost at most two words. More importantly, taking a
macro-crossing branch itself proves `macroSize < blockCount`; that structural
fact forces the relative fields to fit in one word without a size-regime
dispatch. Consequently within-macro execution costs at most 18,
adjacent/left-middle at most 20, and the longest cross-macro execution at most
30. Close/LCA is therefore at most 46, and the whole query at most 76.

Plain English: the algorithm and payload did not change. U3 stopped charging
rank as though it were select and stopped charging compact fields as though
each occupied eight words. The new theorem describes the operations the U2
trace actually emits, and a separate theorem says modeled cost is exactly that
trace's length.

The old-to-new slack is checked termwise: selects remove `2*(16-13)=6`, ranks
remove `3*(16-4)=36`, and interior removes `240-30=210`; total slack is 252,
so `328-252=76`. Fringes have no slack. This is a tight compositional cap for
the proved component inequalities. U3 does not prove that one query realizes
all maxima simultaneously or that no correlated global cap below 76 exists.

Live assumptions are the current trace/accounting boundary:
`TraceResult.toCosted` charges trace length and therefore would count a
synthetic compatibility marker if one were present. The separate
`WordRAM.TraceEvent.nonSyntheticWeight` certificate assigns one to actual
emitted `.readWord`, `.wordRank`, and `.wordSelect` values and zero to
`.syntheticCostOnlyPrimitive`. The canonical execution now proves that every
emitted event is genuine, no synthetic event occurs, and only for that
no-synthetic trace the certificate sum equals both trace length and the
`Costed` cost of the same execution. Instruction dispatch, input/register
access, arithmetic,
option/branch control, fixed-width decode, local BP scan, candidate merge,
trace assembly, and validity checking remain documentary uncharged omissions;
they are not a checked parallel instruction vocabulary. The result is not
compiled Lean time, conventional word-RAM complexity, a serialized-payload
query theorem, or preprocessing complexity.

A skeptical graduate student should next ask two different questions. First,
can E1 define richer instruction semantics, simulate this same execution while
charging every controller operation, and preserve a constant bound? Second,
can a coexistence theorem or concrete
witness determine whether 76 is globally minimal rather than merely the best
clean operation-wise cap presently proved? Neither question reopens U3's
charged-trace theorem.

Coordinator reconstruction rejected the first candidate's hand-written
controller-operation vocabulary because no evaluator produced it. The revised
U3 evidence uses the actual `WordRAM.TraceEvent` type only. As a counterfactual
sanity check, the synthetic constructor cannot satisfy the genuine-event
classification, and its occurrence anywhere forces the certificate sum strictly
below trace length. Thus event classification, synthetic exclusion,
non-synthetic certificate weights, trace length, `Costed` cost, and the `76`
cap now describe one checked computation. This is candidate-complete evidence;
blind exact-commit audit
remains coordinator-owned.

## 2026-07-14 W21 Canonical Paper Theorem Topology

The A05 blind audit accepted the operational `76` proof and rejected one
publication-level mismatch: `RMQPaper` still exported six unqualified profiles
for older direct, interpreted, leaf-trace, word-trace, and size-premised query
computations. Those theorems were checked, but they used an older payload/query
pair and a legacy aggregate budget. A paper reader therefore had multiple
plausible answers to "which succinct RMQ capstone is current?"

The correction proves
`concreteBPNativeSuccinctRMQCanonicalReviewerPayload_globalWordTrace_two_sided_profile`.
It combines, in one theorem type, the doubled-Catalan space envelopes, the
canonical reviewer payload at-most bound, exact physical erasure to that
payload, exact valid queries through the canonical global trace, equality of
that trace's `nonSyntheticWeight` sum with its own `Costed.cost`, and the
uniform bound `76`. The paper alias is
`succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`.
`listIntSuccinctRMQPaperMainTheorem` now also contains the checked literal
equality `SuccinctClassic.queryCost = 76`.

The six older profiles were not deleted. They moved out of
`RMQ.Headlines.RMQ` into `RMQ.Headlines.RMQCompatibility`, where their retained
aliases contain `Legacy` or `Compatibility`. `RMQPaper` imports only the
canonical module; the broad `RMQ.Headlines` barrel explicitly imports both.
This is an abstraction boundary around curated citation topology, not an
attempt to hide every transitively available declaration.

Plain English: the paper now has one construction theorem that says which bits
are counted and which trace queries those same bits. The trace certificate,
trace length, modeled cost, exact answer, and number `76` can no longer be
silently paired with a different historical execution through a coequal
headline alias.

Live assumptions are unchanged. The theorem counts the existing charged trace
events only; controller dispatch, arithmetic, branching, decoding, local scans,
merging, preprocessing, compiled runtime, and serialized-payload query
semantics remain outside U3. A skeptical graduate student should next import
`RMQPaper`, inspect the single construction-facing profile type, and verify that
both its physical-erasure clause and every query clause name the canonical
reviewer payload/global trace. A fresh blind exact-commit audit remains the next
acceptance step.

## 2026-07-14 W21 Self-Contained Paper-Topology Closure

Coordinator reconstruction of the first topology checkpoint found two
different forms of incompleteness. Some removed headline spellings still
survived in live documentation, and the construction capstone was described as
containing read-backing and weight/length/cost clauses that were only proved by
nearby theorems. A lexical claim scan did not expose either problem.

The checked type of
`concreteBPNativeSuccinctRMQCanonicalReviewerPayload_globalWordTrace_two_sided_profile`
now contains the whole advertised join. Its physical words erase exactly to the
canonical counted payload; every successful read in the same canonical trace
has an in-bounds translated physical address containing the returned word; the
non-synthetic certificate sum equals that trace's length and the same
`Costed.cost`; the sum is at most `76`; and the existing space envelopes and
exact answers remain conjuncts. This uses the prompt-permitted direct
successful-read backing rather than claiming that a separate execution packet
is literally nested in the theorem.

The compatibility-only W18 event-value and component-may-path projections now
live in `RMQ.Headlines.RMQCompatibility` under explicit `CompatibilityW18`
names. `RMQ.Headlines.RMQ` retains the current indexed-occurrence,
invocation-preserving, successful closed-valid, mutation, and semantic-adequacy
aliases. The algorithm, payload, global trace, `76` proof, and transitional
source theorem are unchanged.

The reusable workflow lesson is structural: public-symbol migration is not a
lexical claim-scan problem. The production topology lint now searches every
tracked text surface for removed spellings, reads prose and fenced inventories,
and generates Lean `#check` files so documentary headline identifiers resolve
under the broad barrel and canonical paper identifiers also resolve under
`RMQPaper`. Mutations reject retired prose, a fenced transitional name, an
invented dead name, a renamed W18 remnant, and a compatibility alias presented
as current; a canonical paper anchor succeeds.

Plain English: a paper reader can now follow one name to one theorem whose type
itself ties the counted payload, successful physical reads, actual trace,
certificate weights, modeled cost, exact answer, and number `76` together.
Frozen history remains readable, but dead or compatibility-only spellings
cannot silently re-enter current paper documentation.

The model boundary is unchanged. Controller dispatch, arithmetic, branching,
decoding, local scans, merging, serialized-payload querying, preprocessing, and
conventional word-RAM time remain outside U3. A skeptical graduate student
should next inspect whether the direct successful-read clause plus exact erasure
is the right reusable simulation premise for E1's richer small-step machine.
Fresh blind exact-commit audit remains coordinator-owned.

## 2026-07-14 W21 Frozen-History Allowance Boundary

Coordinator reconstruction found one remaining policy bypass after the Lean
capstone and canonical/compatibility split were accepted: the topology lint
skipped every file under the digest and audit-report directories, and the
claim policy carried matching broad path allowances. That made directory
placement, rather than an occurrence's checked role, determine whether a
retired paper alias was visible to the gate.

The repaired boundary registers exactly one old-alias line in each of two
immutable June snapshots. Admission requires the exact normalized path, exact
case-sensitive marker-plus-line content, and exactly one occurrence. The marker
is rejected everywhere else. The README-linked July publication digest and all
audit reports are fully scanned and their documentary headline names are
resolved. The strict claim policy uses the same two path-and-line conjunctions;
neither mechanism exempts a directory.

Production mutations now show both sides of the rule: a retired alias in the
current publication digest or an audit report rejects; the registered snapshot
occurrence accepts; the same text at a current path rejects; and casual,
misplaced, malformed, or duplicate markers reject. Every virtual mutation checks
tracked state before and after. Plain English: frozen history is immutable
evidence with a checked address and exact content, not a label that a new claim
can give itself. The accepted algorithm, payload, trace, theorem topology, and
charged-trace-only `76` model boundary are unchanged. A skeptical graduate
student should next rerun the production mutations at the exact candidate
commit and verify that no new snapshot exception can be added without changing
both policy data and its regression. Fresh blind exact-commit audit remains
coordinator-owned.

## 2026-07-15 Canonical Publication Cleanup

The publication prose was rebuilt from the last sound U3 theorem checkpoint
after repeated document-only patches kept rediscovering stale candidate,
route-split, and readiness language. The cleanup retains one undated current
digest and one compatibility-history document, removes process status from the
reader-facing claim surface, and rewrites the trust packets around the actual
payload, physical execution, provenance, exactness, width, and `76`
charged-trace theorem chain.

No Lean theorem, payload, query route, or cost model changed. The key workflow
lesson is that claim scanners are tripwires, not interpreters of English. The
public document set is now reviewed directly against the canonical theorem and
consumer chain; unrelated spoke documents no longer receive copied RMQ
boilerplate. A skeptical reviewer should compare the concise trust packet and
current digest with the checked type of
`succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`, then verify
that the compatibility module is absent from `RMQPaper`.

## 2026-07-15 A06 Editorial Fixed Point

The A06 blind audit found one duplicated July 1 snapshot inside the current
family map and two proof-campaign labels in canonical headline comments. The
duplicate block was removed in full, and the comments now describe stable
semantic interfaces rather than worker phases. No theorem, payload, query
route, trace, or cost model changed.

The paper-topology gate now rejects those two exact classes on the bounded
current reader surface. This keeps development chronology available in the
decision and audit records while ensuring that the public source and family map
read as durable mathematical exposition.

## 2026-07-19 M1-R5 Current-Frontier Reviewer-Native Adequacy Candidate

M1-R5 reconstructs the useful R4 machine-adequacy layer on the repaired current
base without importing its stale theorem bodies. The central object is a
24-field certificate over the current canonical payload, 22 physical sources,
logical segments `0..22`, exact supplied-store execution, ordered footprint,
first-order controller, and reviewer width. A separate 24-field type consumes
each fact by literal projection, and a guarded ordinary-list packet connects
the public query, canonical costed execution, interpreted controller, and exact
supplied physical result.

The conceptual change is dependency, not a new algorithm. The paper theorem
now asks for those guarded objects and directly asks that the same canonical
trace's `nonSyntheticWeight` sum be at most `210`. That field comes from the
current theorem chain ending in the checked principled cost equality, not from
an asserted numeral. Safe layout agreement is still convenient, but its result,
backing, cost, and exactness statements first pass through exact agreement on
the dynamic ordered reads and equality of the complete `TraceResult`.

Plain English: a reviewer can follow one typed packet from the `List Int`
validity guard to the real supplied-store execution and its exact current cost
certificate. Deleting any certificate field, substituting a sibling object, or
weakening the public proposition is meant to break a named consumer rather than
leave an unused wrapper.

The live assumptions remain explicit: payload bits, proof-only certificate
fields, modeled ticks, emitted events, physical allocation, Lean runtime, and
measured performance are distinct categories. The route is word-addressed over
a supplied store. S1 raw `List Bool` decoding/querying, E1 small-step controller
charging, A1 refactoring, V1 artifact freeze, preprocessing, and conventional
word-RAM complexity are outside this rung.

The strongest skeptical graduate-student question is whether the public 210
field is genuinely object-identical and anti-vacuous. The replay answers by
compiling a weakened 211 certificate and paper theorem, then requiring the
independent 210 expected type to reject it; the other 40 reject/one accept cases
probe every field and public link. Coordinator exact-commit reconstruction and
a fresh-blind audit are downstream prerequisites for acceptance.

## 2026-07-20 M1-R5-R1 Safe-Store and Portable-Replay Repair

The rejected M1-R5 result had the right safe-store equality but the wrong
reason for it: read containment depended on the older safe complete-result
theorem, so the later dynamic-store wrapper did not make dynamic agreement
genuinely primary. M1-R5-R1 follows the actual supplied-store program instead.
It proves that every emitted `readWord` event uses a logical segment below
`23`, carries that fact through the safe footprint, converts safe agreement to
agreement on the first execution's ordered reads, and only then applies the
ordered-dynamic complete-result theorem. The guarded list packet and literal
paper theorem now expose the safe corollary, and the independent expected type
pins it.

Plain English: changing memory outside the addresses the query can actually
read cannot change its value, trace, or modeled cost. We now know which
addresses it can read by inspecting the evaluator's select, rank, LCA, fringe,
interior, instruction, and program structure—not by first assuming the two
executions are already equal.

The evidence machinery was repaired at the same boundary. Omitted selection
is distinct from explicitly empty selection; every mutation harness starts
from a genuinely clean repository; Windows owns descendants with a Job Object;
POSIX owns them with a `setsid` process group; output and deadlines are
bounded; and child-spawning sleepers test cleanup. The exact 41 semantic cases
and 16 topology cases are unchanged. The final aggregate gate, rather than a
redundant standalone rerun, owns each full suite once.

Live assumptions remain. The route queries a supplied word-addressed store,
not raw serialized `List Bool` payload bits. Only payload reads are charged in
the current model; bounded instruction dispatch, decoding, arithmetic,
branching, candidate merging, trace assembly, and guards remain uncharged.
The accurate claim is that no input-size-dependent or unbounded event-silent
loop remains. E1 must still charge controller steps explicitly, and S1 must
still connect serialized payload bits to querying.

A skeptical graduate student should ask whether the structural source proof
really covers every callback and both LCA branches, and whether the legacy
safe theorem can slip back into the public chain unnoticed. The focused Lean
builds answer the first question; the load-bearing body checks plus the
`R1LEGACY` mutation answer the second. Native Ubuntu process-group execution,
fresh-blind exact-commit audit, coordinator acceptance, and integration remain
downstream steps.

## 2026-07-20 M1-R5-R2 Normalization-Safe Clean-Baseline Repair

The R1 replay machinery correctly required a clean tracked worktree, clean
untracked state, and clean index, but its shared Git wrapper changed the rules
while observing them: every command forced `core.autocrlf=false`. In a fresh
Windows worktree checked out under the host's `core.autocrlf=true`, ordinary
Git and blob hashing agreed that the tree was clean, while that counterfactual
observer reported broad modifications and stopped the replay before its
selector tests.

R2 changes the observer, not the clean-tree contract. Bounded state queries now
retain the checkout's actual normalization configuration while still disabling
the user-global excludes file so untracked files remain visible. A named
temporary-repository regression commits a newline-bearing LF blob, explicitly
checks it out with `core.autocrlf=true` as CRLF, and runs the production shared
observer. It also reruns the same observer core with the rejected forced-false
prefix to reproduce the false positive, then proves that real tracked,
untracked, and staged/index changes still dirty their respective channels.

The first native Ubuntu replay exposed a second portability assumption in the
same shared boundary. PowerShell discovered both `/usr/bin/git` and `/bin/git`,
and both `/usr/bin/setsid` and `/bin/setsid`; collecting `.Source` therefore
produced an array where the process launcher requires one executable. The
shared helper now collapses application aliases to the first scalar command-
resolution path before either Git observation or POSIX launch. A named
duplicate-alias regression exercises that production resolver, and the native
child-spawning deadline control still uses `setsid` process-group ownership.

Plain English: the gate now asks whether the checkout changed according to the
checkout's own Git rules. It no longer invents a different line-ending policy
for the inspection. That makes a clean Windows checkout portable without
turning the clean-baseline check into a status-only or ignore-differences test.

The live assumptions are unchanged. The replay still requires an initially
clean repository, preserves process-tree ownership and deadlines, and leaves
the 41 semantic cases, A01/A02 topology, 24-field certificate, segment-23
boundary, cost-210 derivation, guarded list packet, and safe-store proof chain
untouched. The fixture's local Git configuration exists only inside its
validated temporary directory.

A skeptical graduate student should next ask whether the exact committed tree
reaches the selector, sleeper, startup, F21, policy, and topology verdicts on
both Windows and native Ubuntu, rather than merely passing a synthetic config
test. The final R3 ledger now answers that question with independently labeled
Windows reconstruction, actual native `setsid` ownership, focused controls,
and the reused byte-identical exact-source aggregate. Coordinator acceptance
and fresh-blind audit are separate.

## 2026-07-21 M1-R5-R3 Durable Portability Evidence

R3 changes no implementation or theorem. It transfers the tested R2 scripts
byte-for-byte from `aa6733c9b958b2b0048d95cb23286f76436d9cff` directly onto
parent `334d22d0c6a3421cd73a95b42a5fa51e73edeff3`, then repairs the committed
matrix and decision evidence that had still described the work as unfinished.
The source proof chain remains actual execution/program/source topology to
direct `segment < 23` containment, safe-to-ordered-dynamic agreement, complete
`TraceResult` equality, current safe alias, guarded list packet, literal paper
theorem, and independent expected-type checker. The compatibility-only legacy
theorem does not return to that chain.

The evidence is now provenance-aware. M1-R5-R3 independently ran the Windows
parser, exact registry, CRLF/selector, focused claim, and A01 controls. It also
ran real Ubuntu 24.04.4 LTS selector, deadline, portability, and topology
portability controls under WSL2. The native route resolved `/usr/bin`/`/bin`
aliases to scalar tools, used `setsid` process-group ownership, classified
positive deadlines, and proved every recorded root and child absent. A first
selector wrapper timeout and a five-second topology PID-receipt failure are
kept as diagnosed scheduling evidence; successful materially revised retries,
not those failures, support closure.

Plain English: the code had already been repaired, but the repository still
told two incompatible stories about whether the repair had been demonstrated.
This commit makes the durable story match the executions without copying chat
claims wholesale or pretending that deterministic POSIX planning is native
execution. The one 3101.473-second aggregate from the byte-identical R2 source
is labeled reused source/semantic coverage; R3 does not rerun the full 41-case
replay, 16-case topology suite, broad Lean build, startup, F21, or expected-type
build merely because evidence prose changed.

Live assumptions are unchanged: the theorem uses the current supplied
word-addressed store and cost model; payload bits, proof-only facts, modeled
ticks, traces, and compiled execution behavior remain distinct;
B7/E1/width/space facts and S1/E1/A1 separation are untouched.
Coordinator reconstruction and the fresh-blind exact-commit audit are
downstream certification, not substitutes
for local evidence.

A skeptical graduate student should next ask whether a fresh auditor, given
only the final commit, can reproduce the direct-parent/one-commit/script-blob
identity and independently obtain the same platform-sensitive verdicts. That
is now the right next question: no local status cell asks for execution already
claimed complete, and the remaining uncertainty belongs to independent audit.

## 2026-07-22 M1-R5-R6 Strict-Design-Closed Wording and Policy Repair

M1-R5-R6 starts again from the clean unpublished construction/governance merge
`d8dccacd6ce4c5a45a9abff71db33d600c2ecaf1`. The terminal R5 worktree is only a
design hint: none of its files, logs, timings, statuses, or native receipts is
candidate evidence. The source facts and the pre-repair production bypass are
reconstructed on this branch.

Two Lean comments now say exactly what the checked declarations already said.
The paper root names the uniform `<= 210` certificate. The reviewer-physical
comment names logical sources `0..22`; this remains compatible with 22 physical
source descriptions because logical sources 0 and 19 share one description.
Declaration-neutral comparison preserves theorem names, types, bodies, proof
terms, imports, executable definitions, and the direct `segment < 23` to safe
store to ordered-dynamic complete-`TraceResult` chain.

The production event-silent policy now classifies a documented zero-remaining
syntax category over both `computation` and `work`, with no path-wide,
same-line-keyword, or pair allowance. The seven former allowance words cannot
change the final strict verdict. Replayable fixtures exercise the actual
production scanner across held-outs, near misses, policy paths, focused
single-file input, drive-qualified absolute input, deadline control, and clean
restoration. The accepted statement remains deliberately narrower: no
input-size-dependent or unbounded event-silent loop remains, while bounded
dispatch, register movement, fixed-width decoding, arithmetic/comparison,
option tests, branching, merging, trace assembly, and guards do remain.

The strict-design obstruction is closed by owning and updating both companion
ledgers. DD-20260722-001 records that the Lean changes are comment alignment,
not a theorem or cost improvement. WDD-20260722-004 records the production
claim-policy boundary without deleting or renumbering WDD-20260722-005 or
WDD-20260722-006. The inherited architecture and lifecycle decisions,
including `ARCH-CONTRACT-NO-ASSUMED-CAPSTONE` and
`STRICT-DESIGN-CHECK-WRITE-SCOPE-CLOSURE`, remain in force.

Plain English: the formal machine story was already stronger than two stale
comments, and the claim scanner had a loophole that a single word could open.
This repair synchronizes the comments and removes that loophole while leaving
the machine construction, cost, payload, trace, and public propositions alone.

Live assumptions are unchanged. The current route queries a supplied
word-addressed store rather than raw serialized payload bits; only payload
reads are charged; bounded controller work remains uncharged; preprocessing
and conventional word-RAM complexity are separate. S1, E1, and A1 therefore
remain distinct obligations.

A skeptical graduate student should ask whether the two Lean files are truly
comment-only, whether every former allowance word fails through the production
final verdict on relative and absolute inputs, and whether real Ubuntu uses a
scalar executable plus `setsid` process-group ownership without survivors.
The R6 matrix records those exact focused checks. Coordinator reconstruction
and a new fresh-blind exact-commit audit remain mandatory downstream; they are
not replaced by this local candidate.

## 2026-07-22 M1-R5-R8 Frozen Matrix Category-Delimiter Repair

M1-R5-R8 starts from exact unpublished governed base
`3bf7b6c8c5c3518760a2000f37d706937c280cca`, whose ordered parents are rejected
source candidate `deb38ee441d30701aa008101a6ec3f38066215a4` and current
governance `f44a09b12dbe7dd14ed395cb69cff142edfc019f`. The source candidate and
its fresh-blind audit remain immutable evidence objects rather than trusted
verdict prose.

A single strict UTF-8 decoder and stable-ID parser reconstructed the exact
matrix blob `008dda141fe1f2c9e5a14eab5debb917b44686cf`. Under the required rule
that every unescaped pipe is a Markdown delimiter even inside a code span, the
negative fixture has 83 unique inherited IDs, 82 eight-cell rows, and one
nine-cell row at `REQ-M1R5R4-CLAIM-POLICY-ALLOWANCE-BYPASS`. Replacing only
that delimiter in memory by inserting one ASCII backslash produces 83 unique
inherited rows and no non-eight-cell row.

The durable repair performs exactly that one-byte insertion. Complete-row
comparison by stable ID leaves 82 inherited rows byte-identical to the rejected
blob and makes the target row equal to its rejected form plus that one
backslash, without changing its requirement, consumer, challenge, evidence
meaning, or status. Four frozen R8 bookkeeping rows bring the matrix to 87
unique eight-cell rows and record the strict-byte, governance, exact-parent,
and immutable-evidence obligations.

Conceptually, nothing about the RMQ machine changes. The inherited R6 content
already meant that the production policy recognized the intended event-silent
category; the broken delimiter only made one evidence row parse into the wrong
number of Markdown cells. Plainly: this repair makes the table say the same
thing in a structurally valid way.

All semantic assumptions and boundaries remain inherited. The direct
`segment < 23` containment to safe-to-dynamic agreement to ordered-dynamic
complete `TraceResult` equality to current safe alias to guarded packet to
literal paper theorem to independent expected-type consumer chain is preserved
by exact non-owned blob identity, not claimed as newly executed evidence. The
same is true of the 24-field certificate, F01-F24/Q01-Q11/P01-P05/C01 registry,
A01/A02 topology, 40-reject/1-accept verdicts, claim-policy fixtures, platform
ownership controls, payload, cost, and public surfaces. Broad Lean, replay,
topology, platform, and aggregate checks are therefore deliberately not
duplicated for this two-document leaf.

No design or workflow decision changes: `M1R2-MATRIX-SCHEMA` already detected
the isolated Markdown escaping defect, while `FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY`
and `NAMED-REGRESSION-REALITY` prescribe its exact reconstruction. A skeptical
graduate student should next ask whether an independent auditor of the final
commit obtains the same 87-ID/eight-cell result, the same one-byte target-row
transformation, and exact base blobs for every non-owned path. Coordinator
reconstruction, a new fresh-blind exact-commit audit, integration, publication,
push, and retirement remain mandatory downstream and are not local R8 evidence.

## 2026-07-22 M1-R5-R9 Exact Frozen Positive Policy Fixture

M1-R5-R9 starts from clean unpublished governed base
`c9375cf83a55c122b27c56a73c6027f36faea643`, whose ordered parents are
immutable rejected R8 candidate `d6796285a3b9d79ebc78422695d196f26449e771`
and current governance `b07fcc5470349f7cdc261f82ee6d8c320c65923e`.
The audit report at `648eebc9e8d66c9e4c509c5875f42a5ccdd747ff`
was read as an untrusted lead. Its prose, timings, status, and verdict did not
substitute for reconstruction from the exact candidate and production script.

Strict UTF-8 parsing found 87 unique inherited eight-cell acceptance rows.
The frozen R4 requirement contains the exact accepted sentence, but fixed-
string search found that sentence nowhere outside matrix/audit evidence. The
production registry instead had 119 ordered unique fixture objects and the
materially different, broader
`m1r5-bounded-event-silent-distinction-accepted` control. All 119 objects and
matching expected IDs were frozen before editing.

The repair preserves every inherited object and adds one distinct committed
fixture immediately after that broader positive:
`m1r5r9-exact-frozen-bounded-event-silent-distinction-accepted`. Its path is
`docs/PAPER_MODEL_ADEQUACY.md`, its expected verdict is acceptance, its term is
`forbidden-unqualified-no-event-silent-computation`, and its text is byte-for-
byte the sentence frozen by the requirement. The aligned expected-ID entry is
inserted at the same position, and only the expected accept count changes from
37 to 38. The resulting registry has 120 unique ordered fixtures, 82 rejects,
38 accepts, and the unchanged 16 context cases.

Both focused controls executed through the production strict scanner rather
than a copied predicate. The exact new positive passed in 5.173 seconds, and
the inherited named unqualified negative
`m1r5-unqualified-no-event-silent-computation-rejected` passed its expected
rejection in 7.296 seconds. Each run first validated the exact 120-object
registry, duplicate/missing/verdict-drift controls, positive subprocess
deadline cleanup, unique `-OnlyCase` selection, and final tracked-state
restoration.

Conceptually, the classifier did not need a new language rule. The missing
piece was durable evidence for the exact positive boundary already frozen by
the contract. WDD-20260722-010 records why the exact control is additive, why
the broader positive must remain, and why weakening the production policy or
using a disposable report-only fixture would be unsound.

Plain English: the repository already accepted the right sentence, but it did
not keep that exact sentence in the replay suite. It now does. The stronger
false sentence saying no event-silent computation remains still rejects, and
the more detailed accurate positive remains as a separate test.

All semantic and machine assumptions remain inherited. The direct
`segment < 23` to safe-to-dynamic agreement to ordered-dynamic complete
`TraceResult` equality to current safe alias to guarded packet to literal paper
theorem to independent expected-type chain is preserved by exact non-owned
blob identity, not claimed as newly executed R9 evidence. The same applies to
the 24-field certificate, F01-F24/Q01-Q11/P01-P05/C01 registry, A01/A02,
selector/deadline/platform ownership code, payload, cost, topology, policy
JSON/Markdown, production scanner, public prose, and Lean declarations.

A skeptical graduate student should next ask whether a fresh-blind auditor of
the immutable R9 commit independently obtains the exact 120-fixture ordering,
both focused verdicts, all 91 eight-cell rows, 87 byte-identical inherited
rows, and exact base blobs for every non-owned path. That reconstruction and
audit, followed by coordinator acceptance and integration, remain downstream;
this local repair does not claim merge, publication, push, or roadmap closure.

## 2026-07-22 M1 Coordinator Acceptance and Integration

The coordinator accepted exact M1 candidate
`977a4df8b5d9e908fe66d012dd242006790ebaf3` after independently auditing the
fresh-blind report committed as
`e7c936d8a070a1db26e87b60c656044ee8a37b56`. The report is the sole-path commit
over exact report base `373026670bc12faa1ec764475f8233c79caf8330`;
its blob is `bc5144abff8d4974799ae285782b67b0669bbb90`, SHA-256
`F22BA4712BB264F9E2AD1D90CD25727136D9557F0A3258D97574CE4C823F7599`,
and length 42,133 bytes.

Coordinator reconstruction used one strict UTF-8 decoder over raw Git blobs.
It found 91 ordered unique eight-cell candidate rows, all first 87 complete
rows byte-identical to R8, the exact four R9 additions, and 91 report
dispositions in the same order with no non-PASS entry. The production-script
delta is exactly one fixture object, one aligned expected ID, and accept count
`37 -> 38`; the inherited broader positive, named negative, classifier, policy,
and every non-owned candidate blob are preserved. The committed report tree
then passed strict claim drift with 1,444 hits and zero failures, strict design
classification against its exact report base, and committed-range
`git diff --check`.

The report's retained Windows and native Ubuntu evidence clones were checked
again at exact candidate tree `c2d42585428743f6fb8730bf1c716ae3b669cf51`
with clean tracked, index, and untracked state. All recorded Windows and Ubuntu
timeout PIDs were absent, as were the native deadline/topology sleeper
patterns. The unchanged aggregate gate, full 41-case semantic replay, full
120-case policy campaign, full topology suite, and broad Lean build were not
repeated: candidate-local and auditor-local focused checks already cover the
only changed fixture/documentary risk, while exact blob identity preserves the
previously certified Lean and process-control implementation.

Exact pre-integration main/governance
`b07fcc5470349f7cdc261f82ee6d8c320c65923e` was a clean ancestor of the report
chain, so integration was a conflict-free fast-forward that preserved the
current governance bytes and included the accepted audit report. No push or
publication occurred. No new failure mode or workflow rule was discovered;
WDD-20260722-010 already records the isolated exact-fixture omission and its
durable production regression.

Conceptually, M1 now closes the supplied-store machine-adequacy rung: the
24-field reviewer-native certificate, direct dynamic-read agreement,
ordered-read complete `TraceResult` equality, safe corollary, guarded packet,
literal paper theorem, and independent expected-type consumer are integrated
on one theorem/object chain. Plainly: the public RMQ result now carries the
reviewer-facing machine certificate and its exact replayable evidence on main,
rather than only on an audited candidate branch.

Lifecycle disposition: M1-R5-R9 is Accepted, Integrated, and archived through
the committed report; its worker and auditor branches/worktrees are retained
pending separately authorized cleanup. The automated M1 watch has no
successor and is retired after this integration record. Local-rung status and
M1 roadmap-node status are both closed. S1 remains the explicitly deferred
serialized-payload rung, and E1 remains an independent sibling; neither should
be misreported as part of this M1 closure.

The live assumptions remain the stated supplied-store model, the charged-event
cost model rather than conventional word-RAM or Lean runtime time, the
Mathlib-free Lean/Std plus `omega` trust boundary, and the half-open leftmost
RMQ semantics. A skeptical graduate student should next ask whether S1 can
connect this accepted supplied-store theorem to a raw serialized payload
without weakening the same-object and returned-value dependencies; that is a
separate deferred architecture task, not residual M1 work.
