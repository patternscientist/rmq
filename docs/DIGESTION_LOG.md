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
- what the work just done now means in plain English;
- what assumptions are live, especially payload bits, proof-only fields,
  charged reads, and Lean runtime nonclaims;
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
  `n + o(n)` constant-query profile, plus an active compressed/FID fixed-weight
  route/class-length construction path. The latest digested chunk-route layer
  gives concrete fixed-size chunks, a sentinel fallback block, access-route
  exactness, class/length metadata budget bridges, the log-chunk primary
  block-code budget, and a specialized log-chunk route/class-length envelope
  profile together with a no-inhabitant theorem for that computed-RRR envelope
  under fixed local query cost. The replacement shared-table table/RAM
  route-directory envelope now exists, has a conditional compressed/FID public
  bridge, and has a log-chunk specialization that consumes the primary
  block-code budget. A route-field-table adapter feeds the existing
  payload-backed route tables into that envelope. The split-width table/RAM
  repair now separates global route-field width from local class/length width
  and has its own log-chunk profile consuming the primary budget. The global
  constructor remains open because dense log-chunk decoder tables are formally
  not `o(n)`; the old single-width route/class metadata design is also formally
  ruled out when class/length fields are padded to route width.
- Union-find: a finite partition specification, costed reference operations,
  a parent-pointer forest refinement, union-by-rank/root-mass/rank-power
  invariants, full-compression find refinement, rank-gap/log-rank amortized
  checkpoints, explicit rank-bucket-width accounting, and a local/global
  rank-slack compression-drop kernel. The Tarjan inverse-Ackermann theorem
  remains open.

## Current Digests

- [`digests/RMQ_PROOF_MAP.md`](digests/RMQ_PROOF_MAP.md): index and shared
  assumptions ledger for the digest layer.
- [`digests/COORDINATOR_COMPLETION_LOG.md`](digests/COORDINATOR_COMPLETION_LOG.md):
  time-stamped coordinator completion reports in the proof-digestion format.
- [`digests/RMQ_CAPSTONE.md`](digests/RMQ_CAPSTONE.md): classroom proof map
  for the stable RMQ capstone.
- [`digests/RANK_SELECT_FID_FRONTIER.md`](digests/RANK_SELECT_FID_FRONTIER.md):
  rank/select FID frontier after the chunk-route milestone.
- [`digests/UNION_FIND_AMORTIZATION_FRONTIER.md`](digests/UNION_FIND_AMORTIZATION_FRONTIER.md):
  union-find amortization frontier around rank-gap, rank-bucket, and
  rank-slack potential checkpoints.

## Current Rank/Select Note

The fixed-weight compressed/FID spoke now separates three issues that were easy
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

## Digestion Tasks

1. Turn the RMQ capstone into a two-page lecture-style proof map:
   lower bound, upper bound, payload model, query model, and nonclaims.
2. Turn the rank/select frontier into a glossary of fixed-weight codes, RRR/FID
   local blocks, route tables, charged reads, and the remaining primary-budget
   theorem.
3. Turn the union-find spoke into a sequence of ordinary data-structure
   invariants: parent forest, representative refinement, rank discipline,
   root-mass accounting, path compression, and the gap to Tarjan.
4. Maintain a short "assumptions ledger" that can be read aloud before a talk,
   review, or onboarding session: what is model-level, what is executable, what
   is proof-only, and what is not claimed.
