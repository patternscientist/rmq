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
  exactness, and class/length metadata budget bridges. The global compressed
  FID constructor remains open on route exactness for rank/select and the
  primary block-code budget.
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
fixed-weight primary codes are bounded by the raw bit length plus `o(n)`, which
is a useful accounting sanity check but not the compressed/FID
`log binomial + o(n)` theorem. The live mathematical question is the
enumerative bridge from a product of per-block fixed-weight universes back to
the global fixed-weight universe, plus the charged route-directory construction
that consumes the already-proved sentinel access/rank/select route equations.

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
