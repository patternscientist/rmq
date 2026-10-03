# Current Project Digestion: Canonical Succinct RMQ Publication Story

For the V1 reader path and comparison of query and construction models, see
[the V1 guide](../V1_GUIDE.md). The additive lifecycle surface is scoped separately in
[the claims packet](../../artifact/CLAIMS.md); preprocessing exclusions below describe the
query-only results, not an absence of construction theorems from the repository.

**Status.** This is the sole current public project digestion. It describes the
publication-facing RMQ theorem surface. Dated digests are source-history
artifacts, not competing current summaries. When
prose and Lean disagree, the checked Lean proposition is authoritative.

**Canonical proposition.** The canonical reviewer payload and canonical global
trace are joined by
`RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`.
That capstone packages the at-most `2*n + o(n)` payload, its exact
physical-word erasure, direct positional backing for successful reads, exact
valid half-open leftmost RMQ answers, non-synthetic trace accounting, and the
uniform charged-trace bound `210`. Controller operations remain outside the
charged event model, so this is not a conventional word-RAM or Lean runtime
bound. On the exact same canonical trace, the separate strong theorem
`RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` proves
that every emitted event is a payload-word read. A separate accepted theorem,
`RMQ.Headlines.succinctRMQFullyChargedPackedQuery`, charges every primitive
instruction of a different, numeric-memory execution; it is explained in its
own section below and has passed independent audit.

## What The Main Theorem Says

For an ordinary list of integers, preprocessing discards the values and keeps
the shape of the leftmost-minimum Cartesian tree. The shape is represented by
balanced-parentheses bits plus a sublinear auxiliary payload. The paper-facing
list theorem is `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`; it retains
the repository's half-open query contract, rejects invalid or empty ranges,
and returns the leftmost minimum index for every valid range.

The theorem now literally consumes the guarded 24-field reviewer-native
certificate, its independent required-facts projection, and the guarded list
packet. It also states, on that packet's canonical execution, the direct
`nonSyntheticWeight` sum bound `<= 210` and complete supplied-store
`TraceResult` equality under agreement on the first execution's ordered
dynamic reads. A committed 41-case replay deletes every field and mutates the
public composition, with 40 expected rejects and one expected-accept control.
This integrated M1 theorem remains a word-addressed supplied-store theorem; raw
serialized-payload decoding/querying is the separate S1 rung.

The construction-facing capstone and the separate strong event theorem state
six facts about one object and one execution:

1. the auxiliary overhead is `o(n)` and the canonical reviewer payload has
   length at most `2*n + overhead n`;
2. the physical reviewer words flatten exactly to that payload;
3. every successful payload read in the canonical global trace is backed by
   the corresponding in-bounds physical word;
4. every emitted event is `readWord`, proved by
   `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`, and
   no synthetic cost-only marker occurs;
5. the non-synthetic certificate sum equals trace length and the same
   `Costed.cost`, and is at most `210`;
6. erasing the valid-query result gives the reference `scanWindow` answer.

The lower side is packaged beside the upper side through the doubled-Catalan
space envelopes. It is an information-theoretic encoding lower bound, not a
query-time lower bound.

## Why The Number Is About The Actual Trace

The current cost is derived from the operations emitted by the accepted
execution:

```text
2 * select35 + (2 * rank11 + 2 * endpointFringe37 + interior33) + rank11 = 210
```

`TraceResult.toCosted` charges trace length. Independently,
`WordRAM.TraceEvent.nonSyntheticWeight` assigns unit certificate weight to
genuine read/primitive constructors and zero to the synthetic marker. The
canonical execution proves more strongly that all of its events are
`readWord` and that the
marker is absent. The checked certificate sum therefore equals both the trace
length and the modeled cost before the uniform upper bound is applied.

This is proposition-level evidence: the cost theorem, physical backing,
payload bound, and exact answer do not live on sibling executions or merely
adjacent lemmas. They are conjuncts of the construction-facing profile; the
readWord-only fact is a separate theorem quantified over that exact trace, not
a field silently attributed to the profile.

## Supplied Stores, Physical Words, And Provenance

The supplied-store evaluator reads a caller-provided store. Agreement with the
canonical store on the checked footprint preserves the complete result and
trace, and every successful supplied-store read remains backed by the canonical
reviewer payload. The physical evaluator translates component reads into the
single pre-execution reviewer word list; flattening those words yields exactly
the public payload.

The safe checked footprint is an overapproximation. Its equality theorem first
derives agreement on the canonical execution's ordered dynamic read footprint,
then applies exact complete-result determinism; value and cost equalities are
projections of that same `TraceResult` equality rather than sibling proofs.

Occurrence-level provenance retains the global trace position, program
instruction occurrence, prefix-folded pre-state, component-local position,
invocation parameters, source, and multiplicity-preserving offset. Separate
existential nonvacuity theorems show that every counted source is exercised by
some valid closed execution. These facts do not turn proof-only data into
payload and do not make every source active on every query.

## The Cost-Model Boundary

The charged events on the accepted route are attempted payload-word reads. The
charged-trace theorem does not charge instruction dispatch, input or register
access, option tests, branching, arithmetic, decoding, local scanning,
candidate merging, trace assembly, or the public validity guard. That theorem
also does not prove:

- compiled Lean wall-clock performance;
- a serialized-payload API with a controller whose every step is charged;
- preprocessing time inside the same machine;
- conventional word-RAM complexity for every controller operation of its own
  execution; or
- global minimality of the constant `210`.

Those remain true of the charged-trace theorem, and they do not weaken the
checked statement inside its explicit model. Charging every controller
operation is now addressed separately, for a different execution, by the
accepted construction in the next section. Neither query theorem includes
preprocessing; the additive lifecycle model now supplies that separate route.

## The Separate Accepted Primitive Machine

**What changed conceptually.** The theorems above count charged payload reads
on a logical trace and leave the controller's own work free. The accepted construction
`RMQ.Headlines.succinctRMQFullyChargedPackedQuery` counts that work too, for a
different execution. Preprocessing builds one numeric memory, `buildMemory xs`:
174 metadata words that serialize the sizes, widths and layout descriptors of
the shape, followed by the existing packed allocation of the payload, densely
repacked into words of `w(n)` bits with
`log2(n+2)+1 <= w(n) <= 192*(log2(n+2)+1)`. One closed program of 837,572
primitive instructions, the same for every list and every size, answers
queries on that memory. Its instructions are ordinary register-machine steps
(load, constant, move, arithmetic, comparison, jump, register jump,
branch-if-zero and halt), and each executed instruction costs one step.

**What it means in plain English.** For every list and every pair of
endpoints that fit in a machine word, running that fixed program on that
memory halts within at most 837,572 steps and returns the leftmost minimum of
every valid range, as proved by
`RMQ.Headlines.succinctRMQFullyChargedPackedQuery`; invalid ranges are
rejected before any memory read. The memory, the program text and the
registers together take `2n + o(n)` bits. The number 837,572 is simply the
length of the program: the program is loop-free, so no run can take more
steps than it has instructions, and the committed valid-query fixtures take
6,003 to 16,358 steps. On a valid range the loads the machine performs are
exactly the metadata loads followed by the logical reads of the charged-trace
execution, each turned into one or two physical loads, so the new machine
reads what the logical analysis says it reads.

**Live assumptions.** Multiplication, division, remainder, variable shifts
and bitwise operations cost one step each, an arithmetic word-RAM convention.
Every executed operation is proved not to overflow, underflow, divide by zero
or shift by the word width or more, so the natural-number evaluator agrees
with `w(n)`-bit arithmetic. Endpoints outside the word domain are rejected by
an uncharged value-level check, and no instruction bound is claimed for
parsing them. The code and scratch storage is roughly 1.68 to 4.2 million
words; it exceeds `n` for every `n` below about `2^28`, so the `2n + o(n)`
statement absorbs it only asymptotically. Preprocessing time and space are
unbounded and unclaimed, and Lean runtime is separate from the model. The
status is ACCEPTED: the theorem is kernel checked and consumed by an
independent typed client, and the committed replay campaign, the aggregate
gate and a fresh blind source audit with its tooling correction review have passed.

**Reusable proof ideas.**

- Loop-free compilation. Structured source with statically expanded,
  proved-bounded repetition compiles to forward-jump code, so the step budget
  is the program length and needs no loop analysis.
- Serialized geometry. Size and shape parameters live in a counted metadata
  prefix that the program loads, instead of in code specialized to `n`; the
  code stays uniform and the metadata is charged as data.
- Dense repacking at a wider word. The existing cells are re-chunked into
  wider words, so only a lower-order header and rounding are added and the
  leading `2n` coefficient survives.
- Generic evaluation boundaries and register write frames. Proofs compose
  hundreds of thousands of instructions through block-level lemmas, so the
  kernel never unfolds the whole program.
- Constructor-complete static field maxima. One maximum over every encoded
  field of every instruction, dormant branch arms included, bounds all
  operands without enumerating executions.
- Proved absence of overflow. Excluding overflow, underflow, zero division
  and oversized shifts on every executed transition makes natural-number
  arithmetic equal to `w(n)`-bit arithmetic, so no wraparound convention is
  left unstated.

**What a skeptical graduate student should inspect next.** Whether the
837,572 budget of `RMQ.Headlines.succinctRMQFullyChargedPackedQuery` is a
meaningful constant or only the program length (it is only the length, far
above observed runs, and no path-sensitive bound is proved); whether the
unit-cost multiplication, division and shift convention matches the word-RAM
they have in mind; whether the uncharged outer word-domain check hides work
(it compares the two endpoints with `2^w(n)`, and that comparison is not
charged); how large `n` must be before the code and scratch term is genuinely
lower order; whether the typed client really fails when any certificate field
is weakened, which the committed replay campaign is meant to show; and
how the separate lifecycle construction and reusable-query theorem connects
to this query-only interface and its distinct execution model.

## Publication Topology

`RMQPaper.lean` imports only `RMQ.Headlines.RMQ`. The canonical headline module
contains the current construction, list, adequacy, store, provenance, and cost
aliases, and also the accepted primitive-machine alias described above.
Historical query profiles and old cost/regime companions remain
checked through the separately named `RMQ.Headlines.RMQCompatibility` module,
which is available from the broad `RMQ.Headlines` barrel but is not imported by
the paper root.

The historical public identity `canonicalTransitionalQueryCost = 328` is
literal-pinned. The live raw-expression compatibility constant is separately
named `liveCompatibilityQueryCost = 352`; neither replaces the paper-facing
`210` theorem.

Detailed chronology is quarantined in
[`SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md`](SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md).
## How To Check The Claim

The shortest paper-facing checks are:

```powershell
lake build RMQPaper
lake env lean scripts/headline_axiom_check.lean
powershell -ExecutionPolicy Bypass -File scripts/paper_topology_lint.ps1
powershell -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict
```

The full repository acceptance command is:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/gate.ps1
```

The gate includes the committed packed-query replay,
`scripts/packed_query_replay.ps1`, which needs a clean committed tree.

The topology and claim checks are tripwires for stale names and known wording
hazards. They do not establish the meaning of surrounding English; that still
requires theorem-directed review.
