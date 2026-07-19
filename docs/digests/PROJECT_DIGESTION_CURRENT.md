# Current Project Digestion: Canonical Succinct RMQ Publication Story

**Status.** This is the sole current public project digestion. It describes the
publication-facing RMQ theorem surface. Dated digests are source-history
artifacts, not competing current summaries. When
prose and Lean disagree, the checked Lean proposition is authoritative.

**Canonical proposition.** The canonical reviewer payload and canonical global
trace are joined by
`RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`.
The same checked theorem packages the at-most `2*n + o(n)` payload, its exact
physical-word erasure, direct positional backing for successful reads, exact
valid half-open leftmost RMQ answers, non-synthetic trace accounting, and the
uniform charged-trace bound `210`. Controller operations remain outside the
charged event model, so this is not a conventional word-RAM or Lean runtime
bound.

## What The Main Theorem Says

For an ordinary list of integers, preprocessing discards the values and keeps
the shape of the leftmost-minimum Cartesian tree. The shape is represented by
balanced-parentheses bits plus a sublinear auxiliary payload. The paper-facing
list theorem is `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`; it retains
the repository's half-open query contract, rejects invalid or empty ranges,
and returns the leftmost minimum index for every valid range.

The construction-facing theorem states six facts about one object and one
execution:

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
adjacent lemmas. They are conjuncts of the same construction-facing profile.

## Supplied Stores, Physical Words, And Provenance

The supplied-store evaluator reads a caller-provided store. Agreement with the
canonical store on the checked footprint preserves the complete result and
trace, and every successful supplied-store read remains backed by the canonical
reviewer payload. The physical evaluator translates component reads into the
single pre-execution reviewer word list; flattening those words yields exactly
the public payload.

Occurrence-level provenance retains the global trace position, program
instruction occurrence, prefix-folded pre-state, component-local position,
invocation parameters, source, and multiplicity-preserving offset. Separate
existential nonvacuity theorems show that every counted source is exercised by
some valid closed execution. These facts do not turn proof-only data into
payload and do not make every source active on every query.

## The Cost-Model Boundary

The charged events on the accepted route are attempted payload-word reads. The
theorem does not charge instruction dispatch, input or register
access, option tests, branching, arithmetic, decoding, local scanning,
candidate merging, trace assembly, or the public validity guard. The current
Lean theorem also does not prove:

- compiled Lean wall-clock performance;
- a serialized-payload API with a fully charged controller;
- preprocessing time inside the same machine;
- conventional word-RAM complexity for every controller operation; or
- global minimality of the constant `210`.

Those are downstream machine-model or engineering obligations. They do not
weaken the checked statement inside the explicit charged-trace model.

## Publication Topology

`RMQPaper.lean` imports only `RMQ.Headlines.RMQ`. The canonical headline module
contains the current construction, list, adequacy, store, provenance, and cost
aliases. Historical query profiles and old cost/regime companions remain
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

The topology and claim checks are tripwires for stale names and known wording
hazards. They do not establish the meaning of surrounding English; that still
requires theorem-directed review.
