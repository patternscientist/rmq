# Word-RAM Review Packet

This packet isolates the current machine-model claim from stronger runtime or
compiler claims. The canonical RMQ result uses a traced payload-access model
with checked storage, provenance, and width properties. It is deliberately not
presented as a complete conventional word-RAM semantics.

## Machine Objects

`RMQ.Core.WordRAM` supplies the first-order payload-read and word-primitive
substrate used by the query components. A `TraceResult` contains a value and an
ordered event list; `TraceResult.toCosted` assigns cost equal to the event-list
length.

The canonical whole-query trace emits only:

- `readWord` for an attempted indexed payload-word read;
- `wordRank` for a word-local rank primitive; and
- `wordSelect` for a word-local select primitive.

The compatibility constructor `syntheticCostOnlyPrimitive` exists in the trace
datatype, but the canonical execution proves that it is absent.

## Canonical Physical Store

The reviewer route has one pre-execution physical word list. Its component
regions have checked offsets, and flattening the list recovers exactly the
public `SuccinctClassic.buildPayload`. The physical supplied-store adapter
translates logical component addresses into this list; it does not append an
uncounted execution payload.

For the physical execution, the checked surface provides:

- refinement to the canonical logical execution;
- preservation of value, cost, event order, failures, repetitions, and
  footprint;
- successful-read backing by an in-bounds physical word;
- complete-execution equality under agreement on the consumed ordered
  footprint; and
- value-level sensitivity to a consumed decisive-word change.

## Operational Provenance

Every indexed read occurrence can be followed from the global trace to its
producing instruction occurrence and prefix-folded state, then to its
component-local occurrence, invocation parameters, source, and global offset.
The source manifest is exhaustive for the canonical payload. Separate
nonvacuity theorems witness every counted source and shared-BP consumer in some
valid closed whole-query execution, while a fresh unused segment is rejected
by the same operational relation.

This is stronger than event-value membership or a category-only label: the
evidence is attached to the indexed occurrence that was actually emitted.

## Width Discipline

The query-independent reviewer capacity is linear in input size, and its
derived word width has a checked logarithmic upper bound. The same bound covers:

- every stored and returned physical word;
- translated live and sentinel addresses;
- segment encodings;
- query indices;
- word-rank/select operands and results; and
- every address in the consumed physical footprint.

Arithmetic in the present register layer is mathematical `Nat` arithmetic with
explicit fit/no-overflow side conditions. It is not implicit machine-word
wraparound.

## Cost Theorem

The canonical component cap is:

```text
2 * select13 + (2 * rank4 + 2 * endpointFringe4 + interior30) + rank4 = 76
```

The same execution proves:

1. every emitted event is `readWord`, `wordRank`, or `wordSelect`;
2. the synthetic marker is absent;
3. the `nonSyntheticWeight` sum equals event-list length;
4. that sum equals the same execution's `Costed.cost`; and
5. the sum is at most `76`.

The construction-facing theorem
`RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`
joins these facts to payload size, physical erasure, read backing, and exact
query semantics.

## Uncharged Boundary

The event language does not currently charge controller dispatch,
input/register access, option tests, arithmetic, branches, fixed-width decode,
local BP scans, candidate merges, trace assembly, or the public validity guard.
The checked `76` result is therefore a charged-trace theorem. It is not a claim
about compiled Lean time or a complete conventional word-RAM instruction
count.

The next machine-level strengthening should define a compact small-step
controller semantics and prove that it simulates this same payload-backed
execution while charging those operations. That extension should refine the
current theorem rather than create a sibling query algorithm.

## Compatibility

Older readiness, route-split, large-regime, zero-block, and transitional cost
theorems remain available only through the compatibility surface. Their exact
chronology is in
[`digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md`](digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md).
They are not premises of the canonical reviewer route.

## Checks

```powershell
lake build RMQPaper
lake env lean scripts/wordram_axiom_check.lean
lake env lean scripts/headline_axiom_check.lean
lake exe rmq_succinct_classic_cost_harness
powershell -ExecutionPolicy Bypass -File scripts/review_wordram.ps1
```

The cost harness reports model events, not wall-clock benchmarks. The axiom
inventories and review script are curated regression checks; the theorem types
remain the authoritative evidence.
