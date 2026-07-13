# Final RMQ Model Adequacy
## Canonical U2 Machine Adequacy

The reviewer path uses one pre-execution list,
`concreteBPNativeSuccinctRMQReviewerPhysicalWords`, whose erasure is exactly the
canonical public payload. The segmented logical execution refines to positional
reads from that list while preserving result, cost, ordered trace, failures,
and footprint.

Its query-independent width is
`concreteBPNativeSuccinctRMQReviewerWordBits n = machineWordBits (400000 *
(n + 1))`, not a trace-local post-hoc width. Checked theorems give linear
capacity, `reviewerWordBits n <= 20 * (log2 (n + 2) + 1)`, and bounds for every
stored/returned word, translated live or dead address, segment encoding, query
operand, primitive operand/result, and consumed footprint address.

The interior result is constructed only from indexed supplied-store reads.
`canonicalRelativeRmmInteriorRangeFootprint_recorded` identifies the recorded
footprint with the execution log;
`canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_of_agree` proves
dynamic-footprint determinacy. At whole-query level, agreement on the actual
ordered logical read footprint determines the complete supplied `TraceResult`,
including failures and repeated reads. Successful-read backing and returned-word bounds
are lifted to the canonical reviewer payload and physical store. Empty,
singleton, size-two, and symbolic threshold-boundary cases are kernel checked.

This remains a mathematical Word-RAM/cost model. It is not a compiled Lean
runtime or hardware timing claim.


This note is the reviewer-facing map for the final BP-native succinct RMQ query
model. The Lean anchor is:

```lean
RMQ.Headlines.succinctRMQFinalTraceModelAdequacy
```

It packages existing checked theorem surfaces. It does not introduce a new
algorithm, a new cost model, or a verified CPU/compiler semantics.

## Costed And TraceResult

The public query theorem is stated over `Costed`: it has a value and a modeled
step count. The adequacy packet relates that `Costed` query to a
`WordRAM.TraceResult`:

```lean
concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
  shape left right =
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
      shape left right).toCosted
```

So the modeled step count is the length/cost projection of an explicit event
trace, rather than an opaque aggregate charge.

## Events

Final query events are classified as either:

- `readWord` payload-read events, or
- word-local primitives such as `wordRank` and `wordSelect`.

Word-local primitives model constant-time machine-word operations on already
available words. They are counted events, but they do not read payload memory.

## No Synthetic Cost-Only Events

Earlier migration layers used `TraceResult.ofCosted` to preserve old aggregate
costs while structural traces were still being rebuilt. The final all-size path
has a dedicated theorem that no event is
`TraceEvent.syntheticCostOnlyPrimitive`.

This matters because the final trace is not hiding a query step behind a marker
that has cost but no data provenance.

## Payload Reads

Every read event agrees with the concrete final global read store:

```lean
concreteBPNativeSuccinctRMQGlobalReadStore shape
```

Successful reads are also backed by the counted flat payload layout. The
adequacy packet includes the theorem that a successful read

```lean
WordRAM.TraceEvent.readWord segment index (some word)
```

implies both:

- the segment is counted in the final flat payload, and
- the `(segment, index, word)` read has explicit flat-payload backing evidence.

This is the anti-oracle point: successful query reads must come from counted
payload words, not proof-only fields or a free certificate.

## Bounded Event Data

The trace carries a concrete finite bit width:

```lean
concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
  shape left right
```

Every payload-read address and every natural operand/result exposed by a
word-local primitive fits that width. This is still a model-level bound, not a
claim about a particular hardware instruction set.

## Supplied Stores

The supplied-store replay is anchored by:

```lean
RMQ.Headlines.succinctRMQFinalSuppliedStoreAdequacy
RMQ.Headlines.succinctRMQFinalFullModelSoundness
```

It packages the facts that reads match the caller-provided `WordRAM.ReadStore`,
the concrete global read store instance recovers the canonical final trace and
interpreter refinement, no synthetic cost-only events appear, and agreement on
the final layout footprint gives store-parametricity and equality with the
canonical global trace.

The footprint theorem uses a safe final-layout overapproximation. It is not an
exact dynamic read-set theorem, and it is not claimed to be minimal. The current
full-model packet includes the theorem that every emitted supplied-store and
canonical payload-read event lies inside that safe footprint; exactness then
transfers to any supplied store agreeing with the canonical global store on the
footprint.

## Zero-Block Leaf Guard

One leaf-level supplied-store blemish is disclosed explicitly. The zero-block
same-block supplied-store decoder currently flattens the supplied BP-code words
and checks `bits = shape.bpCode` before returning the canonical structural
answer. On corrupted stores that fail this guard, the leaf may return `none`
rather than decode arbitrary garbage. This is a model boundary and nonclaim, not
a proof bug: the final footprint-agreement theorems state exactness and cost
transfer for stores agreeing with the canonical global store on the declared
footprint.

## The Constant

The current reviewer-route modeled bound is the checked transitional sum
`328`. It is proved by
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional`
and evaluated by
`concreteBPNativeSuccinctRMQCanonicalTransitionalQueryCost_eq`. The sum is
three close-select/final-rank costs plus
`canonicalCompactBPCloseQueryCostWithRankSeed`, whose interior contribution
is the physical 240-read canonical directory cap.

The supplied-store and full-model companions transfer the same `328` bound
under final footprint agreement. The older `118` Ready theorem, route-split
`4144`, and aggregate `196727` survive only as compatibility facts for
pre-canonical execution stories. They are not current reviewer-route claims.
The paper-level claim is that the query is constant in the stated model and
that the model's counted reads are payload-backed. It is not a claim that this
Lean code is production serialization, optimized machine code, or a verified
CPU implementation.

## Non-Claims

The adequacy packet does not prove:

- compiled Lean execution performance;
- a compiler correctness theorem;
- a full CPU or memory hierarchy semantics;
- production-ready serialization;
- an exact or minimal dynamic read-set characterization.
- arbitrary-garbage decoding for corrupted zero-block supplied-store words; the
  zero-block leaf currently guards by checking `bits = shape.bpCode`.

It does prove a model-adequacy bridge: the final query's modeled constant-cost
execution has an explicit trace, explicit counted payload reads, bounded event
data, no synthetic cost-only markers, and exact RMQ semantics through the
existing final exactness theorem:

```lean
RMQ.Headlines.succinctRMQFinalTraceModelAdequacyExact
```
