# Final RMQ Model Adequacy

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

The current fixed modeled query-cost bound is `65585`. This is a checked model
constant, not execution-performance evidence. It is the fixed corollary of the
route-split all-size theorem: Ready costs `118`, active non-Ready costs `568`,
inactive non-Ready costs `88`, and the zero-block BP-code scan is the maximum.
The old `196727` aggregate remains checked as a legacy compatibility theorem,
but it is no longer the paper-facing all-size cost alias. There is still a
separate fast-regime cost theorem for the same final global trace:
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_of_size_ge_readyThreshold`.
Under `SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold <= shape.size`,
it uses Ready interior cost `30` and proves
`SuccinctFinal.concreteBPNativeSuccinctRMQFastRegimeQueryCost = 118`, excluding
the zero-block same-block scan and active non-Ready bounded interior scan. The
supplied-store/full-model companions transfer this fast bound under the same
final-layout footprint agreement. The older `2^128` premise is only a
compatibility/large-regime strengthening, not the current explanation for
readiness.

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
