# Final RMQ Model Adequacy
## Canonical U2 Machine Adequacy

The reviewer path uses one pre-execution list,
`concreteBPNativeSuccinctRMQReviewerPhysicalWords`, whose erasure is exactly the
canonical public payload. It is assembled from one exhaustive typed 20-source
universe that includes canonical close. For every indexed read, W19 retains the
same global position, closed-program instruction occurrence, state obtained by
folding the exact preceding prefix, component-local position, exact invocation
parameters, physical source, region, and logical segment. Every counted source
and exact shared-BP consumer has a successful occurrence through an actual
closed whole-query execution under a valid ordinary `List Int` query.
The manifest also proves exclusive source regions, complete logical-segment
coverage, and exclusion of legacy duplicate close/interior sources.

W19 deliberately uses two differently quantified packets. The parameterized
`ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy shape left right` retains
indexed forward provenance for that exact query. The proof-only,
non-parameterized
`ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy` states global
reviewer-manifest facts: each counted source and shared-BP consumer has some
closed valid execution witness, successful predicate `P` implies mutation
predicate `Q`, and fresh segment 21 fails `Q`. The paper theorem consumes that
global packet once, not underneath a current-query `ValidRange` premise.
`SuccinctRMQClassicProvenance.lean` is only the proof-import seam. This split
keeps symbolic witness construction out of the native validator link closure;
it does not replace or alter the genuine `SuccinctRMQClassic` execution checked
by the validator and cost harness.

A counterfactual fresh segment `21` with the plausible existing
`canonicalClose` label has no witness under the same common closed-valid-
occurrence relation. The positive predicate existentially requires `some word`;
the mutation predicate permits any `word?`, and
`ReviewerProducerClaim.hasOperationalProducer_of_successful` is the checked
`P -> Q` bridge. W18 event-value and component may-read theorems remain
compatibility facts and do not carry this reviewer claim.

The existing supplied-store evaluator is run through
`concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter`, which actually reads
the caller's flat store at checked translated physical addresses. Canonical
flat-physical execution refines the logical execution while preserving decoded
result, modeled cost, ordered successful and failed reads, repeated reads, and
the execution-derived physical footprint.

Its query-independent width is
`concreteBPNativeSuccinctRMQReviewerWordBits n = machineWordBits (400000 *
(n + 1))`, not a trace-local post-hoc width. Checked theorems give linear
capacity, `reviewerWordBits n <= 20 * (log2 (n + 2) + 1)`, and bounds for every
stored/returned word, translated live or dead address, segment encoding, query
operand, primitive operand/result, and consumed footprint address.

At whole-query level,
`concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint_recorded` identifies
the physical footprint with the execution's ordered read projection. Agreement
on the first execution's consumed ordered physical footprint determines the
complete physical `TraceResult`, including failures and repeated reads. The
checked theorem
`concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator`
identifies the physical answer with the translated supplied-store evaluator at
`.value`; a decisive singleton corruption changes the real answer from
`some 0` to `none`, while the value-ignore mutant retains stale `some 0`.
Successful-read backing and returned-word bounds are
lifted to the canonical reviewer payload and physical store. Empty, singleton,
size-two, and symbolic threshold-boundary cases are kernel checked.

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

The logical supplied-store packet also retains a safe final-layout
overapproximation; that auxiliary footprint is not claimed minimal. In
contrast, the reviewer flat-physical footprint is execution-derived and is
exactly the read projection consumed by that execution. The current
full-model packet includes the theorem that every emitted supplied-store and
canonical payload-read event lies inside that safe footprint; exactness then
transfers to any supplied store agreeing with the canonical global store on the
footprint.

## Compatibility-Only Zero-Block Leaf Guard

One compatibility leaf-level supplied-store blemish is disclosed explicitly.
The zero-block
same-block supplied-store decoder currently flattens the supplied BP-code words
and checks `bits = shape.bpCode` before returning the canonical structural
answer. On corrupted stores that fail this guard, the leaf may return `none`
rather than decode arbitrary garbage. This is a model boundary and nonclaim, not
a proof bug. This leaf is not reachable from the uniform canonical reviewer
route; it remains only on compatibility/history surfaces.

## The Constant

The current reviewer-route modeled bound is the principled charged-trace sum
`76`. It is proved by
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace`
and evaluated by
`concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`. The sum is
`2*select13 + (2*rank4 + 2*fringe4 + interior30) + rank4`.
`...cost_eq_trace_length` ties the modeled cost to the emitted trace. The
transitional `328` theorem remains for U2 comparison.

The supplied-store and full-model companions transfer the same `76` bound
under final footprint agreement. The older `118` Ready theorem, route-split
`4144`, and aggregate `196727` survive only as compatibility facts for
pre-canonical execution stories. They are not current reviewer-route claims.
The paper-level claim is that the query is constant in the stated model and
that the model's counted reads are payload-backed. It is not a claim that this
Lean code is production serialization, optimized machine code, or a verified
CPU implementation.

Currently charged operations are attempted payload-word reads and word-rank /
word-select primitives. The named E1 inventory assigns zero weight to
instruction dispatch, inputs/registers, arithmetic, option tests, branching,
fixed-width decode, local BP scan, candidate merge, trace assembly, and the
validity guard. U3 therefore does not prove conventional word-RAM complexity.

## Non-Claims

The adequacy packet does not prove:

- compiled Lean execution performance;
- a compiler correctness theorem;
- a full CPU or memory hierarchy semantics;
- production-ready serialization;
- minimality of the auxiliary safe logical layout footprint (the reviewer
  flat-physical footprint itself is execution-derived and recorded exactly);
- arbitrary-garbage decoding for corrupted zero-block supplied-store words; the
  zero-block leaf currently guards by checking `bits = shape.bpCode`.

It does prove a model-adequacy bridge: the final query's modeled constant-cost
execution has an explicit trace, explicit counted payload reads, bounded event
data, no synthetic cost-only markers, and exact RMQ semantics through the
existing final exactness theorem:

```lean
RMQ.Headlines.succinctRMQFinalTraceModelAdequacyExact
```
