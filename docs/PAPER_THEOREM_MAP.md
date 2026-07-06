# Paper Theorem Map

This is a short citation map for the paper-facing theorem surfaces. The full
inventory remains in `docs/FAMILY_SUMMARY.md`.

## Main RMQ Upper Bound

```lean
RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery
RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery
```

These are the reader-facing ordinary-list theorem and the construction-facing
BP-native Cartesian-shape theorem: exact leftmost RMQ answers, `2*n + o(n)`
payload bits, and constant modeled query cost.

## Final Trace Model Adequacy

```lean
RMQ.Headlines.succinctRMQFinalTraceModelAdequacy
RMQ.Headlines.succinctRMQFinalTraceModelAdequacyExact
RMQ.Headlines.succinctRMQFinalSuppliedStoreAdequacy
```

These are the reviewer-facing anchors for what the modeled constant query
means. They package the existing final trace facts: `Costed` equals
`TraceResult.toCosted`, the trace refines the interpreted whole-query program,
the fixed modeled cost bound holds, trace events are reads or word primitives,
reads match the global store, event data are bounded, no synthetic cost-only
events appear, successful reads are backed by counted flat payload words, and
the supplied-store replay is store-parametric under final-layout footprint
agreement.

The footprint is a safe layout overapproximation, not an exact dynamic read-set
claim.

## Flat Payload And No-Synthetic Story

```lean
RMQ.Headlines.succinctRMQFlatPayloadStoreNoSyntheticExecutionStory
RMQ.Headlines.listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory
```

These connect the final global trace to the query-independent counted flat
payload layout and expose the list-facing version of that execution story.

## Lower Bound

```lean
RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack
```

This is the coefficient-correct Catalan lower-bound slack in doubled integer
form, kept separate from the upper-bound construction.

## Non-Claims

The public theorem map does not assert Lean runtime performance, compiler
correctness, full CPU semantics, production serialization, or an exact dynamic
footprint theorem. See `docs/PAPER_MODEL_ADEQUACY.md` for the model-adequacy
scope.
