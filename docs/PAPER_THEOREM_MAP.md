# Paper Theorem Map

This is a short citation map for the paper-facing theorem surfaces. The full
inventory remains in `docs/FAMILY_SUMMARY.md`.
For a reviewer-grade table mapping paper claim rows to aliases, source
theorems, source files, and exact commands, see
`PAPER_CLAIM_CORRESPONDENCE.md`.

## Main RMQ Upper Bound

```lean
RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem
RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery
RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery
```

These are the paper-facing ordinary-list theorem, the shorter list-facing
profile, and the construction-facing BP-native Cartesian-shape theorem: exact
leftmost RMQ answers, `2*n + o(n)` payload bits, constant modeled query cost,
and the final flat-payload/no-synthetic execution story.

## Final Trace Model Adequacy

```lean
RMQ.Headlines.succinctRMQFinalTraceModelAdequacy
RMQ.Headlines.succinctRMQFinalTraceModelAdequacyExact
RMQ.Headlines.succinctRMQFinalSuppliedStoreAdequacy
RMQ.Headlines.succinctRMQFinalFullModelSoundness
RMQ.Headlines.succinctRMQFinalFullModelSoundnessExactOfFootprintGlobal
RMQ.Headlines.listIntSuccinctRMQQueryCostedWithStoreEqQueryCostedOfFootprint
RMQ.Headlines.listIntSuccinctRMQFinalFullModelSoundnessExactOfFootprintGlobal
RMQ.Headlines.listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal
RMQ.Headlines.listIntSuccinctRMQFastRegimeFinalFullModelCostLeOfFootprintGlobal
RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreSuccessfulReadsBackedByCountedFlatPayloadOfFootprintGlobal
RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedWithStoreCostLeOfFootprintGlobal
RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceRouteSplitCostedCostLe
RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedCostLe
RMQ.Headlines.succinctRMQFastRegimeGlobalPayloadStoreCostLeOfReadyThreshold
RMQ.Headlines.succinctRMQFastRegimeSuppliedStoreCostLeOfFootprintGlobal
RMQ.Headlines.succinctRMQFastRegimeFinalFullModelCostLeOfFootprintGlobal
```

These are the reviewer-facing anchors for what the modeled constant query
means. They package the existing final trace facts: `Costed` equals
`TraceResult.toCosted`, the trace refines the interpreted whole-query program,
the fixed modeled cost bound holds, trace events are reads or word primitives,
reads match the global store, event data are bounded, no synthetic cost-only
events appear, successful reads are backed by counted flat payload words, and
the supplied-store replay is store-parametric under final-layout footprint
agreement. The full-model packet also records that emitted supplied-store and
canonical reads are inside the safe footprint, and that footprint agreement
with the canonical global store recovers the canonical trace and exact result.
The list-facing aliases expose the same footprint-agreement story at the
ordinary `List Int` surface: the supplied-store query is equal to canonical
`SuccinctClassic.queryCosted`, valid windows erase to the list RMQ answer, and
the all-size plus fast-regime cost bounds transfer. The store/model aliases
expose the direct supplied-store transfer theorems for counted flat-payload
backing and modeled cost under footprint agreement.
The all-size cost aliases now expose a route-split theorem plus the clean fixed
corollary `SuccinctFinal.concreteBPNativeSuccinctRMQCleanAllSizeQueryCost =
65585`; the legacy `196727` aggregate is retained under explicit compatibility
aliases because it sums fallback costs that the structural route takes
mutually exclusively. The fast-regime aliases add the Ready-threshold cost theorem: when
`SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold <= shape.size`, the
same final global trace has modeled cost at most the named constant
`SuccinctFinal.concreteBPNativeSuccinctRMQFastRegimeQueryCost = 118`, and the
same bound transfers to supplied-store/full-model statements under footprint
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

This is the coefficient-correct Catalan/entropy lower-bound slack in doubled
integer form, kept separate from the upper-bound construction. It is not the
Liu-Yu/Liu cell-probe lower bound.

## Non-Claims

The public theorem map does not assert compiled Lean execution performance, compiler
correctness, full CPU semantics, production serialization, or an exact/minimal
dynamic read-set characterization. See `docs/PAPER_MODEL_ADEQUACY.md` for the
model-adequacy scope.
