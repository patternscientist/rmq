# Paper Theorem Map
## Canonical U2 Reviewer Route

The current paper route is uniform for every size. Its primary anchors are:

```lean
RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCanonicalTransitionalCostedCostLe
RMQ.Headlines.succinctRMQCanonicalTransitionalQueryCostEq
RMQ.Headlines.succinctRMQCanonicalTransitionalFinalFullModelCostLeOfFootprintGlobal
RMQ.Headlines.listIntSuccinctRMQCanonicalTransitionalFinalFullModelCostLeOfFootprintGlobal
RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreSuccessfulReadsBackedByCanonicalReviewerPayloadOfFootprintGlobal
RMQ.Headlines.succinctRMQReviewerPhysicalWordsErasePublicPayload
RMQ.Headlines.succinctRMQReviewerPhysicalExecutionRefinesLogical
RMQ.Headlines.succinctRMQReviewerPhysicalFootprintRecorded
RMQ.Headlines.succinctRMQReviewerPhysicalStoreAdapter
RMQ.Headlines.succinctRMQReviewerPhysicalExecutionEqOfOrderedFootprint
RMQ.Headlines.succinctRMQReviewerPhysicalValueFromSuppliedStore
RMQ.Headlines.succinctRMQReviewerPhysicalValueDependency
RMQ.Headlines.succinctRMQReviewerEveryReadOccurrenceProvenance
RMQ.Headlines.succinctRMQReviewerCountedSourceSuccessfulClosedValidOccurrence
RMQ.Headlines.succinctRMQReviewerSharedBPConsumerSuccessfulClosedValidOccurrence
RMQ.Headlines.succinctRMQReviewerSuccessfulOccurrenceImpliesOperationalProducer
RMQ.Headlines.succinctRMQReviewerFreshUnusedSourceNoProducer
RMQ.Headlines.succinctRMQReviewerManifestSemanticAdequacy
RMQ.Headlines.listIntSuccinctRMQRawAdequacyOfValid
RMQ.Headlines.succinctRMQReviewerPhysicalWordsFitLinearCapacity
RMQ.Headlines.succinctRMQReviewerWordBitsLogarithmic
RMQ.Headlines.succinctRMQReviewerPhysicalWordFits
RMQ.Headlines.succinctRMQReviewerSuccessfulReadWordFits
RMQ.Headlines.succinctRMQReviewerPhysicalFootprintAddressFits
RMQ.Headlines.listIntSuccinctRMQQueryCostedInvalid
```

The final trace refines
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted`
and is exact by
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_exact`.
Its one typed 20-source manifest includes canonical close and covers every
read-producing segment. For each indexed read, W19 retains the global
occurrence, program instruction occurrence, folded state, component-local
occurrence, exact invocation parameters, source, and composed-trace offset.
The query-independent manifest packet states that every counted source and
exact shared-BP consumer has some successful actual closed-valid query witness.
A checked bridge maps the successful positive predicate into the mutation-side
arbitrary-result predicate, and fresh segment 21 fails that common relation.
It is consumed once outside the paper theorem's current-query quantifiers; the
indexed forward theorem remains about the exact current trace. Region
exclusivity, segment
coverage, and absence of legacy duplicate close/interior payload sources also
hold. One
pre-execution physical word list erases exactly to the public `buildPayload`.
The existing supplied-store evaluator reads a supplied flat store through a
checked translation adapter. Canonical physical execution refines logical
execution with failures, repetitions, and order preserved. Agreement on the
first execution's consumed ordered physical footprint determines the complete
physical trace, and a checked consumed-address disagreement changes it.
The capacity is linear and the query-independent reviewer width has an explicit
all-size logarithmic bound while covering stored/returned words, addresses, and
primitive operands/results. The principled charged-trace cost is exactly `76`;
the transitional U2 cost remains `328`. Ready-threshold `118`,
route-split, zero-block, `4144`, and `196727` rows are compatibility history
and are not the current reviewer path.


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
profile, and the construction-facing BP-native Cartesian-shape theorem. The
list surface proves `buildPayload.length <= 2*n + overhead n` with little-o
overhead, rejects invalid or empty ranges, returns exact leftmost answers for
valid ranges, and has constant modeled query cost. Exact physical erasure is a
separate theorem; no payload padding manufactures equality.

## Final Trace Model Adequacy

```lean
RMQ.Headlines.succinctRMQFinalTraceModelAdequacy
RMQ.Headlines.succinctRMQReviewerManifestSemanticAdequacy
RMQ.Headlines.listIntSuccinctRMQRawAdequacyOfValid
RMQ.Headlines.succinctRMQFinalTraceModelAdequacyExact
RMQ.Headlines.succinctRMQFinalSuppliedStoreAdequacy
RMQ.Headlines.succinctRMQFinalFullModelSoundness
RMQ.Headlines.succinctRMQFinalFullModelSoundnessExactOfFootprintGlobal
RMQ.Headlines.listIntSuccinctRMQQueryCostedWithStoreEqQueryCostedOfFootprint
RMQ.Headlines.listIntSuccinctRMQFinalFullModelSoundnessExactOfFootprintGlobal
RMQ.Headlines.listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal
RMQ.Headlines.listIntSuccinctRMQCanonicalTransitionalFinalFullModelCostLeOfFootprintGlobal
RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreSuccessfulReadsBackedByCanonicalReviewerPayloadOfFootprintGlobal
RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedWithStoreCostLeOfFootprintGlobal
RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCanonicalTransitionalCostedCostLe
RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedCostLe
RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedCostEqTraceLength
RMQ.Headlines.succinctRMQQueryCostEq
RMQ.Headlines.succinctRMQChargedTraceCostAlgebra
RMQ.Headlines.succinctRMQCanonicalTransitionalQueryCostEq
RMQ.Headlines.succinctRMQCanonicalTransitionalFinalFullModelCostLeOfFootprintGlobal
RMQ.Headlines.succinctRMQPrincipledAllSizeChargedTraceFinalFullModelCostLeOfFootprintGlobal
RMQ.Headlines.succinctRMQReviewerPhysicalWordsErasePublicPayload
RMQ.Headlines.succinctRMQReviewerPhysicalExecutionRefinesLogical
RMQ.Headlines.succinctRMQReviewerPhysicalFootprintRecorded
RMQ.Headlines.succinctRMQReviewerPhysicalStoreAdapter
RMQ.Headlines.succinctRMQReviewerPhysicalExecutionEqOfOrderedFootprint
RMQ.Headlines.succinctRMQReviewerPhysicalValueFromSuppliedStore
RMQ.Headlines.succinctRMQReviewerPhysicalValueDependency
RMQ.Headlines.succinctRMQReviewerEveryReadOccurrenceProvenance
RMQ.Headlines.succinctRMQReviewerCountedSourceSuccessfulClosedValidOccurrence
RMQ.Headlines.succinctRMQReviewerSharedBPConsumerSuccessfulClosedValidOccurrence
RMQ.Headlines.succinctRMQReviewerSuccessfulOccurrenceImpliesOperationalProducer
RMQ.Headlines.succinctRMQReviewerFreshUnusedSourceNoProducer
RMQ.Headlines.succinctRMQReviewerPhysicalWordsFitLinearCapacity
RMQ.Headlines.succinctRMQReviewerWordBitsLogarithmic
RMQ.Headlines.succinctRMQReviewerPhysicalWordFits
RMQ.Headlines.succinctRMQReviewerSuccessfulReadWordFits
RMQ.Headlines.succinctRMQReviewerPhysicalFootprintAddressFits
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
`SuccinctClassic.queryCosted`, valid windows erase to the list RMQ answer, the
principled `76` charged-trace bound transfers, and invalid ranges return `none`.
The store/model aliases
expose the direct supplied-store transfer theorems for counted flat-payload
backing and modeled cost under footprint agreement.
The current final global trace has the uniform canonical charged-trace bound
`SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost = 76`.
The checked sum is `2*13 + (2*4 + 2*4 + 30) + 4`; exact cost is emitted trace
length, with no padding. The separately named transitional U2 sum remains
`328`. Footprint-agreeing supplied-store and full-model aliases transfer the
principled bound. Ready `118`, route-split, `4144`, and `196727` remain
compatibility rows.

This accounting charges payload reads and word-rank/select primitives only.
Controller dispatch, arithmetic, branching, decoding, local scanning, and
candidate merging are explicitly inventoried as zero-weight operations for
the current model. Thus `76` is not a conventional word-RAM runtime theorem;
E1 must reuse the named operation vocabulary in a fully charged simulation.

The whole-query footprint remains a safe final-layout overapproximation. Inside
the canonical interior component, the stronger dynamic footprint is exact: it
is the ordered address projection of the execution that computes the answer.

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
