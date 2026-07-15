# Paper Main Theorem

## English Statement

For every ordinary input list `xs : List Int`, the verified succinct RMQ
construction builds an advertised payload of length at most `2 * xs.length +
overhead xs.length`, where `overhead` is little-o-linear. Every valid half-open RMQ query
returns the exact leftmost range minimum answer under the repository's
value-level list semantics, invalid or empty ranges return `none`, and the
modeled query budget is the uniform charged-trace bound `76`. The final
query also has a checked WordRAM trace/store/payload story: the costed query is
the projection of a trace, successful reads are backed by counted flat payload
words, event data are bounded in the model, no synthetic cost-only trace marker
is used. One pre-execution physical word list, described by an exhaustive typed
20-source universe including canonical close, erases exactly to that same
public payload. The existing supplied-store evaluator runs through a checked
adapter that reads a caller-supplied flat store at translated physical
addresses. Canonical flat-physical execution refines logical execution while
preserving decoded result, cost, ordered successes/failures, repetitions, and
the execution-derived footprint. Agreement on the first execution's consumed
physical footprint determines the complete physical trace; a checked
consumed-address disagreement witness proves the store is observed. One
query-independent logarithmic word width bounds its storage, addresses, and
primitive operands/results.

## Machine-Level Theorem Map

- `RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`:
  construction-facing theorem combining doubled-Catalan space envelopes, the
  canonical reviewer payload bound and exact physical erasure, exact answers
  through the canonical global trace, and that trace's non-synthetic-weight /
  `Costed.cost` equality and uniform bound `76`.
- `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`: list-facing main theorem
  with one query-independent reviewer-manifest semantic packet, the inequality
  `buildPayload.length <= 2n + overhead`,
  `LittleOLinear overhead`, exact physical-word erasure to that same
  `buildPayload`, invalid-range rejection, exact valid RMQ answers, leftmost
  ties, the checked equality `SuccinctClassic.queryCost = 76`, and the
  no-synthetic execution story. The payload is not padded to manufacture
  equality.
- `RMQ.Headlines.succinctRMQFinalFullModelSoundness`: final trace/read-store/
  counted-payload model-soundness packet.
- `RMQ.Headlines.succinctRMQFinalFullModelSoundnessExactOfFootprintGlobal`:
  exact valid RMQ answers for any supplied store agreeing with the canonical
  global store on the declared footprint.
- `RMQ.Headlines.succinctRMQReviewerPhysicalExecutionRefinesLogical`,
  `RMQ.Headlines.succinctRMQReviewerPhysicalExecutionEqOfOrderedFootprint`, and
  `RMQ.Headlines.succinctRMQReviewerPhysicalValueFromSuppliedStore`:
  genuine supplied flat-physical execution, first-footprint determinacy, and
  answer provenance at the translated supplied-store `.value` projection.
- `RMQ.Headlines.succinctRMQReviewerEveryReadOccurrenceProvenance`:
  every indexed read retains its global position, producing instruction
  occurrence, folded prefix state, component-local position, exact invocation
  parameters, source, and multiplicity-preserving embedding.
- `RMQ.Headlines.succinctRMQReviewerManifestSemanticAdequacy`: one global
  certificate that every counted source and exact shared-BP consumer has a
  successful witness through some actual closed whole-query execution under a
  valid list query, that the successful predicate implies the common mutation
  predicate, and that fresh segment 21 fails that predicate. It does not claim
  those sources are read by the current paper-theorem query.
- `RMQ.Headlines.succinctRMQReviewerEveryReadOccurrenceProvenance` and
  `RMQ.Headlines.listIntSuccinctRMQRawAdequacyOfValid`: indexed provenance and
  final trace adequacy remain tied to the exact current query and its validity
  domain.
- `RMQ.Headlines.listIntSuccinctRMQRawAdequacyOfValid` and
  `RMQ.Headlines.listIntSuccinctRMQInvalidPhysicalSemantics`: raw adequacy only
  for valid ranges and one none/empty/zero execution for every invalid range.
- `RMQ.Headlines.listIntSuccinctRMQQueryCostedInvalid`: one validity boundary
  rejects invalid or empty list ranges.
- `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedWithStoreCostLeOfFootprintGlobal`:
  the canonical modeled cost bound transfers to footprint-agreeing supplied
  stores.
- `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack`: entropy/Catalan
  lower-bound surface used for the matching information-theoretic story.

## Lower-Bound Scope

The lower bound in this artifact is an entropy/Catalan counting lower bound for
exact RMQ encodings. It is not the Liu-Yu/Liu cell-probe lower bound, and the
paper artifact should not cite it as such.

## Current Cost Boundary

The canonical all-size reviewer trace has the principled charged-trace bound
`76`, proved by
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace`
and its numeric equality theorem. Its algebra is
`2*13 + (2*4 + 2*4 + 30) + 4`. Every actual emitted event is proved to be
`readWord`, `wordRank`, or `wordSelect`; the trace has no synthetic marker, so
the `WordRAM.TraceEvent.nonSyntheticWeight` certificate sum equals both emitted
trace length and the `Costed` cost of the same execution and is at most `76`.
`TraceResult.toCosted` itself charges trace length and would count a synthetic
compatibility marker if one were present.
Historical cost and execution profiles remain kernel-checked through
`RMQ.Headlines.RMQCompatibility`, under aliases explicitly containing
`Legacy` or `Compatibility`; that module is not imported by `RMQPaper`.

The `76` result makes U3 candidate-complete only inside the explicit
charged-trace model. It
charges payload reads and word-rank/select primitives, not controller
arithmetic, branching, decoding, local scanning, or preprocessing. It is not a
serialized-payload query theorem or conventional word-RAM complexity theorem.
