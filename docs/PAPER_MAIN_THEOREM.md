# Paper Main Theorem

## English Statement

For every ordinary input list `xs : List Int`, the verified succinct RMQ
construction builds an advertised payload of length at most `2 * xs.length +
overhead xs.length`, where `overhead` is little-o-linear. Every valid half-open RMQ query
returns the exact leftmost range minimum answer under the repository's
value-level list semantics, invalid or empty ranges return `none`, and the
modeled query budget is constant. The final
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

- `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`: list-facing main theorem
  with the inequality `buildPayload.length <= 2n + overhead`,
  `LittleOLinear overhead`, exact physical-word erasure to that same
  `buildPayload`, invalid-range rejection, exact valid RMQ answers, leftmost
  ties, modeled constant query cost, and the no-synthetic execution story. The
  payload is not padded to manufacture equality.
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
- `RMQ.Headlines.succinctRMQReviewerEveryReadProducerProvenance`:
  every read-event value has a closed-program instruction at its folded prefix
  state whose local trace contains that value, plus a compatible physical
  source, logical segment, and component path. This W18 checkpoint does not
  retain occurrence positions or concrete invocation parameters.
- `RMQ.Headlines.succinctRMQReviewerCountedSourceProducerMayPath` and
  `RMQ.Headlines.succinctRMQReviewerSharedBPConsumerProducerConnected`:
  reverse may-read evidence for every counted source and same-event paths for
  every select/rank/canonical-close shared-BP dependency.
- `RMQ.Headlines.succinctRMQReviewerFreshUnusedSourceNoProducer`:
  segment 21 with a plausible canonical-close label has no instruction-trace
  producer. This is stronger than, but not yet bridged from, the component
  may-read relation used by the positive counted-source theorem.
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

## Main Open RMQ Frontier

The canonical all-size reviewer trace has the checked transitional bound `328`,
proved by
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional`
and its numeric equality theorem. U3 owns a final explained constant. Ready
`118`, route-split `4144`, zero-block, and `196727` declarations are retained
only as compatibility/history and are not consumed by the paper route.
