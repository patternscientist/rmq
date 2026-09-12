# Paper Main Theorem

## Primitive-query strengthening (accepted)

`RMQ.Headlines.succinctRMQFullyChargedPackedQuery` exports a separate
accepted theorem through `RMQPaper`,
`RMQ.SuccinctFinal.PackedWordRAM.fullyChargedPackedQueryCapstone_holds`. It
concerns a different execution from the statement below: one numeric memory
and one closed loop-free program of 837,572 primitive instructions, with
total data/code/scratch capacity `2n + o(n)`, logarithmic word width, exact
half-open leftmost answers, rejection of representable invalid ranges, and
halting within at most 837,572 steps for every representable endpoint pair.
Every executed primitive instruction is charged, under a word model with
unit-cost multiplication, division, remainder, variable shifts and bitwise
operations. The budget is the program length, far above the 6,003 to 16,358
steps observed on the committed valid-query fixtures. The code and scratch term
is lower order only asymptotically, endpoints outside the word domain are
rejected by an uncharged value-level check, and preprocessing is unclaimed.
Status: ACCEPTED, following the replay campaign, both-host aggregate gates and independent audit. See `docs/WORD_RAM_REVIEW_PACKET.md` for
exact objects and assumptions. The statement below is the paper main theorem
with its own 210 charged-trace bound, which this accepted construction does not change.

## English Statement

For every ordinary input list `xs : List Int`, the verified succinct RMQ
construction builds an advertised payload of length at most `2 * xs.length +
overhead xs.length`, where `overhead` is little-o-linear. Every valid half-open RMQ query
returns the exact leftmost range minimum answer under the repository's
value-level list semantics, invalid or empty ranges return `none`, and the
modeled query budget is the uniform charged-trace bound `210`. The final
query also has a checked WordRAM trace/store/payload story: the costed query is
the projection of a trace, successful reads are backed by counted flat payload
words, event data are bounded in the model, no synthetic cost-only trace marker
is used. One pre-execution physical word list, described by an exhaustive typed
22-source universe over logical segments `0..22`, with BP roles `0` and `19`
sharing one physical source and canonical close included, erases exactly to that same
public payload. The existing supplied-store evaluator runs through a checked
adapter that reads a caller-supplied flat store at translated physical
addresses. Canonical flat-physical execution refines logical execution while
preserving decoded result, cost, ordered successes/failures, repetitions, and
the execution-derived footprint. Agreement on the first execution's consumed
physical footprint determines the complete physical trace; a checked
consumed-address disagreement witness proves the store is observed. One
query-independent logarithmic word width bounds its storage, addresses, and
primitive operands/results.

For every valid list query, the main theorem now literally includes the
24-field `ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed` certificate,
its independently named `ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts`
projection, the guarded `ReviewerNativeMachineAdequacy` packet, and the direct
same-canonical-execution proposition
`sum (map WordRAM.TraceEvent.nonSyntheticWeight trace) <= 210`. The paper proof
obtains that bound by projecting `requires_certificate_weight_le_210`; it does
not restate a numeral beside the packet.

## Machine-Level Theorem Map

- `RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`:
  construction-facing theorem combining doubled-Catalan space envelopes, the
  canonical reviewer payload bound and exact physical erasure, direct
  positional physical backing for each successful read, exact answers through
  the canonical global trace, and that trace's non-synthetic-weight equalities
  to trace length and `Costed.cost`, plus the uniform bound `210`.
- `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`: list-facing main theorem
  with one query-independent reviewer-manifest semantic packet, the inequality
  `buildPayload.length <= 2n + overhead`,
  `LittleOLinear overhead`, exact physical-word erasure to that same
  `buildPayload`, invalid-range rejection, exact valid RMQ answers, leftmost
  ties, the checked equality `SuccinctClassic.queryCost = 210`, and the
  no-synthetic execution story. The payload is not padded to manufacture
  equality. Its M1 conjuncts are pinned independently by an expected-type
  consumer whose complete proof term is this theorem itself.
- `RMQ.Headlines.succinctRMQReviewerMachineWellFormed`,
  `RMQ.Headlines.succinctRMQReviewerMachineRequiredFacts`, and
  `RMQ.Headlines.listIntSuccinctRMQReviewerNativeMachineAdequacy`: the
  certificate, literal 24-field consumer, and guarded four-link list packet on
  the same shape/query/store/trace objects.
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
  predicate, and that fresh segment 23 fails that predicate. It does not claim
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
- `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`:
  strong current vocabulary theorem proving every event in the accepted
  canonical global trace is `readWord`.
- `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack`: entropy/Catalan
  lower-bound surface used for the matching information-theoretic story.
- `RMQ.Headlines.succinctRMQFullyChargedPackedQuery`: the separate accepted
  primitive-machine theorem described at the top of this file. Its numeric
  memory, program and run are distinct objects from the execution above.

## Lower-Bound Scope

The lower bound in this artifact is an entropy/Catalan counting lower bound for
exact RMQ encodings. It is not the Liu-Yu/Liu cell-probe lower bound, and the
paper artifact should not cite it as such.

## Current Cost Boundary

The canonical all-size reviewer trace has the principled charged-trace bound
`210`, proved by
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace`
and its numeric equality theorem. Its algebra is
`2*35 + (2*11 + 2*37 + 33) + 11`. Every actual emitted event is proved to be
`readWord` by
`RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`; the
trace has no synthetic marker, so
the `WordRAM.TraceEvent.nonSyntheticWeight` certificate sum equals both emitted
trace length and the `Costed` cost of the same execution and is at most `210`.
`TraceResult.toCosted` itself charges trace length and would count a synthetic
compatibility marker if one were present.
Historical cost and execution profiles remain kernel-checked through
`RMQ.Headlines.RMQCompatibility`, under aliases explicitly containing
`Legacy` or `Compatibility`; that module is not imported by `RMQPaper`.

The `210` result is scoped to the explicit charged-trace model. It
charges payload reads, not controller
arithmetic, branching, decoding, local scanning, or preprocessing. It is not a
serialized-payload query theorem or conventional word-RAM complexity theorem.
The accepted construction at the top of this file,
`RMQ.Headlines.succinctRMQFullyChargedPackedQuery`, charges every primitive
instruction of its own distinct execution; it does not turn this `210` result
into an instruction count.

For history, `RMQ.SuccinctClassic.canonicalTransitionalQueryCost_eq` is
literal-pinned at `328`. The current raw select/close expression is not that
historical identity: it is separately exported as
`RMQ.SuccinctClassic.liveCompatibilityQueryCost_eq`, with value `352`.
