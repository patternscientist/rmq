# Paper Main Theorem

## English Statement

For every ordinary input list `xs : List Int`, the verified succinct RMQ
construction builds an advertised payload of length at most `2 * xs.length +
overhead xs.length`, where `overhead` is little-o-linear. Every valid half-open RMQ query
returns the exact leftmost range minimum answer under the repository's
value-level list semantics, within the modeled constant query budget. The final
query also has a checked WordRAM trace/store/payload story: the costed query is
the projection of a trace, successful reads are backed by counted flat payload
words, event data are bounded in the model, no synthetic cost-only trace marker
is used. One pre-execution physical word list erases exactly to that same public
payload and refines the segmented execution. Agreement on the execution's
ordered read footprint determines the complete supplied-store trace, and one
query-independent logarithmic word width bounds its storage, addresses, and
primitive operands/results.

## Machine-Level Theorem Map

- `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`: list-facing main theorem
  with `2n + overhead`, `LittleOLinear overhead`, exact valid RMQ answers,
  leftmost ties, modeled constant query cost, and the no-synthetic flat-payload
  execution story.
- `RMQ.Headlines.succinctRMQFinalFullModelSoundness`: final trace/read-store/
  counted-payload model-soundness packet.
- `RMQ.Headlines.succinctRMQFinalFullModelSoundnessExactOfFootprintGlobal`:
  exact valid RMQ answers for any supplied store agreeing with the canonical
  global store on the declared footprint.
- `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreSuccessfulReadsBackedByCountedFlatPayloadOfFootprintGlobal`:
  supplied-store successful reads are backed by counted flat payload under
  footprint agreement.
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
