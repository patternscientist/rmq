# Trust Audit Packet

This packet is the shortest reviewer path through the current succinct RMQ
claim. It records the checked objects that carry the result and the boundary of
the model. Historical route and cost chronology is kept separately in
[`digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md`](digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md).

## Canonical Proposition

The construction-facing anchor is:

```lean
RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile
```

The stronger event-vocabulary anchor on the exact same trace is:

```lean
RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly
```

The construction capstone's checked type joins one canonical reviewer payload and one canonical global
trace. For every valid half-open query over a Cartesian shape, it packages:

- payload length at most `2*n + overhead n`, with `overhead = o(n)`;
- exact erasure of the physical reviewer words to that payload;
- direct positional physical backing for every successful trace read;
- only `readWord` events, proved by
  `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`, and no synthetic cost marker;
- certificate weight equal to trace length and the same `Costed.cost`;
- uniform charged-trace cost at most `210`; and
- the exact leftmost RMQ answer.

The separate strong anchor proves universally on that same canonical trace
that every emitted event satisfies `isReadWord`; this stronger conjunct is not
part of the construction capstone's own checked type.

The ordinary-list endpoint is:

```lean
RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem
```

It uses the repository's half-open range contract and leftmost tie policy,
returns `none` on invalid or empty ranges, and transfers the construction to
`List Int` semantics. Its literal type also consumes the valid-query
`ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed` certificate, the
independent 24-field `ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts`,
the guarded `ReviewerNativeMachineAdequacy` packet, and the direct same-trace
weighted-event sum bound `<= 210`.

## Evidence Chain

### Payload identity

`SuccinctClassic.buildPayload` is the public payload. The physical reviewer
word list is fixed before the query, flattens exactly to that payload, and has
checked component offsets. The payload theorem is an at-most bound; no padding
is used to manufacture equality.

### Supplied-store dependence

The physical evaluator calls the supplied-store query path through a checked
address translation. It preserves the logical result, modeled cost, ordered
successful and failed reads, repetitions, and the execution-derived footprint.
Agreement on the first execution's consumed ordered footprint determines the
complete physical execution. Separate corruption theorems show that changing a
consumed decisive word can change the returned value.

The certificate is exported as
`RMQ.Headlines.succinctRMQReviewerMachineWellFormed`; its typed consumer as
`RMQ.Headlines.succinctRMQReviewerMachineRequiredFacts`; and the guarded list
packet as `RMQ.Headlines.listIntSuccinctRMQReviewerNativeMachineAdequacy`. The
consumer is not a copied conjunction: every one of its 24 differently named
fields is a literal projection. Safe-footprint corollaries first establish
exact ordered dynamic-read agreement and complete `TraceResult` equality. The
committed 41-case replay checks 24 field deletions, 11 object/proposition
substitutions, five public-composition mutations, and one expected-accept
control; the 210 case additionally compiles a weakened 211 theorem before the
independent 210 expected type rejects it.

### Read provenance

For an indexed read in the current global trace, the provenance theorem retains
the global occurrence, producing instruction occurrence, prefix-folded state,
component-local occurrence, invocation parameters, source, and composed-trace
offset. A separate existential packet proves that every counted source and
shared-BP consumer is exercised by some valid closed whole-query execution.
These are different quantifier statements: the latter does not say every query
reads every source.

### Exactness and invalid inputs

The global trace refines the canonical interpreted query and erases to the
reference `scanWindow` answer on valid ranges. The public validity guard gives
the same `none`, empty-trace, and zero-cost behavior across the canonical,
supplied-store, and physical wrappers for invalid inputs.

### Width and capacity

The reviewer capacity is linear in `n`; the pre-execution reviewer word width
has a checked logarithmic upper bound. The same width bounds physical words,
live and sentinel addresses, segment encodings, query operands, primitive
operands and results, and consumed footprint addresses.

## Cost Boundary

The current component derivation is:

```text
2 * select35 + (2 * rank11 + 2 * endpointFringe37 + interior33) + rank11 = 210
```

`TraceResult.toCosted` charges trace length. The separate
`TraceEvent.nonSyntheticWeight` certificate assigns one to `readWord`,
`wordRank`, and `wordSelect`, and zero to the synthetic compatibility marker.
The canonical trace proves that every emitted event is `readWord` and no marker is
present, so certificate weight equals both trace length and modeled cost.

This theorem does not charge controller dispatch, input/register access, option
tests, arithmetic, branching, decoding, local scanning, candidate merging,
trace assembly, or the public validity guard. Consequently `210` is an explicit
charged-trace bound, not conventional word-RAM time or compiled Lean runtime.
The separate accepted theorem in the next section charges every primitive
instruction of its own, different execution.

## Separate Accepted Primitive Machine

`RMQ.Headlines.succinctRMQFullyChargedPackedQuery` (producer
`RMQ.SuccinctFinal.PackedWordRAM.fullyChargedPackedQueryCapstone_holds`) is a
different proposition about a different execution, and it is ACCEPTED: it
is kernel checked with the same three standard axioms and consumed by an
independent typed client, and its committed replay campaign, the aggregate
gate and a fresh blind source audit with its tooling correction review have passed. For every
`xs : List Int` it fixes one numeric memory `buildMemory xs` and one closed
loop-free program of 837,572 primitive instructions. For every
representable endpoint pair the run halts within at most 837,572 steps, every
executed instruction counts, and every word, operand and prefix state fits one
logarithmic width. Valid ranges return the leftmost minimum, and
representable invalid ranges return packet `0` with no memory reads. Memory,
literal program encoding and registers occupy `2n + o(n)` bits.

The live assumptions a reviewer should check are unit-cost multiplication,
division, remainder, variable shifts and bitwise operations (division and
remainder go beyond the multiplication model of the word-RAM literature and
are an explicit additional assumption); an uncharged
value-level check that rejects endpoints outside the word domain; absorption
of the code and scratch storage into `o(n)` only asymptotically (that storage
exceeds `n` for every `n` below about `2^28`); and a step budget equal to the
loop-free program length, far above the 6,003 to 16,358 steps observed on
the committed valid-query fixtures. Full details are in
[`WORD_RAM_REVIEW_PACKET.md`](WORD_RAM_REVIEW_PACKET.md).

## Compatibility Boundary

`RMQPaper.lean` imports only `RMQ.Headlines.RMQ`. Historical direct,
large-regime, route-split, and transitional cost aliases are exposed only by
`RMQ.Headlines.RMQCompatibility` and the broad `RMQ.Headlines` barrel. They
remain checked results but are not alternative paper capstones.

## Reproduction

From the repository root:

```powershell
lake build RMQPaper
lake env lean scripts/headline_axiom_check.lean
lake env lean scripts/wordram_axiom_check.lean
lake exe rmq_succinct_classic_validate
lake exe rmq_succinct_classic_cost_harness
pwsh -NoProfile -File scripts/packed_query_replay.ps1
powershell -ExecutionPolicy Bypass -File scripts/gate.ps1
```

The packed-query replay requires a clean committed tree; the aggregate gate
also runs it.

The curated axiom inventories should report only the repository's accepted Lean
foundations, such as propositional extensionality, classical choice, and
quotient soundness. The executable validators are corroborating evidence; they
do not replace the universal theorems.

## Non-Claims

The canonical charged-trace theorem does not establish:

- compiled Lean wall-clock performance;
- a fully charged small-step controller for its own execution (the separate
  accepted theorem `RMQ.Headlines.succinctRMQFullyChargedPackedQuery` charges every
  primitive instruction of a distinct execution instead);
- end-to-end preprocessing complexity in the same machine;
- a serialized-payload query API with conventional word-RAM cost; or
- global minimality of the numerical constant `210`.

The accepted theorem `RMQ.Headlines.succinctRMQFullyChargedPackedQuery` does not
establish preprocessing time or space, compiled Lean wall-clock performance,
attainment of its 837,572-step budget, or a machine-instruction bound for
parsing endpoints outside the word domain.

## Reviewer Reading Order

1. `RMQ/Headlines/RMQ.lean`
2. `RMQ/Core/SuccinctFinalRAM.lean`
3. `RMQ/Core/SuccinctFinalStoreParam.lean`
4. `RMQ/Core/SuccinctFinalModelAdequacy.lean`
5. `RMQ/Core/SuccinctRMQClassic.lean`
6. `docs/PAPER_CLAIM_CORRESPONDENCE.md`
7. `docs/PAPER_MODEL_ADEQUACY.md`
8. for the separate accepted theorem: `RMQ/Core/WordRAM/Packed/Capstone.lean`,
   `RMQ/Validation/PackedQueryContract.lean` and
   `docs/WORD_RAM_REVIEW_PACKET.md`
