# Final RMQ Model Adequacy

## Canonical Machine Adequacy

The reviewer path uses one pre-execution list,
`concreteBPNativeSuccinctRMQReviewerPhysicalWords`, whose erasure is exactly the
canonical public payload. It is assembled from one exhaustive typed 22-source
universe (23 logical segments; segments 0 and 19 share the BP-code source)
that includes canonical close and the four-Russians fringe/select chunk-table
sources at segments 21 and 22. For every indexed read, the provenance layer retains the
same global position, closed-program instruction occurrence, state obtained by
folding the exact preceding prefix, component-local position, exact invocation
parameters, physical source, region, and logical segment. Every counted source
and exact shared-BP consumer has a successful occurrence through an actual
closed whole-query execution under a valid ordinary `List Int` query; the
fringe chunk table additionally has a successful occurrence for EACH of the
three read leaves that consume it (select, rank, and LCA/canonical close),
and both chunk-table segments carry checked repeated-equal-read witnesses:
one valid execution reads the same table word at two distinct global trace
positions with two separately indexed provenance receipts
(`repeated_equal_read_occurrences_have_distinct_receipts` instantiated on
actual executions, recorded as fields of the manifest packet).
The manifest also proves exclusive source regions, complete logical-segment
coverage, and exclusion of legacy duplicate close/interior sources.

The provenance layer deliberately uses two differently quantified packets. The parameterized
`ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy shape left right` retains
indexed forward provenance for that exact query. The proof-only,
non-parameterized
`ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy` states global
reviewer-manifest facts: each counted source and shared-BP consumer has some
closed valid execution witness, successful predicate `P` implies mutation
predicate `Q`, and fresh segment 23 fails `Q`. The paper theorem consumes that
global packet once, not underneath a current-query `ValidRange` premise.
`SuccinctRMQClassicProvenance.lean` is only the proof-import seam. This split
keeps symbolic witness construction out of the native validator link closure;
it does not replace or alter the genuine `SuccinctRMQClassic` execution checked
by the validator and cost harness.

A counterfactual fresh segment `23` with the plausible existing
`canonicalClose` label has no witness under the same common closed-valid-
occurrence relation. The positive predicate existentially requires `some word`;
the mutation predicate permits any `word?`, and
`ReviewerProducerClaim.hasOperationalProducer_of_successful` is the checked
`P -> Q` bridge. Earlier event-value and component may-read theorems remain
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

The construction-facing join theorem is
`RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`.
It places the canonical payload bound, physical erasure, exact global trace,
direct positional physical backing for each successful read, non-synthetic
weight equality to trace length and `Costed.cost`, and uniform `210` bound in
one checked type.

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

## Events And The Declared Charge Policy

Since the B2/B3 four-Russians recharge, the accepted route's charged event
vocabulary is `readWord` ONLY. The checked structural theorem is

```lean
concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only
```

(headline `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`):
every event of the accepted whole-query global word trace is a
`WordRAM.TraceEvent.readWord` constructor, for every shape and query. The
`wordRank`/`wordSelect` word-local primitives remain defined for
legacy/compatibility surfaces (the frozen 76/142/328 routes) but are never
emitted by the accepted route.

The declared charge policy is therefore:

- **Charged**: attempted payload-word reads (`readWord segment index word?`),
  one model tick each, including failed reads. Every charged trace event is a
  memory read; the trace-level cost of a query is its read count.
- **Uncharged**: instruction dispatch, register moves, fixed-width decode of a
  fetched word into register values (mixed-radix unpack of a table entry),
  bounded arithmetic/comparison on register values, option tests, branching,
  candidate merges, trace assembly, and the validity guard.

Why the uncharged remainder is benign in this model: after B2/B3 **and B6**
every uncharged step is a BOUNDED-PER-STEP register computation - a
constant-shape decode or merge between two charged reads - not an unbounded
scan. The old event-silent per-position fringe scan and in-word rank/select
loops are gone from the charged route; their replacements visit at most a
literal number of chunks (8 per machine word, 33 per fringe window; the
33-cap identity is checked in `ChargedFringeChunks.lean`, the 8-per-word cap
and its all-size regime identities in
`ChargedWordChunks.lean`/`ChargedTableRegime.lean`), each chunk contributing
one charged read plus constant register work.

B6 closes the last exception to that sentence. Until B6 the claim was FALSE
of one leg: the canonical close/LCA dispatcher's SAME-BLOCK branch still
called `localBPSameBlockCloseSeededCosted`, which declared `cost := 4` while
running `localBPSeededPrefixRangeMinExcess` /
`localBPSeededPrefixRangeArgMinPrefixPos` over
`rightClose - leftClose + 1` window positions - a scan whose length grows
with `blockSize = 2*(Nat.log2 size + 1)` and so is not bounded per step. That
branch is live, not legacy: every singleton query routes to it, and the cost
harness reports `canonicalRoute=sameBlock` executions at n = 64 and n = 128.

The same-block leg is now charged by the same chunk fold as the endpoint
fringe, reading the SAME segment-21 `bpFringeChunkTable`, with these checked
caps:

- `bpChunkedSameBlockCloseSeededCosted_cost_le : cost <= 37`
  (`ChargedSameBlockChunks.lean`) - 4 window-word reads plus at most 33 chunk
  reads, the chunk counter capped at `Nat.min (relHi / c + 1) 33`, with no
  size hypothesis and no readiness guard, so it holds at n = 0, 1, 2 too.
- `bpChunkedSameBlockCloseDecodedCostedWithRankSeed_cost_le :
  cost <= rankCost + 37` once the directory rank seed is threaded.
- `canonicalLcaCloseCostedWithRankSeed_cost_le_principled` - the branch cap is
  a MAX over the two arms, not a sum, and the cross-block arm's existing
  `2*rankCost + 2*37 + interior` absorbs the same-block arm's `rankCost + 37`
  (at `rankCost = 11` and the current interior cap: 48 <= 129), so B6 changed
  no cost-algebra field.
- `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq` therefore
  re-derived by `rfl` to **207 at B6, unchanged**. The literal did not move
  *at B6* because the branch cap genuinely absorbed the new reads, not because
  the new reads were left out of the accounting - the per-chunk
  `readWord 21 _ _` events are in the trace and are counted.

  It has since moved, for a different and equally accounted reason: see the
  next subsection.

## Why the Literal Moved: Representation Artifact vs Algorithmic Work

B7 recharges the interior directory's sparse-level reads and moves the
interior component `30 -> 33`, hence `closeLCA 126 -> 129` and the
whole-query literal `207 -> 210`. That movement is the charge policy working
as intended, and it is worth being precise about why, because "the constant
went up" and "the algorithm got slower" are different statements and only the
first is true.

The distinction the charge policy draws is between:

- **Algorithmic work** - the comparisons, merges and candidate selections that
  the RMQ algorithm performs. These are what an algorithms paper counts, and
  B7 changes none of them: the interior route decides the same candidates from
  the same operands in the same order.
- **Representation artifacts** - the memory touches required to get an operand
  out of the chosen succinct encoding at all. A sparse level table must be
  read before its entry can be compared. Nothing about the algorithm requires
  those reads; they are the price of the representation, and a different
  encoding of the same algorithm would pay a different price.

A word-RAM charge policy must charge BOTH, because the model's unit of cost is
the memory touch, not the comparison. That is the whole point of running the
accounting in `Costed` against an explicit store rather than counting
operations on paper. So when B7 makes the sparse-level reads reachable, three
more `readWord` events genuinely appear in the trace, and the literal must
absorb them or the accounting would be false.

What must NOT happen - and is the failure mode this section exists to rule out
- is the reverse: leaving a representation artifact uncharged on the grounds
that it is "not algorithmic work". That is exactly the event-silent defect
that B2, B3 and B6 each removed one instance of. An uncharged read is not a
cheaper algorithm; it is an unmodelled one.

The bridge lemmas that carry the moved literal, so the chain is checkable
rather than asserted:

- `canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_literal_of_size_ge_four_of_bounded`
  - the tight interior content, stated against the literal `30`, proved from
  the four branch caps (`18`, `20`, `20`, `30`).
- `canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded`
  - the same fact restated against the cap FIELD, so consumers survive a
  recharge. Derived from the `_literal` form by `Nat.le_trans`.
- `canonicalRelativeRmmPrincipledInteriorChargedTraceCost_announced_slack_of_size_ge_four_of_bounded`
  - the staging artifact described below.
- `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCloseCost_eq`
  (`= 129`) and `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`
  (`= 210`) - the re-derived algebra identities, both by `rfl`.
- `concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost_eq` (`= 207`)
  - the retired literal, frozen rather than deleted, pinned to literal
  components so no later recharge can silently rewrite it.

### Announced slack at the staging commit

The interior cap and the sparse-level store extension land as two commits, so
that each is separately reviewable and separately green. Between them the cap
is `33` while the route reachable at that commit still costs at most `30`.

That looseness is not left to prose. It is stated and checked by
`canonicalRelativeRmmPrincipledInteriorChargedTraceCost_announced_slack_of_size_ge_four_of_bounded`,
which proves both that the current route stays within `30` and that the
declared cap strictly exceeds `30`. A reader who wants to know whether the
published constant is tight can ask the checker instead of trusting this
paragraph. The theorem is retired - deleted, not weakened - by the commit that
makes the bound tight again, and it is not provable after that commit.

What remains uncharged on the accepted route after B6 is exactly the register
list above, and it is bounded per step at every leg: each charged read is
followed by a constant-shape mixed-radix unpack of one table entry and a
constant number of comparisons/merges, with no remaining loop whose trip count
depends on input size. There is no event-silent computation left on the
accepted route. The E1 machine (the amended
E1 target of `OPTION_B_CHARGED_FRINGE_DESIGN.md`) will define the richer
instruction semantics that individually charges every controller, decode,
arithmetic, comparison, branch, and register step, and prove a separate
literal total; until then these omissions are documentary and enumerated
here, not silently absorbed into an unbounded primitive.

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

Every payload-read address fits that width (and, on the frozen historical
routes that still emit word-local primitives, every primitive operand/result
does too). This is still a model-level bound, not a claim about a particular
hardware instruction set.

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

## Compatibility Boundary

Detailed earlier cost, dispatch, and leaf-level supplied-store chronology is
quarantined in the explicit
[`compatibility history`](digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md).
Those facts are not reachable from the uniform canonical reviewer route and do
not form part of this current model-adequacy statement.

## The Constant

The current reviewer-route modeled bound is the principled charged-trace sum
`210`. It is proved by
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace`
and evaluated by
`concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`. The sum is
`2*select35 + (2*rank11 + 2*fringe37 + interior30) + rank11`, derived (never
asserted) from the component algebra; the retired 142 (silent in-word
rank/select), 76 (silent fringe), and 328 (transitional) literals stay frozen
as historical constants with their chains still checked.
The operational bridge classifies every event in the actual canonical trace as
`readWord` (the readWord-only vocabulary theorem above), excludes
`syntheticCostOnlyPrimitive`, and proves that the direct
`WordRAM.TraceEvent.nonSyntheticWeight` certificate sum equals both trace
length and the `Costed` cost of the same execution. This equality is proved for
the canonical no-synthetic trace; `TraceResult.toCosted` itself charges trace
length and would count a synthetic compatibility marker if one were present.
The non-synthetic-weighted trace is then bounded by `210`. A counterfactual
theorem proves that inserting a synthetic event anywhere would make the
certificate sum strictly smaller than trace length.

The supplied-store and full-model companions transfer the same `210` bound
under final footprint agreement. Earlier execution stories are compatibility
facts only and are not current reviewer-route claims.
The paper-level claim is that the query is constant in the stated model and
that the model's counted reads are payload-backed. It is not a claim that this
Lean code is production serialization, optimized machine code, or a verified
CPU implementation.

The charged/uncharged boundary is the declared charge policy in the Events
section above: attempted payload-word reads are the only charged trace
events, the uncharged remainder is enumerated there and is bounded-per-step
register computation, and the current theorem does not define a substitute
controller vocabulary or prove conventional word-RAM complexity. E1 must
define its richer instruction semantics and prove a simulation separately.

## Non-Claims

The adequacy packet does not prove:

- compiled Lean execution performance;
- a compiler correctness theorem;
- a full CPU or memory hierarchy semantics;
- production-ready serialization;
- minimality of the auxiliary safe logical layout footprint (the reviewer
  flat-physical footprint itself is execution-derived and recorded exactly);
- arbitrary-garbage decoding for legacy supplied-store compatibility leaves.

It does prove a model-adequacy bridge: the final query's modeled constant-cost
execution has an explicit trace, explicit counted payload reads, bounded event
data, no synthetic cost-only markers, and exact RMQ semantics through the
existing final exactness theorem:

```lean
RMQ.Headlines.succinctRMQFinalTraceModelAdequacyExact
```
