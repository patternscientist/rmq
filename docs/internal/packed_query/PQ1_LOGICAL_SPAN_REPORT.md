Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

This declaration concerns the bounded PQ1-LS canonical logical-span leaf.
The lead's separate join assembles and compiles the complete packed controller.

Worker: PQ1-LS (`numeric_span`, returning). Branch:
`codex/fully-charged-packed-query-v1`. Worktree:
`C:/Users/poin/.codex/worktrees/a84a/RMQ`.
Base: `9e2720b991e203d22a2787abf66dbfb9888088fb`. Shared HEAD observed at
finalization: `b0af10d14121c7b11a7d3eb7cb1515c618a0da4b`; the lead advanced the
shared branch during this leaf. This worker made no commit.
Governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
Canonical proof-sprint preflight passed with actual runtime catalog
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`. The skill and completion
gate were applied. The matrix froze four prompt requirements and five assigned
invariants before implementation; nine exact UTF-8 block comparisons passed.

Owned files: `RMQ/Core/WordRAM/Packed/LogicalSpan.lean`, this report, and
`docs/internal/packed_query/PQ1_LOGICAL_SPAN_MATRIX.md`. No staging, commits,
shared-ledger writes, completed Span/SpanAssembly edits, or changes to another
worker's modules were performed. The completed matrix is the evidence ledger.

## Executable construction

All names below use namespace `RMQ.SuccinctFinal.PackedWordRAM`. Import
`RMQ.Core.WordRAM.Packed.LogicalSpan`.

`reviewerLogicalSpan n lc sc segment index : Option NumericSpan` is the frozen
scalar specification. Segments below23 other than20 read the four numbers in
`regularDescriptor n lc sc segment` through `regularSpan`. Segment20 maps the
existing interior classifier to its closed absolute bit address and actual
read width. A segment at or above23 returns none.

`directLogicalReadNat` has the exact executable body:

```lean
(reviewerLogicalSpan n lc sc segment index).bind fun span =>
  (decodeSpanNat (wordWidth n)
    (metadataWordCount * wordWidth n + span.position) span.length memory).map
      fun value => (value, span.length)
```

Its only inputs are Nat scalars and numeric memory. The value comes from
`decodeSpanNat` on that supplied memory. The old shape, bit lists, semantic
store, and proofs do not enter this function. The output preserves logical
length independently of numeric value: a present empty word yields
`some (0,0)`, while an absent word yields none.

## Complete checked propositions

The descriptor equations required by Locate are public:

```lean
reviewerLogicalSpan_regular (n lc sc segment index : Nat)
  (hsegment : segment < 23) (h20 : segment ≠ 20) :
  reviewerLogicalSpan n lc sc segment index =
    regularDescriptorSpan n lc sc segment index

reviewerLogicalSpan_interior_descriptors (n lc sc index : Nat) :
  reviewerLogicalSpan n lc sc 20 index =
    interiorComponents.findSome? (interiorDescriptorSpan n lc sc index)

selectCeilDiv_eq_packedChunkCount (len width : Nat) (hw : 0 < width) :
  GenericSelect.selectCeilDiv len width = packedChunkCount len width
```

`regularDescriptorSpan` passes fields0..3, each accessed with `getD 0`, to
`regularSpan` in base/bits/stride/count order. `interiorDescriptorSpan` passes
fields0..4 to `interiorSpan` in prefix/count/base/entryWidth/chunks order,
together with `packedBpCodeWordWidth n`. The latter theorem covers all eight
components in `interiorComponents` order and all indices. The internal range
proof abstracts the eight component counts, so arithmetic does not unfold the
large geometry definitions. It requires no positivity of component counts.
The ceil-division equivalence uses the existing positive BP word width.

For every `n lc sc` and every `request : PackedReviewerLogicalRequest`,
`reviewerLogicalSpan_old_geometry` proves the following conjunction:

```lean
packedReviewerLogicalPlan n lc sc request =
  ((reviewerLogicalSpan n lc sc request.segment request.index).map fun span =>
    spanPlan (packedReviewerCellWidth n) span.position span.length).getD [] ∧
(∀ cells, packedReviewerLogicalDecode n lc sc request cells =
  (reviewerLogicalSpan n lc sc request.segment request.index).map fun span =>
    packedReviewerDecodeSpan n span.position span.length cells)
```

For every such request and span, `reviewerLogicalSpan_length_le` takes only
`reviewerLogicalSpan n lc sc request.segment request.index = some span` and
concludes `span.length ≤ packedReviewerCellWidth n`. The proof instantiates the
old all-decoder width theorem on a sufficiently long false bit window to
recover the requested length. That window exists only in a proof; it supplies
no executable reply or payload field.

`decodeSpanNat_repacked_span` is fully general in
`headers : List Nat`, `width : Nat`, `old : List (List Bool)`, `position len : Nat`.
Its only premises and complete conclusion are:

```lean
0 < width → len ≤ width →
(position + len ≤ old.flatten.length ∨ len = 0) →
decodeSpanNat width (headers.length * width + position) len
  (repackWords headers width old) =
some (bitsToNatLE ((old.flatten.drop position).take len))
```

This covers arbitrary unaligned and crossing original bit spans, without an
old-cell alignment premise. It reuses the numeric decoder's separate raw word
loads and fragment arithmetic. No executable double-width concatenation was
introduced. The zero-length alternative needs no bound on nominal position.

`reviewerLogicalSpan_canonical_fits`, for every shape/request/span with
canonical geometry equal to `some span`, concludes:

```lean
span.position + span.length ≤ (packedReviewerMemory shape).flatten.length ∨
  span.length = 0
```

It derives the positive-span bound from the old canonical plan's address
theorem and uniform full-cell allocation, rather than assuming successful
logical reads or storage readiness.

The two main canonical theorems have no hypotheses:

```lean
directLogicalReadNat_eq_reviewer (shape : CartesianShape)
  (request : PackedReviewerLogicalRequest) :
  directLogicalReadNat shape.size (longCount shape) (packedReviewerSparseCount shape)
    (shapeMemory shape) request.segment request.index =
  (packedReviewerLogicalRead shape.size (longCount shape) (packedReviewerSparseCount shape)
    (packedReviewerMemory shape) request).map fun bits => (bitsToNatLE bits, bits.length)

directLogicalReadNat_eq_globalReadStore (shape : CartesianShape) (segment index : Nat) :
  directLogicalReadNat shape.size (longCount shape) (packedReviewerSparseCount shape)
    (shapeMemory shape) segment index =
  ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index).map
    fun bits => (bitsToNatLE bits, bits.length)
```

The latter consumes the former and the existing exact canonical logical-read
refinement. A proof-only request supplies arbitrary fixed invocation/site tags;
its segment and index are exactly the requested inputs.

## Object identity and dependency chain

The allocation's literal construction is
`shapeMemory shape = repackWords (metadata shape) (wordWidth shape.size)
(packedReviewerMemory shape)`. `metadata_length` proves length174, exactly
`metadataWordCount`. The proof applies `decodeSpanNat_repacked_span` to those
same metadata, width, and old-memory arguments. `oldWidth_lt_wordWidth` supplies
the new-width bound from the logical span's old-width bound. The old fetch and
decode theorem recovers the same flattened bit slice; its length is proved
equal to the requested logical length. Thus both sides have the same value
and length, including empty and absent words.

`shapeMemory_capacity_le` counts this very `shapeMemory shape` object;
`buildMemory xs` wraps it at `cartesianShape xs`. No sibling allocation,
same-size proxy, answer cache, or proof-carried reply enters the chain. The
canonical theorem concerns the literal allocation used by the space theorem.

The new numeric decoder uses its memory's indexed first word and, on crossing,
indexed successor word. Old logical plan addresses establish bit bounds in the
proof; they are not identified with the new physical probe occurrences. Ordered
new physical attempts and their positional backing are the existing separate
SpanAssembly theorem surface consumed by the lead's next assembly join.

## Typed consumers and verification

`logicalSpan_canonical_consumer` independently spells the full universally
quantified global-store equality and directly consumes
`directLogicalReadNat_eq_globalReadStore`. The following additional typed
consumers are in the same checked module:

- `logicalSpan_empty_consumer` and `logicalSpan_singleton_consumer`: exact
  canonical equality for arbitrary segment and index, specialized only to the
  empty and singleton shapes.
- `logicalSpan_dead_interior_consumer`: every shape at segment20 and
  `packedInteriorComponentWords shape.size` returns none.
- `logicalSpan_empty_sentinel_consumer`: empty shape, segment19, index0 returns
  `some (0,0)`. The general `directLogicalReadNat_empty_alias` holds for any
  numeric lc/sc and memory at n0; `directLogicalReadNat_zero` proves successful
  empty reply for every present zero-length span, regardless of position.

These checks constrain independently stated presence/value/length projections.
They supplement the universal proofs; no finite fixture or native decision
establishes the universal claim. No mutation campaign is claimed or assigned.

Final standalone Lean check emitted `.olean/.ilean`, exited0, and produced no
warnings or errors (approximately 10 seconds, warm local imports, explicit
single-process slot). Source SHA256:
`ad3dc3b45b4f9967ca6ad7b1a66f018b0a9532fbb82958a3185796692bef82d6`.
Initial development errors were focused classifier simplification/branch
reduction and empty-alias normalization; all are repaired in the final file.
An imported check independently restated the canonical and descriptor theorem
types and printed eight key dependency inventories: exit 0 in 6.04 seconds; only
`propext`, `Classical.choice`, and `Quot.sound` occur. The durable exact-type
and boundary consumers are in the owned Lean source; the imported check was a
generated local validation artifact.
Required repository token and native-decision scans found no matches.
`git diff --check` passed. New owned-file `--no-index --check` comparisons
reported no whitespace errors (exit 1 denotes their expected content changes).
Exact frozen-row byte checks passed all nine rows again after matrix completion.
The matrix records coverage, failure repairs, and final command roles.

No broad Lake build or aggregate gate was run: this is the frozen narrow proof
leaf and its direct consumers. The lead owns final integrated design-policy,
committed-range, and aggregate certification. There is no worker commit.

## Design decision proposal and proof digestion

The lead already selected direct repacked bit spans. Suggested evidence for
its DESIGN_DECISIONS entry: use the old absolute logical-bit geometry directly
on densely repacked words, rather than first recovering two old physical cells
and then applying the old-cell decoder. This removes a redundant execution
layer while preserving the exact original logical slice. The rejected layer
remains a correct helper from PQ1-SPAN; it is unnecessary for the selected
assembly. The consequences are a single span decoder and a distinct new
physical address sequence. Value and actual logical length must remain paired,
because numeric zero alone cannot distinguish empty words and zero-valued
nonempty words. The canonical equality and descriptor equations above supply
the supporting evidence. No ADD/process decision was changed.

Conceptually, the proof isolates the logical slice from its old physical
packing. In plain English, every word the original canonical store can return
is now recovered, with its exact bit length, from the same counted numeric
allocation. Every absence is preserved too. The canonical theorem has no
readiness, successful-read, nonzero-size, special-count, or one-word-entry
assumption. The general repacking lemma retains only positive width, bounded
span length, and endpoint fit or zero length.

A skeptical reader can check that empty sentinels beyond the allocation do
not acquire an endpoint premise, that sparse words use the actual sparse count,
and that interior final chunks preserve their short width. These questions
map to the zero-span alternative, all-parameter old-geometry theorem, and exact
interiorDescriptorSpan equation respectively, and are covered by the checked
theorems. The separate next join is the lead's metadata-source assembly and
full controller; this report makes no whole-machine cost or width claim.
