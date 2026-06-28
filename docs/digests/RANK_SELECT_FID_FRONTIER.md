# Rank/Select FID Frontier Digest

Snapshot: 2026-06-28. This note digests the rank/select spoke after the
chunk-route milestone. It is written for a reader who knows what rank and
select are, but not the local Lean naming scheme.

## What Changed Conceptually

The plain-bitvector Jacobson/Clark theorem is already landed:

```lean
#check RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery
#check RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery
```

The moving frontier is compressed/FID rank/select. The goal is to store a
fixed-weight bitvector using about
`log2 (binomialCount n m) + o(n)` bits, while still supporting access, rank,
and select in constant modeled time. The latest primary-budget milestone does
not finish that theorem, but it removes a central counting hypothesis for
sentinel log chunks: per-block fixed-weight codes now fit under the global
fixed-weight payload budget plus the `o(n)` log-chunk block count.

## Plain English Story

A fixed-weight bitvector has exactly `m` ones among `n` positions. Instead of
storing all `n` bits, the compressed representation can store the index of that
bitvector among all bitvectors with the same weight. This is the enumerative
code. The project has already checked the finite universe, the encode/decode
round trip, and a packed readback baseline.

The first baseline is deliberately slow: read the whole packed code, decode the
entire bitvector, then answer access/rank/select. That proves non-oracularity
but not constant query time.

The RRR/FID direction is to split the bitvector into chunks. Each chunk carries
a fixed-weight code. Query routing should read a small number of route words,
find the addressed chunk, read that chunk's packed code and class/length
metadata, and run a local decoder. The chunk-route milestone makes that
addressing story concrete:

- `RMQ.RankSelect.fixedWeightChunkBlocksLengthLe` bounds ordinary chunk count
  by `bits.length / blockSize + 1`.
- `RMQ.RankSelect.fixedWeightChunkBlocksWithSentinelLengthLe` adds one empty
  sentinel block and bounds total routeable blocks by
  `bits.length / blockSize + 2`.
- `RMQ.RankSelect.fixedWeightChunkBlocksWithSentinelGetSentinel` identifies
  the fallback block for invalid routes.
- `RMQ.RankSelect.fixedWeightChunkAccessRouteWithSentinel` gives a concrete
  access route: in-range queries go to the computed chunk; invalid queries go
  to the sentinel.
- `RMQ.RankSelect.fixedWeightChunkBlocksGetAccessExact` proves the local
  chunk-offset bit agrees with the original bitvector.
- `RMQ.RankSelect.fixedWeightBlockClassLengthTableOverheadLeChunkBudget` and
  `RMQ.RankSelect.fixedWeightBlockClassLengthTableOverheadLeChunkSentinelBudget`
  feed the chunk-count bounds into the class/length metadata budget.

In plain English: the project now has a verified way to cut the bitvector into
addressable pieces, add a harmless fallback piece, and prove that the access
route lands on the right local bit. It also has the enumerative accounting
bridge saying that the product of the per-block fixed-weight universes does
not exceed the global fixed-weight universe, up to one integer-code slack bit
per block.

## Live Assumptions

- The query cost is modeled. Reads from bounded stores and fixed-width tables
  are charged under the repository's RAM/indexed-access convention.
- The specialized log-chunk computed-RRR envelope is formally obstructed under
  a fixed local query cost. The replacement table/RAM envelope is now present,
  and its log-chunk profile now consumes the primary block-code budget. The
  split-width repair is also present: route fields and local class/length
  fields have independent widths. Its concrete shared decoder payload and the
  final route/rank/select directory constructor are still open.
- For sentinel log chunks, the primary block-code budget is now discharged by
  `RMQ.RankSelect.fixedWeightLogChunkBlockPayloadBudgetLePayloadBudgetAddBound`
  and consumed by the log-chunk ambient/envelope profile theorems.
- Generic non-log-chunk profile shapes can still be conditional on their own
  primary block-code budget.
- Route exactness must come from charged route/class-length tables, not from
  proof-only access to a decoded bitvector.
- Dense all-code decoder tables at log-chunk size are formally too large:
  `RMQ.RankSelect.noFixedWeightLogChunkDenseDecoderLittleO` rules out counting
  that design as `o(n)` auxiliary payload. The positive constructor needs a
  smaller/shared decoder discipline.
- The current route-field-table adapter is payload-backed, but route fields
  such as base ranks and block starts cannot simply share the narrow
  class/length field width. The split-width table/RAM envelope now supplies
  that separation; the next design must instantiate it with concrete route
  payloads and a compact shared decoder.

## Theorem Anchors

The public adapter shape is
`RMQ.RankSelect.fixedWeightCompressedAuxiliaryToCompressedFamilyProfile`.

The local and ambient construction anchors are:

- `RMQ.RankSelect.fixedWeightComputedRRRBlockKernelProfile`;
- `RMQ.RankSelect.fixedWeightComputedRRRClassLengthBlockKernelProfile`;
- `RMQ.RankSelect.fixedWeightAmbientComputedRRRBlockCompositionProfile`;
- `RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeProfile`;
- `RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFixedBlockSizeWordBoundedCompressedProfileOfBlockBounds`;
- `RMQ.RankSelect.fixedWeightAmbientBlockCompositionWordBoundedCompressedProfileOfPrimaryBudget`.
- `RMQ.RankSelect.fixedWeightBlockPayloadBudgetLePayloadBudgetFlattenAddBlocks`;
- `RMQ.RankSelect.fixedWeightLogChunkBlockPayloadBudgetLePayloadBudgetAddBound`;
- `RMQ.RankSelect.fixedWeightAmbientBlockCompositionWordBoundedCompressedProfileOfLogChunkBlocks`;
- `RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfLogChunkBlocks`.
- `RMQ.RankSelect.fixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeWordBoundedCompressedProfile`.
- `RMQ.RankSelect.noFixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily`.
- `RMQ.RankSelect.fixedWeightAmbientTableRAMRouteDirectoryProfile`.
- `RMQ.RankSelect.fixedWeightAmbientTableRAMRouteDirectoryFamilyWordBoundedCompressedProfileOfPrimaryBudget`.
- `RMQ.RankSelect.fixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyWordBoundedCompressedProfile`.
- `RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToTableRAMRouteDirectoryFamily`.
- `RMQ.RankSelect.noFixedWeightLogChunkDenseDecoderLittleO`.
- `RMQ.RankSelect.noFixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyRouteWidthClassLength`.
- `RMQ.RankSelect.fixedWeightAmbientTableRAMSplitWidthRouteDirectoryProfile`.
- `RMQ.RankSelect.fixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamilyWordBoundedCompressedProfileOfPrimaryBudget`.
- `RMQ.RankSelect.fixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamilyWordBoundedCompressedProfile`.
- `RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToSplitWidthTableRAMRouteDirectoryFamily`.

## Skeptical Grad Student Questions

**Did this close compressed/FID rank/select?**

No. It closed a route-and-chunk layer needed by the global constructor, proved
that the specialized computed-RRR log-chunk envelope cannot itself be the final
constructor target with fixed local query cost, and then added the replacement
charged table/RAM route-directory envelope. The latest step consumes the
log-chunk primary block-code budget in that table/RAM profile, proves that the
old single-width route/class-length design is itself obstructed, and adds the
split-width table/RAM profile that separates route fields from local
class/length fields. The remaining public compressed/FID theorem needs a
concrete instantiation of that split-width family with payload-backed route
directories and a counted shared decoder payload. The dense log-chunk decoder
and route-width class/length shortcuts are now formal dead ends, not missing
lemmas.

**Why add a sentinel chunk?**

It makes total query routing uniform. Invalid or out-of-range cases can route
to an empty fallback block without changing the flattened represented bits.
This helps total functions stay simple while preserving the semantics.

**What is the difference between the packed readback baseline and the FID
target?**

The readback baseline proves the answers depend on payload by reading and
decoding the whole packed representation. The FID target must read only a
constant-size route/local payload slice per query.

**What should the next proof worker actually build?**

A concrete charged route-directory family that instantiates
`FixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamily`: build a
sublinear shared decoder payload, prove its `o(n)` budget under the chosen
microblock size, and build route payloads whose charged reads provide the
access/rank/select route fields without forcing linear class/length metadata.

