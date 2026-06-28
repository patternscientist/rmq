# Rank/Select FID Frontier Digest

Snapshot: 2026-06-28. This note digests the rank/select compressed/FID spoke
after the log-chunk primary-budget bridge, the table/RAM route-directory
envelope, and the split-width route-vs-class/length repair merged to `main`.

This note is for a reader who may not know rank/select. For a bitvector,
`access i` asks for the bit at position `i`; `rank b i` counts how many bits
equal to `b` appear before position `i`; `select b k` asks where the `k`th
bit equal to `b` occurs.

## What Changed Conceptually

The plain-bitvector Jacobson/Clark theorem is already landed:

```lean
#check RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery
#check RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery
```

The moving frontier is compressed/FID rank/select. A fixed-weight bitvector
has exactly `m` one-bits among `n` positions. The compressed target is to store
the bitvector near the information-theoretic count
`log2 (binomialCount n m)`, not by storing all `n` bits, while still answering
access/rank/select in constant modeled time.

The merged primary-budget bridge says that sentinel-log-chunk per-block
fixed-weight codes fit under the global fixed-weight payload budget plus
`o(n)`. The merged split-width table/RAM layer then separates wide route fields
from narrow local class/length fields, avoiding the formally obstructed
single-width metadata design.

## Plain English Story

RRR/FID decomposes the bitvector into blocks. Each block stores its own length,
its number of ones, and a code saying which fixed-weight pattern it contains.
A query should read a small route record, jump to the addressed block, read
that block's code and metadata, and answer locally.

The already-merged chunk-route layer gives:

- `RMQ.RankSelect.fixedWeightChunkAccessRouteWithSentinel`;
- `RMQ.RankSelect.fixedWeightChunkRankRouteWithSentinel`;
- `RMQ.RankSelect.fixedWeightChunkSelectRouteWithSentinel`;
- `RMQ.RankSelect.fixedWeightLogChunkBlockClassLengthTableOverheadLe`;
- `RMQ.RankSelect.fixedWeightLogChunkRouteWidthClassLengthOverheadNotLittleO`.

In words: the project knows how to cut the bitvector into log-sized chunks,
add an empty sentinel chunk for total routing, prove access/rank/select route
equations, prove narrow class/length metadata is `o(n)`, and prove one
tempting padded metadata layout is too large.

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

**Why was the primary budget hard?**

A block decomposition can accidentally lose compression if each block pays its
own rounded-up code length. The new theorem uses a finite counting/product
argument to show the product of block universes fits inside the global
fixed-weight universe plus one slack bit per block.

**What is still possibly oracle-like?**

Any profile that assumes route fields or exact local answers as proof data
rather than deriving them from charged payload reads. The next family must
consume the route equations through a concrete store.

**What should the next proof worker actually build?**

A concrete charged route-directory family that instantiates
`FixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamily`: build a
sublinear shared decoder payload, prove its `o(n)` budget under the chosen
microblock size, and build route payloads whose charged reads provide the
access/rank/select route fields without forcing linear class/length metadata.

A concrete charged route-directory/local-decoder family over
`fixedWeightLogChunkBlocksWithSentinel`, consuming the split-width table/RAM
profile rather than the older single-width route/class-length envelope.
The stop condition should be a public compressed/FID profile with no
proof-only route fields and a uniform constant modeled query bound.
