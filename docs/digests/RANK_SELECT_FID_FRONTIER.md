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
and select in constant modeled time. The recent chunk-route milestone does not
finish that theorem. It gives the global router a concrete set of blocks and a
sentinel fallback, so later route tables can point to real charged block-code
words rather than to an implicit decoded bitvector.

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
route lands on the right local bit. That is a routing milestone, not a finished
compressed dictionary.

## Live Assumptions

- The query cost is modeled. Reads from bounded stores and fixed-width tables
  are charged under the repository's RAM/indexed-access convention.
- Local computed-RRR decoding still has an explicit local cost discipline.
  The global constant-time theorem needs a uniform bounded-regime story.
- Several profiles are conditional on the primary block-code budget:
  the sum of per-block fixed-weight code budgets must be at most the global
  fixed-weight payload budget plus an `o(n)` overhead.
- Route exactness must come from charged route/class-length tables, not from
  proof-only access to a decoded bitvector.

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

## Skeptical Grad Student Questions

**Did this close compressed/FID rank/select?**

No. It closed a route-and-chunk layer needed by the global constructor. The
remaining public compressed/FID theorem still needs the primary block-code
budget and route exactness for rank/select from concrete charged tables.

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

A concrete charged route-directory family over the chunk blocks, plus the
primary block-code budget. The worker should avoid route fields whose exactness
is supplied by proof-only decoded bits.

