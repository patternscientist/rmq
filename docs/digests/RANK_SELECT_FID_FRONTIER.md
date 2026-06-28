# Rank/Select FID Frontier Digest

Snapshot: 2026-06-28. Stable base is `main` at `c92c8af`. The log-chunk
primary-budget statements in this note are branch-relative to the latest
rank/select proof worktree until that branch merges.

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

The branch-relative update is that sentinel log chunks now have the primary
fixed-weight budget bridge. Previously the digest could only say that the
per-block codes fit under raw `n + o(n)`. The new proof says the per-block
fixed-weight codes fit under the global fixed-weight payload budget plus
`o(n)`.

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

The branch-local primary-budget bridge adds:

- `RMQ.RankSelect.binomialCountMulLeAdd`;
- `RMQ.RankSelect.fixedWeightBlockPayloadBudgetLePayloadBudgetFlattenAddBlocks`;
- `RMQ.RankSelect.fixedWeightLogChunkBlockPayloadBudgetLePayloadBudgetAddBound`;
- `RMQ.RankSelect.fixedWeightAmbientBlockCompositionWordBoundedCompressedProfileOfLogChunkBlocks`;
- `RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfLogChunkBlocks`.

In words: choosing one fixed-weight pattern per block is no more expensive
than choosing the whole fixed-weight bitvector at once, except for one slack
bit per block. Since log chunks give `o(n)` blocks, that slack is an auxiliary
`o(n)` term.

## Live Assumptions

- This is still a modeled RAM/indexed-access theorem. Charged table and word
  reads are mathematical cost events, not Lean runtime measurements.
- The log-chunk primary budget is branch-relative until the proof branch
  merges.
- Generic non-log-chunk profile shapes can still be conditional on their own
  primary block-code budgets.
- The full compressed/FID construction still needs a concrete charged
  route-directory/local-decoder family. Route facts by themselves are not
  executable payload.
- Local computed-RRR decoding still needs a uniform constant-time regime in
  the final family.

## Skeptical Grad Student Questions

**Did this close compressed/FID rank/select?**

No. It removed the log-chunk primary-budget blocker. The remaining theorem is
the concrete family: route fields and class/length data must be read from
counted payload, and the local decoder must fit the constant modeled query
budget.

**Why was the primary budget hard?**

A block decomposition can accidentally lose compression if each block pays its
own rounded-up code length. The new theorem uses a finite counting/product
argument to show the product of block universes fits inside the global
fixed-weight universe plus one slack bit per block.

**What is still possibly oracle-like?**

Any profile that assumes route fields or exact local answers as proof data
rather than deriving them from charged payload reads. The next family must
consume the route equations through a concrete store.

**What should the next proof worker build?**

A concrete charged route-directory/local-decoder family over
`fixedWeightLogChunkBlocksWithSentinel`, consuming
`fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfLogChunkBlocks`.
The stop condition should be a public compressed/FID profile with no
proof-only route fields and a uniform constant modeled query bound.
