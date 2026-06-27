# Rank/Select Spoke

Snapshot: 2026-06-25. This note records the first extracted succinct
data-structure spoke in the RMQ repository: plain bitvector access/rank/select.

## Import

Use the standalone import root:

```lean
import RMQRankSelect
```

`RMQRankSelect` exposes the public bitvector spec plus the concrete
Jacobson/Clark construction as a plain-bitvector API. Its proof-support import
closure currently shares the succinct-space and shape/lower-bound
infrastructure, so this is not yet a minimal dependency root. It does not
expose an RMQ/LCA/Fischer-Heun backend or the final succinct RMQ capstone as
its public API.

Verification:

```powershell
lake build RMQRankSelect
lake env lean scripts/rank_select_axiom_check.lean
```

## Public Headline

For plain bitvectors, the rank/select analogue of the RMQ `2n + o(n), O(1)`
headline is:

- store the `n` input bits plus `o(n)` auxiliary bits;
- support `access i`, `rank b i`, and `select b k`;
- charge a uniform constant number of modeled word-RAM/indexed-access steps per
  query;
- use exact reference semantics `bits[i]?`,
  `Succinct.rankPrefix b bits i`, and `Succinct.select b bits k`.

The reusable theorem shape is:

```lean
RMQ.RankSelectSpec.BitVectorRankSelectFamily.n_plus_o_constant_query_profile
```

This is not an existence theorem by itself: it packages the theorem once a
family is supplied.

The concrete landed Jacobson/Clark family theorem is exposed publicly as:

```lean
RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery
```

It proves `LittleOLinear` auxiliary overhead and, for every
`bits : List Bool`, counted payload length
`bits.length + jacobsonClarkRankSelectOverhead bits.length`, exact stored-bit
access, exact rank, exact select, and one fixed modeled query-cost bound.

The strengthened public word-bounded profile is:

```lean
RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery
```

It exposes the construction-level storage discipline: the Jacobson rank payload
words erase to the stored bitvector, and every Jacobson-rank or Clark-select
payload word read by the concrete adapter has length bounded by
`SuccinctRank.machineWordBits bits.length`.

## Compressed/FID Surface

The first compressed/FID layer is now exposed through:

```lean
RMQ.RankSelect.fixedWeightBitstrings
RMQ.RankSelect.fixedWeightBitstringsLength
RMQ.RankSelect.fixedWeightEncode?
RMQ.RankSelect.fixedWeightDecode?
RMQ.RankSelect.fixedWeightCode
RMQ.RankSelect.fixedWeightCodecRoundTrip
RMQ.RankSelect.fixedWeightDecodeEqSomeIff
RMQ.RankSelect.fixedWeightCodeLtPayloadBudgetPow
RMQ.RankSelect.fixedWeightPayloadBudget
RMQ.RankSelect.fixedWeightPackedPayload
RMQ.RankSelect.fixedWeightPackedPayloadLength
RMQ.RankSelect.fixedWeightPackedPayloadBitsToNatLE
RMQ.RankSelect.fixedWeightDecodePackedPayload
RMQ.RankSelect.fixedWeightPackedPayloadProfile
RMQ.RankSelect.fixedWeightPackedReadbackPayloadCosted
RMQ.RankSelect.fixedWeightPackedReadbackDecodeCosted
RMQ.RankSelect.fixedWeightPackedReadbackAccessCosted
RMQ.RankSelect.fixedWeightPackedReadbackRankCosted
RMQ.RankSelect.fixedWeightPackedReadbackSelectCosted
RMQ.RankSelect.fixedWeightPackedReadbackDirectory
RMQ.RankSelect.fixedWeightPackedReadbackDirectoryProfile
RMQ.RankSelect.fixedWeightPackedReadbackWordCount
RMQ.RankSelect.FixedWeightPackedReadbackData
RMQ.RankSelect.fixedWeightPackedReadbackDataOfChunks
RMQ.RankSelect.fixedWeightPackedReadbackDataProfile
RMQ.RankSelect.fixedWeightPackedReadbackDataOfChunksProfile
RMQ.RankSelect.fixedWeightAuxiliaryWordReadsCostedCost
RMQ.RankSelect.fixedWeightAuxiliaryWordReadsCostedErase
RMQ.RankSelect.fixedWeightDependentAuxiliaryWordReadsCostedCost
RMQ.RankSelect.fixedWeightDependentAuxiliaryWordReadsCostedErase
RMQ.RankSelect.compressedDirectoryProfile
RMQ.RankSelect.FixedWeightCompressedAuxiliaryData
RMQ.RankSelect.fixedWeightCompressedAuxiliaryDataProfile
RMQ.RankSelect.FixedWeightDependentAuxiliaryData
RMQ.RankSelect.fixedWeightDependentAuxiliaryDataProfile
RMQ.RankSelect.FixedWeightCompressedAuxiliaryFamily
RMQ.RankSelect.fixedWeightCompressedAuxiliaryToCompressedFamily
RMQ.RankSelect.fixedWeightCompressedAuxiliaryConstantQueryProfile
RMQ.RankSelect.fixedWeightCompressedAuxiliaryToCompressedFamilyProfile
RMQ.RankSelect.FixedWeightTableBackedFIDData
RMQ.RankSelect.fixedWeightTableBackedFIDDataProfile
RMQ.RankSelect.fixedWeightDecodedWordTablePayload
RMQ.RankSelect.fixedWeightDecodedWordTableOverhead
RMQ.RankSelect.fixedWeightDecodedWordTablePayloadLength
RMQ.RankSelect.fixedWeightDecodedWordBoundedStoreGetFixedWeightCode
RMQ.RankSelect.fixedWeightPackedCodeBoundedStoreGetZero
RMQ.RankSelect.FixedWeightTableRAMBlockData
RMQ.RankSelect.fixedWeightTableRAMBlockDataProfile
RMQ.RankSelect.fixedWeightTableRAMBlockToDependentAuxiliaryData
RMQ.RankSelect.fixedWeightTableRAMBlockDependentAuxiliaryDataProfile
RMQ.RankSelect.fixedWeightTableRAMBlockDependentAuxiliaryBridgeProfile
RMQ.RankSelect.fixedWeightTableRAMBlockDependentAuxiliaryFullProfile
RMQ.RankSelect.FixedWeightTableRAMBlockDependentReadProfile
RMQ.RankSelect.fixedWeightTableRAMBlockDependentReadProfile
RMQ.RankSelect.CompressedFamily
RMQ.RankSelect.compressedFixedWeightConstantQueryProfile
```

The fixed-weight universe is counted by a Mathlib-free binomial recurrence:
`fixedWeightBitstringsLength` proves that the number of length-`n` bitvectors
with exactly `k` true bits is `binomialCount n k`. The compressed profile uses
payload budget

```lean
Nat.log2 (binomialCount bits.length (trueCount bits)) + 1 + overhead bits.length
```

with `LittleOLinear overhead` and constant modeled `access`, `rank`, and
`select`. This is the target theorem shape for fully indexable dictionaries
(FID).

The canonical finite-universe codec spine is now also present:
`fixedWeightEncode?` finds a bitvector's rank in its fixed-weight universe,
`fixedWeightDecode?` indexes that universe, `fixedWeightDecodeEqSomeIff`
characterizes the two directions using `fixedWeightBitstringsNodup`, and
`fixedWeightCodecRoundTrip` gives the total encode/decode round trip. The
total code `fixedWeightCode` is proved below both
`binomialCount bits.length (trueCount bits)` and
`2 ^ fixedWeightPayloadBudget bits`. The packed realization
`fixedWeightPackedPayload` stores this canonical index with `natToBitsLE`;
`fixedWeightPackedPayloadProfile` proves the payload has exactly
`fixedWeightPayloadBudget bits` bits, reads back to `fixedWeightCode` through
`bitsToNatLE`, and decodes to the original bitvector.

The first charged query consumer is
`fixedWeightPackedReadbackDirectory`: it stores exactly
`fixedWeightPackedPayload bits`, charges each access/rank/select query the full
`fixedWeightPayloadBudget bits` readback cost, decodes through
`bitsToNatLE`/`fixedWeightDecode?`, and then answers against the decoded
reference bitvector. This is deliberately not the final constant-query FID; it
is the non-oracular readback baseline that proves queries depend on the packed
payload rather than proof-only fields.

The sharper readback scaffold is `FixedWeightPackedReadbackData`: it stores the
same packed payload in a `BoundedPayloadWordStore`, proves every readback word
is bounded by the chosen `wordSize`, charges one modeled read per stored word,
and exposes `fixedWeightPackedReadbackDataOfChunksProfile` for the canonical
chunking constructor. This still reads the whole packed representation per
query.

The current constant-query join layer is
`FixedWeightCompressedAuxiliaryData`: it stores the canonical
`fixedWeightPackedPayload bits` in one bounded word store, stores an auxiliary
payload of exactly `overhead` bits in a second bounded word store, and gives
each query an explicit packed-store and auxiliary-store read schedule. The
query cost is proved from the length of those schedules, and
`fixedWeightCompressedAuxiliaryDataProfile` converts the data into a
`CompressedDirectory`. At the family level,
`fixedWeightCompressedAuxiliaryConstantQueryProfile` feeds
`compressedFixedWeightConstantQueryProfile` whenever the auxiliary overhead is
`o(n)`. The named adapter theorem
`fixedWeightCompressedAuxiliaryToCompressedFamilyProfile` is the public
citation point for the generic theorem shape: once a future construction
supplies a `FixedWeightCompressedAuxiliaryFamily`, converting it to
`CompressedFamily` immediately gives the fixed-weight payload budget,
`LittleOLinear` auxiliary overhead, and constant modeled query profile.

This is the generic FID join surface, not yet the finished RRR/Clark
construction. A concrete non-oracular instantiation still has to provide local
evaluators whose exactness follows from the charged read values, rather than
from proof-only access to the decoded bitvector. In particular, the old
readback baseline remains useful as a reference consumer, but it is not the
constant-query compressed theorem path.

The dependent-read variant is `FixedWeightDependentAuxiliaryData`, backed by
`fixedWeightDependentAuxiliaryWordReadsCostedCost` and
`fixedWeightDependentAuxiliaryWordReadsCostedErase`. It generalizes the
static auxiliary schedules above by letting the auxiliary read schedule depend
on the charged packed-store read values. This is the missing scaffold for
RRR-style local blocks: a code/class read can choose the next table address
without forcing a static schedule. Its public profile
`fixedWeightDependentAuxiliaryDataProfile` still remains pointwise and still
has abstract evaluator fields; concrete non-oracular instances must expose
fixed code over the charged reads, and a family proof needs an `o(n)`
auxiliary payload construction.

The first stricter pointwise refinement is `FixedWeightTableBackedFIDData`.
Its query code is fixed: access, rank, and select are one charged
fixed-width payload-table read plus a small decoder. The table payloads are
counted inside the auxiliary payload, every table word is bounded by the
chosen `wordSize`, and the data requires `wordSize <= Nat.log2 bits.length + 1`
to avoid a one-huge-word interpretation. The profile
`fixedWeightTableBackedFIDDataProfile` is therefore stronger than the generic
auxiliary adapter because it has no arbitrary evaluator fields. It is still
pointwise scaffolding: dense answer tables can be too large, so the next
construction must replace those entries with true RRR/FID local tables and
charged routing while preserving the same fixed query shape.

The first concrete local RRR-style kernel is `FixedWeightTableRAMBlockData`.
It reads the packed fixed-weight code from the counted payload, uses that
charged read value as the address into the universal decoded-word table for
the block length and weight, then runs the repository's RAM word primitives for
rank and select. Its profile is exposed as
`fixedWeightTableRAMBlockDataProfile`, with query cost `<= 3` and with both
the packed-code payload and dense decoded-word-table payload accounted for.
The stronger `fixedWeightTableRAMBlockDependentReadProfile` exposes the actual
dependent-read spine: slot-zero packed-code read, decoded-word table read at
the erased code, direct decoded-word access, and fixed RAM primitives for
rank/select. The adapter
`fixedWeightTableRAMBlockDependentAuxiliaryDataProfile` also packages the same
kernel as an instance of the generic dependent auxiliary scaffold, and
`fixedWeightTableRAMBlockDependentAuxiliaryBridgeProfile` proves that the
scaffold-backed directory agrees with the direct local block directory on
payload, query costs, and erased answers. The combined public citation point is
`fixedWeightTableRAMBlockDependentAuxiliaryFullProfile`. This removes the
arbitrary-evaluator escape hatch at the block level. It is not the finished
compressed/FID family because the universal decoded-word table is dense and
the current word-size discipline is local to the block length; the remaining
work is an ambient/global block directory whose counted auxiliary payload is
`o(n)` and whose machine-word bound is stated against the ambient universe.

## Module Boundary

The reusable public spec is:

- `RMQ/Core/RankSelectSpec.lean`
- `RMQ/Core/RankSelectCompressed.lean`
- `RMQ/Core/RankSelectPublic.lean`

The concrete construction currently lives in:

- `RMQ/Core/SuccinctRank.lean`
- `RMQ/Core/SuccinctSelect.lean`
- `RMQ/Core/SuccinctSelect/TwoLevel.lean`
- `RMQ/Core/SuccinctSelect/Obstructions.lean`
- `RMQ/Core/SuccinctSelect/DenseLocalTables.lean`
- `RMQ/Core/SuccinctSelect.lean`
- `RMQ/Core/GenericSelect/LowLevel.lean`
- `RMQ/Core/GenericSelect/SelectFacts.lean`
- `RMQ/Core/GenericSelect/Arithmetic.lean`
- `RMQ/Core/GenericSelect/DenseEntryTable.lean`
- `RMQ/Core/GenericSelect/DenseWord.lean`
- `RMQ/Core/GenericSelect/RelativeSplit.lean`
- `RMQ/Core/GenericSelect/LegacyNames.lean`
- `RMQ/Core/GenericSelect/Params.lean`
- `RMQ/Core/GenericSelect/Primitives.lean`
- `RMQ/Core/GenericSelect/PrimitiveLegacyNames.lean`
- `RMQ/Core/GenericSelect/Slots.lean`
- `RMQ/Core/GenericSelect/Entries.lean`
- `RMQ/Core/GenericSelect/FlagRank.lean`
- `RMQ/Core/GenericSelect/RelativeTables.lean`
- `RMQ/Core/GenericSelect/Directory.lean`
- `RMQ/Core/GenericSelect/SelectSource.lean`
- `RMQ/Core/GenericSelect/Source.lean`
- `RMQ/Core/GenericSelect/Family.lean`
- `RMQ/Core/GenericSelect/BPCompat.lean`
- `RMQ/Core/GenericSelectLegacy.lean`

The old flat `GenericSelectParams` / `GenericSelectPrimitives` modules and the
`GenericSelect/Tables` module are compatibility barrels, not canonical homes for
new work.

The intended direction is:

```text
Succinct -> SuccinctSpace -> RankSelectSpec
Succinct -> SuccinctSpace -> SuccinctRank -> GenericSelect.SelectSource
SuccinctRank -> SuccinctSelect.{TwoLevel,Obstructions,DenseLocalTables}
GenericSelect.SelectSource --feeds downstream proposal--> SuccinctSelect
SuccinctRank -> GenericSelect.{SelectFacts,Arithmetic}
GenericSelect.SelectFacts -> GenericSelect.Arithmetic
GenericSelect.Arithmetic -> GenericSelect.DenseEntryTable
GenericSelect.DenseEntryTable -> GenericSelect.DenseWord
GenericSelect.DenseWord -> GenericSelect.RelativeSplit
GenericSelect.RelativeSplit -> GenericSelect.LowLevel
GenericSelect.LowLevel -> GenericSelect.{Params,Primitives}
GenericSelect.Primitives -> GenericSelect.PrimitiveLegacyNames
GenericSelect.{LegacyNames,PrimitiveLegacyNames} -> GenericSelectLegacy
GenericSelect.{Params,Primitives}
  -> GenericSelect.{Slots,Entries,FlagRank,RelativeTables,Directory,Source,
                    Family} -> SuccinctFinal
GenericSelect.SelectSource -> GenericSelect.Source
```

`RankSelectSpec` should stay small and upstream. Construction modules may adapt
into it, but it should not import the proposal/generic builders.
`RankSelectPublic` is the downstream facade that is allowed to import the
concrete Jacobson/Clark construction and expose short names.

## What Landed

The rank side uses:

```lean
RMQ.SuccinctRank.jacobsonRankData_profile
RMQ.SuccinctRank.jacobsonRankFamily_constant_query_profile
```

The select side uses the generic sparse-exception Clark-style source:

```lean
RMQ.GenericSelect.sparseExceptionSelectSource_profile
RMQ.GenericSelect.SparseExceptionSelectData.profile
RMQ.GenericSelect.SparseExceptionDirectory.profile
```

The public adapter combines one Jacobson rank directory with two select
sources, one for `false` and one for `true`:

```lean
RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery
RMQ.GenericSelect.jacobsonClarkRankSelectDirectory_profile
RMQ.GenericSelect.jacobsonClarkBitVectorRankSelectDirectory_profile
RMQ.GenericSelect.sparseExceptionSelectSource_rankSelectSpec_adapter_profile
RMQ.GenericSelect.jacobsonClarkRankSelectOverhead_littleO
RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile
RMQ.GenericSelect.jacobsonClarkRankSelectFamily_word_bounded_n_plus_o_constant_query_profile
```

The auxiliary payload is padded only to publish a clean exact overhead
expression. Query methods still call the concrete Jacobson rank data and the
concrete sparse/dense Clark select sources.

## Scope Notes

The public theorem is model-scoped. Constant query time means the repository's
modeled RAM/indexed-access cost: stored-bit access, table reads, and word
rank/select primitives are charged as constant-cost operations. It is not a
claim about Lean `List` runtime.

`ChargedSelectPositionSource` remains a contract boundary, not by itself a
non-oracular builder. The theorem
`RMQ.SuccinctSelect.chargedSelectPositionSource_allows_empty_select_oracle`
records the pitfall. The concrete public family avoids that escape by routing
through the built `GenericSelect.sparseExceptionSelectSource` construction.

The generic implementation now uses neutral select helper names internally.
Older `falseSelect*` spellings are quarantined in
`RMQ/Core/GenericSelect/LegacyNames.lean` and BP-specific bridge lemmas live in
the terminal compatibility root. The public facade keeps downstream users on
neutral `RMQ.RankSelect.*` names.

## Remaining Frontier

The plain-bitvector `n + o(n), O(1)` milestone is landed. The next research
targets are:

1. a concrete compressed/FID instantiation that composes
   `FixedWeightTableRAMBlockData`-style local kernels across blocks with
   charged global routing and `o(n)` counted auxiliary payload, then feeds the
   resulting family through `fixedWeightCompressedAuxiliaryConstantQueryProfile`;
2. deepening the landed `RMQBPNavigation` spoke into a fuller
   balanced-parentheses tree-navigation API over the same public rank/select
   surface;
3. neutral naming/facade polish if this module is later moved into a broader
   verified data-structures repository.
