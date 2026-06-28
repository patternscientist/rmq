# Rank/Select Spoke

Snapshot: 2026-06-27. This note records the first extracted succinct
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
RMQ.RankSelect.FixedWeightComputedRRRBlockData
RMQ.RankSelect.fixedWeightComputedRRRDecodeTicks
RMQ.RankSelect.fixedWeightComputedRRRQueryCost
RMQ.RankSelect.fixedWeightDecodedWordFromCode
RMQ.RankSelect.fixedWeightDecodedWordFromCodeFixedWeightCode
RMQ.RankSelect.fixedWeightComputedRRRDecodeFromReadValuesCosted
RMQ.RankSelect.fixedWeightComputedRRRDecodeFromReadValuesCostedEraseSingleton
RMQ.RankSelect.FixedWeightComputedRRRClassLengthBlockData
RMQ.RankSelect.fixedWeightComputedRRRClassLengthQueryCost
RMQ.RankSelect.fixedWeightComputedRRRClassLengthBlockSizeQueryCost
RMQ.RankSelect.fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
RMQ.RankSelect.fixedWeightComputedRRRDecodeFromClassLengthReadValuesCostedEraseSingleton
RMQ.RankSelect.FixedWeightComputedRRRClassLengthBlockKernelProfile
RMQ.RankSelect.fixedWeightComputedRRRClassLengthBlockKernelProfile
RMQ.RankSelect.fixedWeightComputedRRRClassLengthBlockDependentAuxiliaryDataProfile
RMQ.RankSelect.fixedWeightBlockLengthEntries
RMQ.RankSelect.fixedWeightBlockClassEntries
RMQ.RankSelect.fixedWeightBlockClassLengthTableWords
RMQ.RankSelect.fixedWeightBlockClassLengthTablePayload
RMQ.RankSelect.fixedWeightBlockClassLengthTableOverhead
RMQ.RankSelect.fixedWeightBlockClassLengthTableOverheadBudget
RMQ.RankSelect.fixedWeightChunkBlocks
RMQ.RankSelect.fixedWeightChunkBlockCountBound
RMQ.RankSelect.fixedWeightChunkBlocksWithSentinel
RMQ.RankSelect.fixedWeightChunkBlockCountBoundWithSentinel
RMQ.RankSelect.fixedWeightLogChunkBlockSize
RMQ.RankSelect.fixedWeightLogChunkBlocks
RMQ.RankSelect.fixedWeightLogChunkBlockCountBound
RMQ.RankSelect.fixedWeightLogChunkBlocksWithSentinel
RMQ.RankSelect.fixedWeightLogChunkBlockCountBoundWithSentinel
RMQ.RankSelect.fixedWeightLogChunkBlockSizePos
RMQ.RankSelect.fixedWeightLogChunkBlockCountBoundLittleO
RMQ.RankSelect.fixedWeightLogChunkBlockCountBoundWithSentinelLittleO
RMQ.RankSelect.fixedWeightChunkBlocksFlatten
RMQ.RankSelect.fixedWeightChunkBlocksLengthLe
RMQ.RankSelect.fixedWeightChunkBlocksBlockLengthLe
RMQ.RankSelect.fixedWeightChunkBlocksWithSentinelFlatten
RMQ.RankSelect.fixedWeightChunkBlocksWithSentinelLengthLe
RMQ.RankSelect.fixedWeightChunkBlocksWithSentinelBlockLengthLe
RMQ.RankSelect.fixedWeightLogChunkBlocksFlatten
RMQ.RankSelect.fixedWeightLogChunkBlocksLengthLe
RMQ.RankSelect.fixedWeightLogChunkBlocksBlockLengthLe
RMQ.RankSelect.fixedWeightLogChunkBlocksWithSentinelFlatten
RMQ.RankSelect.fixedWeightLogChunkBlocksWithSentinelLengthLe
RMQ.RankSelect.fixedWeightLogChunkBlocksWithSentinelBlockLengthLe
RMQ.RankSelect.fixedWeightChunkBlocksWithSentinelGetSentinel
RMQ.RankSelect.fixedWeightChunkBlocksWithSentinelGetChunk
RMQ.RankSelect.fixedWeightChunkBlocksGetAccessExact
RMQ.RankSelect.fixedWeightChunkBlocksGetRankPrefixAddExact
RMQ.RankSelect.fixedWeightChunkBlocksGetSelectExactOfGlobalSelect
RMQ.RankSelect.fixedWeightChunkAccessRouteWithSentinel
RMQ.RankSelect.fixedWeightChunkRankRouteWithSentinel
RMQ.RankSelect.fixedWeightChunkSelectRouteWithSentinel
RMQ.RankSelect.fixedWeightBlockClassLengthTablePayloadLength
RMQ.RankSelect.FixedWeightAmbientComputedRRRClassLengthTableData
RMQ.RankSelect.FixedWeightAmbientComputedRRRClassLengthTableProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRClassLengthTableProfile
RMQ.RankSelect.FixedWeightComputedRRRBlockKernelProfile
RMQ.RankSelect.fixedWeightComputedRRRBlockKernelProfile
RMQ.RankSelect.fixedWeightComputedRRRBlockToBoundedCompressedDirectory
RMQ.RankSelect.fixedWeightComputedRRRBlockBoundedCompressedDirectoryProfile
RMQ.RankSelect.fixedWeightComputedRRRBlockToDependentAuxiliaryData
RMQ.RankSelect.fixedWeightComputedRRRBlockDependentAuxiliaryDataProfile
RMQ.RankSelect.fixedWeightComputedRRRBlockDependentAuxiliaryBridgeProfile
RMQ.RankSelect.fixedWeightComputedRRRBlockDependentAuxiliaryFullProfile
RMQ.RankSelect.FixedWeightAmbientComputedRRRAccessRoute
RMQ.RankSelect.FixedWeightAmbientComputedRRRRankRoute
RMQ.RankSelect.FixedWeightAmbientComputedRRRSelectRoute
RMQ.RankSelect.FixedWeightAmbientComputedRRRBlockData
RMQ.RankSelect.fixedWeightAmbientComputedRRRBlockToCompositionData
RMQ.RankSelect.FixedWeightAmbientComputedRRRBlockCompositionProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRBlockCompositionProfile
RMQ.RankSelect.FixedWeightAmbientComputedRRRRouteTableData
RMQ.RankSelect.FixedWeightAmbientComputedRRRRouteTableFamily
RMQ.RankSelect.FixedWeightAmbientComputedRRRBlockSizeRouteTableData
RMQ.RankSelect.FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableAccessMetadataReadsCosted
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableRankMetadataReadsCosted
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableSelectMetadataReadsCosted
RMQ.RankSelect.FixedWeightAmbientComputedRRRRouteTableReadProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableReadProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableToComputedRRRBlockData
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableToCompositionData
RMQ.RankSelect.FixedWeightAmbientComputedRRRRouteTableProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableFamilyDirectory
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableFamilyProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyDirectory
RMQ.RankSelect.fixedWeightAmbientComputedRRRBlockSizeRouteTableProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyProfile
RMQ.RankSelect.FixedWeightAmbientComputedRRRDecodedAccessRoute
RMQ.RankSelect.FixedWeightAmbientComputedRRRDecodedRankRoute
RMQ.RankSelect.FixedWeightAmbientComputedRRRDecodedSelectRoute
RMQ.RankSelect.FixedWeightAmbientComputedRRRDecodedRouteTableData
RMQ.RankSelect.FixedWeightAmbientComputedRRRDecodedRouteTableFamily
RMQ.RankSelect.FixedWeightAmbientComputedRRRDecodedMetadataReadProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRDecodedMetadataReadProfile
RMQ.RankSelect.FixedWeightAmbientComputedRRRDecodedRouteTableProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRDecodedRouteTableProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRDecodedRouteTableFamilyDirectory
RMQ.RankSelect.fixedWeightAmbientComputedRRRDecodedRouteTableFamilyProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableWordBoundedCompressedProfileOfPrimaryBudget
RMQ.RankSelect.fixedWeightAmbientComputedRRRBlockSizeRouteTableWordBoundedCompressedProfileOfPrimaryBudget
RMQ.RankSelect.fixedWeightAmbientComputedRRRDecodedRouteTableWordBoundedCompressedProfileOfPrimaryBudget
RMQ.RankSelect.FixedWeightAmbientComputedRRRPackedRouteTableData
RMQ.RankSelect.FixedWeightAmbientComputedRRRPackedRouteTableFamily
RMQ.RankSelect.fixedWeightAmbientComputedRRRPackedAccessMetadataReadValuesEq
RMQ.RankSelect.fixedWeightAmbientComputedRRRPackedRankMetadataReadValuesEq
RMQ.RankSelect.fixedWeightAmbientComputedRRRPackedSelectMetadataReadValuesEq
RMQ.RankSelect.FixedWeightAmbientComputedRRRPackedRouteTableProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRPackedRouteTableProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRPackedRouteTableFamilyDirectory
RMQ.RankSelect.fixedWeightAmbientComputedRRRPackedRouteTableFamilyProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRPackedRouteTableWordBoundedCompressedProfileOfPrimaryBudget
RMQ.RankSelect.FixedWeightAmbientComputedRRRRouteFieldTablesData
RMQ.RankSelect.FixedWeightAmbientComputedRRRRouteFieldTablesFamily
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTablesToPackedRouteTableData
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTablesPackedProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTablesFamilyDirectory
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTablesFamilyProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTablesWordBoundedCompressedProfileOfPrimaryBudget
RMQ.RankSelect.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
RMQ.RankSelect.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutToPackedRouteTableData
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutPackedProfile
RMQ.RankSelect.fixedWeightRouteFieldTableLayoutPayloadLength
RMQ.RankSelect.fixedWeightRouteFieldTableLayoutBoundedStoreWordsToList
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutOfCanonicalFixedWidthTables
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutToRouteClassLengthTableEnvelopeData
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutToRouteClassLengthTableEnvelopeProfile
RMQ.RankSelect.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
RMQ.RankSelect.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthEnvelopeToClassLengthAmbientBlockCompositionData
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverheadLittleO
RMQ.RankSelect.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamilyDirectory
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamilyProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfPrimaryBudget
RMQ.RankSelect.FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
RMQ.RankSelect.fixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamilyDirectory
RMQ.RankSelect.fixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeWordBoundedCompressedProfile
RMQ.RankSelect.noFixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
RMQ.RankSelect.noFixedWeightComputedRRRClassLengthLogChunkBlockSizeUniformCost
RMQ.RankSelect.noFixedWeightLogChunkRouteFieldTableLayoutFamilyToEnvelopeUniformCost
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyDirectory
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToRouteClassLengthTableEnvelopeFamilyProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFixedBlockSizeRouteClassLengthTableEnvelopeFamilyProfile
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutWordBoundedCompressedProfileOfPrimaryBudget
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfPrimaryBudget
RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFixedBlockSizeWordBoundedCompressedProfileOfBlockBounds
RMQ.RankSelect.fixedWeightBlockClassLengthTableOverheadLeOfBounds
RMQ.RankSelect.fixedWeightBlockClassLengthTableOverheadLeBudget
RMQ.RankSelect.fixedWeightBlockClassLengthTableOverheadLeChunkBudget
RMQ.RankSelect.fixedWeightBlockClassLengthTableOverheadLeChunkSentinelBudget
RMQ.RankSelect.FixedWeightTableRAMBlockData
RMQ.RankSelect.fixedWeightTableRAMBlockDataProfile
RMQ.RankSelect.fixedWeightTableRAMBlockToDependentAuxiliaryData
RMQ.RankSelect.fixedWeightTableRAMBlockDependentAuxiliaryDataProfile
RMQ.RankSelect.fixedWeightTableRAMBlockDependentAuxiliaryBridgeProfile
RMQ.RankSelect.fixedWeightTableRAMBlockDependentAuxiliaryFullProfile
RMQ.RankSelect.FixedWeightTableRAMBlockDependentReadProfile
RMQ.RankSelect.fixedWeightTableRAMBlockDependentReadProfile
RMQ.RankSelect.fixedWeightBlockCodeWords
RMQ.RankSelect.fixedWeightBlockCodePayload
RMQ.RankSelect.fixedWeightBlockPayloadBudget
RMQ.RankSelect.fixedWeightBlockCodePayloadLength
RMQ.RankSelect.fixedWeightBlockCodeBoundedStore
RMQ.RankSelect.fixedWeightBlockCodeBoundedStoreWordsToList
RMQ.RankSelect.fixedWeightAmbientBlockCodeStoreGetOfAligned
RMQ.RankSelect.fixedWeightBlockCodeBoundedStoreGetOfBlock
RMQ.RankSelect.fixedWeightAmbientBlockAuxiliaryOverhead
RMQ.RankSelect.fixedWeightAmbientBlockAuxiliaryOverheadLittleO
RMQ.RankSelect.FixedWeightAmbientBlockCompositionData
RMQ.RankSelect.fixedWeightAmbientBlockCompositionDataProfile
RMQ.RankSelect.fixedWeightAmbientBlockCompositionWordBoundedDataProfile
RMQ.RankSelect.FixedWeightAmbientBlockCompositionFamily
RMQ.RankSelect.fixedWeightAmbientBlockCompositionFamilyProfile
RMQ.RankSelect.fixedWeightAmbientBlockCompositionFamilyWordBoundedProfile
RMQ.RankSelect.fixedWeightAmbientBlockCompositionCompressedProfileOfPrimaryBudget
RMQ.RankSelect.fixedWeightAmbientBlockCompositionCompressedOverhead
RMQ.RankSelect.fixedWeightAmbientBlockCompositionWordBoundedCompressedProfileOfPrimaryBudget
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

The first table-backed local RRR-style checkpoint is
`FixedWeightTableRAMBlockData`. It reads the packed fixed-weight code from the
counted payload, uses that charged read value as the address into the universal
decoded-word table for the block length and weight, then runs the repository's
RAM word primitives for rank and select. Its profile is exposed as
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
`fixedWeightTableRAMBlockDependentAuxiliaryFullProfile`.

The replacement ambient table/RAM envelope is now present:
`FixedWeightAmbientTableRAMRouteDirectoryData` stores primary block
fixed-weight codes, a charged route store, a charged class/length store, and a
charged shared decoded-word table. Its access/rank/select queries read the
routed code word, read class/length plus route metadata, compute the shared
decode-table slot from those charged values, perform one charged decoded-word
read, and then use fixed RAM word primitives. The pointwise profile
`fixedWeightAmbientTableRAMRouteDirectoryProfile` records the payload split,
route-read equations for access/rank/select route fields, ambient word bounds,
and exact constant-modeled query behavior. The family theorem
`fixedWeightAmbientTableRAMRouteDirectoryFamilyWordBoundedCompressedProfileOfPrimaryBudget`
adds the public compressed/FID shape: if route overhead, class/length overhead,
decoder overhead, and the primary block-code slack are all `o(n)`, the resulting
compressed fixed-weight directory has payload
`fixedWeightPayloadBudget bits + o(n)` and constant modeled queries. This is a
positive replacement for the obstructed computed-RRR envelope, but it is still
conditional on a concrete counted shared decoder payload construction and the
microblock/slot arithmetic proving that decoder overhead is actually `o(n)`.
The log-chunk specialization
`fixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyWordBoundedCompressedProfile`
now consumes the existing primary block-code budget and narrow log-chunk
class/length overhead, so the primary-budget premise is no longer part of that
public table/RAM profile. The route-field-table adapter
`fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToTableRAMRouteDirectoryFamily`
also feeds the existing payload-backed fixed-width route tables into this
envelope. The repaired split-width envelope
`fixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamilyWordBoundedCompressedProfileOfPrimaryBudget`
and its log-chunk specialization
`fixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamilyWordBoundedCompressedProfile`
keep route-field width independent from class/length-field width; the adapter
`fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToSplitWidthTableRAMRouteDirectoryFamily`
feeds the existing charged route tables into that split-width family. Two
capstone shortcuts are now formally ruled out: a dense all-code
decoder at log-chunk size is not `o(n)`
(`noFixedWeightLogChunkDenseDecoderLittleO`), and padding class/length metadata
to route-width fields is not `o(n)`
(`fixedWeightLogChunkRouteWidthClassLengthOverheadNotLittleO`). More directly,
`noFixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyRouteWidthClassLength`
rules out the old single-width log-chunk table/RAM family when its class/length
field width is the route width. The remaining positive path must instantiate
the split-width envelope with concrete route-directory payloads and a genuinely
sublinear shared decoder discipline.

The stricter packed-code-only local checkpoint is now
`FixedWeightComputedRRRBlockData`. Its counted payload is exactly
`fixedWeightPackedPayload bits`, with no dense
`fixedWeightDecodedWordTablePayload`. Queries read the packed code word, spend
the explicit `fixedWeightComputedRRRDecodeTicks bits` evaluator budget to
compute the decoded local word, and then answer access/rank/select with fixed
code and RAM word primitives. `fixedWeightComputedRRRBlockKernelProfile`
records the direct local directory facts, while
`fixedWeightComputedRRRBlockDependentAuxiliaryDataProfile` packages the same
kernel through the generic dependent-read scaffold with zero auxiliary payload.
`fixedWeightComputedRRRBlockBoundedCompressedDirectoryProfile` is the bounded
local-regime finisher: if the caller supplies
`fixedWeightComputedRRRQueryCost bits <= queryCost`, then the same packed-code
kernel is a public compressed/FID directory with zero auxiliary payload and
all access/rank/select costs bounded by `queryCost`.
`fixedWeightComputedRRRBlockDependentAuxiliaryBridgeProfile` proves the generic
dependent-auxiliary adapter exposes the same payload, costs, and erased answers
as the direct local computed-RRR directory, and
`fixedWeightComputedRRRBlockDependentAuxiliaryFullProfile` packages that bridge
with the direct kernel profile and dependent-auxiliary directory profile.
This removes the local dense-table payload and arbitrary-evaluator escape hatch
simultaneously. It is still not the finished constant-time compressed/FID
family: the theorem isolates the local constant-bound premise, and global
composition must still discharge it from a concrete block-size primitive/table
model while also providing charged class/routing metadata.

The class/length-read local checkpoint is
`FixedWeightComputedRRRClassLengthBlockData`. It stores the packed fixed-weight
code plus two fixed-width metadata words for the local block length and class
(`trueCount`). `fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted`
decodes only from charged class/length read values plus the charged packed-code
read value, and
`fixedWeightComputedRRRDecodeFromClassLengthReadValuesCostedEraseSingleton`
proves exact readback for the canonical words. The profile
`fixedWeightComputedRRRClassLengthBlockKernelProfile` records the concrete
payload/read equations, word bounds, and access/rank/select exactness, and
`fixedWeightComputedRRRClassLengthBlockDependentAuxiliaryDataProfile` packages
the same kernel through the generic dependent-read scaffold with auxiliary
reads `[0, 1]`. This closes the local class/length readback gap for a single
block; the route/class-length envelope below now feeds those same reads from a
global charged metadata store.

That local checkpoint is now consumed by
`FixedWeightAmbientComputedRRRBlockData`. It produces a
`FixedWeightAmbientBlockCompositionData` whose query evaluators are fixed code:
read the routed packed block-code word, charge the route/class metadata reads
from the auxiliary store, run the computed local RRR decoder through
`toDependentAuxiliaryData`, and combine the local answer with the route
metadata. `fixedWeightAmbientComputedRRRBlockCompositionProfile` records the
ambient directory profile, code-store alignment, singleton charged code reads
for every route, local dependent-auxiliary profiles for the routed blocks, and
the discipline
`metadataReads.length <= routeCost`,
`fixedWeightComputedRRRQueryCost block <= localQueryCost`, and
`routeCost + localQueryCost <= queryCost`. The block-size refinement
`FixedWeightAmbientComputedRRRBlockSizeRouteTableData` derives that local-cost
premise from the uniform bound
`fixedWeightComputedRRRBlockSizeQueryCost blockSize = 2 ^ blockSize + blockSize + 2`
and the proved block-length discipline. Its family/profile theorems
`fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyProfile` and
`fixedWeightAmbientComputedRRRBlockSizeRouteTableWordBoundedCompressedProfileOfPrimaryBudget`
carry the derived local-cost cap through the ambient route-table layer. This is
the first ambient/global surface where the local decoded-table payload is gone
and the local kernel is actually consumed with a non-oracular block-size cost
discipline.

The route/class metadata has a counted table envelope in
`FixedWeightAmbientComputedRRRRouteTableData` and the family profile
`fixedWeightAmbientComputedRRRRouteTableFamilyProfile`. This layer owns a
concrete `routePayload` plus bounded `routeStore`, exposes the charged
metadata-read kernels
`fixedWeightAmbientComputedRRRRouteTableAccessMetadataReadsCosted`,
`fixedWeightAmbientComputedRRRRouteTableRankMetadataReadsCosted`, and
`fixedWeightAmbientComputedRRRRouteTableSelectMetadataReadsCosted`, proves the
erased read values are exactly the bounded-store reads at each route schedule,
and packages the auxiliary payload under the existing
`fixedWeightAmbientBlockAuxiliaryOverhead` little-o envelope. This base layer
still carries semantic route fields directly; the stricter decoded layer below
adds the charged-read decoder discipline while leaving concrete route-table
builders and the final constant local decode bound as future work.

That route/class envelope now has a stricter decoded-metadata checkpoint:
`FixedWeightAmbientComputedRRRDecodedRouteTableData` adds explicit metadata
read schedules and fixed decoders for the access/rank/select route fields.
`fixedWeightAmbientComputedRRRDecodedMetadataReadProfile` proves that mapping
those decoders over the charged route-store reads recovers the block index,
offset/base-rank/local-limit, or local occurrence/block-start fields consumed
by the ambient evaluator.  `fixedWeightAmbientComputedRRRDecodedRouteTableProfile`
and `fixedWeightAmbientComputedRRRDecodedRouteTableFamilyProfile` package those
facts with the existing route-table and `o(n)` route-payload envelope. This is
refined by `FixedWeightAmbientComputedRRRPackedRouteTableData`, whose public
readback lemmas show that access metadata reads return two fixed-width
`natToBitsLE` route words and rank/select metadata reads return three such
words.  `fixedWeightAmbientComputedRRRPackedRouteTableProfile` and
`fixedWeightAmbientComputedRRRPackedRouteTableFamilyProfile` carry this
fixed-width route-word discipline through the same ambient query profile and
`o(n)` route-payload envelope. This is still not a concrete global FID builder:
the packed record itself assumes per-slot word equations, but the new
`FixedWeightAmbientComputedRRRRouteFieldTablesData` constructor derives those
equations from a canonical `FixedWidthNatTable.ofEntries` route-field table.
The stronger `FixedWeightAmbientComputedRRRRouteFieldTableLayoutData` layer
splits the route fields into eight canonical fixed-width tables, concatenates
their words in route-store order, and proves the packed route profile from
local table slots. The analogous per-block length/class table substrate is now
present: `FixedWeightAmbientComputedRRRClassLengthTableData` stores
`fixedWeightBlockLengthEntries` and `fixedWeightBlockClassEntries` as two
fixed-width table segments, proves the counted payload length
`fixedWeightBlockClassLengthTablePayloadLength`, proves charged readback in
`fixedWeightAmbientComputedRRRClassLengthTableProfile`, and
`FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData` pairs that
table with the eight-table route layout in
`fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeProfile`. That
profile now concatenates route and class/length stores into one charged
ambient auxiliary store and exposes
`fixedWeightAmbientComputedRRRRouteClassLengthEnvelopeToClassLengthAmbientBlockCompositionData`,
whose ambient evaluator consumes the class/length prefix before running the
local RRR kernel. The adapter
`fixedWeightAmbientComputedRRRRouteFieldTableLayoutToRouteClassLengthTableEnvelopeProfile`
builds the envelope from an eight-table route layout under block-size and
local-cost side conditions. The family surface
`fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamilyProfile`
adds the combined route plus class/length `o(n)` accounting under a supplied
class/length-overhead budget, and
`fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfPrimaryBudget`
carries that through the conditional compressed/FID bridge. The route layout
also has a canonical constructor spine:
`fixedWeightRouteFieldTableLayoutPayloadLength` accounts for the eight
concatenated fixed-width route tables,
`fixedWeightRouteFieldTableLayoutBoundedStoreWordsToList` proves the canonical
store alignment, and
`fixedWeightAmbientComputedRRRRouteFieldTableLayoutOfCanonicalFixedWidthTables`
builds the route layout without assuming `routeStore_words_eq`. At the family
level,
`fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToRouteClassLengthTableEnvelopeFamilyProfile`
promotes an eight-table layout family to the combined class/length envelope,
and
`fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfPrimaryBudget`
carries that constructor through the conditional compressed/FID bridge. The
fixed block-size specialization
`fixedWeightAmbientComputedRRRRouteFieldTableLayoutFixedBlockSizeRouteClassLengthTableEnvelopeFamilyProfile`
packages the uniform `blockSize`/`fieldWidth` case and fixes the local budget to
the class/length block-size query cost. The global compressed/FID budget bridge
is
`fixedWeightAmbientComputedRRRRouteFieldTableLayoutFixedBlockSizeWordBoundedCompressedProfileOfBlockBounds`:
it takes `blocks.length <= blockCountBound bits.length` and
`fieldWidth <= fieldWidthBound bits.length`, packages the class/length
metadata budget as `fixedWeightBlockClassLengthTableOverheadBudget`, feeds
`fixedWeightBlockClassLengthTableOverheadLeBudget`, and returns the
word-bounded compressed/FID profile for the promoted route/class-length
envelope. The fixed-size chunk decomposition side is now concrete:
`fixedWeightChunkBlocks` wraps `SuccinctSpace.chunkPayloadWords`,
`fixedWeightChunkBlocksLengthLe` proves the useful
`blocks.length <= bits.length / blockSize + 1` bound, and
`fixedWeightBlockClassLengthTableOverheadLeChunkBudget` feeds that bound
directly into the class/length metadata budget. For total query routes,
`fixedWeightChunkBlocksWithSentinel` appends one empty sentinel block without
changing the flattened bits; `fixedWeightChunkBlocksWithSentinelLengthLe`
proves the routing-friendly `bits.length / blockSize + 2` bound, and
`fixedWeightChunkBlocksWithSentinelGetSentinel` identifies the fallback block
for invalid access/select cases. The log-sized variants
`fixedWeightLogChunkBlocks`, `fixedWeightLogChunkBlocksWithSentinel`, and
their length theorems specialize the same decomposition to
`Nat.log2 bits.length + 1` block size, while
`fixedWeightLogChunkBlockCountBoundLittleO` and
`fixedWeightLogChunkBlockCountBoundWithSentinelLittleO` prove the block-count
budget is `o(n)`.
The class/length directory side has been narrowed to the right width:
`fixedWeightLogChunkClassLengthFieldWidthBoundLittleO` proves the `log log n`
field-width bound is `o(n)`, `fixedWeightLogChunkClassLengthOverheadLittleO`
packages the resulting total overhead, and
`fixedWeightLogChunkBlockClassLengthTableOverheadLe` feeds the sentinel
log-chunk bounds into the table envelope. The route-width-padded alternative is
not just unaesthetic; `fixedWeightLogChunkRouteWidthClassLengthOverheadNotLittleO`
formalizes that storing class/length metadata at route width already costs
linear space.
The chunk/sentinel route exactness legs are now constructive:
`fixedWeightChunkAccessRouteWithSentinel` routes in-range positions to the
computed chunk and invalid positions to the sentinel, with
`fixedWeightChunkBlocksGetAccessExact` proving the stored-bit equation.
`fixedWeightChunkRankRouteWithSentinel` uses
`fixedWeightChunkBlocksGetRankPrefixAddExact` to add the prefix rank before the
routed block to the local chunk rank, and routes boundary/out-of-range rank
queries to the sentinel with full-prefix base rank.
`fixedWeightChunkSelectRouteWithSentinel` uses
`fixedWeightChunkBlocksGetSelectExactOfGlobalSelect` to localize a successful
global select to its selected chunk, and routes missing selects to the
sentinel. The remaining global constructor task is now a charged route-table
family over these chunk blocks that reads the route fields from payload, proves
rank/select route exactness, and resolves the metadata-width/local-decoder
discipline needed for a full compressed/FID theorem. The primary block-code
budget for these sentinel log chunks is now proved separately and consumed by
the log-chunk profile theorems.

The ambient/global block-composition predecessor is now present. It stores one
canonical fixed-weight code word per block through
`fixedWeightBlockCodePayload`, keeps the remaining directory bits in the
separate `fixedWeightAmbientBlockAuxiliaryOverhead` envelope, and proves that
this auxiliary envelope is `o(n)` by reusing the existing
`logLogSampledDirectoryOverhead` arithmetic. `FixedWeightAmbientBlockCompositionData`
packages the charged code-store and auxiliary-store reads, while
`fixedWeightAmbientBlockCompositionWordBoundedDataProfile` and
`fixedWeightAmbientBlockCompositionFamilyWordBoundedProfile` expose the ambient
machine-word bound against `Nat.log2 bits.length + 1` for both stores. The
alignment facts
`fixedWeightBlockCodeBoundedStoreWordsToList`,
`fixedWeightAmbientBlockCodeStoreGetOfAligned`, and
`fixedWeightBlockCodeBoundedStoreGetOfBlock` are the narrow bridge needed by a
later global router to read block `b`'s packed code word.

The ambient family theorem proves payload
`fixedWeightBlockPayloadBudget (blocks bits) + o(n)` with bounded payload
stores. The conditional bridges
`fixedWeightAmbientBlockCompositionCompressedProfileOfPrimaryBudget` and
`fixedWeightAmbientBlockCompositionWordBoundedCompressedProfileOfPrimaryBudget`
isolate the generic primary-budget theorem: for every `bits`,
`fixedWeightBlockPayloadBudget (blocks bits) <= fixedWeightPayloadBudget bits + primaryOverhead bits.length`
with `primaryOverhead = o(n)`. The word-bounded bridge additionally carries
the directory profile and ambient word-size discipline into the
`fixedWeightPayloadBudget bits + o(n)` compressed/FID shape.
The same conditional compressed bridge is now exposed directly for route-table
families by
`fixedWeightAmbientComputedRRRRouteTableWordBoundedCompressedProfileOfPrimaryBudget`
and
`fixedWeightAmbientComputedRRRBlockSizeRouteTableWordBoundedCompressedProfileOfPrimaryBudget`
and for decoded route-table families by
`fixedWeightAmbientComputedRRRDecodedRouteTableWordBoundedCompressedProfileOfPrimaryBudget`.
The packed route-word refinement is exposed by
`fixedWeightAmbientComputedRRRPackedRouteTableWordBoundedCompressedProfileOfPrimaryBudget`.
The canonical field-table constructors expose the same conditional bridge
through
`fixedWeightAmbientComputedRRRRouteFieldTablesWordBoundedCompressedProfileOfPrimaryBudget`
and
`fixedWeightAmbientComputedRRRRouteFieldTableLayoutWordBoundedCompressedProfileOfPrimaryBudget`.
These are generic compressed/FID public theorem shapes for arbitrary ambient
computed-RRR route layers, still conditional on a primary block-code budget.
For the log-sized sentinel chunk decomposition, that primary-budget premise is
now discharged. The generic bridge
`fixedWeightBlockPayloadBudgetLePayloadBudgetFlattenAddBlocks` proves that the
sum of per-block fixed-weight code widths is at most the global fixed-weight
payload budget for the flattened bitvector plus one slack bit per block. It is
based on `binomialCountMulLeAdd`, the Mathlib-free product/counting inequality
for concatenated fixed-weight universes. Specializing to sentinel log chunks,
`fixedWeightLogChunkBlockPayloadBudgetLePayloadBudgetAddBound` proves
```
fixedWeightBlockPayloadBudget (fixedWeightLogChunkBlocksWithSentinel bits)
  <= fixedWeightPayloadBudget bits
       + fixedWeightLogChunkBlockCountBoundWithSentinel bits.length
```
and the block-count overhead is already `o(n)`.
The consumed profiles
`fixedWeightAmbientBlockCompositionWordBoundedCompressedProfileOfLogChunkBlocks`
and
`fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfLogChunkBlocks`
therefore remove the explicit `primaryOverhead`/`hprimary` premise for families
whose block decomposition is `fixedWeightLogChunkBlocksWithSentinel`.
The specialized public surface
`fixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeWordBoundedCompressedProfile`
goes one step further: the theorem statement itself fixes the blocks to
`fixedWeightLogChunkBlocksWithSentinel` and fixes the class/length metadata
budget to `fixedWeightLogChunkClassLengthOverhead`, so there is no separate
`hblocks` argument or arbitrary class-length overhead to instantiate.
This surface is now known to be the wrong final constructor target:
`noFixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily`
proves that it cannot be inhabited with a fixed modeled local query cost,
because the component type still uses the current computed-RRR class/length
local decoder. The smaller obstruction
`noFixedWeightComputedRRRClassLengthLogChunkBlockSizeUniformCost` isolates the
unbounded local-cost function, and
`noFixedWeightLogChunkRouteFieldTableLayoutFamilyToEnvelopeUniformCost`
blocks the route-field-layout promotion path under exact log-chunk block-size
discipline.
The older theorem `fixedWeightLogChunkBlockPayloadBudgetLeLengthAddBound`
remains as a conservative raw upper bound
`fixedWeightBlockPayloadBudget (fixedWeightLogChunkBlocksWithSentinel bits)
  <= bits.length + o(n)`.
The remaining compressed/FID capstone gap is no longer this primary bridge for
log chunks, nor the abstract replacement envelope: the new
`FixedWeightAmbientTableRAMRouteDirectoryFamily` supplies the charged
route-directory/local-decoder family shape, and
`FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily` consumes the primary
block-code budget for sentinel log chunks. The new
`FixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamily` and
`FixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamily` retire the
single-width metadata collision by separating route and class/length widths.
The live gap is now the positive concrete constructor: supply concrete
route-directory payloads and a genuinely sublinear shared decoder payload for
that split-width family, then connect the existing chunk-route exactness to
charged directory reads. A dense all-code decoder for log chunks is ruled out by
`noFixedWeightLogChunkDenseDecoderLittleO`, and route-width-padded
class/length metadata is already known not to be `o(n)`.

## Module Boundary

The reusable public spec is:

- `RMQ/Core/RankSelectSpec.lean`
- `RMQ/Core/RankSelectCompressed.lean`
- `RMQ/Core/RankSelectCompressedSplit.lean`
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
   the class/length-read computed RRR kernel across the ambient
   block-composition scaffold, instantiates charged route tables for the
   now-constructive access/rank/select chunk routes, separates or otherwise
   narrows the class/length metadata width so log-sized chunks keep `o(n)`
   auxiliary payload, proves the enumerative block-primary budget bridge into
   the global fixed-weight payload, and replaces the current computed local
   decode-cost premise with a uniform constant table/RAM kernel;
2. deepening the landed `RMQBPNavigation` spoke into a fuller
   balanced-parentheses tree-navigation API over the same public rank/select
   surface;
3. neutral naming/facade polish if this module is later moved into a broader
   verified data-structures repository.
