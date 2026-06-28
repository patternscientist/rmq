import RMQ.Core.RankSelectSpec
import RMQ.Core.RankSelectCompressed
import RMQ.Core.GenericSelect.Family

/-!
Public facade for the standalone rank/select spoke.

The construction modules keep detailed Jacobson/Clark and sparse-exception
names. This module gives the reusable bitvector surface short, neutral names
for downstream data-structure spokes.
-/

namespace RMQ.RankSelect

/-- Public bitvector rank/select directory shape. -/
abbrev Directory :=
  RMQ.RankSelectSpec.BitVectorRankSelectDirectory

/-- Public bitvector rank/select family shape. -/
abbrev Family :=
  RMQ.RankSelectSpec.BitVectorRankSelectFamily

/-- Public compressed/FID bitvector rank/select directory shape. -/
abbrev CompressedDirectory :=
  RMQ.RankSelectSpec.CompressedBitVectorRankSelectDirectory

/-- Public compressed/FID directory profile theorem. -/
theorem compressedDirectoryProfile
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : CompressedDirectory bits overhead queryCost) :
    directory.payload.length <=
        RMQ.RankSelectSpec.fixedWeightPayloadBudget bits + overhead /\
      (forall i,
        (directory.accessQueryCosted i).cost <= queryCost /\
          (directory.accessQueryCosted i).erase = bits[i]?) /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <= queryCost /\
          (directory.rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <= queryCost /\
          (directory.selectQueryCosted target occurrence).erase =
            Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.CompressedBitVectorRankSelectDirectory.profile directory

/-- Public compressed/FID bitvector rank/select family shape. -/
abbrev CompressedFamily :=
  RMQ.RankSelectSpec.CompressedBitVectorRankSelectFamily

/-- Costed bounded-word read sequence used by compressed/FID auxiliary kernels. -/
abbrev fixedWeightAuxiliaryWordReadsCosted
    {payload : List Bool} {wordSize : Nat}
    (store :
      SuccinctSpace.BoundedPayloadWordStore payload wordSize) :=
  RMQ.RankSelectSpec.boundedPayloadWordReadsCosted store

/-- Cost of a bounded-word read sequence. -/
theorem fixedWeightAuxiliaryWordReadsCostedCost
    {payload : List Bool} {wordSize : Nat}
    (store :
      SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (indices : List Nat) :
    (fixedWeightAuxiliaryWordReadsCosted store indices).cost =
      indices.length := by
  exact RMQ.RankSelectSpec.boundedPayloadWordReadsCosted_cost store indices

/-- Erased bounded-word read sequence used by compressed/FID auxiliary kernels. -/
abbrev fixedWeightAuxiliaryWordReadValues
    {payload : List Bool} {wordSize : Nat}
    (store :
      SuccinctSpace.BoundedPayloadWordStore payload wordSize) :=
  RMQ.RankSelectSpec.boundedPayloadWordReadValues store

/-- Erasure of a bounded-word read sequence. -/
theorem fixedWeightAuxiliaryWordReadsCostedErase
    {payload : List Bool} {wordSize : Nat}
    (store :
      SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (indices : List Nat) :
    (fixedWeightAuxiliaryWordReadsCosted store indices).erase =
      fixedWeightAuxiliaryWordReadValues store indices := by
  exact RMQ.RankSelectSpec.boundedPayloadWordReadsCosted_erase store indices

/-- Dependent charged word reads used by RRR-style local block kernels. -/
abbrev fixedWeightDependentAuxiliaryWordReadsCosted
    {primaryPayload auxPayload : List Bool} {wordSize : Nat}
    (primaryStore :
      SuccinctSpace.BoundedPayloadWordStore primaryPayload wordSize)
    (auxStore :
      SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize)
    (primaryReads : List Nat)
    (auxReads : List (Option (List Bool)) -> List Nat) :=
  RMQ.RankSelectSpec.dependentPayloadWordReadsCosted
    primaryStore auxStore primaryReads auxReads

/-- Cost of dependent charged word reads. -/
theorem fixedWeightDependentAuxiliaryWordReadsCostedCost
    {primaryPayload auxPayload : List Bool} {wordSize : Nat}
    (primaryStore :
      SuccinctSpace.BoundedPayloadWordStore primaryPayload wordSize)
    (auxStore :
      SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize)
    (primaryReads : List Nat)
    (auxReads : List (Option (List Bool)) -> List Nat) :
    (fixedWeightDependentAuxiliaryWordReadsCosted primaryStore auxStore
        primaryReads auxReads).cost =
      primaryReads.length +
        (auxReads
          (fixedWeightAuxiliaryWordReadValues primaryStore
            primaryReads)).length := by
  exact
    RMQ.RankSelectSpec.dependentPayloadWordReadsCosted_cost
      primaryStore auxStore primaryReads auxReads

/-- Erasure of dependent charged word reads. -/
theorem fixedWeightDependentAuxiliaryWordReadsCostedErase
    {primaryPayload auxPayload : List Bool} {wordSize : Nat}
    (primaryStore :
      SuccinctSpace.BoundedPayloadWordStore primaryPayload wordSize)
    (auxStore :
      SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize)
    (primaryReads : List Nat)
    (auxReads : List (Option (List Bool)) -> List Nat) :
    (fixedWeightDependentAuxiliaryWordReadsCosted primaryStore auxStore
        primaryReads auxReads).erase =
      (fixedWeightAuxiliaryWordReadValues primaryStore primaryReads,
        fixedWeightAuxiliaryWordReadValues auxStore
          (auxReads
            (fixedWeightAuxiliaryWordReadValues primaryStore
              primaryReads))) := by
  exact
    RMQ.RankSelectSpec.dependentPayloadWordReadsCosted_erase
      primaryStore auxStore primaryReads auxReads

/-- Constant-bounded compressed/FID auxiliary data over a fixed-weight code. -/
abbrev FixedWeightCompressedAuxiliaryData :=
  RMQ.RankSelectSpec.FixedWeightCompressedAuxiliaryData

/-- Pointwise compressed/FID auxiliary data with dependent auxiliary reads. -/
abbrev FixedWeightDependentAuxiliaryData :=
  RMQ.RankSelectSpec.FixedWeightDependentAuxiliaryData

/-- Ambient/global block-composed fixed-weight data. -/
abbrev FixedWeightAmbientBlockCompositionData :=
  RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionData

/-- Family of ambient/global block-composed fixed-weight data. -/
abbrev FixedWeightAmbientBlockCompositionFamily :=
  RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionFamily

/-- Family of constant-bounded compressed/FID auxiliary data. -/
abbrev FixedWeightCompressedAuxiliaryFamily :=
  RMQ.RankSelectSpec.FixedWeightCompressedAuxiliaryFamily

/-- Pointwise table-backed FID data with fixed charged table-read queries. -/
abbrev FixedWeightTableBackedFIDData :=
  RMQ.RankSelectSpec.FixedWeightTableBackedFIDData

/-- Universal fixed-weight decoded-word table payload. -/
abbrev fixedWeightDecodedWordTablePayload :=
  RMQ.RankSelectSpec.fixedWeightDecodedWordTablePayload

/-- Bit cost of the universal fixed-weight decoded-word table. -/
abbrev fixedWeightDecodedWordTableOverhead :=
  RMQ.RankSelectSpec.fixedWeightDecodedWordTableOverhead

/-- Length of the universal fixed-weight decoded-word table payload. -/
abbrev fixedWeightDecodedWordTablePayloadLength :=
  RMQ.RankSelectSpec.fixedWeightDecodedWordTablePayload_length

/-- Canonical payload store for the universal fixed-weight decoded-word table. -/
abbrev fixedWeightDecodedWordStore :=
  RMQ.RankSelectSpec.fixedWeightDecodedWordStore

/-- Canonical bounded store for the universal fixed-weight decoded-word table. -/
abbrev fixedWeightDecodedWordBoundedStore :=
  RMQ.RankSelectSpec.fixedWeightDecodedWordBoundedStore

/-- Decoded fixed-weight entries are present in the bounded decoded-word store. -/
abbrev fixedWeightDecodedWordBoundedStoreGetOfDecode
    {n k code : Nat} {word : List Bool} {wordSize : Nat}
    (hn : n <= wordSize)
    (hdec :
      RMQ.RankSelectSpec.fixedWeightDecode? n k code = some word) :=
  RMQ.RankSelectSpec.fixedWeightDecodedWordBoundedStore_get?_of_decode
    hn hdec

/-- The decoded-word store returns the source bitvector at its canonical code. -/
abbrev fixedWeightDecodedWordBoundedStoreGetFixedWeightCode :=
  RMQ.RankSelectSpec.fixedWeightDecodedWordBoundedStore_get?_fixedWeightCode

/-- Canonical one-word bounded store for the packed fixed-weight code. -/
abbrev fixedWeightPackedCodeBoundedStore :=
  RMQ.RankSelectSpec.fixedWeightPackedCodeBoundedStore

/-- The packed-code store returns the packed fixed-weight payload at slot zero. -/
abbrev fixedWeightPackedCodeBoundedStoreGetZero :=
  RMQ.RankSelectSpec.fixedWeightPackedCodeBoundedStore_get?_zero

/-- Local table/RAM fixed-weight block kernel with fixed charged queries. -/
abbrev FixedWeightTableRAMBlockData :=
  RMQ.RankSelectSpec.FixedWeightTableRAMBlockData

/-- Local computed fixed-weight/RRR block kernel over the packed code only. -/
abbrev FixedWeightComputedRRRBlockData :=
  RMQ.RankSelectSpec.FixedWeightComputedRRRBlockData

/-- Local computed RRR block kernel with charged class/length metadata reads. -/
abbrev FixedWeightComputedRRRClassLengthBlockData :=
  RMQ.RankSelectSpec.FixedWeightComputedRRRClassLengthBlockData

/-- Global fixed-width table of per-block length/class metadata. -/
abbrev FixedWeightAmbientComputedRRRClassLengthTableData :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRClassLengthTableData

/-- Ambient access route metadata for computed fixed-weight/RRR blocks. -/
abbrev FixedWeightAmbientComputedRRRAccessRoute :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRAccessRoute

/-- Ambient rank route metadata for computed fixed-weight/RRR blocks. -/
abbrev FixedWeightAmbientComputedRRRRankRoute :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRankRoute

/-- Ambient select route metadata for computed fixed-weight/RRR blocks. -/
abbrev FixedWeightAmbientComputedRRRSelectRoute :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRSelectRoute

/--
Ambient/global block composition data backed by the computed local RRR kernel.
-/
abbrev FixedWeightAmbientComputedRRRBlockData :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockData

/-- Payload-backed route/class metadata table layer for ambient computed RRR. -/
abbrev FixedWeightAmbientComputedRRRRouteTableData :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableData

/-- Route/class metadata table layer with derived block-size local query cap. -/
abbrev FixedWeightAmbientComputedRRRBlockSizeRouteTableData :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockSizeRouteTableData

/-- Family of payload-backed route/class metadata tables. -/
abbrev FixedWeightAmbientComputedRRRRouteTableFamily :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableFamily

/-- Family of block-size route/class metadata tables. -/
abbrev FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily

/-- Decoded access route metadata recovered from charged table reads. -/
abbrev FixedWeightAmbientComputedRRRDecodedAccessRoute :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedAccessRoute

/-- Decoded rank route metadata recovered from charged table reads. -/
abbrev FixedWeightAmbientComputedRRRDecodedRankRoute :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedRankRoute

/-- Decoded select route metadata recovered from charged table reads. -/
abbrev FixedWeightAmbientComputedRRRDecodedSelectRoute :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedSelectRoute

/-- Route/class table data with decoded route fields from charged reads. -/
abbrev FixedWeightAmbientComputedRRRDecodedRouteTableData :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedRouteTableData

/-- Family of decoded route/class metadata tables. -/
abbrev FixedWeightAmbientComputedRRRDecodedRouteTableFamily :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedRouteTableFamily

/-- Route/class table data whose route fields are fixed-width payload words. -/
abbrev FixedWeightAmbientComputedRRRPackedRouteTableData :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRPackedRouteTableData

/-- Family of packed fixed-width route/class metadata tables. -/
abbrev FixedWeightAmbientComputedRRRPackedRouteTableFamily :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRPackedRouteTableFamily

/-- Canonical fixed-width route field table constructor data. -/
abbrev FixedWeightAmbientComputedRRRRouteFieldTablesData :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTablesData

/-- Family of canonical fixed-width route field table constructors. -/
abbrev FixedWeightAmbientComputedRRRRouteFieldTablesFamily :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTablesFamily

/-- Eight-table fixed-width route field layout data. -/
abbrev FixedWeightAmbientComputedRRRRouteFieldTableLayoutData :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData

/-- Family of eight-table fixed-width route field layouts. -/
abbrev FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily

/-- Route-field layout paired with concrete per-block length/class tables. -/
abbrev FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData

/-- Family of route-field layouts paired with concrete class/length tables. -/
abbrev FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily

/-- Counted fixed-weight bitvector universe used by the compressed/FID budget. -/
abbrev fixedWeightBitstrings :=
  RMQ.RankSelectSpec.fixedWeightBitstrings

/-- Mathlib-free binomial-count recurrence for fixed-weight bitvectors. -/
abbrev binomialCount :=
  RMQ.RankSelectSpec.binomialCount

/-- Number of true bits in a bitvector. -/
abbrev trueCount :=
  RMQ.RankSelectSpec.trueCount

/-- Fixed-weight information-theoretic payload budget for one bitvector. -/
abbrev fixedWeightPayloadBudget :=
  RMQ.RankSelectSpec.fixedWeightPayloadBudget

/-- Fixed-weight bitvector universe count. -/
abbrev fixedWeightBitstringsLength :=
  RMQ.RankSelectSpec.fixedWeightBitstrings_length

/-- Fixed-weight bitvector universes contain no duplicate entries. -/
abbrev fixedWeightBitstringsNodup :=
  RMQ.RankSelectSpec.fixedWeightBitstrings_nodup

/-- Canonical fixed-weight encoder into the counted universe. -/
abbrev fixedWeightEncode? :=
  RMQ.RankSelectSpec.fixedWeightEncode?

/-- Canonical fixed-weight decoder from the counted universe. -/
abbrev fixedWeightDecode? :=
  RMQ.RankSelectSpec.fixedWeightDecode?

/-- Total canonical fixed-weight code for a bitvector. -/
abbrev fixedWeightCode :=
  RMQ.RankSelectSpec.fixedWeightCode

/-- The total canonical code is produced by `fixedWeightEncode?`. -/
abbrev fixedWeightEncodeEqSomeFixedWeightCode :=
  RMQ.RankSelectSpec.fixedWeightEncode?_eq_some_fixedWeightCode

/-- Encode/decode round-trip fact for the canonical fixed-weight codec spine. -/
abbrev fixedWeightCodecRoundTrip :=
  RMQ.RankSelectSpec.fixedWeightCodec_roundTrip

/-- Valid decoded entries encode back to their source index. -/
abbrev fixedWeightEncodeFixedWeightDecode
    {n k code : Nat} {bits : List Bool}
    (hdec : fixedWeightDecode? n k code = some bits) :=
  RMQ.RankSelectSpec.fixedWeightEncode?_fixedWeightDecode? hdec

/-- Two-sided characterization of canonical fixed-weight decode. -/
abbrev fixedWeightDecodeEqSomeIff
    {n k code : Nat} {bits : List Bool} :=
  RMQ.RankSelectSpec.fixedWeightDecode?_eq_some_iff
    (n := n) (k := k) (code := code) (bits := bits)

/-- Encoded fixed-weight indices are bounded by the binomial-count universe. -/
abbrev fixedWeightEncodeLtBinomialCount
    {bits : List Bool} {code : Nat}
    (henc : fixedWeightEncode? bits = some code) :=
  RMQ.RankSelectSpec.fixedWeightEncode?_lt_binomialCount henc

/-- The total canonical code is bounded by the binomial-count universe. -/
abbrev fixedWeightCodeLtBinomialCount :=
  RMQ.RankSelectSpec.fixedWeightCode_lt_binomialCount

/-- Encoded fixed-weight indices fit in the fixed-weight payload budget. -/
abbrev fixedWeightEncodeLtPayloadBudgetPow
    {bits : List Bool} {code : Nat}
    (henc : fixedWeightEncode? bits = some code) :=
  RMQ.RankSelectSpec.fixedWeightEncode?_lt_payloadBudgetPow henc

/-- The total canonical code fits in the fixed-weight payload budget. -/
abbrev fixedWeightCodeLtPayloadBudgetPow :=
  RMQ.RankSelectSpec.fixedWeightCode_lt_payloadBudgetPow

/-- Concrete fixed-weight packed payload for one bitvector. -/
abbrev fixedWeightPackedPayload :=
  RMQ.RankSelectSpec.fixedWeightPackedPayload

/-- The packed fixed-weight payload has exactly the fixed-weight budget length. -/
abbrev fixedWeightPackedPayloadLength :=
  RMQ.RankSelectSpec.fixedWeightPackedPayload_length

/-- Decoding the packed payload word as a natural recovers the canonical code. -/
abbrev fixedWeightPackedPayloadBitsToNatLE :=
  RMQ.RankSelectSpec.fixedWeightPackedPayload_bitsToNatLE

/-- Decoding the packed payload code recovers the original bitvector. -/
abbrev fixedWeightDecodePackedPayload :=
  RMQ.RankSelectSpec.fixedWeightDecode?_packedPayload

/-- Combined fixed-weight packed-payload profile. -/
abbrev fixedWeightPackedPayloadProfile :=
  RMQ.RankSelectSpec.fixedWeightPackedPayload_profile

/-- Charged full-payload readback of the concrete fixed-weight packed payload. -/
abbrev fixedWeightPackedReadbackPayloadCosted :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackPayloadCosted

/-- Charged full-payload decode of the concrete fixed-weight packed payload. -/
abbrev fixedWeightPackedReadbackDecodeCosted :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackDecodeCosted

/-- Access through the charged fixed-weight packed readback decoder. -/
abbrev fixedWeightPackedReadbackAccessCosted :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackAccessCosted

/-- Rank through the charged fixed-weight packed readback decoder. -/
abbrev fixedWeightPackedReadbackRankCosted :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackRankCosted

/-- Select through the charged fixed-weight packed readback decoder. -/
abbrev fixedWeightPackedReadbackSelectCosted :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackSelectCosted

/-- Concrete charged packed-payload readback directory for one bitvector. -/
abbrev fixedWeightPackedReadbackDirectory :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackDirectory

/-- Profile for the charged packed-payload readback directory. -/
abbrev fixedWeightPackedReadbackDirectoryProfile :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackDirectory_profile

/-- Number of bounded payload words in the chunked packed readback view. -/
abbrev fixedWeightPackedReadbackWordCount :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackWordCount

/-- Chunked bounded-word readback data for the packed fixed-weight payload. -/
abbrev FixedWeightPackedReadbackData :=
  RMQ.RankSelectSpec.FixedWeightPackedReadbackData

/-- Canonical chunked bounded-word readback data. -/
abbrev fixedWeightPackedReadbackDataOfChunks :=
  RMQ.RankSelectSpec.FixedWeightPackedReadbackData.ofChunks

/-- Profile for chunked bounded-word packed readback data. -/
abbrev fixedWeightPackedReadbackDataProfile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :=
  RMQ.RankSelectSpec.FixedWeightPackedReadbackData.profile data

/-- Profile for canonical chunked bounded-word packed readback data. -/
abbrev fixedWeightPackedReadbackDataOfChunksProfile
    (bits : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :=
  RMQ.RankSelectSpec.FixedWeightPackedReadbackData.ofChunks_profile
    bits hword

/-- Packed fixed-weight words for each block in a block decomposition. -/
abbrev fixedWeightBlockCodeWords :=
  RMQ.RankSelectSpec.fixedWeightBlockCodeWords

/-- Per-block source lengths for the ambient class/length metadata table. -/
abbrev fixedWeightBlockLengthEntries :=
  RMQ.RankSelectSpec.fixedWeightBlockLengthEntries

/-- Per-block source classes for the ambient class/length metadata table. -/
abbrev fixedWeightBlockClassEntries :=
  RMQ.RankSelectSpec.fixedWeightBlockClassEntries

/-- Counted primary payload for block-coded fixed-weight blocks. -/
abbrev fixedWeightBlockCodePayload :=
  RMQ.RankSelectSpec.fixedWeightBlockCodePayload

/-- Fixed-width payload words for the per-block class/length metadata table. -/
abbrev fixedWeightBlockClassLengthTableWords :=
  RMQ.RankSelectSpec.fixedWeightBlockClassLengthTableWords

/-- Counted payload for the per-block class/length metadata table. -/
abbrev fixedWeightBlockClassLengthTablePayload :=
  RMQ.RankSelectSpec.fixedWeightBlockClassLengthTablePayload

/-- Counted bit overhead of the per-block class/length metadata table. -/
abbrev fixedWeightBlockClassLengthTableOverhead :=
  RMQ.RankSelectSpec.fixedWeightBlockClassLengthTableOverhead

/-- Family-level overhead budget for per-block class/length metadata tables. -/
abbrev fixedWeightBlockClassLengthTableOverheadBudget :=
  RMQ.RankSelectSpec.fixedWeightBlockClassLengthTableOverheadBudget

/-- Fixed-size chunk decomposition used by the ambient fixed-weight block track. -/
abbrev fixedWeightChunkBlocks :=
  RMQ.RankSelectSpec.fixedWeightChunkBlocks

/-- Block-count budget for fixed-size chunk decompositions. -/
abbrev fixedWeightChunkBlockCountBound :=
  RMQ.RankSelectSpec.fixedWeightChunkBlockCountBound

/-- Fixed-size chunk decomposition with one empty sentinel block for total routes. -/
abbrev fixedWeightChunkBlocksWithSentinel :=
  RMQ.RankSelectSpec.fixedWeightChunkBlocksWithSentinel

/-- Block-count budget for fixed-size chunk decompositions with a sentinel. -/
abbrev fixedWeightChunkBlockCountBoundWithSentinel :=
  RMQ.RankSelectSpec.fixedWeightChunkBlockCountBoundWithSentinel

/-- Fixed-size chunk blocks flatten back to the original bitvector. -/
theorem fixedWeightChunkBlocksFlatten
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    (bits : List Bool) :
    SuccinctSpace.flattenPayloadWords
        (fixedWeightChunkBlocks blockSize bits) = bits := by
  exact
    RMQ.RankSelectSpec.fixedWeightChunkBlocks_flatten
      hblockSize bits

/-- Fixed-size chunk decompositions use at most `n / blockSize + 1` blocks. -/
theorem fixedWeightChunkBlocksLengthLe
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    (bits : List Bool) :
    (fixedWeightChunkBlocks blockSize bits).length <=
      fixedWeightChunkBlockCountBound blockSize bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightChunkBlocks_length_le
      hblockSize bits

/-- Every fixed-size chunk block has length at most the chunk size. -/
theorem fixedWeightChunkBlocksBlockLengthLe
    {blockSize : Nat} {bits block : List Bool}
    (hmem : List.Mem block (fixedWeightChunkBlocks blockSize bits)) :
    block.length <= blockSize := by
  exact
    RMQ.RankSelectSpec.fixedWeightChunkBlocks_block_length_le
      hmem

/-- Sentinel chunk blocks flatten back to the original bitvector. -/
theorem fixedWeightChunkBlocksWithSentinelFlatten
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    (bits : List Bool) :
    SuccinctSpace.flattenPayloadWords
        (fixedWeightChunkBlocksWithSentinel blockSize bits) = bits := by
  exact
    RMQ.RankSelectSpec.fixedWeightChunkBlocksWithSentinel_flatten
      hblockSize bits

/-- Sentinel chunk decompositions use at most `n / blockSize + 2` blocks. -/
theorem fixedWeightChunkBlocksWithSentinelLengthLe
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    (bits : List Bool) :
    (fixedWeightChunkBlocksWithSentinel blockSize bits).length <=
      fixedWeightChunkBlockCountBoundWithSentinel
        blockSize bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightChunkBlocksWithSentinel_length_le
      hblockSize bits

/-- Every sentinel chunk block has length at most the chunk size. -/
theorem fixedWeightChunkBlocksWithSentinelBlockLengthLe
    {blockSize : Nat} {bits block : List Bool}
    (hmem :
      List.Mem block (fixedWeightChunkBlocksWithSentinel blockSize bits)) :
    block.length <= blockSize := by
  exact
    RMQ.RankSelectSpec.fixedWeightChunkBlocksWithSentinel_block_length_le
      hmem

/-- The appended sentinel block is readable at the chunk-list length. -/
theorem fixedWeightChunkBlocksWithSentinelGetSentinel
    (blockSize : Nat) (bits : List Bool) :
    (fixedWeightChunkBlocksWithSentinel blockSize bits)[
        (fixedWeightChunkBlocks blockSize bits).length]? = some [] := by
  exact
    RMQ.RankSelectSpec.fixedWeightChunkBlocksWithSentinel_get_sentinel
      blockSize bits

/-- Any ordinary chunk read is also readable before the sentinel block. -/
theorem fixedWeightChunkBlocksWithSentinelGetChunk
    {blockSize : Nat} {bits block : List Bool} {blockIndex : Nat}
    (hget :
      (fixedWeightChunkBlocks blockSize bits)[blockIndex]? =
        some block) :
    (fixedWeightChunkBlocksWithSentinel blockSize bits)[blockIndex]? =
      some block := by
  exact
    RMQ.RankSelectSpec.fixedWeightChunkBlocksWithSentinel_get_chunk
      hget

/-- A chunk block read at `i / blockSize` contains exactly `bits[i]?`. -/
theorem fixedWeightChunkBlocksGetAccessExact
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    {bits block : List Bool} {i : Nat}
    (hget :
      (fixedWeightChunkBlocks blockSize bits)[i / blockSize]? =
        some block) :
    block[i - (i / blockSize) * blockSize]? = bits[i]? := by
  exact
    RMQ.RankSelectSpec.fixedWeightChunkBlocks_get?_access_exact
      hblockSize hget

/--
Concrete access route for sentinel chunk blocks. In-range accesses route to
the computed chunk; invalid accesses route to the empty sentinel block.
-/
abbrev fixedWeightChunkAccessRouteWithSentinel :=
  @RMQ.RankSelectSpec.fixedWeightChunkAccessRouteWithSentinel

/-- Bound the class/length metadata overhead from block-count and field-width caps. -/
theorem fixedWeightBlockClassLengthTableOverheadLeOfBounds
    {fieldWidth fieldWidthBound blockCountBound : Nat}
    {blocks : List (List Bool)}
    (hblocks : blocks.length <= blockCountBound)
    (hfield : fieldWidth <= fieldWidthBound) :
    fixedWeightBlockClassLengthTableOverhead fieldWidth blocks <=
      (blockCountBound + blockCountBound) * fieldWidthBound := by
  exact
    RMQ.RankSelectSpec.fixedWeightBlockClassLengthTableOverhead_le_of_bounds
      hblocks hfield

/-- Bound the class/length metadata overhead by a family-level budget function. -/
theorem fixedWeightBlockClassLengthTableOverheadLeBudget
    {fieldWidth : Nat} {blockCountBound fieldWidthBound : Nat -> Nat}
    {blocks : List (List Bool)} {n : Nat}
    (hblocks : blocks.length <= blockCountBound n)
    (hfield : fieldWidth <= fieldWidthBound n) :
    fixedWeightBlockClassLengthTableOverhead fieldWidth blocks <=
      fixedWeightBlockClassLengthTableOverheadBudget
        blockCountBound fieldWidthBound n := by
  exact
    RMQ.RankSelectSpec.fixedWeightBlockClassLengthTableOverhead_le_budget
      hblocks hfield

/-- Bound class/length metadata overhead for fixed-size chunk blocks. -/
theorem fixedWeightBlockClassLengthTableOverheadLeChunkBudget
    {blockSize fieldWidth : Nat} {fieldWidthBound : Nat -> Nat}
    {bits : List Bool} {blocks : List (List Bool)}
    (hblockSize : 0 < blockSize)
    (hblocks :
      blocks = fixedWeightChunkBlocks blockSize bits)
    (hfield : fieldWidth <= fieldWidthBound bits.length) :
    fixedWeightBlockClassLengthTableOverhead fieldWidth blocks <=
      fixedWeightBlockClassLengthTableOverheadBudget
        (fixedWeightChunkBlockCountBound blockSize)
        fieldWidthBound bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightBlockClassLengthTableOverhead_le_chunk_budget
      hblockSize hblocks hfield

/-- Bound class/length metadata overhead for sentinel fixed-size chunk blocks. -/
theorem fixedWeightBlockClassLengthTableOverheadLeChunkSentinelBudget
    {blockSize fieldWidth : Nat} {fieldWidthBound : Nat -> Nat}
    {bits : List Bool} {blocks : List (List Bool)}
    (hblockSize : 0 < blockSize)
    (hblocks :
      blocks = fixedWeightChunkBlocksWithSentinel blockSize bits)
    (hfield : fieldWidth <= fieldWidthBound bits.length) :
    fixedWeightBlockClassLengthTableOverhead fieldWidth blocks <=
      fixedWeightBlockClassLengthTableOverheadBudget
        (fixedWeightChunkBlockCountBoundWithSentinel blockSize)
        fieldWidthBound bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightBlockClassLengthTableOverhead_le_chunk_sentinel_budget
      hblockSize hblocks hfield

/-- Sum of per-block fixed-weight code budgets. -/
abbrev fixedWeightBlockPayloadBudget :=
  RMQ.RankSelectSpec.fixedWeightBlockPayloadBudget

/-- Length of the block-coded primary fixed-weight payload. -/
abbrev fixedWeightBlockCodePayloadLength :=
  RMQ.RankSelectSpec.fixedWeightBlockCodePayload_length

/-- Length of the per-block class/length metadata payload. -/
abbrev fixedWeightBlockClassLengthTablePayloadLength :=
  RMQ.RankSelectSpec.fixedWeightBlockClassLengthTablePayload_length

/-- Bounded word store for per-block fixed-weight code words. -/
abbrev fixedWeightBlockCodeBoundedStore :=
  RMQ.RankSelectSpec.fixedWeightBlockCodeBoundedStore

/-- The canonical block-code store is word-aligned with the block-code list. -/
theorem fixedWeightBlockCodeBoundedStoreWordsToList
    (blocks : List (List Bool)) {wordSize : Nat}
    (hcode :
      forall {block : List Bool}, List.Mem block blocks ->
        fixedWeightPayloadBudget block <= wordSize) :
    (fixedWeightBlockCodeBoundedStore blocks hcode).store.words.toList =
      fixedWeightBlockCodeWords blocks := by
  exact
    RMQ.RankSelectSpec.fixedWeightBlockCodeBoundedStore_words_toList
      blocks hcode

/-- Any aligned block-code store reads the packed code for the addressed block. -/
theorem fixedWeightAmbientBlockCodeStoreGetOfAligned
    {blocks : List (List Bool)} {wordSize : Nat}
    {store :
      SuccinctSpace.BoundedPayloadWordStore
        (fixedWeightBlockCodePayload blocks) wordSize}
    (halign : store.store.words.toList = fixedWeightBlockCodeWords blocks)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    store.store.words[blockIndex]? =
      some (fixedWeightPackedPayload block) := by
  exact
    RMQ.RankSelectSpec.fixedWeightAmbientBlockCodeStore_get?_of_aligned
      halign hblock

/-- The canonical block-code store reads the packed code for the addressed block. -/
theorem fixedWeightBlockCodeBoundedStoreGetOfBlock
    (blocks : List (List Bool)) {wordSize : Nat}
    (hcode :
      forall {block : List Bool}, List.Mem block blocks ->
        fixedWeightPayloadBudget block <= wordSize)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    (fixedWeightBlockCodeBoundedStore blocks hcode).store.words[blockIndex]? =
      some (fixedWeightPackedPayload block) := by
  exact
    RMQ.RankSelectSpec.fixedWeightBlockCodeBoundedStore_get?_of_block
      blocks hcode hblock

/-- Ambient `o(n)` auxiliary envelope for block-composed fixed-weight data. -/
abbrev fixedWeightAmbientBlockAuxiliaryOverhead :=
  RMQ.RankSelectSpec.fixedWeightAmbientBlockAuxiliaryOverhead

/-- The ambient block-composition auxiliary envelope is `o(n)`. -/
theorem fixedWeightAmbientBlockAuxiliaryOverheadLittleO
    (slots : Nat) :
    SuccinctSpace.LittleOLinear
      (fixedWeightAmbientBlockAuxiliaryOverhead slots) := by
  exact
    RMQ.RankSelectSpec.fixedWeightAmbientBlockAuxiliaryOverhead_littleO
      slots

/-- Profile for constant-bounded compressed/FID auxiliary data. -/
abbrev fixedWeightCompressedAuxiliaryDataProfile
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData
        bits overhead wordSize queryCost) :=
  RMQ.RankSelectSpec.FixedWeightCompressedAuxiliaryData.directory_profile data

/-- Directory profile for pointwise dependent-read compressed/FID data. -/
abbrev FixedWeightDependentAuxiliaryDirectoryProfile
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost) :
    Prop :=
  RMQ.RankSelectSpec.FixedWeightDependentAuxiliaryData.DirectoryProfile data

/-- Profile for pointwise dependent-read compressed/FID data. -/
theorem fixedWeightDependentAuxiliaryDataProfile
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost) :
    FixedWeightDependentAuxiliaryDirectoryProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightDependentAuxiliaryData.directory_profile
      data

/-- Directory profile for ambient/global block-composed fixed-weight data. -/
abbrev FixedWeightAmbientBlockCompositionDirectoryProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost) : Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionData.DirectoryProfile
    data

/-- Profile for ambient/global block-composed fixed-weight data. -/
theorem fixedWeightAmbientBlockCompositionDataProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost) :
    FixedWeightAmbientBlockCompositionDirectoryProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionData.directory_profile
      data

/--
Ambient block-composition profile with explicit ambient machine-word bounds
for code and auxiliary payload reads.
-/
theorem fixedWeightAmbientBlockCompositionWordBoundedDataProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost) :
    FixedWeightAmbientBlockCompositionDirectoryProfile data /\
      (forall {word : List Bool},
        List.Mem word data.codeStore.store.words.toList ->
          word.length <= Nat.log2 bits.length + 1) /\
      (forall {word : List Bool},
        List.Mem word data.auxStore.store.words.toList ->
          word.length <= Nat.log2 bits.length + 1) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionData.word_bounded_directory_profile
      data

/--
Family-level profile for ambient/global block-composed fixed-weight data with
`o(n)` counted auxiliary payload.
-/
theorem fixedWeightAmbientBlockCompositionFamilyProfile
    {slots queryCost : Nat}
    (family :
      FixedWeightAmbientBlockCompositionFamily slots queryCost) :
    SuccinctSpace.LittleOLinear
        (fixedWeightAmbientBlockAuxiliaryOverhead slots) /\
      forall bits : List Bool,
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionFamily.directory
            family bits
        data.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          data.auxPayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (family.wordSize bits.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (data.accessCosted i).cost <= queryCost /\
              (data.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (data.rankCosted target pos).cost <= queryCost /\
              (data.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (data.selectCosted target occurrence).cost <= queryCost /\
              (data.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionFamily.ambient_block_composition_profile
      family

/--
Family-level ambient block-composition profile with explicit ambient
machine-word bounds for code and auxiliary payload reads.
-/
theorem fixedWeightAmbientBlockCompositionFamilyWordBoundedProfile
    {slots queryCost : Nat}
    (family :
      FixedWeightAmbientBlockCompositionFamily slots queryCost) :
    SuccinctSpace.LittleOLinear
        (fixedWeightAmbientBlockAuxiliaryOverhead slots) /\
      forall bits : List Bool,
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionFamily.directory
            family bits
        data.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          data.auxPayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word data.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word data.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (data.accessCosted i).cost <= queryCost /\
              (data.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (data.rankCosted target pos).cost <= queryCost /\
              (data.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (data.selectCosted target occurrence).cost <= queryCost /\
              (data.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionFamily.word_bounded_profile
      family

/--
Conditional bridge from ambient block composition to the public compressed/FID
payload shape, isolating the remaining primary block-code budget theorem.
-/
theorem fixedWeightAmbientBlockCompositionCompressedProfileOfPrimaryBudget
    {slots queryCost : Nat}
    (family :
      FixedWeightAmbientBlockCompositionFamily slots queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (fun n =>
          primaryOverhead n +
            fixedWeightAmbientBlockAuxiliaryOverhead slots n) /\
      forall bits : List Bool,
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionFamily.directory
            family bits
        data.payload.length <=
            fixedWeightPayloadBudget bits +
              (primaryOverhead bits.length +
                fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          (forall i,
            (data.accessCosted i).cost <= queryCost /\
              (data.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (data.rankCosted target pos).cost <= queryCost /\
              (data.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (data.selectCosted target occurrence).cost <= queryCost /\
              (data.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionFamily.compressed_profile_of_primary_budget
      family primaryOverhead hprimaryO hprimary

/-- Total overhead for the ambient block-composition compressed bridge. -/
abbrev fixedWeightAmbientBlockCompositionCompressedOverhead
    (slots : Nat) (primaryOverhead : Nat -> Nat) : Nat -> Nat :=
  RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionFamily.compressedOverhead
    slots primaryOverhead

/--
Word-bounded ambient block-composition bridge to the public compressed/FID
payload shape, assuming the remaining primary block-code budget theorem.
-/
theorem fixedWeightAmbientBlockCompositionWordBoundedCompressedProfileOfPrimaryBudget
    {slots queryCost : Nat}
    (family :
      FixedWeightAmbientBlockCompositionFamily slots queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (fixedWeightAmbientBlockCompositionCompressedOverhead
          slots primaryOverhead) /\
      forall bits : List Bool,
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionFamily.directory
            family bits
        FixedWeightAmbientBlockCompositionDirectoryProfile data /\
          data.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          data.payload.length <=
            fixedWeightPayloadBudget bits +
              fixedWeightAmbientBlockCompositionCompressedOverhead
                slots primaryOverhead bits.length /\
          data.auxPayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word data.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word data.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (data.accessCosted i).cost <= queryCost /\
              (data.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (data.rankCosted target pos).cost <= queryCost /\
              (data.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (data.selectCosted target occurrence).cost <= queryCost /\
              (data.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionFamily.word_bounded_compressed_profile_of_primary_budget
      family primaryOverhead hprimaryO hprimary

/-- Convert a compressed/FID auxiliary family into the public family shape. -/
abbrev fixedWeightCompressedAuxiliaryToCompressedFamily
    {overhead : Nat -> Nat} {wordSize queryCost : Nat}
    (family :
      FixedWeightCompressedAuxiliaryFamily overhead wordSize queryCost) :=
  RMQ.RankSelectSpec.FixedWeightCompressedAuxiliaryFamily.toCompressedFamily
    family

/-- Constant-query profile for compressed/FID auxiliary families. -/
theorem fixedWeightCompressedAuxiliaryConstantQueryProfile
    {overhead : Nat -> Nat} {wordSize queryCost : Nat}
    (family :
      FixedWeightCompressedAuxiliaryFamily overhead wordSize queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall bits : List Bool,
        (((family.toCompressedFamily).directory bits).payload.length <=
          fixedWeightPayloadBudget bits + overhead bits.length) /\
          (forall i,
            (((family.toCompressedFamily).directory bits).accessQueryCosted
                i).cost <= queryCost /\
              (((family.toCompressedFamily).directory bits).accessQueryCosted
                i).erase = bits[i]?) /\
          (forall target pos,
            (((family.toCompressedFamily).directory bits).rankQueryCosted
                target pos).cost <= queryCost /\
              (((family.toCompressedFamily).directory bits).rankQueryCosted
                target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (((family.toCompressedFamily).directory bits).selectQueryCosted
                target occurrence).cost <= queryCost /\
              (((family.toCompressedFamily).directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact RMQ.RankSelectSpec.FixedWeightCompressedAuxiliaryFamily.constant_query_profile
    family

/-- Profile for pointwise table-backed fixed-weight FID data. -/
abbrev fixedWeightTableBackedFIDDataProfile
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost) :=
  RMQ.RankSelectSpec.FixedWeightTableBackedFIDData.directory_profile data

/-- Profile for local table/RAM fixed-weight block data. -/
abbrev fixedWeightTableRAMBlockDataProfile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :=
  RMQ.RankSelectSpec.FixedWeightTableRAMBlockData.directory_profile data

/-- Explicit decode budget for the computed local fixed-weight/RRR kernel. -/
abbrev fixedWeightComputedRRRDecodeTicks :=
  RMQ.RankSelectSpec.fixedWeightComputedRRRDecodeTicks

/-- Uniform local query cap for the computed fixed-weight/RRR kernel. -/
abbrev fixedWeightComputedRRRQueryCost :=
  RMQ.RankSelectSpec.fixedWeightComputedRRRQueryCost

/-- Local query cap for the class/length-read computed RRR kernel. -/
abbrev fixedWeightComputedRRRClassLengthQueryCost :=
  RMQ.RankSelectSpec.fixedWeightComputedRRRClassLengthQueryCost

/-- Block-size query cap for the packed-code-only computed RRR kernel. -/
abbrev fixedWeightComputedRRRBlockSizeQueryCost :=
  RMQ.RankSelectSpec.fixedWeightComputedRRRBlockSizeQueryCost

/-- Block-size query cap for the class/length-read computed RRR kernel. -/
abbrev fixedWeightComputedRRRClassLengthBlockSizeQueryCost :=
  RMQ.RankSelectSpec.fixedWeightComputedRRRClassLengthBlockSizeQueryCost

/-- The binomial recurrence is bounded by the full Boolean universe. -/
abbrev binomialCountLeTwoPow :=
  RMQ.RankSelectSpec.binomialCount_le_two_pow

/-- Bounded block length gives a uniform computed-RRR local query cap. -/
abbrev fixedWeightComputedRRRQueryCostLeBlockSize
    {bits : List Bool} {blockSize : Nat}
    (hlen : bits.length <= blockSize) :=
  RMQ.RankSelectSpec.fixedWeightComputedRRRQueryCost_le_blockSize
    (bits := bits) hlen

/--
Bounded block length gives a uniform class/length-read computed-RRR local
query cap.
-/
abbrev fixedWeightComputedRRRClassLengthQueryCostLeBlockSize :=
  @RMQ.RankSelectSpec.fixedWeightComputedRRRClassLengthQueryCost_le_blockSize

/-- Decode a fixed-weight code for the class determined by the source block. -/
abbrev fixedWeightDecodedWordFromCode :=
  RMQ.RankSelectSpec.fixedWeightDecodedWordFromCode

/-- The canonical fixed-weight code decodes back to its source block. -/
abbrev fixedWeightDecodedWordFromCodeFixedWeightCode :=
  RMQ.RankSelectSpec.fixedWeightDecodedWordFromCode_fixedWeightCode

/-- Computed decode from charged packed-code read values. -/
abbrev fixedWeightComputedRRRDecodeFromReadValuesCosted :=
  RMQ.RankSelectSpec.fixedWeightComputedRRRDecodeFromReadValuesCosted

/-- Charged packed-code readback decodes to the source block. -/
abbrev fixedWeightComputedRRRDecodeFromReadValuesCostedEraseSingleton :=
  RMQ.RankSelectSpec.fixedWeightComputedRRRDecodeFromReadValuesCosted_erase_singleton

/-- Decode local block length/class from charged fixed-width metadata words. -/
abbrev fixedWeightClassLengthFromReadValues :=
  RMQ.RankSelectSpec.fixedWeightClassLengthFromReadValues

/-- Decode a local fixed-weight word from charged class/length and code reads. -/
abbrev fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted :=
  RMQ.RankSelectSpec.fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted

/-- Charged class/length metadata plus code reads decode to the source block. -/
abbrev fixedWeightComputedRRRDecodeFromClassLengthReadValuesCostedEraseSingleton
    {fieldWidth : Nat} {block : List Bool}
    (hlen : block.length < 2 ^ fieldWidth)
    (hclass : trueCount block < 2 ^ fieldWidth) :=
  RMQ.RankSelectSpec.fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted_erase_singleton
    (fieldWidth := fieldWidth) (block := block) hlen hclass

/-- Profile for local computed fixed-weight/RRR block data. -/
abbrev FixedWeightComputedRRRBlockKernelProfile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) : Prop :=
  RMQ.RankSelectSpec.FixedWeightComputedRRRBlockData.KernelProfile data

/-- Profile for local class/length-read computed fixed-weight/RRR block data. -/
abbrev FixedWeightComputedRRRClassLengthBlockKernelProfile
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) : Prop :=
  RMQ.RankSelectSpec.FixedWeightComputedRRRClassLengthBlockData.ClassLengthKernelProfile
    data

/--
The local computed fixed-weight/RRR kernel reads only the packed fixed-weight
code word and then spends its explicit decode budget before answering
access/rank/select exactly.
-/
theorem fixedWeightComputedRRRBlockKernelProfile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    FixedWeightComputedRRRBlockKernelProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightComputedRRRBlockData.computed_rrr_block_kernel_profile
      data

/--
The class/length-read local RRR kernel reads concrete metadata words for the
block length and class, reads the packed code, and answers access/rank/select
from the decoded block.
-/
theorem fixedWeightComputedRRRClassLengthBlockKernelProfile
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    FixedWeightComputedRRRClassLengthBlockKernelProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightComputedRRRClassLengthBlockData.class_length_kernel_profile
      data

/-- The class/length-read local kernel instantiates the dependent-read scaffold. -/
theorem fixedWeightComputedRRRClassLengthBlockDependentAuxiliaryDataProfile
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    (RMQ.RankSelectSpec.FixedWeightComputedRRRClassLengthBlockData.toDependentAuxiliaryData
      data).DirectoryProfile := by
  exact
    RMQ.RankSelectSpec.FixedWeightComputedRRRClassLengthBlockData.dependent_auxiliary_data_profile
      data

/-- Profile for the global per-block length/class metadata table. -/
abbrev FixedWeightAmbientComputedRRRClassLengthTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth) : Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRClassLengthTableData.ClassLengthTableProfile
    data

/-- Concrete fixed-width tables supply charged block length/class reads. -/
theorem fixedWeightAmbientComputedRRRClassLengthTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth) :
    FixedWeightAmbientComputedRRRClassLengthTableProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRClassLengthTableData.class_length_table_profile
      data

/-- Widen the local computed RRR block to any caller-supplied query budget. -/
abbrev fixedWeightComputedRRRBlockToBoundedCompressedDirectory
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    {queryCost : Nat}
    (hquery : fixedWeightComputedRRRQueryCost bits <= queryCost) :=
  RMQ.RankSelectSpec.FixedWeightComputedRRRBlockData.toBoundedCompressedDirectory
    data hquery

/--
If the explicit local computed-RRR budget fits a caller-supplied constant,
the packed-code-only local kernel is a compressed/FID directory with zero
auxiliary payload and all queries bounded by that constant.
-/
theorem fixedWeightComputedRRRBlockBoundedCompressedDirectoryProfile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    {queryCost : Nat}
    (hquery : fixedWeightComputedRRRQueryCost bits <= queryCost) :
    let directory :=
      fixedWeightComputedRRRBlockToBoundedCompressedDirectory data hquery
    directory.payload = fixedWeightPackedPayload bits /\
      directory.payload.length = fixedWeightPayloadBudget bits /\
      directory.payload.length <= fixedWeightPayloadBudget bits + 0 /\
      data.readCodeCosted.cost = 1 /\
      data.readCodeCosted.erase = RMQ.RankSelectSpec.fixedWeightCode bits /\
      data.decodedWordCosted.cost =
        fixedWeightComputedRRRDecodeTicks bits + 1 /\
      data.decodedWordCosted.erase = bits /\
      fixedWeightComputedRRRQueryCost bits <= queryCost /\
      (forall i,
        (directory.accessQueryCosted i).cost <= queryCost /\
          (directory.accessQueryCosted i).erase = bits[i]?) /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <= queryCost /\
          (directory.rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <=
            queryCost /\
          (directory.selectQueryCosted target occurrence).erase =
            Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightComputedRRRBlockData.bounded_compressed_directory_profile
      data hquery

/--
Bridge profile equating the direct computed-RRR local directory and the
dependent-auxiliary scaffold-backed directory.
-/
abbrev FixedWeightComputedRRRBlockDependentAuxiliaryBridgeProfile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    Prop :=
  RMQ.RankSelectSpec.FixedWeightComputedRRRBlockData.DependentAuxiliaryBridgeProfile
    data

/--
The dependent-auxiliary adapter has the same payload and charged query
behavior as the direct packed-code-only computed-RRR block directory.
-/
theorem fixedWeightComputedRRRBlockDependentAuxiliaryBridgeProfile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    FixedWeightComputedRRRBlockDependentAuxiliaryBridgeProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightComputedRRRBlockData.dependent_auxiliary_bridge_profile
      data

/-- Adapt a computed local RRR block kernel to the dependent auxiliary scaffold. -/
abbrev fixedWeightComputedRRRBlockToDependentAuxiliaryData
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :=
  RMQ.RankSelectSpec.FixedWeightComputedRRRBlockData.toDependentAuxiliaryData
    data

/--
The computed local RRR block kernel is a generic dependent-read
compressed/FID directory with zero auxiliary payload.
-/
theorem fixedWeightComputedRRRBlockDependentAuxiliaryDataProfile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    FixedWeightDependentAuxiliaryDirectoryProfile
      (fixedWeightComputedRRRBlockToDependentAuxiliaryData data) := by
  exact
    RMQ.RankSelectSpec.FixedWeightComputedRRRBlockData.dependent_auxiliary_data_profile
      data

/--
Full local computed-RRR block package: direct packed-code kernel profile,
generic dependent-auxiliary directory profile, and equivalence with the direct
block directory.
-/
theorem fixedWeightComputedRRRBlockDependentAuxiliaryFullProfile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    FixedWeightComputedRRRBlockKernelProfile data /\
      FixedWeightDependentAuxiliaryDirectoryProfile
        (fixedWeightComputedRRRBlockToDependentAuxiliaryData data) /\
      FixedWeightComputedRRRBlockDependentAuxiliaryBridgeProfile data := by
  exact
    ⟨fixedWeightComputedRRRBlockKernelProfile data,
      fixedWeightComputedRRRBlockDependentAuxiliaryDataProfile data,
      fixedWeightComputedRRRBlockDependentAuxiliaryBridgeProfile data⟩

/--
Convert ambient computed-RRR block data to the generic ambient block-composition
surface.
-/
abbrev fixedWeightAmbientComputedRRRBlockToCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockData.toAmbientBlockCompositionData
    data

/-- Profile for ambient computed-RRR block-composition data. -/
abbrev FixedWeightAmbientComputedRRRBlockCompositionProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockData.CompositionProfile
    data

/--
The ambient computed-RRR layer consumes the packed-code-only local block
adapter inside the ambient/global block-composition profile.
-/
theorem fixedWeightAmbientComputedRRRBlockCompositionProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRBlockCompositionProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockData.computed_rrr_block_composition_profile
      data

/-- Convert route/class table data to the underlying ambient computed-RRR layer. -/
abbrev fixedWeightAmbientComputedRRRRouteTableToComputedRRRBlockData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableData.toComputedRRRBlockData
    data

/-- Convert route/class table data to the generic ambient block-composition layer. -/
abbrev fixedWeightAmbientComputedRRRRouteTableToCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableData.toAmbientBlockCompositionData
    data

/-- Charged auxiliary metadata reads for an access route. -/
abbrev fixedWeightAmbientComputedRRRRouteTableAccessMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableData.accessMetadataReadsCosted
    data i

/-- Charged auxiliary metadata reads for a rank route. -/
abbrev fixedWeightAmbientComputedRRRRouteTableRankMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableData.rankMetadataReadsCosted
    data target pos

/-- Charged auxiliary metadata reads for a select route. -/
abbrev fixedWeightAmbientComputedRRRRouteTableSelectMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableData.selectMetadataReadsCosted
    data target occurrence

/-- Public profile for the charged route/class metadata reads. -/
abbrev FixedWeightAmbientComputedRRRRouteTableReadProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableData.RouteTableReadProfile
    data

/--
The route/class metadata reads are concrete bounded-store reads: their modeled
cost is bounded by `routeCost`, and their erased values are the store words at
the route's metadata schedule.
-/
theorem fixedWeightAmbientComputedRRRRouteTableReadProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRRouteTableReadProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableData.route_table_read_profile
      data

/-- Public profile for payload-backed route/class table data. -/
abbrev FixedWeightAmbientComputedRRRRouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableData.RouteTableProfile
    data

/--
Payload-backed route/class tables instantiate the ambient computed-RRR
composition profile, with bounded auxiliary-store read values and schedules.
-/
theorem fixedWeightAmbientComputedRRRRouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRRouteTableProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableData.route_table_profile
      data

/-- The ambient directory produced by a route/class table family. -/
abbrev fixedWeightAmbientComputedRRRRouteTableFamilyDirectory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableFamily.directory
    family bits

/--
Family-level route/class table profile: the auxiliary route payload is
`o(n)`, the composed payload is code bits plus that auxiliary envelope, and all
ambient access/rank/select queries have cost bounded by `queryCost`.
-/
theorem fixedWeightAmbientComputedRRRRouteTableFamilyProfile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    RMQ.SuccinctSpace.LittleOLinear
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableFamily.overhead
          slots) /\
      forall bits : List Bool,
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableFamily.componentData
            family bits
        FixedWeightAmbientComputedRRRRouteTableProfile data /\
          data.routePayload.length =
            RMQ.RankSelectSpec.fixedWeightAmbientBlockAuxiliaryOverhead
              slots bits.length /\
          ((fixedWeightAmbientComputedRRRRouteTableFamilyDirectory
                family bits).payload.length =
            RMQ.RankSelectSpec.fixedWeightBlockPayloadBudget
              (family.blocks bits) +
                RMQ.RankSelectSpec.fixedWeightAmbientBlockAuxiliaryOverhead
                  slots bits.length) /\
          RMQ.SuccinctSpace.flattenPayloadWords
            (family.blocks bits) = bits /\
          (forall i,
            ((fixedWeightAmbientComputedRRRRouteTableFamilyDirectory
                family bits).accessCosted i).cost <= queryCost) /\
          (forall target pos,
            ((fixedWeightAmbientComputedRRRRouteTableFamilyDirectory
                family bits).rankCosted target pos).cost <= queryCost) /\
          (forall target occurrence,
            ((fixedWeightAmbientComputedRRRRouteTableFamilyDirectory
                family bits).selectCosted target occurrence).cost <=
              queryCost) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableFamily.route_table_family_profile
      family

/-- The ambient directory produced by a block-size route/class table family. -/
abbrev fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyDirectory
    {slots blockSize routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily
        slots blockSize routeCost queryCost)
    (bits : List Bool) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily.directory
    family bits

/-- Public profile for pointwise block-size route/class table data. -/
abbrev FixedWeightAmbientComputedRRRBlockSizeRouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize blockSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableData
        bits blocks overhead wordSize blockSize routeCost queryCost) :
    Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockSizeRouteTableData.BlockSizeRouteTableProfile
    data

/--
Block-size route/class tables derive the local computed-RRR query cap from the
stored block-size discipline instead of receiving a per-block local-cost oracle.
-/
theorem fixedWeightAmbientComputedRRRBlockSizeRouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize blockSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableData
        bits blocks overhead wordSize blockSize routeCost queryCost) :
    FixedWeightAmbientComputedRRRBlockSizeRouteTableProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockSizeRouteTableData.block_size_route_table_profile
      data

/--
Family-level block-size route/class profile with a derived local query cap
`2 ^ blockSize + blockSize + 2`.
-/
theorem fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyProfile
    {slots blockSize routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily
        slots blockSize routeCost queryCost) :
    RMQ.SuccinctSpace.LittleOLinear
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily.overhead
          slots) /\
      forall bits : List Bool,
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily.componentData
            family bits
        FixedWeightAmbientComputedRRRBlockSizeRouteTableProfile data /\
          ((fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyDirectory
                family bits).payload.length =
            RMQ.RankSelectSpec.fixedWeightBlockPayloadBudget
              (family.blocks bits) +
                RMQ.RankSelectSpec.fixedWeightAmbientBlockAuxiliaryOverhead
                  slots bits.length) /\
          RMQ.SuccinctSpace.flattenPayloadWords
            (family.blocks bits) = bits /\
          (forall {block : List Bool},
            List.Mem block (family.blocks bits) ->
              fixedWeightComputedRRRQueryCost block <=
                fixedWeightComputedRRRBlockSizeQueryCost blockSize) /\
          (forall i,
            ((fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyDirectory
                family bits).accessCosted i).cost <= queryCost /\
              ((fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyDirectory
                family bits).accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            ((fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyDirectory
                family bits).rankCosted target pos).cost <= queryCost /\
              ((fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyDirectory
                family bits).rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            ((fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyDirectory
                family bits).selectCosted target occurrence).cost <=
                queryCost /\
              ((fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyDirectory
                family bits).selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily.block_size_route_table_family_profile
      family

/-- Adapt a local table/RAM block kernel to the dependent auxiliary scaffold. -/
abbrev fixedWeightTableRAMBlockToDependentAuxiliaryData
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :=
  RMQ.RankSelectSpec.FixedWeightTableRAMBlockData.toDependentAuxiliaryData
    data

/--
The local table/RAM fixed-weight block kernel is an instance of the generic
dependent-read compressed/FID scaffold.
-/
theorem fixedWeightTableRAMBlockDependentAuxiliaryDataProfile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    FixedWeightDependentAuxiliaryDirectoryProfile
      (fixedWeightTableRAMBlockToDependentAuxiliaryData data) := by
  exact
    RMQ.RankSelectSpec.FixedWeightDependentAuxiliaryData.directory_profile
      (RMQ.RankSelectSpec.FixedWeightTableRAMBlockData.toDependentAuxiliaryData
        data)

/-- Detailed dependent-read profile for local table/RAM fixed-weight block data. -/
abbrev FixedWeightTableRAMBlockDependentReadProfile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) : Prop :=
  RMQ.RankSelectSpec.FixedWeightTableRAMBlockData.DependentReadProfile data

/--
The local table/RAM fixed-weight block kernel reads the packed code, uses that
charged value to address the decoded-word table, and then answers with fixed
access/rank/select code.
-/
theorem fixedWeightTableRAMBlockDependentReadProfile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    FixedWeightTableRAMBlockDependentReadProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightTableRAMBlockData.dependent_read_profile
      data

/--
Bridge profile equating the direct local block directory and the
dependent-auxiliary scaffold-backed directory.
-/
abbrev FixedWeightTableRAMBlockDependentAuxiliaryBridgeProfile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) : Prop :=
  RMQ.RankSelectSpec.FixedWeightTableRAMBlockData.DependentAuxiliaryBridgeProfile
    data

/--
The dependent-auxiliary adapter has the same payload and charged query
behavior as the direct local table/RAM block directory.
-/
theorem fixedWeightTableRAMBlockDependentAuxiliaryBridgeProfile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    FixedWeightTableRAMBlockDependentAuxiliaryBridgeProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightTableRAMBlockData.dependent_auxiliary_bridge_profile
      data

/--
Full local table/RAM block package: generic dependent-auxiliary directory
profile, stronger local dependent-read facts, and equivalence with the direct
block directory.
-/
theorem fixedWeightTableRAMBlockDependentAuxiliaryFullProfile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    FixedWeightDependentAuxiliaryDirectoryProfile
        (fixedWeightTableRAMBlockToDependentAuxiliaryData data) /\
      FixedWeightTableRAMBlockDependentReadProfile data /\
      FixedWeightTableRAMBlockDependentAuxiliaryBridgeProfile data := by
  exact
    ⟨fixedWeightTableRAMBlockDependentAuxiliaryDataProfile data,
      fixedWeightTableRAMBlockDependentReadProfile data,
      fixedWeightTableRAMBlockDependentAuxiliaryBridgeProfile data⟩

/-- Public decoded route/class metadata read profile. -/
abbrev FixedWeightAmbientComputedRRRDecodedMetadataReadProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedRouteTableData.DecodedMetadataReadProfile
    data

/--
Decoded route/class metadata reads are charged bounded-store reads, and the
route decoders recover the route fields consumed by the ambient computed-RRR
query layer.
-/
theorem fixedWeightAmbientComputedRRRDecodedMetadataReadProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRDecodedMetadataReadProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedRouteTableData.decoded_metadata_read_profile
      data

/-- Public profile for decoded route/class table data. -/
abbrev FixedWeightAmbientComputedRRRDecodedRouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedRouteTableData.DecodedRouteTableProfile
    data

/--
Decoded route/class tables instantiate the route-table and ambient composition
profiles while proving that decoded route fields come from charged metadata
read values.
-/
theorem fixedWeightAmbientComputedRRRDecodedRouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRDecodedRouteTableProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedRouteTableData.decoded_route_table_profile
      data

/-- The ambient directory produced by a decoded route/class table family. -/
abbrev fixedWeightAmbientComputedRRRDecodedRouteTableFamilyDirectory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedRouteTableFamily.directory
    family bits

/--
Family-level decoded route/class table profile: route metadata payload is
`o(n)`, queries are bounded by `queryCost`, and route fields are decoded from
charged metadata reads before being consumed by the ambient computed-RRR layer.
-/
theorem fixedWeightAmbientComputedRRRDecodedRouteTableFamilyProfile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedRouteTableFamily.overhead
          slots) /\
      forall bits : List Bool,
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedRouteTableFamily.componentData
            family bits
        FixedWeightAmbientComputedRRRDecodedRouteTableProfile data /\
          data.routePayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          ((fixedWeightAmbientComputedRRRDecodedRouteTableFamilyDirectory
                family bits).payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall i,
            ((fixedWeightAmbientComputedRRRDecodedRouteTableFamilyDirectory
                family bits).accessCosted i).cost <= queryCost) /\
          (forall target pos,
            ((fixedWeightAmbientComputedRRRDecodedRouteTableFamilyDirectory
                family bits).rankCosted target pos).cost <= queryCost) /\
          (forall target occurrence,
            ((fixedWeightAmbientComputedRRRDecodedRouteTableFamilyDirectory
                family bits).selectCosted target occurrence).cost <=
              queryCost) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedRouteTableFamily.decoded_route_table_family_profile
      family

/--
Conditional compressed/FID bridge for the existing route/class table family.

Once the primary block-code budget is bounded by the global fixed-weight budget
plus `primaryOverhead`, the route-table family has the public compressed/FID
payload shape with word-bounded stores and exact constant-cost queries.
-/
theorem fixedWeightAmbientComputedRRRRouteTableWordBoundedCompressedProfileOfPrimaryBudget
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (fixedWeightAmbientBlockCompositionCompressedOverhead
          slots primaryOverhead) /\
      forall bits : List Bool,
        let routeData :=
          RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableFamily.componentData
            family bits
        let data := fixedWeightAmbientComputedRRRRouteTableFamilyDirectory
          family bits
        FixedWeightAmbientComputedRRRRouteTableProfile routeData /\
          data.DirectoryProfile /\
          data.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          data.payload.length <=
            fixedWeightPayloadBudget bits +
              fixedWeightAmbientBlockCompositionCompressedOverhead
                slots primaryOverhead bits.length /\
          data.auxPayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word data.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word data.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (data.accessCosted i).cost <= queryCost /\
              (data.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (data.rankCosted target pos).cost <= queryCost /\
              (data.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (data.selectCosted target occurrence).cost <= queryCost /\
              (data.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteTableFamily.word_bounded_compressed_profile_of_primary_budget
      family primaryOverhead hprimaryO hprimary

/--
Conditional compressed/FID bridge for block-size route/class tables.

This is the route-table bridge plus the non-oracular local-cost discipline:
each block's computed-RRR local query cost is bounded by the fixed block-size
cap. The primary block-code budget remains the explicit `hprimary` premise.
-/
theorem fixedWeightAmbientComputedRRRBlockSizeRouteTableWordBoundedCompressedProfileOfPrimaryBudget
    {slots blockSize routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily
        slots blockSize routeCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (fixedWeightAmbientBlockCompositionCompressedOverhead
          slots primaryOverhead) /\
      forall bits : List Bool,
        let blockSizeData :=
          RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily.componentData
            family bits
        let routeData := blockSizeData.toRouteTableData
        let data :=
          fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyDirectory
            family bits
        FixedWeightAmbientComputedRRRBlockSizeRouteTableProfile
          blockSizeData /\
          FixedWeightAmbientComputedRRRRouteTableProfile routeData /\
          data.DirectoryProfile /\
          data.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          data.payload.length <=
            fixedWeightPayloadBudget bits +
              fixedWeightAmbientBlockCompositionCompressedOverhead
                slots primaryOverhead bits.length /\
          data.auxPayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word data.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word data.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (data.accessCosted i).cost <= queryCost /\
              (data.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (data.rankCosted target pos).cost <= queryCost /\
              (data.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (data.selectCosted target occurrence).cost <= queryCost /\
              (data.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  simpa [fixedWeightAmbientBlockCompositionCompressedOverhead,
    fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyDirectory,
    FixedWeightAmbientComputedRRRBlockSizeRouteTableProfile,
    FixedWeightAmbientComputedRRRRouteTableProfile,
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily.compressedOverhead]
    using
      RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily.word_bounded_compressed_profile_of_primary_budget
        family primaryOverhead hprimaryO hprimary

/--
Conditional compressed/FID bridge for decoded route/class metadata tables.

Compared with the route-table bridge above, this profile also carries the
decoded metadata-read proof that route fields are outputs of charged route
payload reads.
-/
theorem fixedWeightAmbientComputedRRRDecodedRouteTableWordBoundedCompressedProfileOfPrimaryBudget
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (fixedWeightAmbientBlockCompositionCompressedOverhead
          slots primaryOverhead) /\
      forall bits : List Bool,
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedRouteTableFamily.componentData
          family bits).DecodedRouteTableProfile /\
          let data :=
            fixedWeightAmbientComputedRRRDecodedRouteTableFamilyDirectory
              family bits
          data.DirectoryProfile /\
            data.payload.length =
              fixedWeightBlockPayloadBudget (family.blocks bits) +
                fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            data.payload.length <=
              fixedWeightPayloadBudget bits +
                fixedWeightAmbientBlockCompositionCompressedOverhead
                  slots primaryOverhead bits.length /\
            data.auxPayload.length =
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
            (forall {word : List Bool},
              List.Mem word data.codeStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall {word : List Bool},
              List.Mem word data.auxStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall i,
              (data.accessCosted i).cost <= queryCost /\
                (data.accessCosted i).erase = bits[i]?) /\
            (forall target pos,
              (data.rankCosted target pos).cost <= queryCost /\
                (data.rankCosted target pos).erase =
                  Succinct.rankPrefix target bits pos) /\
            (forall target occurrence,
              (data.selectCosted target occurrence).cost <= queryCost /\
                (data.selectCosted target occurrence).erase =
                  Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRDecodedRouteTableFamily.word_bounded_compressed_profile_of_primary_budget
      family primaryOverhead hprimaryO hprimary

/-- Public profile for packed fixed-width route/class table data. -/
abbrev FixedWeightAmbientComputedRRRPackedRouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRPackedRouteTableData.PackedRouteTableProfile
    data

/-- Access route metadata is read back as two fixed-width payload words. -/
theorem fixedWeightAmbientComputedRRRPackedAccessMetadataReadValuesEq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) :
    fixedWeightAuxiliaryWordReadValues data.routeData.routeStore
        (data.routeData.accessRoute i).metadataReads =
      [some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.accessRoute i).blockIndex),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.accessRoute i).offset)] := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRPackedRouteTableData.access_packed_metadata_read_values_eq
      data i

/-- Rank route metadata is read back as three fixed-width payload words. -/
theorem fixedWeightAmbientComputedRRRPackedRankMetadataReadValuesEq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat) :
    fixedWeightAuxiliaryWordReadValues data.routeData.routeStore
        (data.routeData.rankRoute target pos).metadataReads =
      [some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.rankRoute target pos).blockIndex),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.rankRoute target pos).localLimit),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.rankRoute target pos).baseRank)] := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRPackedRouteTableData.rank_packed_metadata_read_values_eq
      data target pos

/-- Select route metadata is read back as three fixed-width payload words. -/
theorem fixedWeightAmbientComputedRRRPackedSelectMetadataReadValuesEq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat) :
    fixedWeightAuxiliaryWordReadValues data.routeData.routeStore
        (data.routeData.selectRoute target occurrence).metadataReads =
      [some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.selectRoute target occurrence).blockIndex),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.selectRoute target occurrence).localOccurrence),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.selectRoute target occurrence).blockStart)] := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRPackedRouteTableData.select_packed_metadata_read_values_eq
      data target occurrence

/--
Packed route/class tables instantiate the decoded route-table and ambient
composition profiles using fixed-width metadata words.
-/
theorem fixedWeightAmbientComputedRRRPackedRouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRPackedRouteTableProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRPackedRouteTableData.packed_route_table_profile
      data

/-- The ambient directory produced by a packed route/class table family. -/
abbrev fixedWeightAmbientComputedRRRPackedRouteTableFamilyDirectory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRPackedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRPackedRouteTableFamily.directory
    family bits

/--
Family-level packed route/class table profile: the route payload is `o(n)`,
route fields are recovered from fixed-width charged route words, and the
ambient computed-RRR queries remain bounded by `queryCost`.
-/
theorem fixedWeightAmbientComputedRRRPackedRouteTableFamilyProfile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRPackedRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRPackedRouteTableFamily.overhead
          slots) /\
      forall bits : List Bool,
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRPackedRouteTableFamily.componentData
            family bits
        FixedWeightAmbientComputedRRRPackedRouteTableProfile data /\
          data.routeData.routePayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          ((fixedWeightAmbientComputedRRRPackedRouteTableFamilyDirectory
                family bits).payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall i,
            ((fixedWeightAmbientComputedRRRPackedRouteTableFamilyDirectory
                family bits).accessCosted i).cost <= queryCost) /\
          (forall target pos,
            ((fixedWeightAmbientComputedRRRPackedRouteTableFamilyDirectory
                family bits).rankCosted target pos).cost <= queryCost) /\
          (forall target occurrence,
            ((fixedWeightAmbientComputedRRRPackedRouteTableFamilyDirectory
                family bits).selectCosted target occurrence).cost <=
              queryCost) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRPackedRouteTableFamily.packed_route_table_family_profile
      family

/--
Conditional compressed/FID bridge for packed fixed-width route/class metadata.

Once the primary block-code budget is bounded by the global fixed-weight
budget plus `primaryOverhead`, the packed route-table family has the public
compressed/FID payload shape with word-bounded stores, charged fixed-width
route metadata reads, and exact constant-cost queries.
-/
theorem fixedWeightAmbientComputedRRRPackedRouteTableWordBoundedCompressedProfileOfPrimaryBudget
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRPackedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (fixedWeightAmbientBlockCompositionCompressedOverhead
          slots primaryOverhead) /\
      forall bits : List Bool,
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRPackedRouteTableFamily.componentData
          family bits).PackedRouteTableProfile /\
          let data :=
            fixedWeightAmbientComputedRRRPackedRouteTableFamilyDirectory
              family bits
          data.DirectoryProfile /\
            data.payload.length =
              fixedWeightBlockPayloadBudget (family.blocks bits) +
                fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            data.payload.length <=
              fixedWeightPayloadBudget bits +
                fixedWeightAmbientBlockCompositionCompressedOverhead
                  slots primaryOverhead bits.length /\
            data.auxPayload.length =
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
            (forall {word : List Bool},
              List.Mem word data.codeStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall {word : List Bool},
              List.Mem word data.auxStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall i,
              (data.accessCosted i).cost <= queryCost /\
                (data.accessCosted i).erase = bits[i]?) /\
            (forall target pos,
              (data.rankCosted target pos).cost <= queryCost /\
                (data.rankCosted target pos).erase =
                  Succinct.rankPrefix target bits pos) /\
            (forall target occurrence,
              (data.selectCosted target occurrence).cost <= queryCost /\
                (data.selectCosted target occurrence).erase =
                  Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRPackedRouteTableFamily.word_bounded_compressed_profile_of_primary_budget
      family primaryOverhead hprimaryO hprimary

/-- Convert canonical route field tables to packed route-table data. -/
abbrev fixedWeightAmbientComputedRRRRouteFieldTablesToPackedRouteTableData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTablesData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRPackedRouteTableData
      bits blocks overhead wordSize routeCost localQueryCost queryCost :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTablesData.toPackedRouteTableData
    data

/-- Public packed profile for canonical route field tables. -/
abbrev FixedWeightAmbientComputedRRRRouteFieldTablesPackedProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTablesData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTablesData.RouteFieldTablesProfile
    data

/--
Canonical route field tables derive the packed route-table profile from a
fixed-width `FixedWidthNatTable.ofEntries` payload aligned with the route
store, rather than assuming per-slot route words directly.
-/
theorem fixedWeightAmbientComputedRRRRouteFieldTablesPackedProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTablesData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRRouteFieldTablesPackedProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTablesData.route_field_tables_packed_profile
      data

/-- The ambient directory produced by a route field-table family. -/
abbrev fixedWeightAmbientComputedRRRRouteFieldTablesFamilyDirectory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTablesFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTablesFamily.directory
    family bits

/--
Family-level route field-table profile: canonical fixed-width field tables
feed the packed route-table layer, while retaining the ambient query bounds and
`o(n)` route-payload envelope.
-/
theorem fixedWeightAmbientComputedRRRRouteFieldTablesFamilyProfile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTablesFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTablesFamily.overhead
          slots) /\
      forall bits : List Bool,
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTablesFamily.componentData
            family bits
        FixedWeightAmbientComputedRRRRouteFieldTablesPackedProfile data /\
          data.routeData.routePayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          ((fixedWeightAmbientComputedRRRRouteFieldTablesFamilyDirectory
                family bits).payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall i,
            ((fixedWeightAmbientComputedRRRRouteFieldTablesFamilyDirectory
                family bits).accessCosted i).cost <= queryCost) /\
          (forall target pos,
            ((fixedWeightAmbientComputedRRRRouteFieldTablesFamilyDirectory
                family bits).rankCosted target pos).cost <= queryCost) /\
          (forall target occurrence,
            ((fixedWeightAmbientComputedRRRRouteFieldTablesFamilyDirectory
                family bits).selectCosted target occurrence).cost <=
              queryCost) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTablesFamily.route_field_tables_family_profile
      family

/--
Conditional compressed/FID bridge for canonical route field-table families.

This strengthens the packed route bridge by deriving packed route metadata
words from a canonical fixed-width field table aligned with the route store.
-/
theorem fixedWeightAmbientComputedRRRRouteFieldTablesWordBoundedCompressedProfileOfPrimaryBudget
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTablesFamily
        slots routeCost localQueryCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (fixedWeightAmbientBlockCompositionCompressedOverhead
          slots primaryOverhead) /\
      forall bits : List Bool,
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTablesFamily.componentData
          family bits).RouteFieldTablesProfile /\
          let data :=
            fixedWeightAmbientComputedRRRRouteFieldTablesFamilyDirectory
              family bits
          data.DirectoryProfile /\
            data.payload.length =
              fixedWeightBlockPayloadBudget (family.blocks bits) +
                fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            data.payload.length <=
              fixedWeightPayloadBudget bits +
                fixedWeightAmbientBlockCompositionCompressedOverhead
                  slots primaryOverhead bits.length /\
            data.auxPayload.length =
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
            (forall {word : List Bool},
              List.Mem word data.codeStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall {word : List Bool},
              List.Mem word data.auxStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall i,
              (data.accessCosted i).cost <= queryCost /\
                (data.accessCosted i).erase = bits[i]?) /\
            (forall target pos,
              (data.rankCosted target pos).cost <= queryCost /\
                (data.rankCosted target pos).erase =
                  Succinct.rankPrefix target bits pos) /\
            (forall target occurrence,
              (data.selectCosted target occurrence).cost <= queryCost /\
                (data.selectCosted target occurrence).erase =
                  Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTablesFamily.word_bounded_compressed_profile_of_primary_budget
      family primaryOverhead hprimaryO hprimary

/-- Counted payload for the concatenated eight-table route field layout. -/
abbrev fixedWeightRouteFieldTableLayoutPayload :=
  RMQ.RankSelectSpec.fixedWeightRouteFieldTableLayoutPayload

/-- Length of the concatenated eight-table route field payload. -/
abbrev fixedWeightRouteFieldTableLayoutPayloadLength :=
  RMQ.RankSelectSpec.fixedWeightRouteFieldTableLayoutPayload_length

/-- Canonical bounded store for the concatenated eight-table route field layout. -/
abbrev fixedWeightRouteFieldTableLayoutBoundedStore :=
  RMQ.RankSelectSpec.fixedWeightRouteFieldTableLayoutBoundedStore

/-- The canonical eight-table route field store is aligned to the layout words. -/
abbrev fixedWeightRouteFieldTableLayoutBoundedStoreWordsToList :=
  RMQ.RankSelectSpec.fixedWeightRouteFieldTableLayoutBoundedStore_words_toList

/--
Build an eight-table route field layout with the route store manufactured from
the concatenated fixed-width table words.
-/
abbrev fixedWeightAmbientComputedRRRRouteFieldTableLayoutOfCanonicalFixedWidthTables :=
  @RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData.ofCanonicalFixedWidthTables

/-- Convert an eight-table route field layout to packed route-table data. -/
abbrev fixedWeightAmbientComputedRRRRouteFieldTableLayoutToPackedRouteTableData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRPackedRouteTableData
      bits blocks overhead wordSize routeCost localQueryCost queryCost :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData.toPackedRouteTableData
    data

/-- Public packed profile for eight-table route field layouts. -/
abbrev FixedWeightAmbientComputedRRRRouteFieldTableLayoutPackedProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData.LayoutPackedProfile
    data

/--
Eight canonical fixed-width field tables, concatenated in route-store order,
derive the packed route-table profile consumed by the ambient computed-RRR
query layer.
-/
theorem fixedWeightAmbientComputedRRRRouteFieldTableLayoutPackedProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRRouteFieldTableLayoutPackedProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData.route_field_table_layout_packed_profile
      data

/--
Build a route/class-length envelope from an eight-table route layout under
block-size side conditions.
-/
abbrev fixedWeightAmbientComputedRRRRouteFieldTableLayoutToRouteClassLengthTableEnvelopeData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (hblockSize_lt_fieldWidthPow :
      data.routeData.blockSize < 2 ^ data.fieldWidth)
    (hlocalCost :
      fixedWeightComputedRRRClassLengthBlockSizeQueryCost
        data.routeData.blockSize <= localQueryCost) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData.toRouteClassLengthTableEnvelopeData
    data hblockSize_lt_fieldWidthPow hlocalCost

theorem fixedWeightAmbientComputedRRRRouteFieldTableLayoutToRouteClassLengthTableEnvelopeProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (hblockSize_lt_fieldWidthPow :
      data.routeData.blockSize < 2 ^ data.fieldWidth)
    (hlocalCost :
      fixedWeightComputedRRRClassLengthBlockSizeQueryCost
        data.routeData.blockSize <= localQueryCost) :
    (fixedWeightAmbientComputedRRRRouteFieldTableLayoutToRouteClassLengthTableEnvelopeData
      data hblockSize_lt_fieldWidthPow hlocalCost).RouteClassLengthEnvelopeProfile := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData.route_field_table_layout_to_route_class_length_table_envelope_profile
      data hblockSize_lt_fieldWidthPow hlocalCost

/-- Profile for the route-field layout plus counted block class/length tables. -/
abbrev FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData.RouteClassLengthEnvelopeProfile
    data

/-- Convert the route/class envelope to a packed route table over one combined store. -/
abbrev fixedWeightAmbientComputedRRRRouteClassLengthEnvelopeToCombinedPackedRouteTableData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData.toCombinedPackedRouteTableData
    data

/--
Convert the route/class envelope to the ambient block-composition directory
whose local evaluator consumes the charged class/length prefix.
-/
abbrev fixedWeightAmbientComputedRRRRouteClassLengthEnvelopeToClassLengthAmbientBlockCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData.toClassLengthAmbientBlockCompositionData
    data

/--
The route/class envelope exposes both the packed route-field layout and the
counted per-block length/class metadata table in one combined auxiliary store,
then feeds that store to the class/length-consuming ambient evaluator.
-/
theorem fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData.route_class_length_table_envelope_profile
      data

/-- Combined route plus class/length auxiliary overhead. -/
abbrev fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
    (slots : Nat) (classLengthOverhead : Nat -> Nat) : Nat -> Nat :=
  RMQ.RankSelectSpec.fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
    slots classLengthOverhead

theorem fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverheadLittleO
    (slots : Nat) {classLengthOverhead : Nat -> Nat}
    (hclassLength :
      SuccinctSpace.LittleOLinear classLengthOverhead) :
    SuccinctSpace.LittleOLinear
      (fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
        slots classLengthOverhead) := by
  exact
    RMQ.RankSelectSpec.fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead_littleO
      slots hclassLength

/-- The ambient directory produced by a route/class-length envelope family. -/
abbrev fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamilyDirectory
    {slots routeCost localQueryCost queryCost : Nat}
    {classLengthOverhead : Nat -> Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost classLengthOverhead)
    (bits : List Bool) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.directory
    family bits

/--
Family-level profile for route/class-length envelopes with a separate `o(n)`
budget for the concrete class/length metadata.
-/
theorem fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamilyProfile
    {slots routeCost localQueryCost queryCost : Nat}
    {classLengthOverhead : Nat -> Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost classLengthOverhead) :
    SuccinctSpace.LittleOLinear
        (fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
          slots classLengthOverhead) /\
      forall bits : List Bool,
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.componentData
            family bits
        let directory :=
          fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamilyDirectory
            family bits
        FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeProfile
            data /\
          directory.DirectoryProfile /\
          directory.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              data.totalMetadataOverhead /\
          directory.payload.length <=
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
                slots classLengthOverhead bits.length /\
          directory.auxPayload.length = data.totalMetadataOverhead /\
          directory.auxPayload.length <=
            fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
              slots classLengthOverhead bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word directory.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word directory.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (directory.accessCosted i).cost <= queryCost /\
              (directory.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankCosted target pos).cost <= queryCost /\
              (directory.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectCosted target occurrence).cost <= queryCost /\
              (directory.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.route_class_length_table_envelope_family_profile
      family

/--
Conditional compressed/FID bridge for route/class-length envelope families.
-/
theorem fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfPrimaryBudget
    {slots routeCost localQueryCost queryCost : Nat}
    {classLengthOverhead : Nat -> Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost classLengthOverhead)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.compressedOverhead
          slots classLengthOverhead primaryOverhead) /\
      forall bits : List Bool,
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.componentData
            family bits
        let directory :=
          fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamilyDirectory
            family bits
        FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeProfile
            data /\
          directory.DirectoryProfile /\
          directory.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              data.totalMetadataOverhead /\
          directory.payload.length <=
            fixedWeightPayloadBudget bits +
              RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.compressedOverhead
                slots classLengthOverhead primaryOverhead bits.length /\
          directory.auxPayload.length = data.totalMetadataOverhead /\
          directory.auxPayload.length <=
            fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
              slots classLengthOverhead bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word directory.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word directory.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (directory.accessCosted i).cost <= queryCost /\
              (directory.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankCosted target pos).cost <= queryCost /\
              (directory.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectCosted target occurrence).cost <= queryCost /\
              (directory.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.word_bounded_compressed_profile_of_primary_budget
      family primaryOverhead hprimaryO hprimary

/-- The ambient directory produced by an eight-table route field-layout family. -/
abbrev fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyDirectory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.directory
    family bits

/--
Family-level profile for eight-table route field layouts with `o(n)` route
payload and ambient query-cost bounds.
-/
theorem fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyProfile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.overhead
          slots) /\
      forall bits : List Bool,
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
            family bits
        FixedWeightAmbientComputedRRRRouteFieldTableLayoutPackedProfile data /\
          data.routeData.routePayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          ((fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyDirectory
                family bits).payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall i,
            ((fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyDirectory
                family bits).accessCosted i).cost <= queryCost) /\
          (forall target pos,
            ((fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyDirectory
                family bits).rankCosted target pos).cost <= queryCost) /\
          (forall target occurrence,
            ((fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyDirectory
                family bits).selectCosted target occurrence).cost <=
              queryCost) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.route_field_table_layout_family_profile
      family

/--
Promote an eight-table route field-layout family to the combined
route/class-length envelope family, under the explicit block-size and counted
class/length-overhead side conditions.
-/
abbrev fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToRouteClassLengthTableEnvelopeFamily
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (classLengthOverhead : Nat -> Nat)
    (hclassLengthO :
      SuccinctSpace.LittleOLinear classLengthOverhead)
    (hclassLength_le :
      forall bits : List Bool,
        fixedWeightBlockClassLengthTableOverhead
            (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
              family bits).fieldWidth
            (family.blocks bits) <=
          classLengthOverhead bits.length)
    (hblockSize_lt_fieldWidthPow :
      forall bits : List Bool,
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
          family bits).routeData.blockSize <
          2 ^
            (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
              family bits).fieldWidth)
    (hlocalCost :
      forall bits : List Bool,
        fixedWeightComputedRRRClassLengthBlockSizeQueryCost
            (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
              family bits).routeData.blockSize <=
          localQueryCost) :
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
      slots routeCost localQueryCost queryCost classLengthOverhead :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.toRouteClassLengthTableEnvelopeFamily
    family classLengthOverhead hclassLengthO hclassLength_le
    hblockSize_lt_fieldWidthPow hlocalCost

theorem fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToRouteClassLengthTableEnvelopeFamilyProfile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (classLengthOverhead : Nat -> Nat)
    (hclassLengthO :
      SuccinctSpace.LittleOLinear classLengthOverhead)
    (hclassLength_le :
      forall bits : List Bool,
        fixedWeightBlockClassLengthTableOverhead
            (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
              family bits).fieldWidth
            (family.blocks bits) <=
          classLengthOverhead bits.length)
    (hblockSize_lt_fieldWidthPow :
      forall bits : List Bool,
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
          family bits).routeData.blockSize <
          2 ^
            (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
              family bits).fieldWidth)
    (hlocalCost :
      forall bits : List Bool,
        fixedWeightComputedRRRClassLengthBlockSizeQueryCost
            (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
              family bits).routeData.blockSize <=
          localQueryCost) :
    SuccinctSpace.LittleOLinear
        (fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
          slots classLengthOverhead) /\
      forall bits : List Bool,
        let envelopeFamily :=
          fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToRouteClassLengthTableEnvelopeFamily
            family classLengthOverhead hclassLengthO hclassLength_le
            hblockSize_lt_fieldWidthPow hlocalCost
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.componentData
            envelopeFamily bits
        let directory :=
          fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamilyDirectory
            envelopeFamily bits
        FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeProfile
            data /\
          directory.DirectoryProfile /\
          directory.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              data.totalMetadataOverhead /\
          directory.payload.length <=
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
                slots classLengthOverhead bits.length /\
          directory.auxPayload.length = data.totalMetadataOverhead /\
          directory.auxPayload.length <=
            fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
              slots classLengthOverhead bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word directory.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word directory.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (directory.accessCosted i).cost <= queryCost /\
              (directory.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankCosted target pos).cost <= queryCost /\
              (directory.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectCosted target occurrence).cost <= queryCost /\
              (directory.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamilyProfile
      (fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToRouteClassLengthTableEnvelopeFamily
        family classLengthOverhead hclassLengthO hclassLength_le
        hblockSize_lt_fieldWidthPow hlocalCost)

/--
Fixed block-size/field-width constructor from a route field-layout family to
the combined route/class-length envelope family.
-/
abbrev fixedWeightAmbientComputedRRRRouteFieldTableLayoutFixedBlockSizeRouteClassLengthTableEnvelopeFamily :=
  @RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.toFixedBlockSizeRouteClassLengthTableEnvelopeFamily

/--
Profile theorem for the fixed block-size/field-width route-layout family
constructor.
-/
abbrev fixedWeightAmbientComputedRRRRouteFieldTableLayoutFixedBlockSizeRouteClassLengthTableEnvelopeFamilyProfile :=
  @RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.fixed_block_size_route_class_length_table_envelope_family_profile

/--
Fixed block-size compressed/FID bridge from global block-count and field-width
bounds.
-/
abbrev fixedWeightAmbientComputedRRRRouteFieldTableLayoutFixedBlockSizeWordBoundedCompressedProfileOfBlockBounds :=
  @RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.fixed_block_size_word_bounded_compressed_profile_of_block_bounds

/--
Conditional compressed/FID bridge for eight-table route field-layout families.
-/
theorem fixedWeightAmbientComputedRRRRouteFieldTableLayoutWordBoundedCompressedProfileOfPrimaryBudget
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (fixedWeightAmbientBlockCompositionCompressedOverhead
          slots primaryOverhead) /\
      forall bits : List Bool,
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
          family bits).LayoutPackedProfile /\
          let data :=
            fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyDirectory
              family bits
          data.DirectoryProfile /\
            data.payload.length =
              fixedWeightBlockPayloadBudget (family.blocks bits) +
                fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            data.payload.length <=
              fixedWeightPayloadBudget bits +
                fixedWeightAmbientBlockCompositionCompressedOverhead
                  slots primaryOverhead bits.length /\
            data.auxPayload.length =
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
            (forall {word : List Bool},
              List.Mem word data.codeStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall {word : List Bool},
              List.Mem word data.auxStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall i,
              (data.accessCosted i).cost <= queryCost /\
                (data.accessCosted i).erase = bits[i]?) /\
            (forall target pos,
              (data.rankCosted target pos).cost <= queryCost /\
                (data.rankCosted target pos).erase =
                  Succinct.rankPrefix target bits pos) /\
            (forall target occurrence,
              (data.selectCosted target occurrence).cost <= queryCost /\
                (data.selectCosted target occurrence).erase =
                  Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.word_bounded_compressed_profile_of_primary_budget
      family primaryOverhead hprimaryO hprimary

/--
Compressed/FID bridge after promoting an eight-table route field-layout family
to the combined route/class-length envelope family.
-/
theorem fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfPrimaryBudget
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (classLengthOverhead : Nat -> Nat)
    (hclassLengthO :
      SuccinctSpace.LittleOLinear classLengthOverhead)
    (hclassLength_le :
      forall bits : List Bool,
        fixedWeightBlockClassLengthTableOverhead
            (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
              family bits).fieldWidth
            (family.blocks bits) <=
          classLengthOverhead bits.length)
    (hblockSize_lt_fieldWidthPow :
      forall bits : List Bool,
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
          family bits).routeData.blockSize <
          2 ^
            (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
              family bits).fieldWidth)
    (hlocalCost :
      forall bits : List Bool,
        fixedWeightComputedRRRClassLengthBlockSizeQueryCost
            (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
              family bits).routeData.blockSize <=
          localQueryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.compressedOverhead
          slots classLengthOverhead primaryOverhead) /\
      forall bits : List Bool,
        let envelopeFamily :=
          fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToRouteClassLengthTableEnvelopeFamily
            family classLengthOverhead hclassLengthO hclassLength_le
            hblockSize_lt_fieldWidthPow hlocalCost
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.componentData
            envelopeFamily bits
        let directory :=
          fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamilyDirectory
            envelopeFamily bits
        FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeProfile
            data /\
          directory.DirectoryProfile /\
          directory.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              data.totalMetadataOverhead /\
          directory.payload.length <=
            fixedWeightPayloadBudget bits +
              RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.compressedOverhead
                slots classLengthOverhead primaryOverhead bits.length /\
          directory.auxPayload.length = data.totalMetadataOverhead /\
          directory.auxPayload.length <=
            fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
              slots classLengthOverhead bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word directory.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word directory.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (directory.accessCosted i).cost <= queryCost /\
              (directory.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankCosted target pos).cost <= queryCost /\
              (directory.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectCosted target occurrence).cost <= queryCost /\
              (directory.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfPrimaryBudget
      (fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToRouteClassLengthTableEnvelopeFamily
        family classLengthOverhead hclassLengthO hclassLength_le
        hblockSize_lt_fieldWidthPow hlocalCost)
      primaryOverhead hprimaryO hprimary

/-- Decoded fixed-weight entries have the requested length and true-count. -/
abbrev fixedWeightDecodeMemLengthTrueCount
    {n k code : Nat} {bits : List Bool}
    (hdec : fixedWeightDecode? n k code = some bits) :=
  RMQ.RankSelectSpec.fixedWeightDecode?_mem_length_trueCount hdec

/-- Public compressed/FID family theorem shape. -/
theorem compressedFixedWeightConstantQueryProfile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family :
      CompressedFamily overhead queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall bits : List Bool,
        ((family.directory bits).payload.length <=
          fixedWeightPayloadBudget bits + overhead bits.length) /\
          (forall i,
            ((family.directory bits).accessQueryCosted i).cost <=
                queryCost /\
              ((family.directory bits).accessQueryCosted i).erase =
                bits[i]?) /\
          (forall target pos,
            ((family.directory bits).rankQueryCosted target pos).cost <=
                queryCost /\
              ((family.directory bits).rankQueryCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            ((family.directory bits).selectQueryCosted
                target occurrence).cost <= queryCost /\
              ((family.directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.CompressedBitVectorRankSelectFamily.fixed_weight_constant_query_profile
    family

/--
Public adapter theorem: a fixed-weight auxiliary family converted to the
generic compressed/FID family satisfies the generic fixed-weight
constant-query profile.
-/
theorem fixedWeightCompressedAuxiliaryToCompressedFamilyProfile
    {overhead : Nat -> Nat} {wordSize queryCost : Nat}
    (family :
      FixedWeightCompressedAuxiliaryFamily overhead wordSize queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall bits : List Bool,
        (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).payload.length <=
          fixedWeightPayloadBudget bits + overhead bits.length) /\
          (forall i,
            (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).accessQueryCosted i).cost <=
                queryCost /\
              (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).accessQueryCosted i).erase =
                bits[i]?) /\
          (forall target pos,
            (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).rankQueryCosted target pos).cost <=
                queryCost /\
              (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).rankQueryCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).selectQueryCosted
                target occurrence).cost <=
                queryCost /\
              (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).selectQueryCosted
                  target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightCompressedAuxiliaryFamily.toCompressedFamily_fixed_weight_constant_query_profile
      family

/-- Auxiliary-overhead budget for the concrete Jacobson/Clark family. -/
abbrev jacobsonClarkOverhead :=
  RMQ.GenericSelect.jacobsonClarkRankSelectOverhead

/-- Uniform modeled query cost for the concrete Jacobson/Clark family. -/
abbrev jacobsonClarkQueryCost :=
  RMQ.GenericSelect.jacobsonClarkRankSelectQueryCost

/-- Concrete Jacobson/Clark directory for one stored bitvector. -/
abbrev jacobsonClarkDirectory :=
  RMQ.GenericSelect.jacobsonClarkBitVectorRankSelectDirectory

/-- Concrete Jacobson/Clark rank/select family. -/
abbrev jacobsonClarkFamily :=
  RMQ.GenericSelect.jacobsonClarkRankSelectFamily

/--
Public `n + o(n)`, constant-query theorem for the concrete Jacobson/Clark
rank/select family.
-/
abbrev jacobsonClarkNPlusOConstantQuery :=
  RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile

/--
Public word-bounded profile for the concrete Jacobson/Clark rank/select
family, exposing the machine-word read bounds carried by the concrete
components.
-/
abbrev jacobsonClarkWordBoundedNPlusOConstantQuery :=
  RMQ.GenericSelect.jacobsonClarkRankSelectFamily_word_bounded_n_plus_o_constant_query_profile

end RMQ.RankSelect
