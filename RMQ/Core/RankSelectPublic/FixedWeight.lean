import RMQ.Core.RankSelectSpec
import RMQ.Core.RankSelectCompressed
import RMQ.Core.RankSelectCompressedSplit
import RMQ.Core.RankSelectCompressedSubLog
import RMQ.Core.RankSelectCompressedSubLogDirectory
import RMQ.Core.RankSelectCompressedSubLogRankRoute
import RMQ.Core.RankSelectCompressedSubLogPackedClark
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

/-- Shared decode-table slot for the ambient table/RAM local decoder. -/
abbrev fixedWeightSharedDecodeSlot :=
  RMQ.RankSelectSpec.fixedWeightSharedDecodeSlot

/-- Decode a shared table slot from charged class/length and code reads. -/
abbrev fixedWeightSharedDecodeSlotFromReadValues :=
  RMQ.RankSelectSpec.fixedWeightSharedDecodeSlotFromReadValues

/-- Ambient charged route directory with a shared table/RAM local decoder. -/
abbrev FixedWeightAmbientTableRAMRouteDirectoryData :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMRouteDirectoryData

/-- Family of ambient route directories with counted shared decoder payload. -/
abbrev FixedWeightAmbientTableRAMRouteDirectoryFamily :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMRouteDirectoryFamily

/-- Log-chunk shared-table route-directory family for compressed/FID rank/select. -/
abbrev FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily

/-- Split-width charged route directory with a shared table/RAM local decoder. -/
abbrev FixedWeightAmbientTableRAMSplitWidthRouteDirectoryData :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMSplitWidthRouteDirectoryData

/-- Split-width family of route directories with counted shared decoder payload. -/
abbrev FixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamily :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamily

/--
Log-chunk split-width route-directory family for compressed/FID rank/select.
-/
abbrev FixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamily :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamily

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

/-- Log-chunk route/class-length envelope family with narrow metadata budget. -/
abbrev FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily

/-- Counted fixed-weight bitvector universe used by the compressed/FID budget. -/
abbrev fixedWeightBitstrings :=
  RMQ.RankSelectSpec.fixedWeightBitstrings

/-- Mathlib-free binomial-count recurrence for fixed-weight bitvectors. -/
abbrev binomialCount :=
  RMQ.RankSelectSpec.binomialCount

/-- Number of true bits in a bitvector. -/
abbrev trueCount :=
  RMQ.RankSelectSpec.trueCount

/-- Appending bitvectors adds their true-bit counts. -/
theorem trueCountAppend (xs ys : List Bool) :
    trueCount (xs ++ ys) = trueCount xs + trueCount ys := by
  exact RMQ.RankSelectSpec.trueCount_append xs ys

/-- `binomialCount n 0 = 1` for the local fixed-weight recurrence. -/
theorem binomialCountZeroRight (n : Nat) :
    binomialCount n 0 = 1 := by
  exact RMQ.RankSelectSpec.binomialCount_zero_right n

/-- Adding ambient positions cannot shrink the fixed-weight universe count. -/
theorem binomialCountLeAddLeft (extra n k : Nat) :
    binomialCount n k <= binomialCount (extra + n) k := by
  exact RMQ.RankSelectSpec.binomialCount_le_add_left extra n k

/-- Product of two fixed-weight choices injects into the concatenated universe. -/
theorem binomialCountMulLeAdd (n1 k1 n2 k2 : Nat) :
    binomialCount n1 k1 * binomialCount n2 k2 <=
      binomialCount (n1 + n2) (k1 + k2) := by
  exact RMQ.RankSelectSpec.binomialCount_mul_le_add n1 k1 n2 k2

/-- The local fixed-weight universe is nonempty when the class is in range. -/
theorem binomialCountPosOfLe {n k : Nat}
    (hk : k <= n) : 0 < binomialCount n k := by
  exact RMQ.RankSelectSpec.binomialCount_pos_of_le hk

/-- Fixed-weight information-theoretic payload budget for one bitvector. -/
abbrev fixedWeightPayloadBudget :=
  RMQ.RankSelectSpec.fixedWeightPayloadBudget

/-- A fixed-weight code never needs more than raw length plus one bit. -/
theorem fixedWeightPayloadBudgetLeLengthAddOne
    (bits : List Bool) :
    fixedWeightPayloadBudget bits <= bits.length + 1 := by
  exact RMQ.RankSelectSpec.fixedWeightPayloadBudget_le_length_add_one bits

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

/-- Sum of per-block fixed-weight code budgets. -/
abbrev fixedWeightBlockPayloadBudget :=
  RMQ.RankSelectSpec.fixedWeightBlockPayloadBudget

/-- Block-coded fixed-weight primary payload is at most raw length plus blocks. -/
theorem fixedWeightBlockPayloadBudgetLeFlattenLengthAddBlocks
    (blocks : List (List Bool)) :
    fixedWeightBlockPayloadBudget blocks <=
      (SuccinctSpace.flattenPayloadWords blocks).length + blocks.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightBlockPayloadBudget_le_flatten_length_add_blocks
      blocks

/--
Block-coded fixed-weight primary payload is at most the global fixed-weight
payload budget for the flattened bits plus one slack bit per block.
-/
theorem fixedWeightBlockPayloadBudgetLePayloadBudgetFlattenAddBlocks
    (blocks : List (List Bool)) :
    fixedWeightBlockPayloadBudget blocks <=
      fixedWeightPayloadBudget (SuccinctSpace.flattenPayloadWords blocks) +
        blocks.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightBlockPayloadBudget_le_payloadBudget_flatten_add_blocks
      blocks

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

/-- Log-sized chunk width used by the compressed/FID block-count budget track. -/
abbrev fixedWeightLogChunkBlockSize :=
  RMQ.RankSelectSpec.fixedWeightLogChunkBlockSize

/-- Log-sized chunk decomposition used by the compressed/FID budget track. -/
abbrev fixedWeightLogChunkBlocks :=
  RMQ.RankSelectSpec.fixedWeightLogChunkBlocks

/-- Block-count budget for log-sized chunk decompositions. -/
abbrev fixedWeightLogChunkBlockCountBound :=
  RMQ.RankSelectSpec.fixedWeightLogChunkBlockCountBound

/-- Log-sized chunk decomposition with one empty sentinel block. -/
abbrev fixedWeightLogChunkBlocksWithSentinel :=
  RMQ.RankSelectSpec.fixedWeightLogChunkBlocksWithSentinel

/-- Block-count budget for log-sized chunk decompositions with a sentinel. -/
abbrev fixedWeightLogChunkBlockCountBoundWithSentinel :=
  RMQ.RankSelectSpec.fixedWeightLogChunkBlockCountBoundWithSentinel

/-- Narrow field width for log-chunk block length/class metadata. -/
abbrev fixedWeightLogChunkClassLengthFieldWidthBound :=
  RMQ.RankSelectSpec.fixedWeightLogChunkClassLengthFieldWidthBound

/-- Narrow `o(n)` class/length metadata budget for sentinel log chunks. -/
abbrev fixedWeightLogChunkClassLengthOverhead :=
  RMQ.RankSelectSpec.fixedWeightLogChunkClassLengthOverhead

/-- Route-width-padded class/length overhead over sentinel log chunks. -/
abbrev fixedWeightLogChunkRouteWidthClassLengthOverhead :=
  RMQ.RankSelectSpec.fixedWeightLogChunkRouteWidthClassLengthOverhead

/-- Dense decoder lower bound for log-sized fixed-weight chunks. -/
abbrev fixedWeightLogChunkDenseDecoderLowerBound :=
  RMQ.RankSelectSpec.fixedWeightLogChunkDenseDecoderLowerBound

/-- The log-sized chunk width is positive. -/
theorem fixedWeightLogChunkBlockSizePos (n : Nat) :
    0 < fixedWeightLogChunkBlockSize n := by
  exact RMQ.RankSelectSpec.fixedWeightLogChunkBlockSize_pos n

/-- The narrow class/length field width is positive. -/
theorem fixedWeightLogChunkClassLengthFieldWidthBoundPos (n : Nat) :
    0 < fixedWeightLogChunkClassLengthFieldWidthBound n := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkClassLengthFieldWidthBound_pos n

/-- Log-sized chunk width fits in its narrow class/length field width. -/
theorem fixedWeightLogChunkBlockSizeLtClassLengthFieldWidthPow
    (n : Nat) :
    fixedWeightLogChunkBlockSize n <
      2 ^ fixedWeightLogChunkClassLengthFieldWidthBound n := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlockSize_lt_classLengthFieldWidthPow n

/-- Log-sized chunk decompositions have `o(n)` block-count budget. -/
theorem fixedWeightLogChunkBlockCountBoundLittleO :
    SuccinctSpace.LittleOLinear
      fixedWeightLogChunkBlockCountBound := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlockCountBound_littleO

/-- Sentinel log-sized chunk decompositions have `o(n)` block-count budget. -/
theorem fixedWeightLogChunkBlockCountBoundWithSentinelLittleO :
    SuccinctSpace.LittleOLinear
      fixedWeightLogChunkBlockCountBoundWithSentinel := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlockCountBoundWithSentinel_littleO

/-- The narrow class/length field width is itself `o(n)`. -/
theorem fixedWeightLogChunkClassLengthFieldWidthBoundLittleO :
    SuccinctSpace.LittleOLinear
      fixedWeightLogChunkClassLengthFieldWidthBound := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkClassLengthFieldWidthBound_littleO

/-- Sentinel log-chunk class/length metadata has a narrow `o(n)` budget. -/
theorem fixedWeightLogChunkClassLengthOverheadLittleO :
    SuccinctSpace.LittleOLinear
      fixedWeightLogChunkClassLengthOverhead := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkClassLengthOverhead_littleO

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

/-- Log-sized chunk blocks flatten back to the original bitvector. -/
theorem fixedWeightLogChunkBlocksFlatten
    (bits : List Bool) :
    SuccinctSpace.flattenPayloadWords
        (fixedWeightLogChunkBlocks bits) = bits := by
  exact RMQ.RankSelectSpec.fixedWeightLogChunkBlocks_flatten bits

/-- Log-sized chunk decompositions use at most `n / (log n + 1) + 1` blocks. -/
theorem fixedWeightLogChunkBlocksLengthLe
    (bits : List Bool) :
    (fixedWeightLogChunkBlocks bits).length <=
      fixedWeightLogChunkBlockCountBound bits.length := by
  exact RMQ.RankSelectSpec.fixedWeightLogChunkBlocks_length_le bits

/-- Every log-sized chunk block has length at most `log n + 1`. -/
theorem fixedWeightLogChunkBlocksBlockLengthLe
    {bits block : List Bool}
    (hmem : List.Mem block (fixedWeightLogChunkBlocks bits)) :
    block.length <= fixedWeightLogChunkBlockSize bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlocks_block_length_le hmem

/-- Sentinel log-sized chunk blocks flatten back to the original bitvector. -/
theorem fixedWeightLogChunkBlocksWithSentinelFlatten
    (bits : List Bool) :
    SuccinctSpace.flattenPayloadWords
        (fixedWeightLogChunkBlocksWithSentinel bits) = bits := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlocksWithSentinel_flatten bits

/--
Sentinel log-sized chunk decompositions use at most
`n / (log n + 1) + 2` blocks.
-/
theorem fixedWeightLogChunkBlocksWithSentinelLengthLe
    (bits : List Bool) :
    (fixedWeightLogChunkBlocksWithSentinel bits).length <=
      fixedWeightLogChunkBlockCountBoundWithSentinel bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlocksWithSentinel_length_le bits

/-- Every sentinel log-sized chunk block has length at most `log n + 1`. -/
theorem fixedWeightLogChunkBlocksWithSentinelBlockLengthLe
    {bits block : List Bool}
    (hmem :
      List.Mem block (fixedWeightLogChunkBlocksWithSentinel bits)) :
    block.length <= fixedWeightLogChunkBlockSize bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlocksWithSentinel_block_length_le
      hmem

/-- Every sentinel log-sized chunk block fits in the narrow class/length width. -/
theorem fixedWeightLogChunkBlocksWithSentinelBlockLengthLtClassLengthFieldWidthPow
    {bits block : List Bool}
    (hmem :
      List.Mem block (fixedWeightLogChunkBlocksWithSentinel bits)) :
    block.length <
      2 ^ fixedWeightLogChunkClassLengthFieldWidthBound bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlocksWithSentinel_block_length_lt_classLengthFieldWidthPow
      hmem

/-- Every sentinel log-sized chunk class fits in the narrow class/length width. -/
theorem fixedWeightLogChunkBlocksWithSentinelBlockClassLtClassLengthFieldWidthPow
    {bits block : List Bool}
    (hmem :
      List.Mem block (fixedWeightLogChunkBlocksWithSentinel bits)) :
    trueCount block <
      2 ^ fixedWeightLogChunkClassLengthFieldWidthBound bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlocksWithSentinel_block_class_lt_classLengthFieldWidthPow
      hmem

/--
Log-chunk block coding is bounded by the raw bit length plus the concrete
sentinel block count.
-/
theorem fixedWeightLogChunkBlockPayloadBudgetLeLengthAddBlockCount
    (bits : List Bool) :
    fixedWeightBlockPayloadBudget
        (fixedWeightLogChunkBlocksWithSentinel bits) <=
      bits.length +
        (fixedWeightLogChunkBlocksWithSentinel bits).length := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlockPayloadBudget_le_length_add_blockCount
      bits

/--
Log-chunk block coding is bounded by raw bit length plus the `o(n)` block-count
budget. This is the conservative `n + o(n)` primary bridge, not yet the
fixed-weight `log binomial + o(n)` bridge.
-/
theorem fixedWeightLogChunkBlockPayloadBudgetLeLengthAddBound
    (bits : List Bool) :
    fixedWeightBlockPayloadBudget
        (fixedWeightLogChunkBlocksWithSentinel bits) <=
      bits.length +
        fixedWeightLogChunkBlockCountBoundWithSentinel bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlockPayloadBudget_le_length_add_bound
      bits

/--
Sentinel log-chunk block coding is bounded by the global fixed-weight payload
budget plus the concrete sentinel block count.
-/
theorem fixedWeightLogChunkBlockPayloadBudgetLePayloadBudgetAddBlockCount
    (bits : List Bool) :
    fixedWeightBlockPayloadBudget
        (fixedWeightLogChunkBlocksWithSentinel bits) <=
      fixedWeightPayloadBudget bits +
        (fixedWeightLogChunkBlocksWithSentinel bits).length := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlockPayloadBudget_le_payloadBudget_add_blockCount
      bits

/--
Sentinel log-chunk block coding discharges the primary fixed-weight budget with
the `o(n)` sentinel block-count overhead.
-/
theorem fixedWeightLogChunkBlockPayloadBudgetLePayloadBudgetAddBound
    (bits : List Bool) :
    fixedWeightBlockPayloadBudget
        (fixedWeightLogChunkBlocksWithSentinel bits) <=
      fixedWeightPayloadBudget bits +
        fixedWeightLogChunkBlockCountBoundWithSentinel bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlockPayloadBudget_le_payloadBudget_add_bound
      bits

/--
For the current computed-RRR class/length local decoder, log-sized chunks
eventually exceed any fixed local query budget.
-/
theorem fixedWeightComputedRRRClassLengthLogChunkBlockSizeQueryCostGt
    (localQueryCost : Nat) :
    localQueryCost <
      RMQ.RankSelectSpec.fixedWeightComputedRRRClassLengthBlockSizeQueryCost
        (fixedWeightLogChunkBlockSize (2 ^ localQueryCost)) := by
  exact
    RMQ.RankSelectSpec.fixedWeightComputedRRRClassLengthLogChunkBlockSizeQueryCost_gt
      localQueryCost

/--
No single modeled constant can bound the current computed-RRR class/length
decoder over all sentinel log-chunk block sizes.
-/
theorem noFixedWeightComputedRRRClassLengthLogChunkBlockSizeUniformCost
    (localQueryCost : Nat) :
    ¬ (forall n : Nat,
        RMQ.RankSelectSpec.fixedWeightComputedRRRClassLengthBlockSizeQueryCost
            (fixedWeightLogChunkBlockSize n) <=
          localQueryCost) := by
  exact
    RMQ.RankSelectSpec.no_fixedWeightComputedRRRClassLengthLogChunkBlockSizeUniformCost
      localQueryCost

/-- All-false bitvectors have true-count zero. -/
theorem trueCountReplicateFalse (n : Nat) :
    trueCount (List.replicate n false) = 0 := by
  exact RMQ.RankSelectSpec.trueCount_replicate_false n

/--
The current computed-RRR class/length decoder costs `n + 5` on an all-false
block of length `n`, so even this easy class is not uniformly constant over
log-sized blocks.
-/
theorem fixedWeightComputedRRRClassLengthQueryCostReplicateFalse
    (n : Nat) :
    RMQ.RankSelectSpec.fixedWeightComputedRRRClassLengthQueryCost
        (List.replicate n false) =
      n + 5 := by
  exact
    RMQ.RankSelectSpec.fixedWeightComputedRRRClassLengthQueryCost_replicate_false
      n

/-- The concrete sentinel log-chunk class/length table fits the narrow budget. -/
theorem fixedWeightLogChunkBlockClassLengthTableOverheadLe
    (bits : List Bool) :
    fixedWeightBlockClassLengthTableOverhead
        (fixedWeightLogChunkClassLengthFieldWidthBound bits.length)
        (fixedWeightLogChunkBlocksWithSentinel bits) <=
      fixedWeightLogChunkClassLengthOverhead bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlockClassLengthTableOverhead_le bits

/-- Sentinel log chunks cover the source length when multiplied by chunk size. -/
theorem fixedWeightLogChunkBlocksWithSentinelLengthMulBlockSizeGe
    (bits : List Bool) :
    bits.length <=
      (fixedWeightLogChunkBlocksWithSentinel bits).length *
        fixedWeightLogChunkBlockSize bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkBlocksWithSentinel_length_mul_blockSize_ge
      bits

/--
Using route-width fields for class/length metadata over sentinel log chunks
already costs at least the source length.
-/
theorem fixedWeightLogChunkRouteWidthClassLengthTableOverheadGeLength
    (bits : List Bool) :
    bits.length <=
      fixedWeightBlockClassLengthTableOverhead
        (fixedWeightLogChunkBlockSize bits.length)
        (fixedWeightLogChunkBlocksWithSentinel bits) := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkRouteWidthClassLengthTableOverhead_ge_length
      bits

/-- Route-width-padded class/length metadata is not an `o(n)` overhead. -/
theorem fixedWeightLogChunkRouteWidthClassLengthOverheadNotLittleO :
    ¬ SuccinctSpace.LittleOLinear
      fixedWeightLogChunkRouteWidthClassLengthOverhead := by
  exact
    RMQ.RankSelectSpec.fixedWeightLogChunkRouteWidthClassLengthOverhead_not_littleO

/--
Dense all-code decoder tables at the log-chunk block size cannot be counted as
`o(n)` auxiliary payload.
-/
theorem noFixedWeightLogChunkDenseDecoderLittleO
    {decoderOverhead : Nat -> Nat}
    (hdense :
      forall n,
        fixedWeightLogChunkDenseDecoderLowerBound n <=
          decoderOverhead n) :
    ¬ SuccinctSpace.LittleOLinear decoderOverhead := by
  exact
    RMQ.RankSelectSpec.no_fixedWeightLogChunk_dense_decoder_littleO
      hdense

/--
The single-width table/RAM log-chunk family cannot set its class/length table
width to the global route width and still satisfy the narrow log-chunk
class/length `o(n)` budget.
-/
theorem noFixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyRouteWidthClassLength
    {routeOverhead decoderOverhead : Nat -> Nat}
    {routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily
        routeOverhead decoderOverhead routeCost queryCost)
    (hfield :
      forall bits : List Bool,
        (RMQ.RankSelectSpec.FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily.componentData
          family bits).fieldWidth =
          fixedWeightLogChunkBlockSize bits.length) :
    False := by
  exact
    RMQ.RankSelectSpec.no_fixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily_routeWidthClassLength
      family hfield

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
A chunk block read at `pos / blockSize` has the local rank needed to recover
the global rank prefix at `pos`.
-/
theorem fixedWeightChunkBlocksGetRankPrefixAddExact
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    {bits block : List Bool} {target : Bool} {pos : Nat}
    (hpos : pos <= bits.length)
    (hget :
      (fixedWeightChunkBlocks blockSize bits)[pos / blockSize]? =
        some block) :
    Succinct.rankPrefix target bits ((pos / blockSize) * blockSize) +
        Succinct.rankPrefix target block
          (pos - (pos / blockSize) * blockSize) =
      Succinct.rankPrefix target bits pos := by
  exact
    RMQ.RankSelectSpec.fixedWeightChunkBlocks_get?_rankPrefix_add_exact
      hblockSize hpos hget

/--
A chunk block containing a global selected bit gives the matching local select
offset, shifted back by the block start.
-/
theorem fixedWeightChunkBlocksGetSelectExactOfGlobalSelect
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    {bits block : List Bool} {target : Bool}
    {occurrence idx : Nat}
    (hselect : Succinct.select target bits occurrence = some idx)
    (hget :
      (fixedWeightChunkBlocks blockSize bits)[idx / blockSize]? =
        some block) :
    (Succinct.select target block
        (occurrence -
          Succinct.rankPrefix target bits
            ((idx / blockSize) * blockSize))).map
        (fun offset => (idx / blockSize) * blockSize + offset) =
      some idx := by
  exact
    RMQ.RankSelectSpec.fixedWeightChunkBlocks_get?_select_exact_of_global_select
      hblockSize hselect hget

/--
Concrete access route for sentinel chunk blocks. In-range accesses route to
the computed chunk; invalid accesses route to the empty sentinel block.
-/
abbrev fixedWeightChunkAccessRouteWithSentinel :=
  @RMQ.RankSelectSpec.fixedWeightChunkAccessRouteWithSentinel

/--
Concrete rank route for sentinel chunk blocks. In-range rank queries route to
the containing chunk; boundary/out-of-range queries route to the empty sentinel
with full-prefix base rank.
-/
abbrev fixedWeightChunkRankRouteWithSentinel :=
  @RMQ.RankSelectSpec.fixedWeightChunkRankRouteWithSentinel

/--
Concrete select route for sentinel chunk blocks. Successful selects route to
the selected bit's chunk; missing selects route to the empty sentinel.
-/
abbrev fixedWeightChunkSelectRouteWithSentinel :=
  @RMQ.RankSelectSpec.fixedWeightChunkSelectRouteWithSentinel

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


end RMQ.RankSelect
