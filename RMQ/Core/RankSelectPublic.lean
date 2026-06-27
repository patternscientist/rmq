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
