import RMQ.Core.RankSelectPublic.FixedWeight

namespace RMQ.RankSelect

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

/--
Word-bounded ambient block-composition bridge for sentinel log-chunk block
families. This consumes the primary block-code budget using the proved
fixed-weight block-product bridge and the `o(n)` log-chunk block count.
-/
theorem fixedWeightAmbientBlockCompositionWordBoundedCompressedProfileOfLogChunkBlocks
    {slots queryCost : Nat}
    (family :
      FixedWeightAmbientBlockCompositionFamily slots queryCost)
    (hblocks :
      forall bits : List Bool,
        family.blocks bits = fixedWeightLogChunkBlocksWithSentinel bits) :
    SuccinctSpace.LittleOLinear
        (fixedWeightAmbientBlockCompositionCompressedOverhead
          slots fixedWeightLogChunkBlockCountBoundWithSentinel) /\
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
                slots fixedWeightLogChunkBlockCountBoundWithSentinel
                bits.length /\
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
    RMQ.RankSelectSpec.FixedWeightAmbientBlockCompositionFamily.word_bounded_compressed_profile_of_log_chunk_blocks
      family hblocks

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

/-- Pointwise profile for the ambient shared-table table/RAM route directory. -/
abbrev FixedWeightAmbientTableRAMRouteDirectoryProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) : Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMRouteDirectoryData.TableRAMRouteDirectoryProfile
    data

theorem fixedWeightAmbientTableRAMRouteDirectoryProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) :
    FixedWeightAmbientTableRAMRouteDirectoryProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientTableRAMRouteDirectoryData.tableRAM_route_directory_profile
      data

/-- Pointwise profile for the split-width shared-table table/RAM route directory. -/
abbrev FixedWeightAmbientTableRAMSplitWidthRouteDirectoryProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMSplitWidthRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) : Prop :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMSplitWidthRouteDirectoryData.SplitWidthTableRAMRouteDirectoryProfile
    data

theorem fixedWeightAmbientTableRAMSplitWidthRouteDirectoryProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMSplitWidthRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) :
    FixedWeightAmbientTableRAMSplitWidthRouteDirectoryProfile data := by
  exact
    RMQ.RankSelectSpec.FixedWeightAmbientTableRAMSplitWidthRouteDirectoryData.splitWidth_tableRAM_route_directory_profile
      data

/-- Combined `o(n)` overhead for the shared-table route-directory family. -/
abbrev fixedWeightAmbientTableRAMRouteDirectoryFamilyOverhead :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMRouteDirectoryFamily.overhead

/-- Compressed/FID overhead for the shared-table route-directory family. -/
abbrev fixedWeightAmbientTableRAMRouteDirectoryFamilyCompressedOverhead :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMRouteDirectoryFamily.compressedOverhead

/--
Public compressed/FID profile for the shared-table table/RAM route-directory
family, conditional on the primary block-code budget.
-/
abbrev fixedWeightAmbientTableRAMRouteDirectoryFamilyWordBoundedCompressedProfileOfPrimaryBudget :=
  @RMQ.RankSelectSpec.FixedWeightAmbientTableRAMRouteDirectoryFamily.word_bounded_compressed_profile_of_primary_budget

/-- Combined overhead for the split-width shared-table route-directory family. -/
abbrev fixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamilyOverhead :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamily.overhead

/-- Compressed/FID overhead for the split-width shared-table route-directory family. -/
abbrev fixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamilyCompressedOverhead :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamily.compressedOverhead

/--
Public compressed/FID profile for the split-width shared-table table/RAM
route-directory family, conditional on the primary block-code budget.
-/
abbrev fixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamilyWordBoundedCompressedProfileOfPrimaryBudget :=
  @RMQ.RankSelectSpec.FixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamily.word_bounded_compressed_profile_of_primary_budget

/-- Combined `o(n)` overhead for the log-chunk shared-table route-directory family. -/
abbrev fixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyOverhead :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily.overhead

/--
Compressed/FID overhead for the log-chunk shared-table route-directory family.
-/
abbrev fixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyCompressedOverhead :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily.compressedOverhead

/--
Public compressed/FID profile for the log-chunk shared-table route-directory
family.  This consumes the log-chunk primary block-code budget and the narrow
class/length metadata overhead; the remaining assumptions live in the concrete
family component itself.
-/
abbrev fixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyWordBoundedCompressedProfile :=
  @RMQ.RankSelectSpec.FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily.word_bounded_compressed_profile

/--
Combined `o(n)` overhead for the log-chunk split-width shared-table
route-directory family.
-/
abbrev fixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamilyOverhead :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamily.overhead

/--
Compressed/FID overhead for the log-chunk split-width shared-table
route-directory family.
-/
abbrev fixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamilyCompressedOverhead :=
  RMQ.RankSelectSpec.FixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamily.compressedOverhead

/--
Public compressed/FID profile for the log-chunk split-width shared-table
route-directory family. This consumes the log-chunk primary block-code budget
and keeps route metadata width independent from class/length metadata width.
-/
abbrev fixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamilyWordBoundedCompressedProfile :=
  @RMQ.RankSelectSpec.FixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamily.word_bounded_compressed_profile

/--
Adapter from the concrete route-field table layout into the split-width
table/RAM route-directory family.
-/
abbrev fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToSplitWidthTableRAMRouteDirectoryFamily :=
  @RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.toSplitWidthTableRAMRouteDirectoryFamily

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

/--
Compressed/FID bridge for route/class-length envelope families over sentinel
log chunks. This consumes the primary block-code budget, leaving the concrete
envelope family and its class/length overhead as the remaining construction
surface.
-/
theorem fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfLogChunkBlocks
    {slots routeCost localQueryCost queryCost : Nat}
    {classLengthOverhead : Nat -> Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost classLengthOverhead)
    (hblocks :
      forall bits : List Bool,
        family.blocks bits = fixedWeightLogChunkBlocksWithSentinel bits) :
    SuccinctSpace.LittleOLinear
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.compressedOverhead
          slots classLengthOverhead fixedWeightLogChunkBlockCountBoundWithSentinel) /\
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
                slots classLengthOverhead
                fixedWeightLogChunkBlockCountBoundWithSentinel bits.length /\
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
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.word_bounded_compressed_profile_of_log_chunk_blocks
      family hblocks

/-- The ambient directory produced by a log-chunk route/class envelope family. -/
abbrev fixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamilyDirectory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily.directory
    family bits

/--
Compressed/FID bridge for charged route/class-length envelopes over sentinel
log chunks with the narrow class/length metadata budget.

This public surface consumes the log-chunk primary block-code budget and fixes
the block decomposition and class/length overhead in the theorem statement.
-/
theorem fixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeWordBoundedCompressedProfile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily.compressedOverhead
          slots) /\
      forall bits : List Bool,
        let data :=
          RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily.componentData
            family bits
        let directory :=
          fixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamilyDirectory
            family bits
        FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeProfile
            data /\
          directory.DirectoryProfile /\
          directory.payload.length =
            fixedWeightBlockPayloadBudget
                (fixedWeightLogChunkBlocksWithSentinel bits) +
              data.totalMetadataOverhead /\
          directory.payload.length <=
            fixedWeightPayloadBudget bits +
              RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily.compressedOverhead
                slots bits.length /\
          directory.auxPayload.length = data.totalMetadataOverhead /\
          directory.auxPayload.length <=
            fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
              slots fixedWeightLogChunkClassLengthOverhead bits.length /\
          SuccinctSpace.flattenPayloadWords
              (fixedWeightLogChunkBlocksWithSentinel bits) = bits /\
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
    RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily.word_bounded_compressed_profile
      family

/--
The current log-chunk route/class-length envelope family is not inhabitable
with a fixed modeled local query cost, because its component type still uses
the computed-RRR class/length local decoder.
-/
theorem noFixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost) :
    False := by
  exact
    RMQ.RankSelectSpec.no_fixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
      family

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

/--
Promote an eight-table route field-layout family to the shared-table
table/RAM route-directory family.  Route readback is supplied by the concrete
fixed-width payload tables; the remaining supplied payload is the shared
decoder table.
-/
abbrev fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToTableRAMRouteDirectoryFamily
    {slots routeCost localQueryCost queryCost : Nat}
    {classLengthOverhead decoderOverhead : Nat -> Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (hclassLengthO :
      SuccinctSpace.LittleOLinear classLengthOverhead)
    (hdecoderO :
      SuccinctSpace.LittleOLinear decoderOverhead)
    (hblockSize_lt_fieldWidthPow :
      forall bits : List Bool,
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
          family bits).routeData.blockSize <
          2 ^
            (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
              family bits).fieldWidth)
    (decodePayload : forall _bits : List Bool, List Bool)
    (decodeStore :
      forall bits : List Bool,
        SuccinctSpace.BoundedPayloadWordStore
          (decodePayload bits) (family.wordSize bits.length))
    (hdecodePayload_length_eq :
      forall bits : List Bool,
        (decodePayload bits).length = decoderOverhead bits.length)
    (hdecode_word_eq :
      forall bits : List Bool,
        forall {blockIndex : Nat} {block : List Bool},
          (family.blocks bits)[blockIndex]? = some block ->
            (decodeStore bits).store.words[
                fixedWeightSharedDecodeSlot block.length (trueCount block)
                  (fixedWeightCode block)]? = some block)
    (hclassLengthOverhead_bound :
      forall bits : List Bool,
        fixedWeightBlockClassLengthTableOverhead
            (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
              family bits).fieldWidth
            (family.blocks bits) <=
          classLengthOverhead bits.length)
    (hroutePlusTable : routeCost + 5 <= queryCost) :
    FixedWeightAmbientTableRAMRouteDirectoryFamily
      (fixedWeightAmbientBlockAuxiliaryOverhead slots)
      classLengthOverhead decoderOverhead routeCost queryCost :=
  RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.toTableRAMRouteDirectoryFamily
    family hclassLengthO hdecoderO hblockSize_lt_fieldWidthPow
    decodePayload decodeStore hdecodePayload_length_eq hdecode_word_eq
    hclassLengthOverhead_bound hroutePlusTable

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

/--
The current computed-RRR route-field-layout-to-envelope path cannot be a
uniform constant-query log-chunk constructor when its block-size discipline is
exactly the sentinel log-chunk size.
-/
theorem noFixedWeightLogChunkRouteFieldTableLayoutFamilyToEnvelopeUniformCost
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (hblockSize :
      forall bits : List Bool,
        (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
          family bits).routeData.blockSize =
          fixedWeightLogChunkBlockSize bits.length)
    (hlocalCost :
      forall bits : List Bool,
        fixedWeightComputedRRRClassLengthBlockSizeQueryCost
            (RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.componentData
              family bits).routeData.blockSize <=
          localQueryCost) :
    False := by
  exact
    RMQ.RankSelectSpec.no_fixedWeightLogChunkRouteFieldTableLayoutFamilyToEnvelopeUniformCost
      family hblockSize hlocalCost


end RMQ.RankSelect
