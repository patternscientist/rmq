import RMQ.Core.RankSelectCompressed.Base

namespace RMQ

namespace RankSelectSpec

/-- Decode the first charged decoded-table word as a local bit block. -/
def decodedWordFromReadValues :
    List (Option (List Bool)) -> List Bool
  | some word :: _ => word
  | _ => []

@[simp] theorem decodedWordFromReadValues_singleton
    (bits : List Bool) :
    decodedWordFromReadValues [some bits] = bits := by
  simp [decodedWordFromReadValues]


/--
Local RRR-style fixed-weight block data.

The query path is concrete and dependent-read: read the packed fixed-weight
code, use it as an address into the counted universal decode table for this
block length and weight, then run a RAM word primitive on the decoded block.
The decode table is dense and therefore not an `o(n)` family construction by
itself; it is the non-oracular local block kernel the later compressed/FID
directory should use under a smaller table/routing scheme.
-/
structure FixedWeightTableRAMBlockData
    (bits : List Bool) (wordSize : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_machine : wordSize <= Nat.log2 bits.length + 1
  codeWidth_le_wordSize : fixedWeightPayloadBudget bits <= wordSize
  blockWidth_le_wordSize : bits.length <= wordSize

namespace FixedWeightTableRAMBlockData

def decodedTableOverhead
    {bits : List Bool} {wordSize : Nat}
    (_data : FixedWeightTableRAMBlockData bits wordSize) : Nat :=
  fixedWeightDecodedWordTableOverhead bits.length (trueCount bits)

@[simp] theorem decodedTableOverhead_eq
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.decodedTableOverhead =
      fixedWeightDecodedWordTableOverhead bits.length (trueCount bits) := by
  rfl

def packedStore
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightPackedPayload bits) wordSize :=
  fixedWeightPackedCodeBoundedStore bits wordSize
    data.codeWidth_le_wordSize

def decodedStore
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightDecodedWordTablePayload bits.length (trueCount bits))
      wordSize :=
  fixedWeightDecodedWordBoundedStore bits.length (trueCount bits) wordSize
    data.blockWidth_le_wordSize

theorem packed_read_values_zero
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    boundedPayloadWordReadValues data.packedStore [0] =
      [some (fixedWeightPackedPayload bits)] := by
  have hpacked :
      data.packedStore.store.words[0]? =
        some (fixedWeightPackedPayload bits) := by
    simpa [packedStore] using
      fixedWeightPackedCodeBoundedStore_get?_zero bits
        data.codeWidth_le_wordSize
  simp [boundedPayloadWordReadValues, hpacked]

theorem decoded_read_values_code
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    boundedPayloadWordReadValues data.decodedStore [fixedWeightCode bits] =
      [some bits] := by
  have hdecoded :
      data.decodedStore.store.words[fixedWeightCode bits]? = some bits := by
    simpa [decodedStore] using
      fixedWeightDecodedWordBoundedStore_get?_fixedWeightCode bits
        data.blockWidth_le_wordSize
  simp [boundedPayloadWordReadValues, hdecoded]

def payload
    {bits : List Bool} {wordSize : Nat}
    (_data : FixedWeightTableRAMBlockData bits wordSize) : List Bool :=
  fixedWeightPackedPayload bits ++
    fixedWeightDecodedWordTablePayload bits.length (trueCount bits)

@[simp] theorem payload_length
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.payload.length =
      fixedWeightPayloadBudget bits + data.decodedTableOverhead := by
  simp [payload, decodedTableOverhead, fixedWeightPackedPayload_length]

def readCodeCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) : Costed Nat :=
  Costed.bind (data.packedStore.store.readWordCosted 0) fun word? =>
    Costed.pure
      (match word? with
      | some word => SuccinctSpace.bitsToNatLE word
      | none => 0)

@[simp] theorem readCodeCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.readCodeCosted.cost = 1 := by
  simp [readCodeCosted]

@[simp] theorem readCodeCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.readCodeCosted.erase = fixedWeightCode bits := by
  simp [readCodeCosted, packedStore, fixedWeightPackedCodeBoundedStore,
    fixedWeightPackedPayload_bitsToNatLE]

def decodedWordCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    Costed (List Bool) :=
  Costed.bind data.readCodeCosted fun code =>
    Costed.bind (data.decodedStore.store.readWordCosted code) fun word? =>
      Costed.pure (word?.getD [])

@[simp] theorem decodedWordCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.decodedWordCosted.cost = 2 := by
  simp [decodedWordCosted]

@[simp] theorem decodedWordCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.decodedWordCosted.erase = bits := by
  have hdec :
      fixedWeightDecode? bits.length (trueCount bits)
          (fixedWeightCode bits) = some bits :=
    fixedWeightDecode?_fixedWeightEncode?
      (fixedWeightEncode?_eq_some_fixedWeightCode bits)
  have hget :
      data.decodedStore.store.words[fixedWeightCode bits]? = some bits :=
    fixedWeightDecodedWordBoundedStore_get?_of_decode
      data.blockWidth_le_wordSize hdec
  simp [decodedWordCosted, hget]

def accessCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (i : Nat) : Costed (Option Bool) :=
  Costed.map (fun word => word[i]?) data.decodedWordCosted

@[simp] theorem accessCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (i : Nat) :
    (data.accessCosted i).cost = 2 := by
  simp [accessCosted]

@[simp] theorem accessCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (i : Nat) :
    (data.accessCosted i).erase = bits[i]? := by
  simp [accessCosted]

def rankCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind data.decodedWordCosted fun word =>
    (RAM.rankBoolWordPrefix target word pos).toCosted

@[simp] theorem rankCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost = 3 := by
  simp [rankCosted]

@[simp] theorem rankCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  unfold rankCosted
  simp only [Costed.erase_bind, decodedWordCosted_erase]
  change (RAM.rankBoolWordPrefix target bits pos).toCosted.value =
    Succinct.rankPrefix target bits pos
  have hrun := Succinct.rankBoolWordPrefix_toCosted_run target bits pos
  simpa [Costed.run] using congrArg Prod.fst hrun

def selectCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind data.decodedWordCosted fun word =>
    (RAM.selectBoolWord target word occurrence).toCosted

@[simp] theorem selectCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost = 3 := by
  simp [selectCosted]

@[simp] theorem selectCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  unfold selectCosted
  simp only [Costed.erase_bind, decodedWordCosted_erase]
  change (RAM.selectBoolWord target bits occurrence).toCosted.value =
    Succinct.select target bits occurrence
  have hrun := Succinct.selectBoolWord_toCosted_run target bits occurrence
  simpa [Costed.run] using congrArg Prod.fst hrun

def toDependentAuxiliaryData
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    FixedWeightDependentAuxiliaryData
      bits data.decodedTableOverhead wordSize 3 := by
  refine
    { wordSize_pos := data.wordSize_pos
      packedStore := data.packedStore
      auxPayload :=
        fixedWeightDecodedWordTablePayload bits.length (trueCount bits)
      auxStore := data.decodedStore
      aux_length_eq := ?_
      accessPackedReads := fun _ => [0]
      accessAuxReads := fun _ packedWords =>
        [fixedWeightCodeFromReadValues packedWords]
      rankPackedReads := fun _ _ => [0]
      rankAuxReads := fun _ _ packedWords =>
        [fixedWeightCodeFromReadValues packedWords]
      selectPackedReads := fun _ _ => [0]
      selectAuxReads := fun _ _ packedWords =>
        [fixedWeightCodeFromReadValues packedWords]
      accessEvalCosted := fun i _ auxWords =>
        Costed.pure ((decodedWordFromReadValues auxWords)[i]?)
      rankEvalCosted := fun target pos _ auxWords =>
        (RAM.rankBoolWordPrefix target
          (decodedWordFromReadValues auxWords) pos).toCosted
      selectEvalCosted := fun target occurrence _ auxWords =>
        (RAM.selectBoolWord target
          (decodedWordFromReadValues auxWords) occurrence).toCosted
      access_query_cost_le := ?_
      rank_query_cost_le := ?_
      select_query_cost_le := ?_
      access_eval_exact := ?_
      rank_eval_exact := ?_
      select_eval_exact := ?_ }
  · simp [decodedTableOverhead]
  · intro i
    have hpackedValues := data.packed_read_values_zero
    simp [hpackedValues]
  · intro target pos
    have hpackedValues := data.packed_read_values_zero
    have hdecodedValues := data.decoded_read_values_code
    simp [hpackedValues, hdecodedValues]
  · intro target occurrence
    have hpackedValues := data.packed_read_values_zero
    have hdecodedValues := data.decoded_read_values_code
    simp [hpackedValues, hdecodedValues]
  · intro i
    have hpackedValues := data.packed_read_values_zero
    have hdecodedValues := data.decoded_read_values_code
    simp [hpackedValues, hdecodedValues]
  · intro target pos
    have hpackedValues := data.packed_read_values_zero
    have hdecodedValues := data.decoded_read_values_code
    have hrun := Succinct.rankBoolWordPrefix_toCosted_run target bits pos
    simpa [Costed.erase, Costed.run, hpackedValues, hdecodedValues]
      using congrArg Prod.fst hrun
  · intro target occurrence
    have hpackedValues := data.packed_read_values_zero
    have hdecodedValues := data.decoded_read_values_code
    have hrun := Succinct.selectBoolWord_toCosted_run
      target bits occurrence
    simpa [Costed.erase, Costed.run, hpackedValues, hdecodedValues]
      using congrArg Prod.fst hrun

def toCompressedDirectory
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    CompressedBitVectorRankSelectDirectory
      bits data.decodedTableOverhead 3 where
  payload := data.payload
  payload_length_le := by
    simp
  accessCosted := data.accessCosted
  rankCosted := data.rankCosted
  selectCosted := data.selectCosted
  access_cost_le := by
    intro i
    rw [data.accessCosted_cost i]
    omega
  rank_cost_le := by
    intro target pos
    simp
  select_cost_le := by
    intro target occurrence
    simp
  access_exact := data.accessCosted_erase
  rank_exact := data.rankCosted_erase
  select_exact := data.selectCosted_erase

/--
The direct local table/RAM directory and the generic dependent-auxiliary
adapter expose the same charged query behavior.
-/
def DependentAuxiliaryBridgeProfile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) : Prop :=
  ((data.toDependentAuxiliaryData).toCompressedDirectory).payload =
      (data.toCompressedDirectory).payload /\
    (forall i,
      (((data.toDependentAuxiliaryData).toCompressedDirectory).accessQueryCosted
          i).cost =
          ((data.toCompressedDirectory).accessQueryCosted i).cost /\
        (((data.toDependentAuxiliaryData).toCompressedDirectory).accessQueryCosted
          i).erase =
          ((data.toCompressedDirectory).accessQueryCosted i).erase) /\
    (forall target pos,
      (((data.toDependentAuxiliaryData).toCompressedDirectory).rankQueryCosted
          target pos).cost =
          ((data.toCompressedDirectory).rankQueryCosted target pos).cost /\
        (((data.toDependentAuxiliaryData).toCompressedDirectory).rankQueryCosted
          target pos).erase =
          ((data.toCompressedDirectory).rankQueryCosted target pos).erase) /\
    (forall target occurrence,
      (((data.toDependentAuxiliaryData).toCompressedDirectory).selectQueryCosted
          target occurrence).cost =
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).cost /\
        (((data.toDependentAuxiliaryData).toCompressedDirectory).selectQueryCosted
          target occurrence).erase =
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).erase)

theorem dependent_auxiliary_bridge_profile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.DependentAuxiliaryBridgeProfile := by
  constructor
  · rfl
  constructor
  · intro i
    constructor
    · change ((data.toDependentAuxiliaryData).accessCosted i).cost =
        (data.accessCosted i).cost
      have hleft :
          ((data.toDependentAuxiliaryData).accessCosted i).cost = 2 := by
        simp [toDependentAuxiliaryData, FixedWeightDependentAuxiliaryData.accessCosted,
          data.packed_read_values_zero, data.decoded_read_values_code]
      rw [hleft, data.accessCosted_cost i]
    · change ((data.toDependentAuxiliaryData).accessCosted i).erase =
        (data.accessCosted i).erase
      simp
  constructor
  · intro target pos
    constructor
    · change ((data.toDependentAuxiliaryData).rankCosted target pos).cost =
        (data.rankCosted target pos).cost
      have hleft :
          ((data.toDependentAuxiliaryData).rankCosted target pos).cost =
            3 := by
        simp [toDependentAuxiliaryData, FixedWeightDependentAuxiliaryData.rankCosted,
          data.packed_read_values_zero, data.decoded_read_values_code]
      rw [hleft, data.rankCosted_cost target pos]
    · change ((data.toDependentAuxiliaryData).rankCosted target pos).erase =
        (data.rankCosted target pos).erase
      simp
  · intro target occurrence
    constructor
    · change
        ((data.toDependentAuxiliaryData).selectCosted
          target occurrence).cost =
        (data.selectCosted target occurrence).cost
      have hleft :
          ((data.toDependentAuxiliaryData).selectCosted
              target occurrence).cost = 3 := by
        simp [toDependentAuxiliaryData, FixedWeightDependentAuxiliaryData.selectCosted,
          data.packed_read_values_zero, data.decoded_read_values_code]
      rw [hleft, data.selectCosted_cost target occurrence]
    · change
        ((data.toDependentAuxiliaryData).selectCosted
          target occurrence).erase =
        (data.selectCosted target occurrence).erase
      simp

theorem directory_profile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    (data.toCompressedDirectory).payload = data.payload /\
      (data.toCompressedDirectory).payload.length =
        fixedWeightPayloadBudget bits + data.decodedTableOverhead /\
      SuccinctSpace.flattenPayloadWords
          data.packedStore.store.words.toList =
        fixedWeightPackedPayload bits /\
      SuccinctSpace.flattenPayloadWords
          data.decodedStore.store.words.toList =
        fixedWeightDecodedWordTablePayload bits.length (trueCount bits) /\
      wordSize <= Nat.log2 bits.length + 1 /\
      (forall i,
        ((data.toCompressedDirectory).accessQueryCosted i).cost <= 3 /\
          ((data.toCompressedDirectory).accessQueryCosted i).erase =
            bits[i]?) /\
      (forall target pos,
        ((data.toCompressedDirectory).rankQueryCosted target pos).cost <=
            3 /\
          ((data.toCompressedDirectory).rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).cost <= 3 /\
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · rfl
  constructor
  · exact data.payload_length
  constructor
  · exact data.packedStore.erases
  constructor
  · exact data.decodedStore.erases
  constructor
  · exact data.wordSize_le_machine
  constructor
  · intro i
    change (data.accessCosted i).cost <= 3 /\
      (data.accessCosted i).erase = bits[i]?
    exact ⟨by rw [data.accessCosted_cost i]; omega,
      data.accessCosted_erase i⟩
  constructor
  · intro target pos
    change (data.rankCosted target pos).cost <= 3 /\
      (data.rankCosted target pos).erase =
        Succinct.rankPrefix target bits pos
    exact ⟨by rw [data.rankCosted_cost target pos]; omega,
      data.rankCosted_erase target pos⟩
  · intro target occurrence
    change (data.selectCosted target occurrence).cost <= 3 /\
      (data.selectCosted target occurrence).erase =
        Succinct.select target bits occurrence
    exact ⟨by rw [data.selectCosted_cost target occurrence]; omega,
      data.selectCosted_erase target occurrence⟩

/--
Detailed dependent-read profile for the local fixed-weight table/RAM kernel.

This exposes the non-oracular route that the directory profile abstracts over:
the packed code is read from slot zero, the erased code chooses the decoded-word
table address, and rank/select then run fixed RAM word primitives on that
decoded word.  The decoded table is dense, so this is a local block profile
rather than a global `o(n)` FID family theorem.
-/
def DependentReadProfile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) : Prop :=
  data.payload.length =
      fixedWeightPayloadBudget bits + data.decodedTableOverhead /\
    data.decodedTableOverhead =
      fixedWeightDecodedWordTableOverhead bits.length (trueCount bits) /\
    SuccinctSpace.flattenPayloadWords
        data.packedStore.store.words.toList =
      fixedWeightPackedPayload bits /\
    data.packedStore.store.words[0]? =
      some (fixedWeightPackedPayload bits) /\
    fixedWeightPayloadBudget bits <= wordSize /\
    data.readCodeCosted.cost = 1 /\
    data.readCodeCosted.erase = fixedWeightCode bits /\
    SuccinctSpace.flattenPayloadWords
        data.decodedStore.store.words.toList =
      fixedWeightDecodedWordTablePayload bits.length (trueCount bits) /\
    data.decodedStore.store.words[fixedWeightCode bits]? = some bits /\
    bits.length <= wordSize /\
    (forall {word : List Bool},
      List.Mem word data.packedStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall {word : List Bool},
      List.Mem word data.decodedStore.store.words.toList ->
        word.length <= wordSize) /\
    data.decodedWordCosted.cost = 2 /\
    data.decodedWordCosted.erase = bits /\
    wordSize <= Nat.log2 bits.length + 1 /\
    (forall i,
      (data.accessCosted i).cost = 2 /\
        (data.accessCosted i).erase = bits[i]?) /\
    (forall target pos,
      (data.rankCosted target pos).cost = 3 /\
        (data.rankCosted target pos).erase =
          Succinct.rankPrefix target bits pos) /\
    (forall target occurrence,
      (data.selectCosted target occurrence).cost = 3 /\
        (data.selectCosted target occurrence).erase =
          Succinct.select target bits occurrence)

theorem dependent_read_profile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.DependentReadProfile := by
  have hpacked :
      data.packedStore.store.words[0]? =
        some (fixedWeightPackedPayload bits) := by
    simpa [packedStore] using
      fixedWeightPackedCodeBoundedStore_get?_zero bits
        data.codeWidth_le_wordSize
  have hdecoded :
      data.decodedStore.store.words[fixedWeightCode bits]? = some bits := by
    simpa [decodedStore] using
      fixedWeightDecodedWordBoundedStore_get?_fixedWeightCode bits
        data.blockWidth_le_wordSize
  exact
    ⟨data.payload_length,
      data.decodedTableOverhead_eq,
      data.packedStore.erases,
      hpacked,
      data.codeWidth_le_wordSize,
      data.readCodeCosted_cost,
      data.readCodeCosted_erase,
      data.decodedStore.erases,
      hdecoded,
      data.blockWidth_le_wordSize,
      (fun hmem => data.packedStore.word_length_le_of_mem hmem),
      (fun hmem => data.decodedStore.word_length_le_of_mem hmem),
      data.decodedWordCosted_cost,
      data.decodedWordCosted_erase,
      data.wordSize_le_machine,
      (fun i => ⟨data.accessCosted_cost i, data.accessCosted_erase i⟩),
      (fun target pos =>
        ⟨data.rankCosted_cost target pos,
          data.rankCosted_erase target pos⟩),
      (fun target occurrence =>
        ⟨data.selectCosted_cost target occurrence,
          data.selectCosted_erase target occurrence⟩)⟩

end FixedWeightTableRAMBlockData

/--
Shared decoded-table slot for the ambient table/RAM local decoder.

The concrete table construction is allowed to choose this sparse address
layout.  The envelope below only relies on the fact that the charged decoded
table contains the block at this address; the address itself is computed from
charged class/length and packed-code read values.
-/
def fixedWeightSharedDecodeSlot (n k code : Nat) : Nat :=
  (n * (n + 1) + k) * (2 ^ n) + code

def fixedWeightSharedDecodeSlotFromReadValues
    (classLengthWords packedWords : List (Option (List Bool))) : Nat :=
  let classLength := fixedWeightClassLengthFromReadValues classLengthWords
  fixedWeightSharedDecodeSlot classLength.1 classLength.2
    (fixedWeightCodeFromReadValues packedWords)

theorem fixedWeightSharedDecodeSlotFromReadValues_encoded_prefix
    {fieldWidth : Nat} {block : List Bool}
    (rest : List (Option (List Bool)))
    (hlen : block.length < 2 ^ fieldWidth)
    (hclass : trueCount block < 2 ^ fieldWidth) :
    fixedWeightSharedDecodeSlotFromReadValues
        (some (SuccinctSpace.natToBitsLE fieldWidth block.length) ::
          some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block)) ::
          rest)
        [some (fixedWeightPackedPayload block)] =
      fixedWeightSharedDecodeSlot block.length (trueCount block)
        (fixedWeightCode block) := by
  simp [fixedWeightSharedDecodeSlotFromReadValues,
    fixedWeightClassLengthFromReadValues_encoded_prefix rest hlen hclass]

/--
Ambient route-directory plus shared table/RAM local decoder.

This is the replacement envelope for the computed-RRR log-chunk path.  It
keeps the primary fixed-weight block codes, charged route metadata, charged
class/length metadata, and one shared charged decode table in separate payload
segments.  Queries perform a second dependent auxiliary read into the shared
decode table and then run a fixed RAM word primitive, so the modeled local
decoder is constant instead of `binomialCount + blockSize`.
-/
structure FixedWeightAmbientTableRAMRouteDirectoryData
    (bits : List Bool) (blocks : List (List Bool))
    (routeOverhead decoderOverhead wordSize routeCost queryCost : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_ambient : wordSize <= Nat.log2 bits.length + 1
  blockSize : Nat
  blockSize_pos : 0 < blockSize
  blocks_flatten : SuccinctSpace.flattenPayloadWords blocks = bits
  block_length_le :
    forall {block : List Bool}, List.Mem block blocks ->
      block.length <= blockSize
  blockSize_le_wordSize : blockSize <= wordSize
  block_code_width_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightPayloadBudget block <= wordSize
  codeStore :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightBlockCodePayload blocks) wordSize
  codeStore_aligned :
    codeStore.store.words.toList = fixedWeightBlockCodeWords blocks
  routePayload : List Bool
  routeStore :
    SuccinctSpace.BoundedPayloadWordStore routePayload wordSize
  routePayload_length_eq : routePayload.length = routeOverhead
  fieldWidth : Nat
  fieldWidth_le_wordSize : fieldWidth <= wordSize
  classLengthTable :
    FixedWeightAmbientComputedRRRClassLengthTableData
      bits blocks wordSize fieldWidth
  decodePayload : List Bool
  decodeStore :
    SuccinctSpace.BoundedPayloadWordStore decodePayload wordSize
  decodePayload_length_eq : decodePayload.length = decoderOverhead
  decode_word_eq :
    forall {blockIndex : Nat} {block : List Bool},
      blocks[blockIndex]? = some block ->
        decodeStore.store.words[
            fixedWeightSharedDecodeSlot block.length (trueCount block)
              (fixedWeightCode block)]? = some block
  accessRoute :
    forall i,
      FixedWeightAmbientComputedRRRAccessRoute bits blocks i
  rankRoute :
    forall target pos,
      FixedWeightAmbientComputedRRRRankRoute bits blocks target pos
  selectRoute :
    forall target occurrence,
      FixedWeightAmbientComputedRRRSelectRoute
        bits blocks target occurrence
  access_metadata_reads_le :
    forall i, (accessRoute i).metadataReads.length <= routeCost
  rank_metadata_reads_le :
    forall target pos,
      (rankRoute target pos).metadataReads.length <= routeCost
  select_metadata_reads_le :
    forall target occurrence,
      (selectRoute target occurrence).metadataReads.length <= routeCost
  access_route_read_values_eq :
    forall i,
      boundedPayloadWordReadValues routeStore
          (accessRoute i).metadataReads =
        [some (SuccinctSpace.natToBitsLE fieldWidth
            (accessRoute i).blockIndex),
         some (SuccinctSpace.natToBitsLE fieldWidth
            (accessRoute i).offset)]
  rank_route_read_values_eq :
    forall target pos,
      boundedPayloadWordReadValues routeStore
          (rankRoute target pos).metadataReads =
        [some (SuccinctSpace.natToBitsLE fieldWidth
            (rankRoute target pos).blockIndex),
         some (SuccinctSpace.natToBitsLE fieldWidth
            (rankRoute target pos).localLimit),
         some (SuccinctSpace.natToBitsLE fieldWidth
            (rankRoute target pos).baseRank)]
  select_route_read_values_eq :
    forall target occurrence,
      boundedPayloadWordReadValues routeStore
          (selectRoute target occurrence).metadataReads =
        [some (SuccinctSpace.natToBitsLE fieldWidth
            (selectRoute target occurrence).blockIndex),
         some (SuccinctSpace.natToBitsLE fieldWidth
            (selectRoute target occurrence).localOccurrence),
         some (SuccinctSpace.natToBitsLE fieldWidth
            (selectRoute target occurrence).blockStart)]
  route_plus_table_le : routeCost + 5 <= queryCost

namespace FixedWeightAmbientTableRAMRouteDirectoryData

def ofRouteFieldTableLayout
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost localQueryCost
      queryCost : Nat}
    (layout :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks routeOverhead wordSize routeCost localQueryCost
        queryCost)
    (hblockSize_lt_fieldWidthPow :
      layout.routeData.blockSize < 2 ^ layout.fieldWidth)
    (decodePayload : List Bool)
    (decodeStore :
      SuccinctSpace.BoundedPayloadWordStore decodePayload wordSize)
    (decodePayload_length_eq :
      decodePayload.length = decoderOverhead)
    (decode_word_eq :
      forall {blockIndex : Nat} {block : List Bool},
        blocks[blockIndex]? = some block ->
          decodeStore.store.words[
              fixedWeightSharedDecodeSlot block.length (trueCount block)
                (fixedWeightCode block)]? = some block)
    (route_plus_table_le : routeCost + 5 <= queryCost) :
    FixedWeightAmbientTableRAMRouteDirectoryData
      bits blocks routeOverhead decoderOverhead wordSize routeCost
      queryCost where
  wordSize_pos := layout.routeData.wordSize_pos
  wordSize_le_ambient := layout.routeData.wordSize_le_ambient
  blockSize := layout.routeData.blockSize
  blockSize_pos := layout.routeData.blockSize_pos
  blocks_flatten := layout.routeData.blocks_flatten
  block_length_le := layout.routeData.block_length_le
  blockSize_le_wordSize := layout.routeData.blockSize_le_wordSize
  block_code_width_le := layout.routeData.block_code_width_le
  codeStore := layout.routeData.codeStore
  codeStore_aligned := layout.routeData.codeStore_aligned
  routePayload := layout.routeData.routePayload
  routeStore := layout.routeData.routeStore
  routePayload_length_eq := layout.routeData.routePayload_length_eq
  fieldWidth := layout.fieldWidth
  fieldWidth_le_wordSize := layout.fieldWidth_le_wordSize
  classLengthTable :=
    { wordSize_pos := layout.routeData.wordSize_pos
      wordSize_le_ambient := layout.routeData.wordSize_le_ambient
      fieldWidth_le_wordSize := layout.fieldWidth_le_wordSize
      blocks_flatten := layout.routeData.blocks_flatten
      block_code_width_le := layout.routeData.block_code_width_le
      block_length_lt_fieldWidthPow := by
        intro block hmem
        exact Nat.lt_of_le_of_lt
          (layout.routeData.block_length_le hmem)
          hblockSize_lt_fieldWidthPow }
  decodePayload := decodePayload
  decodeStore := decodeStore
  decodePayload_length_eq := decodePayload_length_eq
  decode_word_eq := decode_word_eq
  accessRoute := layout.routeData.accessRoute
  rankRoute := layout.routeData.rankRoute
  selectRoute := layout.routeData.selectRoute
  access_metadata_reads_le := layout.routeData.access_metadata_reads_le
  rank_metadata_reads_le := layout.routeData.rank_metadata_reads_le
  select_metadata_reads_le := layout.routeData.select_metadata_reads_le
  access_route_read_values_eq := by
    intro i
    simpa [FixedWeightAmbientComputedRRRRouteFieldTableLayoutData.toPackedRouteTableData]
      using
        (layout.toPackedRouteTableData.access_packed_metadata_read_values_eq
          i)
  rank_route_read_values_eq := by
    intro target pos
    simpa [FixedWeightAmbientComputedRRRRouteFieldTableLayoutData.toPackedRouteTableData]
      using
        (layout.toPackedRouteTableData.rank_packed_metadata_read_values_eq
          target pos)
  select_route_read_values_eq := by
    intro target occurrence
    simpa [FixedWeightAmbientComputedRRRRouteFieldTableLayoutData.toPackedRouteTableData]
      using
        (layout.toPackedRouteTableData.select_packed_metadata_read_values_eq
          target occurrence)
  route_plus_table_le := route_plus_table_le

def classLengthOverhead
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) : Nat :=
  fixedWeightBlockClassLengthTableOverhead data.fieldWidth blocks

def totalAuxOverhead
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) : Nat :=
  routeOverhead + data.classLengthOverhead + decoderOverhead

def combinedAuxPayload
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) : List Bool :=
  data.routePayload ++
    fixedWeightBlockClassLengthTablePayload data.fieldWidth blocks ++
    data.decodePayload

def combinedAuxStore
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) :
    SuccinctSpace.BoundedPayloadWordStore data.combinedAuxPayload wordSize :=
  boundedPayloadWordStoreAppend
    (boundedPayloadWordStoreAppend data.routeStore
      data.classLengthTable.classLengthStore)
    data.decodeStore

def payload
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) : List Bool :=
  fixedWeightBlockCodePayload blocks ++ data.combinedAuxPayload

@[simp] theorem combinedAuxPayload_length
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) :
    data.combinedAuxPayload.length = data.totalAuxOverhead := by
  simp [combinedAuxPayload, totalAuxOverhead, classLengthOverhead,
    fixedWeightBlockClassLengthTablePayload_length,
    data.routePayload_length_eq, data.decodePayload_length_eq,
    Nat.add_assoc]

@[simp] theorem payload_length
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) :
    data.payload.length =
      fixedWeightBlockPayloadBudget blocks + data.totalAuxOverhead := by
  simp [payload, fixedWeightBlockCodePayload_length]

def routeWordCount
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) : Nat :=
  data.routeStore.store.words.toList.length

def classLengthWordCount
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) : Nat :=
  data.classLengthTable.classLengthStore.store.words.toList.length

def combinedLengthSlot
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (blockIndex : Nat) : Nat :=
  data.routeWordCount + data.classLengthTable.lengthSlot blockIndex

def combinedClassSlot
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (blockIndex : Nat) : Nat :=
  data.routeWordCount + data.classLengthTable.classSlot blockIndex

def decodeBase
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) : Nat :=
  data.routeWordCount + data.classLengthWordCount

def combinedDecodeSlot
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (n k code : Nat) : Nat :=
  data.decodeBase + fixedWeightSharedDecodeSlot n k code

def combinedDecodeSlotFromReadValues
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (classLengthWords packedWords : List (Option (List Bool))) : Nat :=
  data.decodeBase +
    fixedWeightSharedDecodeSlotFromReadValues classLengthWords packedWords

theorem combined_length_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    data.combinedAuxStore.store.words[data.combinedLengthSlot blockIndex]? =
      some (SuccinctSpace.natToBitsLE data.fieldWidth block.length) := by
  have hlocal :
      data.classLengthTable.classLengthStore.store.words[
          data.classLengthTable.lengthSlot blockIndex]? =
        some (SuccinctSpace.natToBitsLE data.fieldWidth block.length) :=
    data.classLengthTable.length_word_eq hblock
  have hlocalList :
      data.classLengthTable.classLengthStore.store.words.toList[
          data.classLengthTable.lengthSlot blockIndex]? =
        some (SuccinctSpace.natToBitsLE data.fieldWidth block.length) := by
    simpa [Array.getElem?_toList] using hlocal
  have hcombined :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.combinedAuxStore
      (pre := data.routeStore.store.words.toList)
      (mid := data.classLengthTable.classLengthStore.store.words.toList)
      (post := data.decodeStore.store.words.toList)
      (by simp [combinedAuxStore, boundedPayloadWordStoreAppend])
      hlocalList
  simpa [combinedLengthSlot, routeWordCount] using hcombined

theorem combined_class_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    data.combinedAuxStore.store.words[data.combinedClassSlot blockIndex]? =
      some (SuccinctSpace.natToBitsLE data.fieldWidth (trueCount block)) := by
  have hlocal :
      data.classLengthTable.classLengthStore.store.words[
          data.classLengthTable.classSlot blockIndex]? =
        some (SuccinctSpace.natToBitsLE data.fieldWidth (trueCount block)) :=
    data.classLengthTable.class_word_eq hblock
  have hlocalList :
      data.classLengthTable.classLengthStore.store.words.toList[
          data.classLengthTable.classSlot blockIndex]? =
        some (SuccinctSpace.natToBitsLE data.fieldWidth (trueCount block)) := by
    simpa [Array.getElem?_toList] using hlocal
  have hcombined :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.combinedAuxStore
      (pre := data.routeStore.store.words.toList)
      (mid := data.classLengthTable.classLengthStore.store.words.toList)
      (post := data.decodeStore.store.words.toList)
      (by simp [combinedAuxStore, boundedPayloadWordStoreAppend])
      hlocalList
  simpa [combinedClassSlot, routeWordCount] using hcombined

theorem combined_decode_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    data.combinedAuxStore.store.words[
        data.combinedDecodeSlot block.length (trueCount block)
          (fixedWeightCode block)]? = some block := by
  have hlocal :
      data.decodeStore.store.words[
          fixedWeightSharedDecodeSlot block.length (trueCount block)
            (fixedWeightCode block)]? = some block :=
    data.decode_word_eq hblock
  have hlocalList :
      data.decodeStore.store.words.toList[
          fixedWeightSharedDecodeSlot block.length (trueCount block)
            (fixedWeightCode block)]? = some block := by
    simpa [Array.getElem?_toList] using hlocal
  have hcombined :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.combinedAuxStore
      (pre := data.routeStore.store.words.toList ++
        data.classLengthTable.classLengthStore.store.words.toList)
      (mid := data.decodeStore.store.words.toList)
      (post := [])
      (by simp [combinedAuxStore, boundedPayloadWordStoreAppend,
        List.append_assoc])
      hlocalList
  simpa [combinedDecodeSlot, decodeBase, routeWordCount,
    classLengthWordCount, Nat.add_assoc] using hcombined

def classLengthMetadataReads
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    {blockIndex : Nat} {block : List Bool}
    (_hblock : blocks[blockIndex]? = some block) : List Nat :=
  [data.combinedLengthSlot blockIndex, data.combinedClassSlot blockIndex]

@[simp] theorem classLengthMetadataReads_length
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    (data.classLengthMetadataReads hblock).length = 2 := by
  simp [classLengthMetadataReads]

theorem classLengthMetadataReadValues_append
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block)
    (routeReads : List Nat) :
    boundedPayloadWordReadValues data.combinedAuxStore
        (data.classLengthMetadataReads hblock ++ routeReads) =
      [some (SuccinctSpace.natToBitsLE data.fieldWidth block.length),
       some (SuccinctSpace.natToBitsLE data.fieldWidth (trueCount block))] ++
        boundedPayloadWordReadValues data.combinedAuxStore routeReads := by
  simp [classLengthMetadataReads, boundedPayloadWordReadValues,
    data.combined_length_word_eq hblock,
    data.combined_class_word_eq hblock]

theorem code_read_values_singleton
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    boundedPayloadWordReadValues data.codeStore [blockIndex] =
      [some (fixedWeightPackedPayload block)] := by
  have hget :
      data.codeStore.store.words[blockIndex]? =
        some (fixedWeightPackedPayload block) :=
    fixedWeightAmbientBlockCodeStore_get?_of_aligned
      data.codeStore_aligned hblock
  simp [boundedPayloadWordReadValues, hget]

def accessAuxReads
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (i : Nat) : List Nat :=
  let route := data.accessRoute i
  data.classLengthMetadataReads route.block_get ++ route.metadataReads

def rankAuxReads
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (target : Bool) (pos : Nat) : List Nat :=
  let route := data.rankRoute target pos
  data.classLengthMetadataReads route.block_get ++ route.metadataReads

def selectAuxReads
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (target : Bool) (occurrence : Nat) : List Nat :=
  let route := data.selectRoute target occurrence
  data.classLengthMetadataReads route.block_get ++ route.metadataReads

def accessCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (i : Nat) : Costed (Option Bool) :=
  let route := data.accessRoute i
  Costed.bind (boundedPayloadWordReadsCosted data.codeStore [route.blockIndex])
    fun codeWords =>
  Costed.bind (boundedPayloadWordReadsCosted data.combinedAuxStore
      (data.accessAuxReads i)) fun auxWords =>
  Costed.bind
      (data.combinedAuxStore.store.readWordCosted
        (data.combinedDecodeSlotFromReadValues auxWords codeWords))
      fun decoded? =>
  Costed.pure ((decoded?.getD [])[route.offset]?)

def rankCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  let route := data.rankRoute target pos
  Costed.bind (boundedPayloadWordReadsCosted data.codeStore [route.blockIndex])
    fun codeWords =>
  Costed.bind (boundedPayloadWordReadsCosted data.combinedAuxStore
      (data.rankAuxReads target pos)) fun auxWords =>
  Costed.bind
      (data.combinedAuxStore.store.readWordCosted
        (data.combinedDecodeSlotFromReadValues auxWords codeWords))
      fun decoded? =>
  Costed.map (fun localRank => route.baseRank + localRank)
    ((RAM.rankBoolWordPrefix target (decoded?.getD [])
      route.localLimit).toCosted)

def selectCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  let route := data.selectRoute target occurrence
  Costed.bind (boundedPayloadWordReadsCosted data.codeStore [route.blockIndex])
    fun codeWords =>
  Costed.bind (boundedPayloadWordReadsCosted data.combinedAuxStore
      (data.selectAuxReads target occurrence)) fun auxWords =>
  Costed.bind
      (data.combinedAuxStore.store.readWordCosted
        (data.combinedDecodeSlotFromReadValues auxWords codeWords))
      fun decoded? =>
  Costed.map (fun local? =>
      local?.map (fun offset => route.blockStart + offset))
    ((RAM.selectBoolWord target (decoded?.getD [])
      route.localOccurrence).toCosted)

theorem accessCosted_cost_le
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (i : Nat) :
    (data.accessCosted i).cost <= queryCost := by
  let route := data.accessRoute i
  have hroute := data.access_metadata_reads_le i
  have htotal := data.route_plus_table_le
  simp [accessCosted, accessAuxReads, List.length_append] at *
  omega

theorem rankCosted_cost_le
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost <= queryCost := by
  let route := data.rankRoute target pos
  have hroute := data.rank_metadata_reads_le target pos
  have htotal := data.route_plus_table_le
  simp [rankCosted, rankAuxReads, List.length_append] at *
  omega

theorem selectCosted_cost_le
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= queryCost := by
  let route := data.selectRoute target occurrence
  have hroute := data.select_metadata_reads_le target occurrence
  have htotal := data.route_plus_table_le
  simp [selectCosted, selectAuxReads, List.length_append] at *
  omega

theorem accessCosted_erase
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (i : Nat) :
    (data.accessCosted i).erase = bits[i]? := by
  let route := data.accessRoute i
  have hmem : List.Mem route.block blocks :=
    List.mem_of_getElem? route.block_get
  have hcode := data.code_read_values_singleton route.block_get
  have haux :=
    data.classLengthMetadataReadValues_append
      route.block_get route.metadataReads
  have hlen := data.classLengthTable.block_length_lt_fieldWidthPow hmem
  have hclass := trueCount_lt_of_length_lt hlen
  have hslot :
      fixedWeightSharedDecodeSlotFromReadValues
          ([some (SuccinctSpace.natToBitsLE data.fieldWidth
              route.block.length),
            some (SuccinctSpace.natToBitsLE data.fieldWidth
              (trueCount route.block))] ++
            boundedPayloadWordReadValues data.combinedAuxStore
              route.metadataReads)
          [some (fixedWeightPackedPayload route.block)] =
        fixedWeightSharedDecodeSlot route.block.length
          (trueCount route.block) (fixedWeightCode route.block) := by
    simpa using
      fixedWeightSharedDecodeSlotFromReadValues_encoded_prefix
        (boundedPayloadWordReadValues data.combinedAuxStore
          route.metadataReads) hlen hclass
  have hdecode :=
    data.combined_decode_word_eq route.block_get
  have hslot' :
      fixedWeightSharedDecodeSlotFromReadValues
          (some (SuccinctSpace.natToBitsLE data.fieldWidth
              route.block.length) ::
            some (SuccinctSpace.natToBitsLE data.fieldWidth
              (trueCount route.block)) ::
            boundedPayloadWordReadValues data.combinedAuxStore
              route.metadataReads)
          [some (fixedWeightPackedPayload route.block)] =
        fixedWeightSharedDecodeSlot route.block.length
          (trueCount route.block) (fixedWeightCode route.block) := by
    simpa using hslot
  have hdecode' :
      data.combinedAuxStore.store.words[
          data.decodeBase +
            fixedWeightSharedDecodeSlot route.block.length
              (trueCount route.block) (fixedWeightCode route.block)]? =
        some route.block := by
    simpa [combinedDecodeSlot] using hdecode
  simpa [accessCosted, accessAuxReads, route, hcode, haux,
    combinedDecodeSlotFromReadValues, hslot', hdecode'] using
    route.access_exact

theorem rankCosted_erase
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  let route := data.rankRoute target pos
  have hmem : List.Mem route.block blocks :=
    List.mem_of_getElem? route.block_get
  have hcode := data.code_read_values_singleton route.block_get
  have haux :=
    data.classLengthMetadataReadValues_append
      route.block_get route.metadataReads
  have hlen := data.classLengthTable.block_length_lt_fieldWidthPow hmem
  have hclass := trueCount_lt_of_length_lt hlen
  have hslot :
      fixedWeightSharedDecodeSlotFromReadValues
          ([some (SuccinctSpace.natToBitsLE data.fieldWidth
              route.block.length),
            some (SuccinctSpace.natToBitsLE data.fieldWidth
              (trueCount route.block))] ++
            boundedPayloadWordReadValues data.combinedAuxStore
              route.metadataReads)
          [some (fixedWeightPackedPayload route.block)] =
        fixedWeightSharedDecodeSlot route.block.length
          (trueCount route.block) (fixedWeightCode route.block) := by
    simpa using
      fixedWeightSharedDecodeSlotFromReadValues_encoded_prefix
        (boundedPayloadWordReadValues data.combinedAuxStore
          route.metadataReads) hlen hclass
  have hdecode :=
    data.combined_decode_word_eq route.block_get
  have hslot' :
      fixedWeightSharedDecodeSlotFromReadValues
          (some (SuccinctSpace.natToBitsLE data.fieldWidth
              route.block.length) ::
            some (SuccinctSpace.natToBitsLE data.fieldWidth
              (trueCount route.block)) ::
            boundedPayloadWordReadValues data.combinedAuxStore
              route.metadataReads)
          [some (fixedWeightPackedPayload route.block)] =
        fixedWeightSharedDecodeSlot route.block.length
          (trueCount route.block) (fixedWeightCode route.block) := by
    simpa using hslot
  have hdecode' :
      data.combinedAuxStore.store.words[
          data.decodeBase +
            fixedWeightSharedDecodeSlot route.block.length
              (trueCount route.block) (fixedWeightCode route.block)]? =
        some route.block := by
    simpa [combinedDecodeSlot] using hdecode
  have hrun :=
    Succinct.rankBoolWordPrefix_toCosted_run
      target route.block route.localLimit
  have hram :
      (RAM.rankBoolWordPrefix target route.block
          route.localLimit).toCosted.erase =
        Succinct.rankPrefix target route.block route.localLimit := by
    simpa [Costed.erase, Costed.run] using congrArg Prod.fst hrun
  simpa [rankCosted, rankAuxReads, route, hcode, haux,
    combinedDecodeSlotFromReadValues, hslot', hdecode', hram] using
    route.rank_exact

theorem selectCosted_erase
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  let route := data.selectRoute target occurrence
  have hmem : List.Mem route.block blocks :=
    List.mem_of_getElem? route.block_get
  have hcode := data.code_read_values_singleton route.block_get
  have haux :=
    data.classLengthMetadataReadValues_append
      route.block_get route.metadataReads
  have hlen := data.classLengthTable.block_length_lt_fieldWidthPow hmem
  have hclass := trueCount_lt_of_length_lt hlen
  have hslot :
      fixedWeightSharedDecodeSlotFromReadValues
          ([some (SuccinctSpace.natToBitsLE data.fieldWidth
              route.block.length),
            some (SuccinctSpace.natToBitsLE data.fieldWidth
              (trueCount route.block))] ++
            boundedPayloadWordReadValues data.combinedAuxStore
              route.metadataReads)
          [some (fixedWeightPackedPayload route.block)] =
        fixedWeightSharedDecodeSlot route.block.length
          (trueCount route.block) (fixedWeightCode route.block) := by
    simpa using
      fixedWeightSharedDecodeSlotFromReadValues_encoded_prefix
        (boundedPayloadWordReadValues data.combinedAuxStore
          route.metadataReads) hlen hclass
  have hdecode :=
    data.combined_decode_word_eq route.block_get
  have hslot' :
      fixedWeightSharedDecodeSlotFromReadValues
          (some (SuccinctSpace.natToBitsLE data.fieldWidth
              route.block.length) ::
            some (SuccinctSpace.natToBitsLE data.fieldWidth
              (trueCount route.block)) ::
            boundedPayloadWordReadValues data.combinedAuxStore
              route.metadataReads)
          [some (fixedWeightPackedPayload route.block)] =
        fixedWeightSharedDecodeSlot route.block.length
          (trueCount route.block) (fixedWeightCode route.block) := by
    simpa using hslot
  have hdecode' :
      data.combinedAuxStore.store.words[
          data.decodeBase +
            fixedWeightSharedDecodeSlot route.block.length
              (trueCount route.block) (fixedWeightCode route.block)]? =
        some route.block := by
    simpa [combinedDecodeSlot] using hdecode
  have hrun :=
    Succinct.selectBoolWord_toCosted_run
      target route.block route.localOccurrence
  have hselect :
      (RAM.selectBoolWord target route.block
          route.localOccurrence).toCosted.erase =
        Succinct.select target route.block route.localOccurrence := by
    simpa [Costed.erase, Costed.run] using congrArg Prod.fst hrun
  simpa [selectCosted, selectAuxReads, route, hcode, haux,
    combinedDecodeSlotFromReadValues, hslot', hdecode', hselect] using
    route.select_exact

def toCompressedDirectory
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost)
    (primaryOverhead totalOverhead : Nat)
    (hprimary :
      fixedWeightBlockPayloadBudget blocks <=
        fixedWeightPayloadBudget bits + primaryOverhead)
    (htotal :
      primaryOverhead + data.totalAuxOverhead <= totalOverhead) :
    CompressedBitVectorRankSelectDirectory bits totalOverhead queryCost where
  payload := data.payload
  payload_length_le := by
    rw [data.payload_length]
    omega
  accessCosted := data.accessCosted
  rankCosted := data.rankCosted
  selectCosted := data.selectCosted
  access_cost_le := data.accessCosted_cost_le
  rank_cost_le := data.rankCosted_cost_le
  select_cost_le := data.selectCosted_cost_le
  access_exact := data.accessCosted_erase
  rank_exact := data.rankCosted_erase
  select_exact := data.selectCosted_erase

def TableRAMRouteDirectoryProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) : Prop :=
  data.payload.length =
      fixedWeightBlockPayloadBudget blocks + data.totalAuxOverhead /\
    data.combinedAuxPayload.length = data.totalAuxOverhead /\
    data.routePayload.length = routeOverhead /\
    data.decodePayload.length = decoderOverhead /\
    (fixedWeightBlockClassLengthTablePayload data.fieldWidth blocks).length =
      data.classLengthOverhead /\
    SuccinctSpace.flattenPayloadWords blocks = bits /\
    SuccinctSpace.flattenPayloadWords data.codeStore.store.words.toList =
      fixedWeightBlockCodePayload blocks /\
    SuccinctSpace.flattenPayloadWords data.combinedAuxStore.store.words.toList =
      data.combinedAuxPayload /\
    (forall i,
      boundedPayloadWordReadValues data.routeStore
          (data.accessRoute i).metadataReads =
        [some (SuccinctSpace.natToBitsLE data.fieldWidth
            (data.accessRoute i).blockIndex),
         some (SuccinctSpace.natToBitsLE data.fieldWidth
            (data.accessRoute i).offset)]) /\
    (forall target pos,
      boundedPayloadWordReadValues data.routeStore
          (data.rankRoute target pos).metadataReads =
        [some (SuccinctSpace.natToBitsLE data.fieldWidth
            (data.rankRoute target pos).blockIndex),
         some (SuccinctSpace.natToBitsLE data.fieldWidth
            (data.rankRoute target pos).localLimit),
         some (SuccinctSpace.natToBitsLE data.fieldWidth
            (data.rankRoute target pos).baseRank)]) /\
    (forall target occurrence,
      boundedPayloadWordReadValues data.routeStore
          (data.selectRoute target occurrence).metadataReads =
        [some (SuccinctSpace.natToBitsLE data.fieldWidth
            (data.selectRoute target occurrence).blockIndex),
         some (SuccinctSpace.natToBitsLE data.fieldWidth
            (data.selectRoute target occurrence).localOccurrence),
         some (SuccinctSpace.natToBitsLE data.fieldWidth
            (data.selectRoute target occurrence).blockStart)]) /\
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
          Succinct.select target bits occurrence)

theorem tableRAM_route_directory_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {routeOverhead decoderOverhead wordSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits blocks routeOverhead decoderOverhead wordSize routeCost
        queryCost) :
    data.TableRAMRouteDirectoryProfile := by
  exact
    ⟨data.payload_length,
      data.combinedAuxPayload_length,
      data.routePayload_length_eq,
      data.decodePayload_length_eq,
      fixedWeightBlockClassLengthTablePayload_length data.fieldWidth blocks,
      data.blocks_flatten,
      data.codeStore.erases,
      data.combinedAuxStore.erases,
      data.access_route_read_values_eq,
      data.rank_route_read_values_eq,
      data.select_route_read_values_eq,
      (fun i => ⟨data.accessCosted_cost_le i,
        data.accessCosted_erase i⟩),
      (fun target pos => ⟨data.rankCosted_cost_le target pos,
        data.rankCosted_erase target pos⟩),
      (fun target occurrence =>
        ⟨data.selectCosted_cost_le target occurrence,
          data.selectCosted_erase target occurrence⟩)⟩

end FixedWeightAmbientTableRAMRouteDirectoryData

/--
Family of ambient route directories with a shared table/RAM local decoder.

The three auxiliary budgets are separated so the model does not blur route
metadata, class/length metadata, and the counted shared decoder table.  The
local query path is fixed by `FixedWeightAmbientTableRAMRouteDirectoryData`;
this family layer only accounts for `o(n)` payload and the primary
fixed-weight block-code bridge.
-/
structure FixedWeightAmbientTableRAMRouteDirectoryFamily
    (routeOverhead classLengthOverhead decoderOverhead : Nat -> Nat)
    (routeCost queryCost : Nat) where
  wordSize : Nat -> Nat
  blocks : List Bool -> List (List Bool)
  component :
    forall bits : List Bool,
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits (blocks bits) (routeOverhead bits.length)
        (decoderOverhead bits.length) (wordSize bits.length)
        routeCost queryCost
  routeOverhead_littleO :
    SuccinctSpace.LittleOLinear routeOverhead
  classLengthOverhead_littleO :
    SuccinctSpace.LittleOLinear classLengthOverhead
  decoderOverhead_littleO :
    SuccinctSpace.LittleOLinear decoderOverhead
  classLengthOverhead_bound :
    forall bits : List Bool,
      (component bits).classLengthOverhead <=
        classLengthOverhead bits.length

namespace FixedWeightAmbientTableRAMRouteDirectoryFamily

def overhead
    (routeOverhead classLengthOverhead decoderOverhead : Nat -> Nat) :
    Nat -> Nat :=
  fun n =>
    routeOverhead n + (classLengthOverhead n + decoderOverhead n)

def compressedOverhead
    (routeOverhead classLengthOverhead decoderOverhead
      primaryOverhead : Nat -> Nat) : Nat -> Nat :=
  fun n =>
    primaryOverhead n +
      overhead routeOverhead classLengthOverhead decoderOverhead n

def componentData
    {routeOverhead classLengthOverhead decoderOverhead : Nat -> Nat}
    {routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientTableRAMRouteDirectoryFamily
        routeOverhead classLengthOverhead decoderOverhead
        routeCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientTableRAMRouteDirectoryData
      bits (family.blocks bits) (routeOverhead bits.length)
      (decoderOverhead bits.length) (family.wordSize bits.length)
      routeCost queryCost :=
  family.component bits

theorem overhead_littleO
    {routeOverhead classLengthOverhead decoderOverhead : Nat -> Nat}
    {routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientTableRAMRouteDirectoryFamily
        routeOverhead classLengthOverhead decoderOverhead
        routeCost queryCost) :
    SuccinctSpace.LittleOLinear
      (overhead routeOverhead classLengthOverhead decoderOverhead) := by
  simpa [overhead] using
    family.routeOverhead_littleO.add
      (family.classLengthOverhead_littleO.add
        family.decoderOverhead_littleO)

theorem compressedOverhead_littleO
    {routeOverhead classLengthOverhead decoderOverhead : Nat -> Nat}
    {routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientTableRAMRouteDirectoryFamily
        routeOverhead classLengthOverhead decoderOverhead
        routeCost queryCost)
    {primaryOverhead : Nat -> Nat}
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead) :
    SuccinctSpace.LittleOLinear
      (compressedOverhead routeOverhead classLengthOverhead
        decoderOverhead primaryOverhead) := by
  simpa [compressedOverhead] using
    hprimaryO.add family.overhead_littleO

def directory
    {routeOverhead classLengthOverhead decoderOverhead : Nat -> Nat}
    {routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientTableRAMRouteDirectoryFamily
        routeOverhead classLengthOverhead decoderOverhead
        routeCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length)
    (bits : List Bool) :
    CompressedBitVectorRankSelectDirectory
      bits
      (compressedOverhead routeOverhead classLengthOverhead
        decoderOverhead primaryOverhead bits.length)
      queryCost := by
  let data := family.componentData bits
  refine
    data.toCompressedDirectory
      (primaryOverhead bits.length)
      (compressedOverhead routeOverhead classLengthOverhead
        decoderOverhead primaryOverhead bits.length)
      (hprimary bits) ?_
  have hclass :
      data.classLengthOverhead <= classLengthOverhead bits.length := by
    simpa [data, componentData] using
      family.classLengthOverhead_bound bits
  dsimp [FixedWeightAmbientTableRAMRouteDirectoryData.totalAuxOverhead,
    compressedOverhead, overhead]
  omega

def toCompressedFamily
    {routeOverhead classLengthOverhead decoderOverhead : Nat -> Nat}
    {routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientTableRAMRouteDirectoryFamily
        routeOverhead classLengthOverhead decoderOverhead
        routeCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    CompressedBitVectorRankSelectFamily
      (compressedOverhead routeOverhead classLengthOverhead
        decoderOverhead primaryOverhead)
      queryCost where
  directory bits := family.directory primaryOverhead hprimary bits
  overhead_littleO := family.compressedOverhead_littleO hprimaryO

theorem word_bounded_compressed_profile_of_primary_budget
    {routeOverhead classLengthOverhead decoderOverhead : Nat -> Nat}
    {routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientTableRAMRouteDirectoryFamily
        routeOverhead classLengthOverhead decoderOverhead
        routeCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead routeOverhead classLengthOverhead
          decoderOverhead primaryOverhead) /\
      forall bits : List Bool,
        let data := family.componentData bits
        let directory := family.directory primaryOverhead hprimary bits
        data.TableRAMRouteDirectoryProfile /\
          directory.payload.length <=
            fixedWeightPayloadBudget bits +
              compressedOverhead routeOverhead classLengthOverhead
                decoderOverhead primaryOverhead bits.length /\
          (forall {word : List Bool},
            List.Mem word data.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word data.combinedAuxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
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
  constructor
  · exact family.compressedOverhead_littleO hprimaryO
  · intro bits
    let data := family.componentData bits
    let directory := family.directory primaryOverhead hprimary bits
    have hdir := directory.profile
    exact
      ⟨data.tableRAM_route_directory_profile,
        hdir.1,
        (fun hmem =>
          Nat.le_trans
            (data.codeStore.word_length_le_of_mem hmem)
            data.wordSize_le_ambient),
        (fun hmem =>
          Nat.le_trans
            (data.combinedAuxStore.word_length_le_of_mem hmem)
            data.wordSize_le_ambient),
        hdir.2.1,
        hdir.2.2.1,
        hdir.2.2.2⟩

end FixedWeightAmbientTableRAMRouteDirectoryFamily

namespace FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily

/--
Consume a concrete route-field table layout as the route layer of the
shared-table table/RAM directory family.

The route payload is no longer a free field of the table/RAM envelope here:
it is the eight-table fixed-width route layout, with packed metadata readback
proved by `FixedWeightAmbientComputedRRRRouteFieldTableLayoutData`.  The
remaining supplied payload is exactly the shared decoder table.
-/
def toTableRAMRouteDirectoryFamily
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
        (family.componentData bits).routeData.blockSize <
          2 ^ (family.componentData bits).fieldWidth)
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
            (family.componentData bits).fieldWidth
            (family.blocks bits) <=
          classLengthOverhead bits.length)
    (hroutePlusTable : routeCost + 5 <= queryCost) :
    FixedWeightAmbientTableRAMRouteDirectoryFamily
      (fixedWeightAmbientBlockAuxiliaryOverhead slots)
      classLengthOverhead decoderOverhead routeCost queryCost where
  wordSize := family.wordSize
  blocks := family.blocks
  component bits :=
    FixedWeightAmbientTableRAMRouteDirectoryData.ofRouteFieldTableLayout
      (family.componentData bits)
      (hblockSize_lt_fieldWidthPow bits)
      (decodePayload bits)
      (decodeStore bits)
      (hdecodePayload_length_eq bits)
      (hdecode_word_eq bits)
      hroutePlusTable
  routeOverhead_littleO :=
    fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots
  classLengthOverhead_littleO := hclassLengthO
  decoderOverhead_littleO := hdecoderO
  classLengthOverhead_bound := by
    intro bits
    simpa [FixedWeightAmbientTableRAMRouteDirectoryData.classLengthOverhead]
      using hclassLengthOverhead_bound bits

end FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily

/--
Log-chunk specialization of the shared-table table/RAM route-directory family.

This fixes the block decomposition to sentinel log chunks and fixes the
class/length metadata budget to the narrow `log log n` field-width budget.
The route metadata and shared decoder budgets remain explicit: closing the
capstone now means constructing those payloads with `o(n)` overhead and the
charged readback equations below.
-/
structure FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily
    (routeOverhead decoderOverhead : Nat -> Nat)
    (routeCost queryCost : Nat) where
  wordSize : Nat -> Nat
  component :
    forall bits : List Bool,
      FixedWeightAmbientTableRAMRouteDirectoryData
        bits (fixedWeightLogChunkBlocksWithSentinel bits)
        (routeOverhead bits.length) (decoderOverhead bits.length)
        (wordSize bits.length) routeCost queryCost
  routeOverhead_littleO :
    SuccinctSpace.LittleOLinear routeOverhead
  decoderOverhead_littleO :
    SuccinctSpace.LittleOLinear decoderOverhead
  classLengthOverhead_bound :
    forall bits : List Bool,
      (component bits).classLengthOverhead <=
        fixedWeightLogChunkClassLengthOverhead bits.length

namespace FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily

def overhead
    (routeOverhead decoderOverhead : Nat -> Nat) : Nat -> Nat :=
  FixedWeightAmbientTableRAMRouteDirectoryFamily.overhead
    routeOverhead fixedWeightLogChunkClassLengthOverhead decoderOverhead

def compressedOverhead
    (routeOverhead decoderOverhead : Nat -> Nat) : Nat -> Nat :=
  FixedWeightAmbientTableRAMRouteDirectoryFamily.compressedOverhead
    routeOverhead fixedWeightLogChunkClassLengthOverhead decoderOverhead
    fixedWeightLogChunkBlockCountBoundWithSentinel

def componentData
    {routeOverhead decoderOverhead : Nat -> Nat}
    {routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily
        routeOverhead decoderOverhead routeCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientTableRAMRouteDirectoryData
      bits (fixedWeightLogChunkBlocksWithSentinel bits)
      (routeOverhead bits.length) (decoderOverhead bits.length)
      (family.wordSize bits.length) routeCost queryCost :=
  family.component bits

def toRouteDirectoryFamily
    {routeOverhead decoderOverhead : Nat -> Nat}
    {routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily
        routeOverhead decoderOverhead routeCost queryCost) :
    FixedWeightAmbientTableRAMRouteDirectoryFamily
      routeOverhead fixedWeightLogChunkClassLengthOverhead decoderOverhead
      routeCost queryCost where
  wordSize := family.wordSize
  blocks := fixedWeightLogChunkBlocksWithSentinel
  component bits := family.componentData bits
  routeOverhead_littleO := family.routeOverhead_littleO
  classLengthOverhead_littleO :=
    fixedWeightLogChunkClassLengthOverhead_littleO
  decoderOverhead_littleO := family.decoderOverhead_littleO
  classLengthOverhead_bound := by
    intro bits
    simpa [componentData] using family.classLengthOverhead_bound bits

def directory
    {routeOverhead decoderOverhead : Nat -> Nat}
    {routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily
        routeOverhead decoderOverhead routeCost queryCost)
    (bits : List Bool) :
    CompressedBitVectorRankSelectDirectory
      bits (compressedOverhead routeOverhead decoderOverhead bits.length)
      queryCost :=
  family.toRouteDirectoryFamily.directory
    fixedWeightLogChunkBlockCountBoundWithSentinel
    (by
      intro bits
      exact
        fixedWeightLogChunkBlockPayloadBudget_le_payloadBudget_add_bound bits)
    bits

/--
Concrete log-chunk compressed/FID bridge for the shared-table table/RAM
route-directory envelope.

The theorem consumes the log-chunk primary block-code budget and the narrow
class/length metadata overhead.  The final statement has no arbitrary block
family, no `hblocks` premise, and no separate primary-budget hypothesis; the
live obligations are the concrete route payload and counted shared decoder
payload supplied by the specialized family.
-/
theorem word_bounded_compressed_profile
    {routeOverhead decoderOverhead : Nat -> Nat}
    {routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily
        routeOverhead decoderOverhead routeCost queryCost) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead routeOverhead decoderOverhead) /\
      forall bits : List Bool,
        let data := family.componentData bits
        let directory := family.directory bits
        data.TableRAMRouteDirectoryProfile /\
          directory.payload.length <=
            fixedWeightPayloadBudget bits +
              compressedOverhead routeOverhead decoderOverhead bits.length /\
          (forall {word : List Bool},
            List.Mem word data.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word data.combinedAuxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
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
  have hprofile :=
    FixedWeightAmbientTableRAMRouteDirectoryFamily.word_bounded_compressed_profile_of_primary_budget
      family.toRouteDirectoryFamily
      fixedWeightLogChunkBlockCountBoundWithSentinel
      fixedWeightLogChunkBlockCountBoundWithSentinel_littleO
      (by
        intro bits
        exact
          fixedWeightLogChunkBlockPayloadBudget_le_payloadBudget_add_bound bits)
  simpa [compressedOverhead, overhead, componentData, directory,
    toRouteDirectoryFamily,
    FixedWeightAmbientTableRAMRouteDirectoryFamily.componentData]
    using hprofile

end FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily

theorem no_fixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily_routeWidthClassLength
    {routeOverhead decoderOverhead : Nat -> Nat}
    {routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily
        routeOverhead decoderOverhead routeCost queryCost)
    (hfield :
      forall bits : List Bool,
        (FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily.componentData
          family bits).fieldWidth =
          fixedWeightLogChunkBlockSize bits.length) :
    False := by
  have hnot :
      ¬ SuccinctSpace.LittleOLinear
        fixedWeightLogChunkClassLengthOverhead := by
    apply fixedWeight_notLittleOLinear_of_self_le
    intro n
    let bits := List.replicate n false
    have hge :
        bits.length <=
          (FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily.componentData
            family bits).classLengthOverhead := by
      simpa [FixedWeightAmbientTableRAMRouteDirectoryData.classLengthOverhead,
        hfield bits] using
        fixedWeightLogChunkRouteWidthClassLengthTableOverhead_ge_length bits
    have hle :
        (FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily.componentData
          family bits).classLengthOverhead <=
          fixedWeightLogChunkClassLengthOverhead bits.length := by
      simpa [FixedWeightAmbientTableRAMLogChunkRouteDirectoryFamily.componentData]
        using family.classLengthOverhead_bound bits
    have hn :
        n <= fixedWeightLogChunkClassLengthOverhead bits.length := by
      simpa [bits] using Nat.le_trans hge hle
    simpa [bits] using hn
  exact hnot fixedWeightLogChunkClassLengthOverhead_littleO

end RankSelectSpec

end RMQ
