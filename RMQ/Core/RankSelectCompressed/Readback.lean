import RMQ.Core.RankSelectCompressed.FixedWeightCodec

namespace RMQ

namespace RankSelectSpec

/--
Charged read of the fixed-weight packed payload.

The cost is the packed payload length, so this is an honest readback scaffold,
not the final constant-time FID query layer.
-/
def fixedWeightPackedReadbackPayloadCosted
    (bits : List Bool) : Costed (List Bool) :=
  Costed.tickValue (fixedWeightPayloadBudget bits)
    (fixedWeightPackedPayload bits)

@[simp] theorem fixedWeightPackedReadbackPayloadCosted_cost
    (bits : List Bool) :
    (fixedWeightPackedReadbackPayloadCosted bits).cost =
      fixedWeightPayloadBudget bits := by
  simp [fixedWeightPackedReadbackPayloadCosted]

@[simp] theorem fixedWeightPackedReadbackPayloadCosted_erase
    (bits : List Bool) :
    (fixedWeightPackedReadbackPayloadCosted bits).erase =
      fixedWeightPackedPayload bits := by
  simp [fixedWeightPackedReadbackPayloadCosted]

/-- Charged readback decode through `bitsToNatLE` and `fixedWeightDecode?`. -/
def fixedWeightPackedReadbackDecodeCosted
    (bits : List Bool) : Costed (Option (List Bool)) :=
  Costed.bind (fixedWeightPackedReadbackPayloadCosted bits) fun payload =>
    Costed.pure
      (fixedWeightDecode? bits.length (trueCount bits)
        (SuccinctSpace.bitsToNatLE payload))

@[simp] theorem fixedWeightPackedReadbackDecodeCosted_cost
    (bits : List Bool) :
    (fixedWeightPackedReadbackDecodeCosted bits).cost =
      fixedWeightPayloadBudget bits := by
  simp [fixedWeightPackedReadbackDecodeCosted]

@[simp] theorem fixedWeightPackedReadbackDecodeCosted_erase
    (bits : List Bool) :
    (fixedWeightPackedReadbackDecodeCosted bits).erase = some bits := by
  simp [fixedWeightPackedReadbackDecodeCosted,
    fixedWeightDecode?_packedPayload]

/-- Access through the charged fixed-weight packed readback decoder. -/
def fixedWeightPackedReadbackAccessCosted
    (bits : List Bool) (i : Nat) : Costed (Option Bool) :=
  Costed.bind (fixedWeightPackedReadbackDecodeCosted bits) fun decoded =>
    Costed.pure
      (match decoded with
      | some bits => bits[i]?
      | none => none)

@[simp] theorem fixedWeightPackedReadbackAccessCosted_cost
    (bits : List Bool) (i : Nat) :
    (fixedWeightPackedReadbackAccessCosted bits i).cost =
      fixedWeightPayloadBudget bits := by
  simp [fixedWeightPackedReadbackAccessCosted]

@[simp] theorem fixedWeightPackedReadbackAccessCosted_erase
    (bits : List Bool) (i : Nat) :
    (fixedWeightPackedReadbackAccessCosted bits i).erase = bits[i]? := by
  simp [fixedWeightPackedReadbackAccessCosted]

/-- Rank through the charged fixed-weight packed readback decoder. -/
def fixedWeightPackedReadbackRankCosted
    (bits : List Bool) (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind (fixedWeightPackedReadbackDecodeCosted bits) fun decoded =>
    Costed.pure
      (match decoded with
      | some bits => Succinct.rankPrefix target bits pos
      | none => 0)

@[simp] theorem fixedWeightPackedReadbackRankCosted_cost
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (fixedWeightPackedReadbackRankCosted bits target pos).cost =
      fixedWeightPayloadBudget bits := by
  simp [fixedWeightPackedReadbackRankCosted]

@[simp] theorem fixedWeightPackedReadbackRankCosted_erase
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (fixedWeightPackedReadbackRankCosted bits target pos).erase =
      Succinct.rankPrefix target bits pos := by
  simp [fixedWeightPackedReadbackRankCosted]

/-- Select through the charged fixed-weight packed readback decoder. -/
def fixedWeightPackedReadbackSelectCosted
    (bits : List Bool) (target : Bool)
    (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind (fixedWeightPackedReadbackDecodeCosted bits) fun decoded =>
    Costed.pure
      (match decoded with
      | some bits => Succinct.select target bits occurrence
      | none => none)

@[simp] theorem fixedWeightPackedReadbackSelectCosted_cost
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (fixedWeightPackedReadbackSelectCosted bits target occurrence).cost =
      fixedWeightPayloadBudget bits := by
  simp [fixedWeightPackedReadbackSelectCosted]

@[simp] theorem fixedWeightPackedReadbackSelectCosted_erase
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (fixedWeightPackedReadbackSelectCosted bits target occurrence).erase =
      Succinct.select target bits occurrence := by
  simp [fixedWeightPackedReadbackSelectCosted]

/--
Compressed rank/select directory profile for one bitvector.

Unlike `BitVectorRankSelectDirectory`, this surface does not charge the raw
`bits.length` stored-bit prefix.  Its payload is bounded by the fixed-weight
universe budget plus `overhead bits.length` auxiliary bits.
-/
structure CompressedBitVectorRankSelectDirectory
    (bits : List Bool) (overhead queryCost : Nat) where
  payload : List Bool
  payload_length_le :
    payload.length <= fixedWeightPayloadBudget bits + overhead
  accessCosted : Nat -> Costed (Option Bool)
  rankCosted : Bool -> Nat -> Costed Nat
  selectCosted : Bool -> Nat -> Costed (Option Nat)
  access_cost_le : forall i, (accessCosted i).cost <= queryCost
  rank_cost_le :
    forall target pos, (rankCosted target pos).cost <= queryCost
  select_cost_le :
    forall target occurrence,
      (selectCosted target occurrence).cost <= queryCost
  access_exact : forall i, (accessCosted i).erase = bits[i]?
  rank_exact :
    forall target pos,
      (rankCosted target pos).erase =
        Succinct.rankPrefix target bits pos
  select_exact :
    forall target occurrence,
      (selectCosted target occurrence).erase =
        Succinct.select target bits occurrence

namespace CompressedBitVectorRankSelectDirectory

def accessQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory :
      CompressedBitVectorRankSelectDirectory bits overhead queryCost)
    (i : Nat) : Costed (Option Bool) :=
  directory.accessCosted i

def rankQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory :
      CompressedBitVectorRankSelectDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  directory.rankCosted target pos

def selectQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory :
      CompressedBitVectorRankSelectDirectory bits overhead queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  directory.selectCosted target occurrence

theorem profile
    {bits : List Bool} {overhead queryCost : Nat}
    (directory :
      CompressedBitVectorRankSelectDirectory bits overhead queryCost) :
    directory.payload.length <=
        fixedWeightPayloadBudget bits + overhead /\
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
  constructor
  · exact directory.payload_length_le
  · constructor
    · intro i
      exact ⟨directory.access_cost_le i, directory.access_exact i⟩
    · constructor
      · intro target pos
        exact
          ⟨directory.rank_cost_le target pos,
            directory.rank_exact target pos⟩
      · intro target occurrence
        exact
          ⟨directory.select_cost_le target occurrence,
            directory.select_exact target occurrence⟩

end CompressedBitVectorRankSelectDirectory

/--
Concrete packed fixed-weight readback directory for one bitvector.

This consumes the packed payload through the charged readback decoder above.
Its query budget is the packed payload budget for this bitvector, so it is a
non-oracular readback construction rather than the final constant-query FID
family.
-/
def fixedWeightPackedReadbackDirectory
    (bits : List Bool) :
    CompressedBitVectorRankSelectDirectory
      bits 0 (fixedWeightPayloadBudget bits) where
  payload := fixedWeightPackedPayload bits
  payload_length_le := by
    simp [fixedWeightPackedPayload_length]
  accessCosted := fixedWeightPackedReadbackAccessCosted bits
  rankCosted := fixedWeightPackedReadbackRankCosted bits
  selectCosted := fixedWeightPackedReadbackSelectCosted bits
  access_cost_le := by
    intro i
    simp
  rank_cost_le := by
    intro target pos
    simp
  select_cost_le := by
    intro target occurrence
    simp
  access_exact := by
    intro i
    simp
  rank_exact := by
    intro target pos
    simp
  select_exact := by
    intro target occurrence
    simp

theorem fixedWeightPackedReadbackDirectory_profile
    (bits : List Bool) :
    (fixedWeightPackedReadbackDirectory bits).payload =
        fixedWeightPackedPayload bits /\
      (fixedWeightPackedReadbackDirectory bits).payload.length =
        fixedWeightPayloadBudget bits /\
      (forall i,
        ((fixedWeightPackedReadbackDirectory bits).accessQueryCosted i).cost =
            fixedWeightPayloadBudget bits /\
          ((fixedWeightPackedReadbackDirectory bits).accessQueryCosted i).erase =
            bits[i]?) /\
      (forall target pos,
        ((fixedWeightPackedReadbackDirectory bits).rankQueryCosted
            target pos).cost = fixedWeightPayloadBudget bits /\
          ((fixedWeightPackedReadbackDirectory bits).rankQueryCosted
            target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((fixedWeightPackedReadbackDirectory bits).selectQueryCosted
            target occurrence).cost =
            fixedWeightPayloadBudget bits /\
          ((fixedWeightPackedReadbackDirectory bits).selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · rfl
  · constructor
    · exact fixedWeightPackedPayload_length bits
    · constructor
      · intro i
        exact
          ⟨fixedWeightPackedReadbackAccessCosted_cost bits i,
            fixedWeightPackedReadbackAccessCosted_erase bits i⟩
      · constructor
        · intro target pos
          exact
            ⟨fixedWeightPackedReadbackRankCosted_cost bits target pos,
              fixedWeightPackedReadbackRankCosted_erase bits target pos⟩
        · intro target occurrence
          exact
            ⟨fixedWeightPackedReadbackSelectCosted_cost bits target occurrence,
              fixedWeightPackedReadbackSelectCosted_erase
                bits target occurrence⟩

/-- Number of bounded payload words in the chunked fixed-weight readback view. -/
def fixedWeightPackedReadbackWordCount
    (bits : List Bool) (wordSize : Nat) : Nat :=
  (SuccinctSpace.chunkPayloadWords wordSize
    (fixedWeightPackedPayload bits)).length

/--
Chunked readback data for the fixed-weight packed payload.

The store is tied to `fixedWeightPackedPayload bits`, and every stored word is
bounded by `wordSize`.
-/
structure FixedWeightPackedReadbackData
    (bits : List Bool) (wordSize : Nat) where
  wordSize_pos : 0 < wordSize
  wordStore :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightPackedPayload bits) wordSize

namespace FixedWeightPackedReadbackData

/-- Canonical chunked readback data for one bitvector and positive word size. -/
def ofChunks
    (bits : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    FixedWeightPackedReadbackData bits wordSize where
  wordSize_pos := hword
  wordStore :=
    SuccinctSpace.BoundedPayloadWordStore.ofChunks
      (fixedWeightPackedPayload bits) hword

/-- Read and flatten all payload words, charging one read per stored word. -/
def readCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    Costed (List Bool) :=
  Costed.map SuccinctSpace.flattenPayloadWords
    data.wordStore.store.readAllWordsCosted

@[simp] theorem readCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    data.readCosted.cost = data.wordStore.store.words.size := by
  simp [readCosted]

@[simp] theorem readCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    data.readCosted.erase = fixedWeightPackedPayload bits := by
  simpa [readCosted] using
    data.wordStore.store.readAllWordsCosted_flatten_erase

/-- Decode the charged chunked payload readback. -/
def decodeCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    Costed (Option (List Bool)) :=
  Costed.bind data.readCosted fun payload =>
    Costed.pure
      (fixedWeightDecode? bits.length (trueCount bits)
        (SuccinctSpace.bitsToNatLE payload))

@[simp] theorem decodeCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    data.decodeCosted.cost = data.wordStore.store.words.size := by
  simp [decodeCosted]

@[simp] theorem decodeCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    data.decodeCosted.erase = some bits := by
  simp [decodeCosted, fixedWeightDecode?_packedPayload]

/-- Access through chunked packed-payload readback. -/
def accessCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (i : Nat) : Costed (Option Bool) :=
  Costed.bind data.decodeCosted fun decoded =>
    Costed.pure
      (match decoded with
      | some bits => bits[i]?
      | none => none)

@[simp] theorem accessCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (i : Nat) :
    (data.accessCosted i).cost = data.wordStore.store.words.size := by
  simp [accessCosted]

@[simp] theorem accessCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (i : Nat) :
    (data.accessCosted i).erase = bits[i]? := by
  simp [accessCosted]

/-- Rank through chunked packed-payload readback. -/
def rankCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind data.decodeCosted fun decoded =>
    Costed.pure
      (match decoded with
      | some bits => Succinct.rankPrefix target bits pos
      | none => 0)

@[simp] theorem rankCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost =
      data.wordStore.store.words.size := by
  simp [rankCosted]

@[simp] theorem rankCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  simp [rankCosted]

/-- Select through chunked packed-payload readback. -/
def selectCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind data.decodeCosted fun decoded =>
    Costed.pure
      (match decoded with
      | some bits => Succinct.select target bits occurrence
      | none => none)

@[simp] theorem selectCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost =
      data.wordStore.store.words.size := by
  simp [selectCosted]

@[simp] theorem selectCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  simp [selectCosted]

theorem read_words_length_le
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    {word : List Bool}
    (hmem : List.Mem word data.wordStore.store.words.toList) :
    word.length <= wordSize :=
  data.wordStore.word_length_le_of_mem hmem

/-- Chunked readback data as a compressed directory with word-count query cost. -/
def toCompressedDirectory
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    CompressedBitVectorRankSelectDirectory
      bits 0 data.wordStore.store.words.size where
  payload := fixedWeightPackedPayload bits
  payload_length_le := by
    simp [fixedWeightPackedPayload_length]
  accessCosted := data.accessCosted
  rankCosted := data.rankCosted
  selectCosted := data.selectCosted
  access_cost_le := by
    intro i
    simp
  rank_cost_le := by
    intro target pos
    simp
  select_cost_le := by
    intro target occurrence
    simp
  access_exact := by
    intro i
    simp
  rank_exact := by
    intro target pos
    simp
  select_exact := by
    intro target occurrence
    simp

theorem profile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    (data.toCompressedDirectory).payload =
        fixedWeightPackedPayload bits /\
      (data.toCompressedDirectory).payload.length =
        fixedWeightPayloadBudget bits /\
      (forall i,
        ((data.toCompressedDirectory).accessQueryCosted i).cost =
            data.wordStore.store.words.size /\
          ((data.toCompressedDirectory).accessQueryCosted i).erase =
            bits[i]?) /\
      (forall target pos,
        ((data.toCompressedDirectory).rankQueryCosted target pos).cost =
            data.wordStore.store.words.size /\
          ((data.toCompressedDirectory).rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).cost =
            data.wordStore.store.words.size /\
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  exact
    And.intro rfl
      (And.intro (fixedWeightPackedPayload_length bits)
        (And.intro
          (fun i =>
            And.intro (data.accessCosted_cost i)
              (data.accessCosted_erase i))
          (And.intro
            (fun target pos =>
              And.intro (data.rankCosted_cost target pos)
                (data.rankCosted_erase target pos))
            (fun target occurrence =>
              And.intro (data.selectCosted_cost target occurrence)
                (data.selectCosted_erase target occurrence)))))

theorem ofChunks_word_count
    (bits : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    ((ofChunks bits hword).wordStore.store.words.size) =
      fixedWeightPackedReadbackWordCount bits wordSize := by
  simp [ofChunks, fixedWeightPackedReadbackWordCount,
    SuccinctSpace.BoundedPayloadWordStore.ofChunks]

theorem ofChunks_profile
    (bits : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    let data := ofChunks bits hword
    (data.toCompressedDirectory).payload =
        fixedWeightPackedPayload bits /\
      (data.toCompressedDirectory).payload.length =
        fixedWeightPayloadBudget bits /\
      (forall i,
        ((data.toCompressedDirectory).accessQueryCosted i).cost =
            fixedWeightPackedReadbackWordCount bits wordSize /\
          ((data.toCompressedDirectory).accessQueryCosted i).erase =
            bits[i]?) /\
      (forall target pos,
        ((data.toCompressedDirectory).rankQueryCosted target pos).cost =
            fixedWeightPackedReadbackWordCount bits wordSize /\
          ((data.toCompressedDirectory).rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).cost =
            fixedWeightPackedReadbackWordCount bits wordSize /\
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  dsimp
  simpa [ofChunks_word_count bits hword] using
    profile (ofChunks bits hword)

end FixedWeightPackedReadbackData

/--
Read a bounded payload-word store at a fixed list of word indices.

This is the small RAM-model kernel used by the compressed/FID auxiliary layer
below: one modeled read is charged per requested word, and the erased result is
exactly the list of words returned by the counted store.
-/
def boundedPayloadWordReadValues
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (indices : List Nat) : List (Option (List Bool)) :=
  indices.map fun i => store.store.words[i]?

@[simp] theorem boundedPayloadWordReadValues_append
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (left right : List Nat) :
    boundedPayloadWordReadValues store (left ++ right) =
      boundedPayloadWordReadValues store left ++
        boundedPayloadWordReadValues store right := by
  simp [boundedPayloadWordReadValues]

def boundedPayloadWordReadsCosted
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize) :
    List Nat -> Costed (List (Option (List Bool)))
  | [] => Costed.pure []
  | i :: rest =>
      Costed.bind (store.store.readWordCosted i) fun word? =>
        Costed.bind (boundedPayloadWordReadsCosted store rest) fun words =>
          Costed.pure (word? :: words)

@[simp] theorem boundedPayloadWordReadsCosted_cost
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (indices : List Nat) :
    (boundedPayloadWordReadsCosted store indices).cost = indices.length := by
  induction indices with
  | nil =>
      simp [boundedPayloadWordReadsCosted]
  | cons i rest ih =>
      simp [boundedPayloadWordReadsCosted, ih, Nat.add_comm]

@[simp] theorem boundedPayloadWordReadsCosted_erase
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (indices : List Nat) :
    (boundedPayloadWordReadsCosted store indices).erase =
      boundedPayloadWordReadValues store indices := by
  induction indices with
  | nil =>
      simp [boundedPayloadWordReadsCosted, boundedPayloadWordReadValues]
  | cons i rest ih =>
      simp [boundedPayloadWordReadsCosted, boundedPayloadWordReadValues, ih]

@[simp] theorem boundedPayloadWordReadsCosted_value
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (indices : List Nat) :
    (boundedPayloadWordReadsCosted store indices).value =
      boundedPayloadWordReadValues store indices := by
  simpa [Costed.erase] using
    boundedPayloadWordReadsCosted_erase store indices

/--
Read a primary bounded payload-word store, then choose the auxiliary read
schedule from the charged primary read values.

This is the generic RAM-model kernel needed by RRR-style local blocks: the
second table address can depend on the packed class/code read without becoming
a proof-only oracle.
-/
def dependentPayloadWordReadsCosted
    {primaryPayload auxPayload : List Bool} {wordSize : Nat}
    (primaryStore :
      SuccinctSpace.BoundedPayloadWordStore primaryPayload wordSize)
    (auxStore :
      SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize)
    (primaryReads : List Nat)
    (auxReads : List (Option (List Bool)) -> List Nat) :
    Costed (List (Option (List Bool)) × List (Option (List Bool))) :=
  Costed.bind (boundedPayloadWordReadsCosted primaryStore primaryReads)
    fun primaryWords =>
      Costed.bind
          (boundedPayloadWordReadsCosted auxStore (auxReads primaryWords))
        fun auxWords =>
          Costed.pure (primaryWords, auxWords)

@[simp] theorem dependentPayloadWordReadsCosted_cost
    {primaryPayload auxPayload : List Bool} {wordSize : Nat}
    (primaryStore :
      SuccinctSpace.BoundedPayloadWordStore primaryPayload wordSize)
    (auxStore :
      SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize)
    (primaryReads : List Nat)
    (auxReads : List (Option (List Bool)) -> List Nat) :
    (dependentPayloadWordReadsCosted primaryStore auxStore primaryReads
        auxReads).cost =
      primaryReads.length +
        (auxReads
          (boundedPayloadWordReadValues primaryStore primaryReads)).length := by
  simp [dependentPayloadWordReadsCosted]

@[simp] theorem dependentPayloadWordReadsCosted_erase
    {primaryPayload auxPayload : List Bool} {wordSize : Nat}
    (primaryStore :
      SuccinctSpace.BoundedPayloadWordStore primaryPayload wordSize)
    (auxStore :
      SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize)
    (primaryReads : List Nat)
    (auxReads : List (Option (List Bool)) -> List Nat) :
    (dependentPayloadWordReadsCosted primaryStore auxStore primaryReads
        auxReads).erase =
      (boundedPayloadWordReadValues primaryStore primaryReads,
        boundedPayloadWordReadValues auxStore
          (auxReads
            (boundedPayloadWordReadValues primaryStore primaryReads))) := by
  simp [dependentPayloadWordReadsCosted]

@[simp] theorem dependentPayloadWordReadsCosted_value
    {primaryPayload auxPayload : List Bool} {wordSize : Nat}
    (primaryStore :
      SuccinctSpace.BoundedPayloadWordStore primaryPayload wordSize)
    (auxStore :
      SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize)
    (primaryReads : List Nat)
    (auxReads : List (Option (List Bool)) -> List Nat) :
    (dependentPayloadWordReadsCosted primaryStore auxStore primaryReads
        auxReads).value =
      (boundedPayloadWordReadValues primaryStore primaryReads,
        boundedPayloadWordReadValues auxStore
          (auxReads
            (boundedPayloadWordReadValues primaryStore primaryReads))) := by
  simpa [Costed.erase] using
    dependentPayloadWordReadsCosted_erase primaryStore auxStore primaryReads
      auxReads


end RankSelectSpec

end RMQ
