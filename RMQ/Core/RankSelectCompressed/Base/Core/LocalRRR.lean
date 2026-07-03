import RMQ.Core.RankSelectCompressed.Base.Core.TableBacked

namespace RMQ

namespace RankSelectSpec

/-- Payload of the universal fixed-weight decoded-word table. -/
def fixedWeightDecodedWordTablePayload (n k : Nat) : List Bool :=
  SuccinctSpace.flattenPayloadWords (fixedWeightBitstrings n k)

/-- Bit cost of the universal fixed-weight decoded-word table. -/
def fixedWeightDecodedWordTableOverhead (n k : Nat) : Nat :=
  binomialCount n k * n

@[simp] theorem fixedWeightDecodedWordTablePayload_length
    (n k : Nat) :
    (fixedWeightDecodedWordTablePayload n k).length =
      fixedWeightDecodedWordTableOverhead n k := by
  unfold fixedWeightDecodedWordTablePayload
  unfold fixedWeightDecodedWordTableOverhead
  calc
    (SuccinctSpace.flattenPayloadWords (fixedWeightBitstrings n k)).length =
        (fixedWeightBitstrings n k).length * n := by
      exact SuccinctSpace.flattenPayloadWords_length_of_forall_length
        (by
          intro word hmem
          exact (fixedWeightBitstrings_mem_length_trueCount hmem).1)
    _ = binomialCount n k * n := by
      rw [fixedWeightBitstrings_length]

/-- Canonical payload store for the universal fixed-weight decoded-word table. -/
def fixedWeightDecodedWordStore (n k : Nat) :
    SuccinctSpace.PayloadWordStore
      (fixedWeightDecodedWordTablePayload n k) where
  words := (fixedWeightBitstrings n k).toArray
  erases := by
    simp [fixedWeightDecodedWordTablePayload]

/--
Canonical bounded payload store for the universal fixed-weight decoded-word
table.
-/
def fixedWeightDecodedWordBoundedStore
    (n k wordSize : Nat) (hn : n <= wordSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightDecodedWordTablePayload n k) wordSize where
  store := fixedWeightDecodedWordStore n k
  word_length_le := by
    intro word hmem
    have hlist : List.Mem word (fixedWeightBitstrings n k) := by
      simpa [fixedWeightDecodedWordStore] using hmem
    have hlen := (fixedWeightBitstrings_mem_length_trueCount hlist).1
    omega

theorem fixedWeightDecodedWordBoundedStore_get?_of_decode
    {n k code : Nat} {word : List Bool} {wordSize : Nat}
    (hn : n <= wordSize)
    (hdec : fixedWeightDecode? n k code = some word) :
    (fixedWeightDecodedWordBoundedStore n k wordSize hn).store.words[code]? =
      some word := by
  simpa [fixedWeightDecodedWordBoundedStore, fixedWeightDecodedWordStore,
    fixedWeightDecode?] using hdec

theorem fixedWeightDecodedWordBoundedStore_get?_fixedWeightCode
    (bits : List Bool) {wordSize : Nat}
    (hn : bits.length <= wordSize) :
    (fixedWeightDecodedWordBoundedStore
        bits.length (trueCount bits) wordSize hn).store.words[fixedWeightCode bits]? =
      some bits := by
  have hdec :
      fixedWeightDecode? bits.length (trueCount bits)
          (fixedWeightCode bits) = some bits := by
    simpa [fixedWeightPackedPayload_bitsToNatLE] using
      fixedWeightDecode?_packedPayload bits
  exact
    fixedWeightDecodedWordBoundedStore_get?_of_decode hn hdec

/-- Canonical one-word store for the packed fixed-weight code. -/
def fixedWeightPackedCodeBoundedStore
    (bits : List Bool) (wordSize : Nat)
    (hcode : fixedWeightPayloadBudget bits <= wordSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightPackedPayload bits) wordSize where
  store :=
    { words := #[fixedWeightPackedPayload bits]
      erases := by
        simp [SuccinctSpace.flattenPayloadWords] }
  word_length_le := by
    intro word hmem
    have hword : word = fixedWeightPackedPayload bits := by
      change List.Mem word (#[fixedWeightPackedPayload bits].toList) at hmem
      cases hmem with
      | head => rfl
      | tail _ htail => cases htail
    rw [hword, fixedWeightPackedPayload_length]
    exact hcode

theorem fixedWeightPackedCodeBoundedStore_get?_zero
    (bits : List Bool) {wordSize : Nat}
    (hcode : fixedWeightPayloadBudget bits <= wordSize) :
    (fixedWeightPackedCodeBoundedStore bits wordSize hcode).store.words[0]? =
      some (fixedWeightPackedPayload bits) := by
  simp [fixedWeightPackedCodeBoundedStore]

/-- Decode the first charged packed-code word as a fixed-weight code. -/
def fixedWeightCodeFromReadValues :
    List (Option (List Bool)) -> Nat
  | some word :: _ => SuccinctSpace.bitsToNatLE word
  | _ => 0

@[simp] theorem fixedWeightCodeFromReadValues_singleton
    (bits : List Bool) :
    fixedWeightCodeFromReadValues [some (fixedWeightPackedPayload bits)] =
      fixedWeightCode bits := by
  simp [fixedWeightCodeFromReadValues, fixedWeightPackedPayload_bitsToNatLE]

/-- Decode one fixed-width class/length metadata word. -/
def fixedWeightClassLengthNatFromReadValue : Option (List Bool) -> Nat
  | some word => SuccinctSpace.bitsToNatLE word
  | none => 0

/--
Decode local block length and class from two charged metadata words.

The first word is the block length, and the second word is the block class
(`trueCount`). Missing reads conservatively decode to zero.
-/
def fixedWeightClassLengthFromReadValues
    (readWords : List (Option (List Bool))) : Nat × Nat :=
  match readWords with
  | length? :: class? :: _ =>
      (fixedWeightClassLengthNatFromReadValue length?,
        fixedWeightClassLengthNatFromReadValue class?)
  | _ => (0, 0)

@[simp] theorem fixedWeightClassLengthNatFromReadValue_encoded
    {fieldWidth value : Nat} (hvalue : value < 2 ^ fieldWidth) :
    fixedWeightClassLengthNatFromReadValue
        (some (SuccinctSpace.natToBitsLE fieldWidth value)) =
      value := by
  simp [fixedWeightClassLengthNatFromReadValue,
    SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt hvalue]

theorem fixedWeightClassLengthFromReadValues_encoded
    {fieldWidth : Nat} {block : List Bool}
    (hlen : block.length < 2 ^ fieldWidth)
    (hclass : trueCount block < 2 ^ fieldWidth) :
    fixedWeightClassLengthFromReadValues
        [some (SuccinctSpace.natToBitsLE fieldWidth block.length),
         some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block))] =
      (block.length, trueCount block) := by
  simp [fixedWeightClassLengthFromReadValues,
    fixedWeightClassLengthNatFromReadValue_encoded hlen,
    fixedWeightClassLengthNatFromReadValue_encoded hclass]

@[simp] theorem fixedWeightClassLengthFromReadValues_encoded_prefix
    {fieldWidth : Nat} {block : List Bool}
    (rest : List (Option (List Bool)))
    (hlen : block.length < 2 ^ fieldWidth)
    (hclass : trueCount block < 2 ^ fieldWidth) :
    fixedWeightClassLengthFromReadValues
        (some (SuccinctSpace.natToBitsLE fieldWidth block.length) ::
          some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block)) ::
          rest) =
      (block.length, trueCount block) := by
  simp [fixedWeightClassLengthFromReadValues,
    fixedWeightClassLengthNatFromReadValue_encoded hlen,
    fixedWeightClassLengthNatFromReadValue_encoded hclass]

/-- Decode a fixed-weight code after length and class have been read. -/
def fixedWeightDecodedWordFromClassLengthCode
    (n k code : Nat) : List Bool :=
  (fixedWeightDecode? n k code).getD []

@[simp] theorem fixedWeightDecodedWordFromClassLengthCode_fixedWeightCode
    (bits : List Bool) :
    fixedWeightDecodedWordFromClassLengthCode
        bits.length (trueCount bits) (fixedWeightCode bits) =
      bits := by
  have hdec :
      fixedWeightDecode? bits.length (trueCount bits)
          (fixedWeightCode bits) = some bits := by
    exact
      fixedWeightDecode?_fixedWeightEncode?
        (fixedWeightEncode?_eq_some_fixedWeightCode bits)
  simp [fixedWeightDecodedWordFromClassLengthCode, hdec]

/--
Decode a local fixed-weight block from charged class/length words and a charged
packed-code word.
-/
def fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
    (classLengthWords packedWords : List (Option (List Bool))) :
    Costed (List Bool) :=
  let classLength := fixedWeightClassLengthFromReadValues classLengthWords
  Costed.tickValue (binomialCount classLength.1 classLength.2 + classLength.1)
    (fixedWeightDecodedWordFromClassLengthCode
      classLength.1 classLength.2
      (fixedWeightCodeFromReadValues packedWords))

@[simp] theorem fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted_cost
    (classLengthWords packedWords : List (Option (List Bool))) :
    (fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
        classLengthWords packedWords).cost =
      let classLength := fixedWeightClassLengthFromReadValues classLengthWords
      binomialCount classLength.1 classLength.2 + classLength.1 := by
  simp [fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted]

@[simp] theorem fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted_erase_singleton
    {fieldWidth : Nat} {block : List Bool}
    (hlen : block.length < 2 ^ fieldWidth)
    (hclass : trueCount block < 2 ^ fieldWidth) :
    (fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
        [some (SuccinctSpace.natToBitsLE fieldWidth block.length),
         some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block))]
        [some (fixedWeightPackedPayload block)]).erase =
      block := by
  simp [fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted,
    fixedWeightClassLengthFromReadValues_encoded hlen hclass]

@[simp] theorem fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted_erase_prefix
    {fieldWidth : Nat} {block : List Bool}
    (rest : List (Option (List Bool)))
    (hlen : block.length < 2 ^ fieldWidth)
    (hclass : trueCount block < 2 ^ fieldWidth) :
    (fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
        ([some (SuccinctSpace.natToBitsLE fieldWidth block.length),
          some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block))] ++
          rest)
        [some (fixedWeightPackedPayload block)]).erase =
      block := by
  simp [fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted,
    fixedWeightClassLengthFromReadValues,
    fixedWeightClassLengthNatFromReadValue_encoded hlen,
    fixedWeightClassLengthNatFromReadValue_encoded hclass]

/--
Explicit evaluator budget for computing one fixed-weight/RRR local block from
its packed code.

This is intentionally not a succinct-family budget. It records that the local
kernel is doing real finite-universe decoding work instead of reading a dense
decoded-word table or using proof-only decoded bits.
-/
def fixedWeightComputedRRRDecodeTicks (bits : List Bool) : Nat :=
  binomialCount bits.length (trueCount bits) + bits.length

@[simp] theorem fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted_cost_prefix
    {fieldWidth : Nat} {block : List Bool}
    (rest : List (Option (List Bool)))
    (hlen : block.length < 2 ^ fieldWidth)
    (hclass : trueCount block < 2 ^ fieldWidth) :
    (fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
        ([some (SuccinctSpace.natToBitsLE fieldWidth block.length),
          some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block))] ++
          rest)
        [some (fixedWeightPackedPayload block)]).cost =
      fixedWeightComputedRRRDecodeTicks block := by
  simp [fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted,
    fixedWeightComputedRRRDecodeTicks,
    fixedWeightClassLengthFromReadValues,
    fixedWeightClassLengthNatFromReadValue_encoded hlen,
    fixedWeightClassLengthNatFromReadValue_encoded hclass]

/-- Uniform query cap for the computed local RRR block kernel. -/
def fixedWeightComputedRRRQueryCost (bits : List Bool) : Nat :=
  fixedWeightComputedRRRDecodeTicks bits + 2

/-- Query cap for the local RRR kernel that reads class/length metadata. -/
def fixedWeightComputedRRRClassLengthQueryCost
    (bits : List Bool) : Nat :=
  fixedWeightComputedRRRDecodeTicks bits + 4

/--
Uniform query cap for all computed-RRR blocks whose source length is at most
`blockSize`.
-/
def fixedWeightComputedRRRBlockSizeQueryCost (blockSize : Nat) : Nat :=
  2 ^ blockSize + blockSize + 2

/-- Block-size cap for the class/length local RRR kernel. -/
def fixedWeightComputedRRRClassLengthBlockSizeQueryCost
    (blockSize : Nat) : Nat :=
  2 ^ blockSize + blockSize + 4

theorem fixedWeightComputedRRRDecodeTicks_le_of_length_le
    {bits : List Bool} {blockSize : Nat}
    (hlen : bits.length <= blockSize) :
    fixedWeightComputedRRRDecodeTicks bits <=
      2 ^ blockSize + blockSize := by
  unfold fixedWeightComputedRRRDecodeTicks
  have hbin :
      binomialCount bits.length (trueCount bits) <=
        2 ^ bits.length :=
    binomialCount_le_two_pow bits.length (trueCount bits)
  have hpow :
      2 ^ bits.length <= 2 ^ blockSize :=
    Nat.pow_le_pow_right (by omega : 0 < 2) hlen
  omega

theorem fixedWeightComputedRRRQueryCost_le_blockSize
    {bits : List Bool} {blockSize : Nat}
    (hlen : bits.length <= blockSize) :
    fixedWeightComputedRRRQueryCost bits <=
      fixedWeightComputedRRRBlockSizeQueryCost blockSize := by
  unfold fixedWeightComputedRRRQueryCost
    fixedWeightComputedRRRBlockSizeQueryCost
  have hticks :=
    fixedWeightComputedRRRDecodeTicks_le_of_length_le
      (bits := bits) hlen
  omega

theorem fixedWeightComputedRRRQueryCost_le_of_block_length_le
    {block : List Bool} {blockSize localQueryCost : Nat}
    (hblock : block.length <= blockSize)
    (hquery :
      fixedWeightComputedRRRBlockSizeQueryCost blockSize <=
        localQueryCost) :
    fixedWeightComputedRRRQueryCost block <= localQueryCost := by
  exact Nat.le_trans
    (fixedWeightComputedRRRQueryCost_le_blockSize
      (bits := block) hblock)
    hquery

theorem fixedWeightComputedRRRClassLengthQueryCost_le_blockSize
    {bits : List Bool} {blockSize : Nat}
    (hlen : bits.length <= blockSize) :
    fixedWeightComputedRRRClassLengthQueryCost bits <=
      fixedWeightComputedRRRClassLengthBlockSizeQueryCost blockSize := by
  unfold fixedWeightComputedRRRClassLengthQueryCost
    fixedWeightComputedRRRClassLengthBlockSizeQueryCost
  have hticks :=
    fixedWeightComputedRRRDecodeTicks_le_of_length_le
      (bits := bits) hlen
  omega

theorem fixedWeightComputedRRRClassLengthQueryCost_le_of_block_length_le
    {block : List Bool} {blockSize localQueryCost : Nat}
    (hblock : block.length <= blockSize)
    (hquery :
      fixedWeightComputedRRRClassLengthBlockSizeQueryCost blockSize <=
        localQueryCost) :
    fixedWeightComputedRRRClassLengthQueryCost block <= localQueryCost := by
  exact Nat.le_trans
    (fixedWeightComputedRRRClassLengthQueryCost_le_blockSize
      (bits := block) hblock)
    hquery

theorem fixedWeightComputedRRRLocalQueryCost_le_of_blocks_bound
    {blocks : List (List Bool)} {blockSize localQueryCost : Nat}
    (hblocks :
      forall {block : List Bool}, List.Mem block blocks ->
        block.length <= blockSize)
    (hquery :
      fixedWeightComputedRRRBlockSizeQueryCost blockSize <=
        localQueryCost) :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <= localQueryCost := by
  intro block hmem
  exact
    fixedWeightComputedRRRQueryCost_le_of_block_length_le
      (hblocks hmem) hquery

theorem fixedWeightComputedRRRClassLengthLocalQueryCost_le_of_blocks_bound
    {blocks : List (List Bool)} {blockSize localQueryCost : Nat}
    (hblocks :
      forall {block : List Bool}, List.Mem block blocks ->
        block.length <= blockSize)
    (hquery :
      fixedWeightComputedRRRClassLengthBlockSizeQueryCost blockSize <=
        localQueryCost) :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRClassLengthQueryCost block <= localQueryCost := by
  intro block hmem
  exact
    fixedWeightComputedRRRClassLengthQueryCost_le_of_block_length_le
      (hblocks hmem) hquery

/-- Decode a fixed-weight code for the block class determined by `bits`. -/
def fixedWeightDecodedWordFromCode (bits : List Bool) (code : Nat) :
    List Bool :=
  (fixedWeightDecode? bits.length (trueCount bits) code).getD []

@[simp] theorem fixedWeightDecodedWordFromCode_fixedWeightCode
    (bits : List Bool) :
    fixedWeightDecodedWordFromCode bits (fixedWeightCode bits) = bits := by
  have hdec :
      fixedWeightDecode? bits.length (trueCount bits)
          (fixedWeightCode bits) = some bits := by
    exact
      fixedWeightDecode?_fixedWeightEncode?
        (fixedWeightEncode?_eq_some_fixedWeightCode bits)
  simp [fixedWeightDecodedWordFromCode, hdec]

/--
Fixed computation over charged packed-code read values.

The only input is the word value returned by the counted packed payload read;
there is no auxiliary decoded-word table and no proof-only access to the block.
-/
def fixedWeightComputedRRRDecodeFromReadValuesCosted
    (bits : List Bool) (packedWords : List (Option (List Bool))) :
    Costed (List Bool) :=
  Costed.tickValue (fixedWeightComputedRRRDecodeTicks bits)
    (fixedWeightDecodedWordFromCode bits
      (fixedWeightCodeFromReadValues packedWords))

@[simp] theorem fixedWeightComputedRRRDecodeFromReadValuesCosted_cost
    (bits : List Bool) (packedWords : List (Option (List Bool))) :
    (fixedWeightComputedRRRDecodeFromReadValuesCosted bits
        packedWords).cost =
      fixedWeightComputedRRRDecodeTicks bits := by
  simp [fixedWeightComputedRRRDecodeFromReadValuesCosted]

@[simp] theorem fixedWeightComputedRRRDecodeFromReadValuesCosted_erase_singleton
    (bits : List Bool) :
    (fixedWeightComputedRRRDecodeFromReadValuesCosted bits
        [some (fixedWeightPackedPayload bits)]).erase =
      bits := by
  simp [fixedWeightComputedRRRDecodeFromReadValuesCosted]

/--
Local fixed-weight/RRR block kernel computed from the packed code only.

The counted payload is just `fixedWeightPackedPayload bits`. Queries read that
code word, spend the explicit `fixedWeightComputedRRRDecodeTicks bits`
evaluator budget to reconstruct the local block, and then use fixed code for
access/rank/select. This avoids the dense
`fixedWeightDecodedWordTablePayload` auxiliary table used by
`FixedWeightTableRAMBlockData`.
-/
structure FixedWeightComputedRRRBlockData
    (ambientLength : Nat) (bits : List Bool) (wordSize : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_ambient : wordSize <= Nat.log2 ambientLength + 1
  codeWidth_le_wordSize : fixedWeightPayloadBudget bits <= wordSize
  blockWidth_le_wordSize : bits.length <= wordSize

namespace FixedWeightComputedRRRBlockData

def packedStore
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightPackedPayload bits) wordSize :=
  fixedWeightPackedCodeBoundedStore bits wordSize
    data.codeWidth_le_wordSize

def payload
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (_data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    List Bool :=
  fixedWeightPackedPayload bits

@[simp] theorem payload_length
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.payload.length = fixedWeightPayloadBudget bits := by
  simp [payload, fixedWeightPackedPayload_length]

theorem packed_read_values_zero
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    boundedPayloadWordReadValues data.packedStore [0] =
      [some (fixedWeightPackedPayload bits)] := by
  have hpacked :
      data.packedStore.store.words[0]? =
        some (fixedWeightPackedPayload bits) := by
    simpa [packedStore] using
      fixedWeightPackedCodeBoundedStore_get?_zero bits
        data.codeWidth_le_wordSize
  simp [boundedPayloadWordReadValues, hpacked]

def readCodeCosted
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    Costed Nat :=
  Costed.bind (data.packedStore.store.readWordCosted 0) fun word? =>
    Costed.pure
      (match word? with
      | some word => SuccinctSpace.bitsToNatLE word
      | none => 0)

@[simp] theorem readCodeCosted_cost
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.readCodeCosted.cost = 1 := by
  simp [readCodeCosted]

@[simp] theorem readCodeCosted_erase
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.readCodeCosted.erase = fixedWeightCode bits := by
  simp [readCodeCosted, packedStore, fixedWeightPackedCodeBoundedStore,
    fixedWeightPackedPayload_bitsToNatLE]

def decodedWordCosted
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    Costed (List Bool) :=
  Costed.bind data.readCodeCosted fun code =>
    Costed.tickValue (fixedWeightComputedRRRDecodeTicks bits)
      (fixedWeightDecodedWordFromCode bits code)

@[simp] theorem decodedWordCosted_cost
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.decodedWordCosted.cost =
      fixedWeightComputedRRRDecodeTicks bits + 1 := by
  simp [decodedWordCosted, Nat.add_comm]

@[simp] theorem decodedWordCosted_erase
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.decodedWordCosted.erase = bits := by
  simp [decodedWordCosted]

def accessCosted
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (i : Nat) : Costed (Option Bool) :=
  Costed.map (fun word => word[i]?) data.decodedWordCosted

@[simp] theorem accessCosted_cost
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (i : Nat) :
    (data.accessCosted i).cost =
      fixedWeightComputedRRRDecodeTicks bits + 1 := by
  simp [accessCosted]

@[simp] theorem accessCosted_erase
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (i : Nat) :
    (data.accessCosted i).erase = bits[i]? := by
  simp [accessCosted]

def rankCosted
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind data.decodedWordCosted fun word =>
    (RAM.rankBoolWordPrefix target word pos).toCosted

@[simp] theorem rankCosted_cost
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost =
      fixedWeightComputedRRRQueryCost bits := by
  simp [rankCosted, fixedWeightComputedRRRQueryCost]

@[simp] theorem rankCosted_erase
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
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
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind data.decodedWordCosted fun word =>
    (RAM.selectBoolWord target word occurrence).toCosted

@[simp] theorem selectCosted_cost
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost =
      fixedWeightComputedRRRQueryCost bits := by
  simp [selectCosted, fixedWeightComputedRRRQueryCost]

@[simp] theorem selectCosted_erase
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
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
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    FixedWeightDependentAuxiliaryData
      bits 0 wordSize (fixedWeightComputedRRRQueryCost bits) := by
  refine
    { wordSize_pos := data.wordSize_pos
      packedStore := data.packedStore
      auxPayload := []
      auxStore :=
        SuccinctSpace.BoundedPayloadWordStore.ofChunks []
          data.wordSize_pos
      aux_length_eq := ?_
      accessPackedReads := fun _ => [0]
      accessAuxReads := fun _ _ => []
      rankPackedReads := fun _ _ => [0]
      rankAuxReads := fun _ _ _ => []
      selectPackedReads := fun _ _ => [0]
      selectAuxReads := fun _ _ _ => []
      accessEvalCosted := fun i packedWords _ =>
        Costed.map (fun word => word[i]?)
          (fixedWeightComputedRRRDecodeFromReadValuesCosted bits
            packedWords)
      rankEvalCosted := fun target pos packedWords _ =>
        Costed.bind
          (fixedWeightComputedRRRDecodeFromReadValuesCosted bits
            packedWords) fun word =>
          (RAM.rankBoolWordPrefix target word pos).toCosted
      selectEvalCosted := fun target occurrence packedWords _ =>
        Costed.bind
          (fixedWeightComputedRRRDecodeFromReadValuesCosted bits
            packedWords) fun word =>
          (RAM.selectBoolWord target word occurrence).toCosted
      access_query_cost_le := ?_
      rank_query_cost_le := ?_
      select_query_cost_le := ?_
      access_eval_exact := ?_
      rank_eval_exact := ?_
      select_eval_exact := ?_ }
  · simp
  · intro i
    simp [data.packed_read_values_zero, fixedWeightComputedRRRQueryCost]
    omega
  · intro target pos
    simp [data.packed_read_values_zero, fixedWeightComputedRRRQueryCost]
    omega
  · intro target occurrence
    simp [data.packed_read_values_zero, fixedWeightComputedRRRQueryCost]
    omega
  · intro i
    simp [data.packed_read_values_zero]
  · intro target pos
    have hdecode :=
      fixedWeightComputedRRRDecodeFromReadValuesCosted_erase_singleton bits
    have hrun := Succinct.rankBoolWordPrefix_toCosted_run target bits pos
    simp only [data.packed_read_values_zero, Costed.erase_bind]
    rw [hdecode]
    change (RAM.rankBoolWordPrefix target bits pos).toCosted.value =
      Succinct.rankPrefix target bits pos
    simpa [Costed.run] using congrArg Prod.fst hrun
  · intro target occurrence
    have hdecode :=
      fixedWeightComputedRRRDecodeFromReadValuesCosted_erase_singleton bits
    have hrun := Succinct.selectBoolWord_toCosted_run
      target bits occurrence
    simp only [data.packed_read_values_zero, Costed.erase_bind]
    rw [hdecode]
    change (RAM.selectBoolWord target bits occurrence).toCosted.value =
      Succinct.select target bits occurrence
    simpa [Costed.run] using congrArg Prod.fst hrun

def toCompressedDirectory
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    CompressedBitVectorRankSelectDirectory
      bits 0 (fixedWeightComputedRRRQueryCost bits) where
  payload := data.payload
  payload_length_le := by
    simp
  accessCosted := data.accessCosted
  rankCosted := data.rankCosted
  selectCosted := data.selectCosted
  access_cost_le := by
    intro i
    rw [data.accessCosted_cost i]
    unfold fixedWeightComputedRRRQueryCost
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

def toBoundedCompressedDirectory
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    {queryCost : Nat}
    (hquery : fixedWeightComputedRRRQueryCost bits <= queryCost) :
    CompressedBitVectorRankSelectDirectory bits 0 queryCost where
  payload := data.payload
  payload_length_le := by
    simp
  accessCosted := data.accessCosted
  rankCosted := data.rankCosted
  selectCosted := data.selectCosted
  access_cost_le := by
    intro i
    rw [data.accessCosted_cost i]
    unfold fixedWeightComputedRRRQueryCost at hquery
    omega
  rank_cost_le := by
    intro target pos
    rw [data.rankCosted_cost target pos]
    exact hquery
  select_cost_le := by
    intro target occurrence
    rw [data.selectCosted_cost target occurrence]
    exact hquery
  access_exact := data.accessCosted_erase
  rank_exact := data.rankCosted_erase
  select_exact := data.selectCosted_erase

/--
Profile for the computed local fixed-weight/RRR block kernel.

There is no decoded auxiliary payload: all exactness comes from a charged read
of the packed fixed-weight code plus the explicit decode tick budget.
-/
def KernelProfile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    Prop :=
  (data.toCompressedDirectory).payload = fixedWeightPackedPayload bits /\
    (data.toCompressedDirectory).payload.length =
      fixedWeightPayloadBudget bits /\
    (data.toCompressedDirectory).payload.length =
      fixedWeightPayloadBudget bits + 0 /\
    SuccinctSpace.flattenPayloadWords
        data.packedStore.store.words.toList =
      fixedWeightPackedPayload bits /\
    data.packedStore.store.words[0]? =
      some (fixedWeightPackedPayload bits) /\
    fixedWeightPayloadBudget bits <= wordSize /\
    bits.length <= wordSize /\
    wordSize <= Nat.log2 ambientLength + 1 /\
    data.readCodeCosted.cost = 1 /\
    data.readCodeCosted.erase = fixedWeightCode bits /\
    data.decodedWordCosted.cost =
      fixedWeightComputedRRRDecodeTicks bits + 1 /\
    data.decodedWordCosted.erase = bits /\
    (forall {word : List Bool},
      List.Mem word data.packedStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall i,
      ((data.toCompressedDirectory).accessQueryCosted i).cost <=
          fixedWeightComputedRRRQueryCost bits /\
        ((data.toCompressedDirectory).accessQueryCosted i).erase =
          bits[i]?) /\
    (forall target pos,
      ((data.toCompressedDirectory).rankQueryCosted target pos).cost =
          fixedWeightComputedRRRQueryCost bits /\
        ((data.toCompressedDirectory).rankQueryCosted target pos).erase =
          Succinct.rankPrefix target bits pos) /\
    (forall target occurrence,
        ((data.toCompressedDirectory).selectQueryCosted
          target occurrence).cost =
          fixedWeightComputedRRRQueryCost bits /\
        ((data.toCompressedDirectory).selectQueryCosted
          target occurrence).erase =
          Succinct.select target bits occurrence)

/--
The computed local fixed-weight/RRR kernel is an instance of the generic
dependent-read compressed/FID scaffold with zero auxiliary payload.
-/
theorem dependent_auxiliary_data_profile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    (data.toDependentAuxiliaryData).DirectoryProfile := by
  exact
    FixedWeightDependentAuxiliaryData.directory_profile
      data.toDependentAuxiliaryData

theorem bounded_compressed_directory_profile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    {queryCost : Nat}
    (hquery : fixedWeightComputedRRRQueryCost bits <= queryCost) :
    let directory := data.toBoundedCompressedDirectory hquery
    directory.payload = fixedWeightPackedPayload bits /\
      directory.payload.length = fixedWeightPayloadBudget bits /\
      directory.payload.length <= fixedWeightPayloadBudget bits + 0 /\
      data.readCodeCosted.cost = 1 /\
      data.readCodeCosted.erase = fixedWeightCode bits /\
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
  let directory := data.toBoundedCompressedDirectory hquery
  have hprofile := directory.profile
  exact
    ⟨rfl,
      by
        change data.payload.length = fixedWeightPayloadBudget bits
        exact data.payload_length,
      hprofile.1,
      data.readCodeCosted_cost,
      data.readCodeCosted_erase,
      data.decodedWordCosted_cost,
      data.decodedWordCosted_erase,
      hquery,
      hprofile.2.1,
      hprofile.2.2.1,
      hprofile.2.2.2⟩

/--
The direct computed-RRR local directory and the generic dependent-auxiliary
adapter expose the same packed payload and charged query behavior.
-/
def DependentAuxiliaryBridgeProfile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    Prop :=
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
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.DependentAuxiliaryBridgeProfile := by
  constructor
  · change (data.toDependentAuxiliaryData).payload = data.payload
    simp [toDependentAuxiliaryData,
      FixedWeightDependentAuxiliaryData.payload, payload]
  constructor
  · intro i
    constructor
    · change ((data.toDependentAuxiliaryData).accessCosted i).cost =
        (data.accessCosted i).cost
      simp [toDependentAuxiliaryData,
        FixedWeightDependentAuxiliaryData.accessCosted,
        data.packed_read_values_zero,
        fixedWeightComputedRRRQueryCost]
      omega
    · change ((data.toDependentAuxiliaryData).accessCosted i).erase =
        (data.accessCosted i).erase
      rw [(data.toDependentAuxiliaryData).accessCosted_erase i,
        data.accessCosted_erase i]
  constructor
  · intro target pos
    constructor
    · change ((data.toDependentAuxiliaryData).rankCosted target pos).cost =
        (data.rankCosted target pos).cost
      simp [toDependentAuxiliaryData,
        FixedWeightDependentAuxiliaryData.rankCosted,
        data.packed_read_values_zero,
        fixedWeightComputedRRRQueryCost]
      omega
    · change ((data.toDependentAuxiliaryData).rankCosted target pos).erase =
        (data.rankCosted target pos).erase
      rw [(data.toDependentAuxiliaryData).rankCosted_erase target pos,
        data.rankCosted_erase target pos]
  · intro target occurrence
    constructor
    · change
        ((data.toDependentAuxiliaryData).selectCosted
          target occurrence).cost =
        (data.selectCosted target occurrence).cost
      simp [toDependentAuxiliaryData,
        FixedWeightDependentAuxiliaryData.selectCosted,
        data.packed_read_values_zero,
        fixedWeightComputedRRRQueryCost]
      omega
    · change
        ((data.toDependentAuxiliaryData).selectCosted
          target occurrence).erase =
        (data.selectCosted target occurrence).erase
      rw [(data.toDependentAuxiliaryData).selectCosted_erase
          target occurrence,
        data.selectCosted_erase target occurrence]

theorem computed_rrr_block_kernel_profile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.KernelProfile := by
  have hpacked :
      data.packedStore.store.words[0]? =
        some (fixedWeightPackedPayload bits) := by
    simpa [packedStore] using
      fixedWeightPackedCodeBoundedStore_get?_zero bits
        data.codeWidth_le_wordSize
  refine
    ⟨rfl,
      by
        change data.payload.length = fixedWeightPayloadBudget bits
        exact data.payload_length,
      by
        change data.payload.length = fixedWeightPayloadBudget bits + 0
        simp,
      data.packedStore.erases,
      hpacked,
      data.codeWidth_le_wordSize,
      data.blockWidth_le_wordSize,
      data.wordSize_le_ambient,
      data.readCodeCosted_cost,
      data.readCodeCosted_erase,
      data.decodedWordCosted_cost,
      data.decodedWordCosted_erase,
      (fun hmem => data.packedStore.word_length_le_of_mem hmem),
      ?_,
      ?_,
      ?_⟩
  · intro i
    exact
      ⟨by
        change (data.accessCosted i).cost <=
          fixedWeightComputedRRRQueryCost bits
        rw [data.accessCosted_cost i]
        unfold fixedWeightComputedRRRQueryCost
        omega,
        data.accessCosted_erase i⟩
  · intro target pos
    exact
      ⟨by
        change (data.rankCosted target pos).cost =
          fixedWeightComputedRRRQueryCost bits
        exact data.rankCosted_cost target pos,
        data.rankCosted_erase target pos⟩
  · intro target occurrence
    exact
      ⟨by
        change (data.selectCosted target occurrence).cost =
          fixedWeightComputedRRRQueryCost bits
        exact data.selectCosted_cost target occurrence,
        data.selectCosted_erase target occurrence⟩

end FixedWeightComputedRRRBlockData

/-- Two fixed-width metadata words for a local block: length, then class. -/
def fixedWeightClassLengthPayload
    (fieldWidth : Nat) (bits : List Bool) : List Bool :=
  SuccinctSpace.natToBitsLE fieldWidth bits.length ++
    SuccinctSpace.natToBitsLE fieldWidth (trueCount bits)

@[simp] theorem fixedWeightClassLengthPayload_length
    (fieldWidth : Nat) (bits : List Bool) :
    (fixedWeightClassLengthPayload fieldWidth bits).length =
      fieldWidth + fieldWidth := by
  simp [fixedWeightClassLengthPayload,
    SuccinctSpace.natToBitsLE_length]

/--
Local RRR block kernel that reads block length and class from charged
metadata words before decoding the packed fixed-weight code.
-/
structure FixedWeightComputedRRRClassLengthBlockData
    (ambientLength : Nat) (bits : List Bool)
    (wordSize fieldWidth : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_ambient : wordSize <= Nat.log2 ambientLength + 1
  fieldWidth_le_wordSize : fieldWidth <= wordSize
  codeWidth_le_wordSize : fixedWeightPayloadBudget bits <= wordSize
  blockLength_lt_fieldWidthPow : bits.length < 2 ^ fieldWidth
  blockClass_lt_fieldWidthPow : trueCount bits < 2 ^ fieldWidth

namespace FixedWeightComputedRRRClassLengthBlockData

def packedStore
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightPackedPayload bits) wordSize :=
  fixedWeightPackedCodeBoundedStore bits wordSize
    data.codeWidth_le_wordSize

def classLengthStore
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightClassLengthPayload fieldWidth bits) wordSize where
  store :=
    { words :=
        #[
          SuccinctSpace.natToBitsLE fieldWidth bits.length,
          SuccinctSpace.natToBitsLE fieldWidth (trueCount bits)]
      erases := by
        simp [fixedWeightClassLengthPayload,
          SuccinctSpace.flattenPayloadWords] }
  word_length_le := by
    intro word hmem
    change
      List.Mem word
        ([
          SuccinctSpace.natToBitsLE fieldWidth bits.length,
          SuccinctSpace.natToBitsLE fieldWidth (trueCount bits)] :
          List (List Bool)) at hmem
    cases hmem with
    | head =>
        simpa [SuccinctSpace.natToBitsLE_length] using
          data.fieldWidth_le_wordSize
    | tail _ htail =>
        cases htail with
        | head =>
            simpa [SuccinctSpace.natToBitsLE_length] using
              data.fieldWidth_le_wordSize
        | tail _ hnil =>
            cases hnil

def payload
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (_data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    List Bool :=
  fixedWeightPackedPayload bits ++
    fixedWeightClassLengthPayload fieldWidth bits

@[simp] theorem payload_length
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    data.payload.length =
      fixedWeightPayloadBudget bits + (fieldWidth + fieldWidth) := by
  simp [payload, fixedWeightPackedPayload_length]

theorem packed_read_values_zero
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    boundedPayloadWordReadValues data.packedStore [0] =
      [some (fixedWeightPackedPayload bits)] := by
  have hpacked :
      data.packedStore.store.words[0]? =
        some (fixedWeightPackedPayload bits) := by
    simpa [packedStore] using
      fixedWeightPackedCodeBoundedStore_get?_zero bits
        data.codeWidth_le_wordSize
  simp [boundedPayloadWordReadValues, hpacked]

theorem classLength_read_values
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    boundedPayloadWordReadValues data.classLengthStore [0, 1] =
      [some (SuccinctSpace.natToBitsLE fieldWidth bits.length),
       some (SuccinctSpace.natToBitsLE fieldWidth (trueCount bits))] := by
  simp [boundedPayloadWordReadValues, classLengthStore]

def decodedWordCosted
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    Costed (List Bool) :=
  Costed.bind
      (boundedPayloadWordReadsCosted data.classLengthStore [0, 1])
      fun classLengthWords =>
    Costed.bind
        (boundedPayloadWordReadsCosted data.packedStore [0])
        fun packedWords =>
      fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
        classLengthWords packedWords

@[simp] theorem decodedWordCosted_cost
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    data.decodedWordCosted.cost =
      fixedWeightComputedRRRDecodeTicks bits + 3 := by
  have hclassLength :=
    fixedWeightClassLengthFromReadValues_encoded
      data.blockLength_lt_fieldWidthPow
      data.blockClass_lt_fieldWidthPow
  simp [decodedWordCosted, data.classLength_read_values,
    data.packed_read_values_zero, fixedWeightComputedRRRDecodeTicks,
    fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted,
    hclassLength]
  omega

@[simp] theorem decodedWordCosted_erase
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    data.decodedWordCosted.erase = bits := by
  simp [decodedWordCosted, data.classLength_read_values,
    data.packed_read_values_zero,
    fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted_erase_singleton
      data.blockLength_lt_fieldWidthPow
      data.blockClass_lt_fieldWidthPow]

def accessCosted
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth)
    (i : Nat) : Costed (Option Bool) :=
  Costed.map (fun word => word[i]?) data.decodedWordCosted

@[simp] theorem accessCosted_cost
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth)
    (i : Nat) :
    (data.accessCosted i).cost =
      fixedWeightComputedRRRDecodeTicks bits + 3 := by
  simp [accessCosted]

@[simp] theorem accessCosted_erase
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth)
    (i : Nat) :
    (data.accessCosted i).erase = bits[i]? := by
  simp [accessCosted]

def rankCosted
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind data.decodedWordCosted fun word =>
    (RAM.rankBoolWordPrefix target word pos).toCosted

@[simp] theorem rankCosted_cost
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost =
      fixedWeightComputedRRRClassLengthQueryCost bits := by
  simp [rankCosted, fixedWeightComputedRRRClassLengthQueryCost,
    fixedWeightComputedRRRDecodeTicks]

@[simp] theorem rankCosted_erase
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth)
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
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind data.decodedWordCosted fun word =>
    (RAM.selectBoolWord target word occurrence).toCosted

@[simp] theorem selectCosted_cost
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost =
      fixedWeightComputedRRRClassLengthQueryCost bits := by
  simp [selectCosted, fixedWeightComputedRRRClassLengthQueryCost,
    fixedWeightComputedRRRDecodeTicks]

@[simp] theorem selectCosted_erase
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  unfold selectCosted
  simp only [Costed.erase_bind, decodedWordCosted_erase]
  change (RAM.selectBoolWord target bits occurrence).toCosted.value =
    Succinct.select target bits occurrence
  have hrun := Succinct.selectBoolWord_toCosted_run
    target bits occurrence
  simpa [Costed.run] using congrArg Prod.fst hrun

def ClassLengthKernelProfile
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    Prop :=
  data.payload.length =
      fixedWeightPayloadBudget bits + (fieldWidth + fieldWidth) /\
    SuccinctSpace.flattenPayloadWords
        data.packedStore.store.words.toList =
      fixedWeightPackedPayload bits /\
    SuccinctSpace.flattenPayloadWords
        data.classLengthStore.store.words.toList =
      fixedWeightClassLengthPayload fieldWidth bits /\
    boundedPayloadWordReadValues data.packedStore [0] =
      [some (fixedWeightPackedPayload bits)] /\
    boundedPayloadWordReadValues data.classLengthStore [0, 1] =
      [some (SuccinctSpace.natToBitsLE fieldWidth bits.length),
       some (SuccinctSpace.natToBitsLE fieldWidth (trueCount bits))] /\
    data.decodedWordCosted.cost =
      fixedWeightComputedRRRDecodeTicks bits + 3 /\
    data.decodedWordCosted.erase = bits /\
    (forall {word : List Bool},
      List.Mem word data.packedStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall {word : List Bool},
      List.Mem word data.classLengthStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall i,
      (data.accessCosted i).cost <=
          fixedWeightComputedRRRClassLengthQueryCost bits /\
        (data.accessCosted i).erase = bits[i]?) /\
    (forall target pos,
      (data.rankCosted target pos).cost =
          fixedWeightComputedRRRClassLengthQueryCost bits /\
        (data.rankCosted target pos).erase =
          Succinct.rankPrefix target bits pos) /\
    (forall target occurrence,
      (data.selectCosted target occurrence).cost =
          fixedWeightComputedRRRClassLengthQueryCost bits /\
        (data.selectCosted target occurrence).erase =
          Succinct.select target bits occurrence)

theorem class_length_kernel_profile
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    data.ClassLengthKernelProfile := by
  exact
    ⟨data.payload_length,
      data.packedStore.erases,
      data.classLengthStore.erases,
      data.packed_read_values_zero,
      data.classLength_read_values,
      data.decodedWordCosted_cost,
      data.decodedWordCosted_erase,
      (fun hmem => data.packedStore.word_length_le_of_mem hmem),
      (fun hmem => data.classLengthStore.word_length_le_of_mem hmem),
      (fun i =>
        ⟨by
          rw [data.accessCosted_cost i]
          unfold fixedWeightComputedRRRClassLengthQueryCost
          omega,
          data.accessCosted_erase i⟩),
      (fun target pos =>
        ⟨data.rankCosted_cost target pos,
          data.rankCosted_erase target pos⟩),
      (fun target occurrence =>
        ⟨data.selectCosted_cost target occurrence,
          data.selectCosted_erase target occurrence⟩)⟩

def toDependentAuxiliaryData
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    FixedWeightDependentAuxiliaryData
      bits (fieldWidth + fieldWidth) wordSize
      (fixedWeightComputedRRRClassLengthQueryCost bits) := by
  refine
    { wordSize_pos := data.wordSize_pos
      packedStore := data.packedStore
      auxPayload := fixedWeightClassLengthPayload fieldWidth bits
      auxStore := data.classLengthStore
      aux_length_eq := by
        simp [fixedWeightClassLengthPayload_length]
      accessPackedReads := fun _ => [0]
      accessAuxReads := fun _ _ => [0, 1]
      rankPackedReads := fun _ _ => [0]
      rankAuxReads := fun _ _ _ => [0, 1]
      selectPackedReads := fun _ _ => [0]
      selectAuxReads := fun _ _ _ => [0, 1]
      accessEvalCosted := fun i packedWords auxWords =>
        Costed.map (fun word => word[i]?)
          (fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
            auxWords packedWords)
      rankEvalCosted := fun target pos packedWords auxWords =>
        Costed.bind
          (fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
            auxWords packedWords) fun word =>
          (RAM.rankBoolWordPrefix target word pos).toCosted
      selectEvalCosted := fun target occurrence packedWords auxWords =>
        Costed.bind
          (fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
            auxWords packedWords) fun word =>
          (RAM.selectBoolWord target word occurrence).toCosted
      access_query_cost_le := ?_
      rank_query_cost_le := ?_
      select_query_cost_le := ?_
      access_eval_exact := ?_
      rank_eval_exact := ?_
      select_eval_exact := ?_ }
  · intro i
    have hclassLength :=
      fixedWeightClassLengthFromReadValues_encoded
        data.blockLength_lt_fieldWidthPow
        data.blockClass_lt_fieldWidthPow
    simp [data.packed_read_values_zero, data.classLength_read_values,
      fixedWeightComputedRRRClassLengthQueryCost,
      fixedWeightComputedRRRDecodeTicks, hclassLength]
    omega
  · intro target pos
    have hclassLength :=
      fixedWeightClassLengthFromReadValues_encoded
        data.blockLength_lt_fieldWidthPow
        data.blockClass_lt_fieldWidthPow
    simp [data.packed_read_values_zero, data.classLength_read_values,
      fixedWeightComputedRRRClassLengthQueryCost,
      fixedWeightComputedRRRDecodeTicks, hclassLength]
    omega
  · intro target occurrence
    have hclassLength :=
      fixedWeightClassLengthFromReadValues_encoded
        data.blockLength_lt_fieldWidthPow
        data.blockClass_lt_fieldWidthPow
    simp [data.packed_read_values_zero, data.classLength_read_values,
      fixedWeightComputedRRRClassLengthQueryCost,
      fixedWeightComputedRRRDecodeTicks, hclassLength]
    omega
  · intro i
    simp [data.packed_read_values_zero, data.classLength_read_values,
      fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted_erase_singleton
        data.blockLength_lt_fieldWidthPow
        data.blockClass_lt_fieldWidthPow]
  · intro target pos
    have hdecode :=
      fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted_erase_singleton
        (fieldWidth := fieldWidth)
        data.blockLength_lt_fieldWidthPow
        data.blockClass_lt_fieldWidthPow
    have hrun := Succinct.rankBoolWordPrefix_toCosted_run target bits pos
    simp only [data.packed_read_values_zero, data.classLength_read_values,
      Costed.erase_bind]
    rw [hdecode]
    change (RAM.rankBoolWordPrefix target bits pos).toCosted.value =
      Succinct.rankPrefix target bits pos
    simpa [Costed.run] using congrArg Prod.fst hrun
  · intro target occurrence
    have hdecode :=
      fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted_erase_singleton
        (fieldWidth := fieldWidth)
        data.blockLength_lt_fieldWidthPow
        data.blockClass_lt_fieldWidthPow
    have hrun := Succinct.selectBoolWord_toCosted_run
      target bits occurrence
    simp only [data.packed_read_values_zero, data.classLength_read_values,
      Costed.erase_bind]
    rw [hdecode]
    change (RAM.selectBoolWord target bits occurrence).toCosted.value =
      Succinct.select target bits occurrence
    simpa [Costed.run] using congrArg Prod.fst hrun

theorem dependent_auxiliary_data_profile
    {ambientLength : Nat} {bits : List Bool}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightComputedRRRClassLengthBlockData
        ambientLength bits wordSize fieldWidth) :
    (data.toDependentAuxiliaryData).DirectoryProfile := by
  exact
    FixedWeightDependentAuxiliaryData.directory_profile
      data.toDependentAuxiliaryData

end FixedWeightComputedRRRClassLengthBlockData

end RankSelectSpec

end RMQ
