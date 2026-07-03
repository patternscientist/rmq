import RMQ.Core.RankSelectCompressed.Base.Core.Auxiliary

namespace RMQ

namespace RankSelectSpec

/-- Decode an optional one-bit table entry as bitvector access. -/
def tableBackedAccessAnswer : Option (Option Nat) -> Option Bool
  | some (some 0) => some false
  | some (some (_ + 1)) => some true
  | _ => none

/-- Decode a rank table miss as the default zero answer. -/
def tableBackedRankAnswer : Option Nat -> Nat
  | some rank => rank
  | none => 0

/-- Decode an optional select table read. -/
def tableBackedSelectAnswer : Option (Option Nat) -> Option Nat
  | some answer => answer
  | none => none

/--
Pointwise table-backed fixed-weight FID data.

Unlike `FixedWeightCompressedAuxiliaryData`, the query procedures here are not
abstract evaluator fields. Access, rank, and select are fixed-width table reads
from counted auxiliary payload, followed by small decoders. This is a concrete
payload-live query layer; its auxiliary tables may still be too large for an
`o(n)` family until a real RRR/FID table construction replaces the dense
entries.
-/
structure FixedWeightTableBackedFIDData
    (bits : List Bool) (overhead wordSize queryCost : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_machine : wordSize <= Nat.log2 bits.length + 1
  packedStore :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightPackedPayload bits) wordSize
  accessWidth : Nat
  accessEntries : List (Option Nat)
  accessTable :
    SuccinctSpace.FixedWidthOptionNatTable accessEntries accessWidth
  rankWidth : Nat
  trueRankEntries : List Nat
  falseRankEntries : List Nat
  rankTables :
    SuccinctSpace.FixedWidthRankSampleTables
      trueRankEntries falseRankEntries rankWidth
  selectWidth : Nat
  trueSelectEntries : List (Option Nat)
  falseSelectEntries : List (Option Nat)
  trueSelectTable :
    SuccinctSpace.FixedWidthOptionNatTable trueSelectEntries selectWidth
  falseSelectTable :
    SuccinctSpace.FixedWidthOptionNatTable falseSelectEntries selectWidth
  access_word_width_le :
    SuccinctSpace.optionNatWordWidth accessWidth <= wordSize
  rank_word_width_le : rankWidth <= wordSize
  select_word_width_le :
    SuccinctSpace.optionNatWordWidth selectWidth <= wordSize
  aux_length_eq :
    accessTable.payload.length + rankTables.payload.length +
        trueSelectTable.payload.length + falseSelectTable.payload.length =
      overhead
  queryCost_ge_one : 1 <= queryCost
  access_exact :
    forall i : Nat,
      tableBackedAccessAnswer (accessEntries[i]?) = bits[i]?
  rank_exact :
    forall (target : Bool) (pos : Nat),
      tableBackedRankAnswer ((rankTables.entries target)[pos]?) =
        Succinct.rankPrefix target bits pos
  select_exact :
    forall (target : Bool) (occurrence : Nat),
      tableBackedSelectAnswer
          (match target with
          | true => trueSelectEntries[occurrence]?
          | false => falseSelectEntries[occurrence]?) =
        Succinct.select target bits occurrence

namespace FixedWeightTableBackedFIDData

def auxPayload
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost) :
    List Bool :=
  data.accessTable.payload ++ data.rankTables.payload ++
    data.trueSelectTable.payload ++ data.falseSelectTable.payload

def payload
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost) :
    List Bool :=
  fixedWeightPackedPayload bits ++ data.auxPayload

@[simp] theorem auxPayload_length
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost) :
    data.auxPayload.length = overhead := by
  have haux :
      data.accessTable.payload.length + data.rankTables.payload.length +
          data.trueSelectTable.payload.length +
            data.falseSelectTable.payload.length =
        overhead := data.aux_length_eq
  unfold auxPayload
  simp only [List.length_append]
  omega

@[simp] theorem payload_length
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost) :
    data.payload.length = fixedWeightPayloadBudget bits + overhead := by
  unfold payload
  simp [fixedWeightPackedPayload_length, data.auxPayload_length]

def selectEntries
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) : List (Option Nat) :=
  match target with
  | true => data.trueSelectEntries
  | false => data.falseSelectEntries

def selectTableReadCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    Costed (Option (Option Nat)) :=
  match target with
  | true => data.trueSelectTable.readCosted occurrence
  | false => data.falseSelectTable.readCosted occurrence

@[simp] theorem selectTableReadCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectTableReadCosted target occurrence).cost = 1 := by
  cases target <;> simp [selectTableReadCosted]

@[simp] theorem selectTableReadCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectTableReadCosted target occurrence).erase =
      (data.selectEntries target)[occurrence]? := by
  cases target <;> simp [selectTableReadCosted, selectEntries]

def accessCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (i : Nat) : Costed (Option Bool) :=
  Costed.map tableBackedAccessAnswer (data.accessTable.readCosted i)

@[simp] theorem accessCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).cost = 1 := by
  simp [accessCosted]

theorem accessCosted_cost_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).cost <= queryCost := by
  simp [data.queryCost_ge_one]

@[simp] theorem accessCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).erase = bits[i]? := by
  simp [accessCosted, data.access_exact]

def rankCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.map tableBackedRankAnswer
    (data.rankTables.sampleCosted target pos)

@[simp] theorem rankCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost = 1 := by
  simp [rankCosted]

theorem rankCosted_cost_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost <= queryCost := by
  simp [data.queryCost_ge_one]

@[simp] theorem rankCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  simp [rankCosted, data.rank_exact]

def selectCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.map tableBackedSelectAnswer
    (data.selectTableReadCosted target occurrence)

@[simp] theorem selectCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost = 1 := by
  simp [selectCosted]

theorem selectCosted_cost_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= queryCost := by
  simp [data.queryCost_ge_one]

@[simp] theorem selectCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  cases target
  · simpa [selectCosted, selectTableReadCosted, selectEntries]
      using data.select_exact false occurrence
  · simpa [selectCosted, selectTableReadCosted, selectEntries]
      using data.select_exact true occurrence

def toCompressedDirectory
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost) :
    CompressedBitVectorRankSelectDirectory bits overhead queryCost where
  payload := data.payload
  payload_length_le := by
    simp
  accessCosted := data.accessCosted
  rankCosted := data.rankCosted
  selectCosted := data.selectCosted
  access_cost_le := data.accessCosted_cost_le
  rank_cost_le := data.rankCosted_cost_le
  select_cost_le := data.selectCosted_cost_le
  access_exact := data.accessCosted_erase
  rank_exact := data.rankCosted_erase
  select_exact := data.selectCosted_erase

theorem access_table_word_length_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    {i : Nat} {word : List Bool}
    (hword : data.accessTable.store.words[i]? = some word) :
    word.length <= wordSize := by
  have hlen := data.accessTable.word_length_of_get? hword
  have hwidth := data.access_word_width_le
  omega

theorem rank_true_table_word_length_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    {i : Nat} {word : List Bool}
    (hword : data.rankTables.trueTable.store.words[i]? = some word) :
    word.length <= wordSize := by
  have hlen := data.rankTables.trueTable.word_length_of_get? hword
  have hwidth := data.rank_word_width_le
  omega

theorem rank_false_table_word_length_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    {i : Nat} {word : List Bool}
    (hword : data.rankTables.falseTable.store.words[i]? = some word) :
    word.length <= wordSize := by
  have hlen := data.rankTables.falseTable.word_length_of_get? hword
  have hwidth := data.rank_word_width_le
  omega

theorem select_true_table_word_length_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    {i : Nat} {word : List Bool}
    (hword : data.trueSelectTable.store.words[i]? = some word) :
    word.length <= wordSize := by
  have hlen := data.trueSelectTable.word_length_of_get? hword
  have hwidth := data.select_word_width_le
  omega

theorem select_false_table_word_length_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    {i : Nat} {word : List Bool}
    (hword : data.falseSelectTable.store.words[i]? = some word) :
    word.length <= wordSize := by
  have hlen := data.falseSelectTable.word_length_of_get? hword
  have hwidth := data.select_word_width_le
  omega

theorem directory_profile
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost) :
    (data.toCompressedDirectory).payload = data.payload /\
      (data.toCompressedDirectory).payload.length =
        fixedWeightPayloadBudget bits + overhead /\
      SuccinctSpace.flattenPayloadWords
          data.packedStore.store.words.toList =
        fixedWeightPackedPayload bits /\
      data.auxPayload.length = overhead /\
      SuccinctSpace.flattenPayloadWords
          data.accessTable.store.words.toList =
        data.accessTable.payload /\
      SuccinctSpace.flattenPayloadWords
          data.rankTables.trueTable.store.words.toList =
        data.rankTables.trueTable.payload /\
      SuccinctSpace.flattenPayloadWords
          data.rankTables.falseTable.store.words.toList =
        data.rankTables.falseTable.payload /\
      SuccinctSpace.flattenPayloadWords
          data.trueSelectTable.store.words.toList =
        data.trueSelectTable.payload /\
      SuccinctSpace.flattenPayloadWords
          data.falseSelectTable.store.words.toList =
        data.falseSelectTable.payload /\
      (forall (i : Nat) (word : List Bool),
        data.accessTable.store.words[i]? = some word ->
          word.length <= wordSize) /\
      (forall (i : Nat) (word : List Bool),
        data.rankTables.trueTable.store.words[i]? = some word ->
          word.length <= wordSize) /\
      (forall (i : Nat) (word : List Bool),
        data.rankTables.falseTable.store.words[i]? = some word ->
          word.length <= wordSize) /\
      (forall (i : Nat) (word : List Bool),
        data.trueSelectTable.store.words[i]? = some word ->
          word.length <= wordSize) /\
      (forall (i : Nat) (word : List Bool),
        data.falseSelectTable.store.words[i]? = some word ->
          word.length <= wordSize) /\
      wordSize <= Nat.log2 bits.length + 1 /\
      (forall i,
        ((data.toCompressedDirectory).accessQueryCosted i).cost <=
            queryCost /\
          ((data.toCompressedDirectory).accessQueryCosted i).erase =
            bits[i]?) /\
      (forall target pos,
        ((data.toCompressedDirectory).rankQueryCosted target pos).cost <=
            queryCost /\
          ((data.toCompressedDirectory).rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).cost <= queryCost /\
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
  · exact data.auxPayload_length
  constructor
  · exact data.accessTable.store.payload_eq_words_join
  constructor
  · exact data.rankTables.trueTable.store.payload_eq_words_join
  constructor
  · exact data.rankTables.falseTable.store.payload_eq_words_join
  constructor
  · exact data.trueSelectTable.store.payload_eq_words_join
  constructor
  · exact data.falseSelectTable.store.payload_eq_words_join
  constructor
  · intro i word hword
    exact data.access_table_word_length_le hword
  constructor
  · intro i word hword
    exact data.rank_true_table_word_length_le hword
  constructor
  · intro i word hword
    exact data.rank_false_table_word_length_le hword
  constructor
  · intro i word hword
    exact data.select_true_table_word_length_le hword
  constructor
  · intro i word hword
    exact data.select_false_table_word_length_le hword
  constructor
  · exact data.wordSize_le_machine
  constructor
  · intro i
    exact ⟨data.accessCosted_cost_le i, data.accessCosted_erase i⟩
  constructor
  · intro target pos
    exact
      ⟨data.rankCosted_cost_le target pos,
        data.rankCosted_erase target pos⟩
  · intro target occurrence
    exact
      ⟨data.selectCosted_cost_le target occurrence,
        data.selectCosted_erase target occurrence⟩

end FixedWeightTableBackedFIDData

end RankSelectSpec

end RMQ
