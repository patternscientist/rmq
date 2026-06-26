import RMQ.Core.SuccinctSpace.BPShape
import RMQ.Core.SuccinctSpace.SelectSamples

/-!
# Stored-word rank/select directories

Payload-live, stored-word, and payload-backed rank/select directory surfaces
used by the balanced-parentheses and succinct-RMQ layers.
-/

namespace RMQ

namespace SuccinctSpace

/--
Payload-live stored-word rank data.

The bitvector itself is stored as counted payload words erasing to `bits`, while
the true/false prefix samples are stored in fixed-width auxiliary payload
tables.  The query path reads exactly those stores and then invokes one
word-level rank primitive; the correctness fields state the usual sampled-rank
decomposition against the reference `Succinct.rankPrefix`.
-/
structure PayloadLiveStoredWordRankData
    (bits : List Bool) (overhead : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  sampleWidth : Nat
  trueEntries : List Nat
  falseEntries : List Nat
  samples : FixedWidthRankSampleTables trueEntries falseEntries sampleWidth
  bitWords : PayloadWordStore bits
  aux_length_eq : samples.payload.length = overhead
  sample_present :
    forall target pos,
      pos <= bits.length ->
        exists sample, (samples.entries target)[pos / wordSize]? = some sample
  word_present :
    forall pos,
      pos <= bits.length ->
        exists word, bitWords.words[pos / wordSize]? = some word
  rank_parts_exact :
    forall target pos sample word,
      pos <= bits.length ->
        (samples.entries target)[pos / wordSize]? = some sample ->
        bitWords.words[pos / wordSize]? = some word ->
          sample +
              RAM.boolRankPrefix target word
                (pos - (pos / wordSize) * wordSize) =
            Succinct.rankPrefix target bits pos

namespace PayloadLiveStoredWordRankData

def wordIndex
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead) (pos : Nat) :
    Nat :=
  pos / data.wordSize

def wordStart
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead) (pos : Nat) :
    Nat :=
  data.wordIndex pos * data.wordSize

def wordOffset
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead) (pos : Nat) :
    Nat :=
  pos - data.wordStart pos

def auxPayload
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead) : List Bool :=
  data.samples.payload

def rankCosted
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind (data.samples.sampleCosted target (data.wordIndex pos))
    fun sample? =>
      Costed.bind (data.bitWords.readWordCosted (data.wordIndex pos))
        fun word? =>
          match sample?, word? with
          | some sample, some word =>
              Costed.map (fun localRank => sample + localRank)
                (RAM.rankBoolWordPrefix target word
                  (data.wordOffset pos)).toCosted
          | _, _ => Costed.pure 0

def rankCostedClamped
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) : Costed Nat :=
  data.rankCosted target (Nat.min pos bits.length)

theorem auxPayload_length
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead) :
    data.auxPayload.length = overhead := by
  exact data.aux_length_eq

theorem rankCosted_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost <= 3 := by
  unfold rankCosted
  cases hsample :
      (data.samples.sampleCosted target (data.wordIndex pos)).value with
  | none =>
      cases hword :
          (data.bitWords.readWordCosted (data.wordIndex pos)).value with
      | none =>
          simp [Costed.bind, Costed.pure, hsample, hword]
      | some word =>
          simp [Costed.bind, Costed.pure, hsample, hword]
  | some sample =>
      cases hword :
          (data.bitWords.readWordCosted (data.wordIndex pos)).value with
      | none =>
          simp [Costed.bind, Costed.pure, hsample, hword]
      | some word =>
          simp [Costed.bind, Costed.map, Costed.pure, hsample, hword]

theorem rankCostedClamped_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    (data.rankCostedClamped target pos).cost <= 3 := by
  exact data.rankCosted_cost_le_three target (Nat.min pos bits.length)

theorem rankCosted_exact
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) {pos : Nat} (hpos : pos <= bits.length) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  rcases data.sample_present target pos hpos with ⟨sample, hsample⟩
  rcases data.word_present pos hpos with ⟨word, hword⟩
  have hsampleValue :
      (data.samples.sampleCosted target (data.wordIndex pos)).value =
        some sample := by
    have h :=
      data.samples.sampleCosted_erase target (data.wordIndex pos)
    simpa [Costed.erase, wordIndex, hsample] using h
  have hwordValue :
      (data.bitWords.readWordCosted (data.wordIndex pos)).value =
        some word := by
    have h :=
      data.bitWords.readWordCosted_erase (data.wordIndex pos)
    simpa [Costed.erase, wordIndex, hword] using h
  have hsum :
      sample +
          RAM.boolRankPrefix target word (data.wordOffset pos) =
        Succinct.rankPrefix target bits pos := by
    simpa [wordOffset, wordStart, wordIndex] using
      data.rank_parts_exact target pos sample word hpos hsample hword
  unfold rankCosted
  simp [Costed.bind, Costed.map, Costed.pure, Costed.erase,
    hsampleValue, hwordValue, hsum]

theorem rankCostedClamped_exact
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    (data.rankCostedClamped target pos).erase =
      Succinct.rankPrefix target bits pos := by
  unfold rankCostedClamped
  have hmin : Nat.min pos bits.length <= bits.length :=
    Nat.min_le_right pos bits.length
  calc
    (data.rankCosted target (Nat.min pos bits.length)).erase =
        Succinct.rankPrefix target bits (Nat.min pos bits.length) := by
      exact data.rankCosted_exact target hmin
    _ = Succinct.rankPrefix target bits pos := by
      exact Succinct.rankPrefix_min_length_eq target bits pos

theorem profile
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead) :
    data.auxPayload.length = overhead /\
      flattenPayloadWords data.bitWords.words.toList = bits /\
      (forall target pos,
        (data.rankCostedClamped target pos).cost <= 3 /\
          (data.rankCostedClamped target pos).erase =
            Succinct.rankPrefix target bits pos) := by
  constructor
  · exact data.auxPayload_length
  · constructor
    · exact data.bitWords.payload_eq_words_join
    · intro target pos
      exact ⟨data.rankCostedClamped_cost_le_three target pos,
        data.rankCostedClamped_exact target pos⟩

end PayloadLiveStoredWordRankData

/--
Certified rank/select directory over a fixed bitvector.

The reference semantics remain `Succinct.rankPrefix` and `Succinct.select`.
The `encodeAux` length is counted separately from the payload bits themselves,
and the costed queries must refine the reference operations at a uniform
`queryCost` bound.  This is the rank/select component slot used by the
componentized balanced-parentheses RMQ space profile below.
-/
structure RankSelectDirectory
    (bits : List Bool) (overhead queryCost : Nat) where
  Aux : Type
  buildAux : Aux
  encodeAux : Aux -> List Bool
  rankCosted : Aux -> Bool -> Nat -> Costed Nat
  selectCosted : Aux -> Bool -> Nat -> Costed (Option Nat)
  aux_length_eq : (encodeAux buildAux).length = overhead
  rank_cost_le :
    forall target pos, (rankCosted buildAux target pos).cost <= queryCost
  select_cost_le :
    forall target occurrence,
      (selectCosted buildAux target occurrence).cost <= queryCost
  rank_exact :
    forall target pos,
      (rankCosted buildAux target pos).erase =
        Succinct.rankPrefix target bits pos
  select_exact :
    forall target occurrence,
      (selectCosted buildAux target occurrence).erase =
        Succinct.select target bits occurrence

namespace RankSelectDirectory

def auxPayload
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost) :
    List Bool :=
  directory.encodeAux directory.buildAux

@[simp] theorem auxPayload_length
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost) :
    directory.auxPayload.length = overhead := by
  exact directory.aux_length_eq

def rankQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  directory.rankCosted directory.buildAux target pos

def selectQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  directory.selectCosted directory.buildAux target occurrence

theorem rankQueryCosted_cost_le
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) :
    (directory.rankQueryCosted target pos).cost <= queryCost := by
  exact directory.rank_cost_le target pos

theorem selectQueryCosted_cost_le
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (directory.selectQueryCosted target occurrence).cost <= queryCost := by
  exact directory.select_cost_le target occurrence

@[simp] theorem rankQueryCosted_erase
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) :
    (directory.rankQueryCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  exact directory.rank_exact target pos

@[simp] theorem selectQueryCosted_erase
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (directory.selectQueryCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  exact directory.select_exact target occurrence

end RankSelectDirectory

/--
Family-level rank/select component: every bitvector gets a certified directory
whose auxiliary payload is `o(n)` and whose query bound is one fixed constant.
-/
structure RankSelectFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall bits : List Bool,
      RankSelectDirectory bits (overhead bits.length) queryCost
  overhead_littleO : LittleOLinear overhead

namespace RankSelectFamily

theorem constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : RankSelectFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall bits : List Bool,
        ((family.directory bits).auxPayload.length = overhead bits.length) /\
          (forall target pos,
            ((family.directory bits).rankQueryCosted target pos).cost <=
                queryCost /\
              ((family.directory bits).rankQueryCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            ((family.directory bits).selectQueryCosted target occurrence).cost <=
                queryCost /\
              ((family.directory bits).selectQueryCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    constructor
    · exact (family.directory bits).auxPayload_length
    · constructor
      · intro target pos
        exact ⟨(family.directory bits).rankQueryCosted_cost_le target pos,
          (family.directory bits).rankQueryCosted_erase target pos⟩
      · intro target occurrence
        exact ⟨(family.directory bits).selectQueryCosted_cost_le target occurrence,
          (family.directory bits).selectQueryCosted_erase target occurrence⟩

end RankSelectFamily

def rankSampleSeqOf
    (target : Bool)
    (trueSamples falseSamples : TableModel.IndexedSeq Nat) :
    TableModel.IndexedSeq Nat :=
  match target with
  | true => trueSamples
  | false => falseSamples

/--
Stored data needed for a faithful bounded rank query.

The query path reads one sampled prefix rank, reads one payload word, and then
uses the RAM word-rank primitive inside that word.  The fields below certify
that those stored objects correspond to the reference bitstring; they do not
let the query compute `rankPrefix` directly.
-/
structure StoredWordRankData
    (bits : List Bool) (overhead : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  words : TableModel.IndexedSeq (List Bool)
  trueSamples : TableModel.IndexedSeq Nat
  falseSamples : TableModel.IndexedSeq Nat
  encodeAux : List Bool
  aux_length_eq : encodeAux.length = overhead
  sample_present :
    forall target pos,
      pos <= bits.length ->
        exists sample,
          (rankSampleSeqOf target trueSamples falseSamples).get?
            (pos / wordSize) = some sample
  word_present :
    forall pos,
      pos <= bits.length ->
        exists word, words.get? (pos / wordSize) = some word
  rank_parts_exact :
    forall target pos sample word,
      pos <= bits.length ->
        (rankSampleSeqOf target trueSamples falseSamples).get?
            (pos / wordSize) = some sample ->
        words.get? (pos / wordSize) = some word ->
          sample +
              RAM.boolRankPrefix target word
                (pos - (pos / wordSize) * wordSize) =
            Succinct.rankPrefix target bits pos

namespace StoredWordRankData

def sampleSeq
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) (target : Bool) :
    TableModel.IndexedSeq Nat :=
  rankSampleSeqOf target data.trueSamples data.falseSamples

def wordIndex
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) (pos : Nat) : Nat :=
  pos / data.wordSize

def wordStart
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) (pos : Nat) : Nat :=
  data.wordIndex pos * data.wordSize

def wordOffset
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) (pos : Nat) : Nat :=
  pos - data.wordStart pos

def rankCosted
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind ((data.sampleSeq target).getCosted (data.wordIndex pos))
    fun sample? =>
      Costed.bind (data.words.getCosted (data.wordIndex pos)) fun word? =>
        match sample?, word? with
        | some sample, some word =>
            Costed.map (fun localRank => sample + localRank)
              (RAM.rankBoolWordPrefix target word
                (data.wordOffset pos)).toCosted
        | _, _ => Costed.pure 0

/--
Total rank query adapter.

The stored-word data is exact on valid prefix positions.  For a total
rank/select directory we clamp out-of-range positions to `bits.length`, using
the fact that prefix rank saturates once the whole bitvector has been counted.
-/
def rankCostedClamped
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) : Costed Nat :=
  data.rankCosted target (Nat.min pos bits.length)

theorem rankCosted_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost <= 3 := by
  unfold rankCosted sampleSeq wordIndex wordOffset wordStart
  cases hsample :
      (rankSampleSeqOf target data.trueSamples data.falseSamples).get?
        (pos / data.wordSize) with
  | none =>
      cases hword : data.words.get? (pos / data.wordSize) with
      | none =>
          simp [TableModel.IndexedSeq.getCosted,
            TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
            hsample, hword,
            Costed.bind, Costed.pure, TableModel.indexedReadCost]
      | some word =>
          simp [TableModel.IndexedSeq.getCosted,
            TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
            hsample, hword,
            Costed.bind, Costed.pure, TableModel.indexedReadCost]
  | some sample =>
      cases hword : data.words.get? (pos / data.wordSize) with
      | none =>
          simp [TableModel.IndexedSeq.getCosted,
            TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
            hsample, hword,
            Costed.bind, Costed.pure, TableModel.indexedReadCost]
      | some word =>
          simp [TableModel.IndexedSeq.getCosted,
            TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
            hsample, hword,
            Costed.bind, Costed.map, Costed.pure,
            TableModel.indexedReadCost]

theorem rankCostedClamped_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    (data.rankCostedClamped target pos).cost <= 3 := by
  exact data.rankCosted_cost_le_three target (Nat.min pos bits.length)

theorem rankCosted_exact
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead)
    (target : Bool) {pos : Nat} (hpos : pos <= bits.length) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  rcases data.sample_present target pos hpos with ⟨sample, hsample⟩
  rcases data.word_present pos hpos with ⟨word, hword⟩
  have hsum :=
    data.rank_parts_exact target pos sample word hpos hsample hword
  have hsum' :
      sample +
          RAM.boolRankPrefix target word
            (pos - data.wordStart pos) =
        Succinct.rankPrefix target bits pos := by
    simpa [wordStart, wordIndex] using hsum
  unfold rankCosted sampleSeq wordIndex wordOffset
  simp [TableModel.IndexedSeq.getCosted,
    TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
    hsample, hword, Costed.bind, Costed.map, Costed.pure, hsum']

theorem rankCostedClamped_exact
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    (data.rankCostedClamped target pos).erase =
      Succinct.rankPrefix target bits pos := by
  unfold rankCostedClamped
  have hmin : Nat.min pos bits.length <= bits.length :=
    Nat.min_le_right pos bits.length
  calc
    (data.rankCosted target (Nat.min pos bits.length)).erase =
        Succinct.rankPrefix target bits (Nat.min pos bits.length) := by
      exact data.rankCosted_exact target hmin
    _ = Succinct.rankPrefix target bits pos := by
      exact Succinct.rankPrefix_min_length_eq target bits pos

theorem rankCosted_profile
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) :
    data.encodeAux.length = overhead /\
      forall target pos,
        (data.rankCosted target pos).cost <= 3 /\
          (pos <= bits.length ->
            (data.rankCosted target pos).erase =
              Succinct.rankPrefix target bits pos) := by
  constructor
  · exact data.aux_length_eq
  · intro target pos
    exact ⟨data.rankCosted_cost_le_three target pos,
      fun hpos => data.rankCosted_exact target hpos⟩

end StoredWordRankData

/--
Payload-live stored-word select data.

Locator reads come from fixed-width payload words; payload-bit reads come from
the bitvector word store; the final in-word selection is the typed word-RAM
primitive.  This closes the same proof-only table gap for select that
`PayloadLiveStoredWordRankData` closes for rank.
-/
structure PayloadLiveStoredWordSelectData
    (bits : List Bool) (overhead : Nat) where
  fieldWidth : Nat
  trueEntries : List (Option StoredWordSelectSample)
  falseEntries : List (Option StoredWordSelectSample)
  samples : FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth
  bitWords : PayloadWordStore bits
  aux_length_eq : samples.payload.length = overhead
  sample_entry_present :
    forall (target : Bool) (occurrence : Nat),
      exists entry, (samples.entries target)[occurrence]? = some entry
  word_present_of_sample :
    forall (target : Bool) (occurrence : Nat)
        (sample : StoredWordSelectSample),
      (samples.entries target)[occurrence]? = some (some sample) ->
        exists word, bitWords.words[sample.wordIndex]? = some word
  select_some_exact :
    forall (target : Bool) (occurrence : Nat)
        (sample : StoredWordSelectSample) (word : List Bool),
      (samples.entries target)[occurrence]? = some (some sample) ->
        bitWords.words[sample.wordIndex]? = some word ->
          (RAM.boolSelectInWord target word
              (occurrence - sample.rankBefore)).map
              (fun offset => sample.wordStart + offset) =
            Succinct.select target bits occurrence
  select_none_exact :
    forall (target : Bool) (occurrence : Nat),
      (samples.entries target)[occurrence]? =
          some (none : Option StoredWordSelectSample) ->
        Succinct.select target bits occurrence = none

namespace PayloadLiveStoredWordSelectData

def auxPayload
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead) : List Bool :=
  data.samples.payload

def selectCosted
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind (data.samples.sampleCosted target occurrence)
    fun entry? =>
      match entry? with
      | none => Costed.pure none
      | some none => Costed.pure none
      | some (some sample) =>
          Costed.bind
            (data.bitWords.readWordCosted sample.wordIndex)
            fun word? =>
              match word? with
              | none => Costed.pure none
              | some word =>
                  Costed.map
                    (fun local? =>
                      local?.map fun offset => sample.wordStart + offset)
                    (RAM.selectBoolWord target word
                      (occurrence - sample.rankBefore)).toCosted

theorem auxPayload_length
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead) :
    data.auxPayload.length = overhead :=
  data.aux_length_eq

theorem selectCosted_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= 3 := by
  unfold selectCosted
  cases hentry :
      (data.samples.sampleCosted target occurrence).value with
  | none =>
      simp [Costed.bind, Costed.pure, hentry]
  | some entry =>
      cases entry with
      | none =>
          simp [Costed.bind, Costed.pure, hentry]
      | some sample =>
          cases hword :
              (data.bitWords.readWordCosted sample.wordIndex).value with
          | none =>
              simp [Costed.bind, Costed.pure, hentry, hword]
          | some word =>
              simp [Costed.bind, Costed.map, Costed.pure, hentry, hword]

theorem selectCosted_exact
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  rcases data.sample_entry_present target occurrence with ⟨entry, hentry⟩
  have hentryValue :
      (data.samples.sampleCosted target occurrence).value =
        some entry := by
    have h := data.samples.sampleCosted_erase target occurrence
    simpa [Costed.erase, hentry] using h
  cases entry with
  | none =>
      have hnone := data.select_none_exact target occurrence hentry
      unfold selectCosted
      simp [Costed.bind, Costed.pure, Costed.erase, hentryValue, hnone]
  | some sample =>
      rcases data.word_present_of_sample target occurrence sample hentry with
        ⟨word, hword⟩
      have hwordValue :
          (data.bitWords.readWordCosted sample.wordIndex).value =
            some word := by
        have h := data.bitWords.readWordCosted_erase sample.wordIndex
        simpa [Costed.erase, hword] using h
      have hexact :=
        data.select_some_exact target occurrence sample word hentry hword
      unfold selectCosted
      simp [Costed.bind, Costed.map, Costed.pure, Costed.erase,
        hentryValue, hwordValue, hexact]

theorem profile
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead) :
    data.auxPayload.length = overhead /\
      flattenPayloadWords data.bitWords.words.toList = bits /\
      forall target occurrence,
        (data.selectCosted target occurrence).cost <= 3 /\
          (data.selectCosted target occurrence).erase =
            Succinct.select target bits occurrence := by
  constructor
  · exact data.auxPayload_length
  · constructor
    · exact data.bitWords.payload_eq_words_join
    · intro target occurrence
      exact ⟨data.selectCosted_cost_le_three target occurrence,
        data.selectCosted_exact target occurrence⟩

end PayloadLiveStoredWordSelectData

/--
Combined rank/select directory whose rank and select components both read from
payload-live stores.

This is still a component boundary, not the final asymptotic instantiation: the
caller must supply compressed sample/locator tables and prove their overhead.
The query path itself is no longer allowed to read arbitrary decoded tables.
-/
def RankSelectDirectory.ofPayloadLiveRankSelectData
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData bits rankOverhead)
    (selectData : PayloadLiveStoredWordSelectData bits selectOverhead) :
    RankSelectDirectory bits (rankOverhead + selectOverhead) 3 where
  Aux := Unit
  buildAux := ()
  encodeAux _ := rankData.auxPayload ++ selectData.auxPayload
  rankCosted _ target pos := rankData.rankCostedClamped target pos
  selectCosted _ target occurrence := selectData.selectCosted target occurrence
  aux_length_eq := by
    simp [rankData.auxPayload_length, selectData.auxPayload_length]
  rank_cost_le := by
    intro target pos
    exact rankData.rankCostedClamped_cost_le_three target pos
  select_cost_le := by
    intro target occurrence
    exact selectData.selectCosted_cost_le_three target occurrence
  rank_exact := by
    intro target pos
    exact rankData.rankCostedClamped_exact target pos
  select_exact := by
    intro target occurrence
    exact selectData.selectCosted_exact target occurrence

theorem RankSelectDirectory.ofPayloadLiveRankSelectData_profile
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData bits rankOverhead)
    (selectData : PayloadLiveStoredWordSelectData bits selectOverhead) :
    ((RankSelectDirectory.ofPayloadLiveRankSelectData
        rankData selectData).auxPayload.length =
        rankOverhead + selectOverhead) /\
      (forall target pos,
        ((RankSelectDirectory.ofPayloadLiveRankSelectData
            rankData selectData).rankQueryCosted target pos).cost <= 3 /\
          ((RankSelectDirectory.ofPayloadLiveRankSelectData
            rankData selectData).rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((RankSelectDirectory.ofPayloadLiveRankSelectData
            rankData selectData).selectQueryCosted target occurrence).cost <=
              3 /\
          ((RankSelectDirectory.ofPayloadLiveRankSelectData
            rankData selectData).selectQueryCosted target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · exact
      (RankSelectDirectory.ofPayloadLiveRankSelectData
        rankData selectData).auxPayload_length
  · constructor
    · intro target pos
      let directory :=
        RankSelectDirectory.ofPayloadLiveRankSelectData rankData selectData
      exact ⟨directory.rankQueryCosted_cost_le target pos,
        directory.rankQueryCosted_erase target pos⟩
    · intro target occurrence
      let directory :=
        RankSelectDirectory.ofPayloadLiveRankSelectData rankData selectData
      exact ⟨directory.selectQueryCosted_cost_le target occurrence,
        directory.selectQueryCosted_erase target occurrence⟩

/-- Family of payload-live stored-word rank/select components. -/
structure PayloadLiveStoredWordRankSelectFamily
    (rankOverhead selectOverhead : Nat -> Nat) where
  rankComponent :
    forall bits : List Bool,
      PayloadLiveStoredWordRankData bits (rankOverhead bits.length)
  selectComponent :
    forall bits : List Bool,
      PayloadLiveStoredWordSelectData bits (selectOverhead bits.length)
  rank_littleO : LittleOLinear rankOverhead
  select_littleO : LittleOLinear selectOverhead

namespace PayloadLiveStoredWordRankSelectFamily

def overhead
    {rankOverhead selectOverhead : Nat -> Nat}
    (_family :
      PayloadLiveStoredWordRankSelectFamily rankOverhead selectOverhead) :
    Nat -> Nat :=
  fun n => rankOverhead n + selectOverhead n

theorem overhead_littleO
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadLiveStoredWordRankSelectFamily rankOverhead selectOverhead) :
    LittleOLinear family.overhead := by
  exact family.rank_littleO.add family.select_littleO

def toRankSelectFamily
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadLiveStoredWordRankSelectFamily rankOverhead selectOverhead) :
    RankSelectFamily family.overhead 3 where
  directory bits :=
    RankSelectDirectory.ofPayloadLiveRankSelectData
      (family.rankComponent bits) (family.selectComponent bits)
  overhead_littleO := family.overhead_littleO

theorem constant_query_profile
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadLiveStoredWordRankSelectFamily rankOverhead selectOverhead) :
    LittleOLinear family.overhead /\
      forall bits : List Bool,
        (((family.toRankSelectFamily).directory bits).auxPayload.length =
          rankOverhead bits.length + selectOverhead bits.length) /\
          (forall target pos,
            (((family.toRankSelectFamily).directory bits).rankQueryCosted
                target pos).cost <= 3 /\
              (((family.toRankSelectFamily).directory bits).rankQueryCosted
                target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (((family.toRankSelectFamily).directory bits).selectQueryCosted
                target occurrence).cost <= 3 /\
              (((family.toRankSelectFamily).directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    exact
      RankSelectDirectory.ofPayloadLiveRankSelectData_profile
        (family.rankComponent bits) (family.selectComponent bits)

end PayloadLiveStoredWordRankSelectFamily

/--
Stored data needed for a faithful bounded select query.

The query path reads one occurrence locator, reads one payload word, and then
uses a RAM word-select primitive inside that word.  A `none` locator certifies
that the requested occurrence does not exist.
-/
structure StoredWordSelectData
    (bits : List Bool) (overhead : Nat) where
  words : TableModel.IndexedSeq (List Bool)
  trueSamples : TableModel.IndexedSeq (Option StoredWordSelectSample)
  falseSamples : TableModel.IndexedSeq (Option StoredWordSelectSample)
  encodeAux : List Bool
  aux_length_eq : encodeAux.length = overhead
  sample_entry_present :
    forall target occurrence,
      exists entry,
        (selectSampleSeqOf target trueSamples falseSamples).get?
          occurrence = some entry
  word_present_of_sample :
    forall target occurrence sample,
      (selectSampleSeqOf target trueSamples falseSamples).get?
          occurrence = some (some sample) ->
        exists word, words.get? sample.wordIndex = some word
  select_some_exact :
    forall target occurrence sample word,
      (selectSampleSeqOf target trueSamples falseSamples).get?
          occurrence = some (some sample) ->
        words.get? sample.wordIndex = some word ->
          (RAM.boolSelectInWord target word
              (occurrence - sample.rankBefore)).map
              (fun offset => sample.wordStart + offset) =
            Succinct.select target bits occurrence
  select_none_exact :
    forall target occurrence,
      (selectSampleSeqOf target trueSamples falseSamples).get?
          occurrence = some none ->
        Succinct.select target bits occurrence = none

namespace StoredWordSelectData

def sampleSeq
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordSelectData bits overhead) (target : Bool) :
    TableModel.IndexedSeq (Option StoredWordSelectSample) :=
  selectSampleSeqOf target data.trueSamples data.falseSamples

def selectCosted
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind ((data.sampleSeq target).getCosted occurrence) fun entry? =>
    match entry? with
    | none => Costed.pure none
    | some none => Costed.pure none
    | some (some sample) =>
        Costed.bind (data.words.getCosted sample.wordIndex) fun word? =>
          match word? with
          | none => Costed.pure none
          | some word =>
              Costed.map
                (fun local? =>
                  local?.map fun offset => sample.wordStart + offset)
                (RAM.selectBoolWord target word
                  (occurrence - sample.rankBefore)).toCosted

theorem selectCosted_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= 3 := by
  unfold selectCosted sampleSeq
  cases hentry :
      (selectSampleSeqOf target data.trueSamples data.falseSamples).get?
        occurrence with
  | none =>
      simp [TableModel.IndexedSeq.getCosted,
        TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
        hentry, Costed.bind, Costed.pure, TableModel.indexedReadCost]
  | some entry =>
      cases entry with
      | none =>
          simp [TableModel.IndexedSeq.getCosted,
            TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
            hentry, Costed.bind, Costed.pure, TableModel.indexedReadCost]
      | some sample =>
          cases hword : data.words.get? sample.wordIndex with
          | none =>
              simp [TableModel.IndexedSeq.getCosted,
                TableModel.IndexedSeq.toAccess,
                TableModel.IndexedAccess.getCosted,
                hentry, hword, Costed.bind, Costed.pure,
                TableModel.indexedReadCost]
          | some word =>
              simp [TableModel.IndexedSeq.getCosted,
                TableModel.IndexedSeq.toAccess,
                TableModel.IndexedAccess.getCosted,
                hentry, hword, Costed.bind, Costed.map, Costed.pure,
                TableModel.indexedReadCost]

theorem selectCosted_exact
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  rcases data.sample_entry_present target occurrence with ⟨entry, hentry⟩
  cases entry with
  | none =>
      have hnone := data.select_none_exact target occurrence hentry
      unfold selectCosted sampleSeq
      simp [TableModel.IndexedSeq.getCosted,
        TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
        hentry, Costed.bind, Costed.pure, hnone]
  | some sample =>
      rcases data.word_present_of_sample target occurrence sample hentry with
        ⟨word, hword⟩
      have hexact :=
        data.select_some_exact target occurrence sample word hentry hword
      unfold selectCosted sampleSeq
      simp [TableModel.IndexedSeq.getCosted,
        TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
        hentry, hword, Costed.bind, Costed.map, Costed.pure, hexact]

theorem selectCosted_profile
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordSelectData bits overhead) :
    data.encodeAux.length = overhead /\
      forall target occurrence,
        (data.selectCosted target occurrence).cost <= 3 /\
          (data.selectCosted target occurrence).erase =
            Succinct.select target bits occurrence := by
  constructor
  · exact data.aux_length_eq
  · intro target occurrence
    exact ⟨data.selectCosted_cost_le_three target occurrence,
      data.selectCosted_exact target occurrence⟩

end StoredWordSelectData

/--
Combined rank/select directory with payload-live rank samples.

This is an intermediate migration adapter: rank goes through
`PayloadLiveStoredWordRankData`, so its sample and bit-word reads are tied to
concrete counted payload stores.  Select is still the existing stored-word
component and remains a separate target for the next payload-live migration.
-/
def RankSelectDirectory.ofPayloadLiveRankStoredSelectData
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData bits rankOverhead)
    (selectData : StoredWordSelectData bits selectOverhead) :
    RankSelectDirectory bits (rankOverhead + selectOverhead) 3 where
  Aux := Unit
  buildAux := ()
  encodeAux _ := rankData.auxPayload ++ selectData.encodeAux
  rankCosted _ target pos := rankData.rankCostedClamped target pos
  selectCosted _ target occurrence := selectData.selectCosted target occurrence
  aux_length_eq := by
    simp [rankData.auxPayload_length, selectData.aux_length_eq]
  rank_cost_le := by
    intro target pos
    exact rankData.rankCostedClamped_cost_le_three target pos
  select_cost_le := by
    intro target occurrence
    exact selectData.selectCosted_cost_le_three target occurrence
  rank_exact := by
    intro target pos
    exact rankData.rankCostedClamped_exact target pos
  select_exact := by
    intro target occurrence
    exact selectData.selectCosted_exact target occurrence

theorem RankSelectDirectory.ofPayloadLiveRankStoredSelectData_profile
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData bits rankOverhead)
    (selectData : StoredWordSelectData bits selectOverhead) :
    ((RankSelectDirectory.ofPayloadLiveRankStoredSelectData
        rankData selectData).auxPayload.length =
        rankOverhead + selectOverhead) /\
      (forall target pos,
        ((RankSelectDirectory.ofPayloadLiveRankStoredSelectData
            rankData selectData).rankQueryCosted target pos).cost <= 3 /\
          ((RankSelectDirectory.ofPayloadLiveRankStoredSelectData
            rankData selectData).rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((RankSelectDirectory.ofPayloadLiveRankStoredSelectData
            rankData selectData).selectQueryCosted target occurrence).cost <=
              3 /\
          ((RankSelectDirectory.ofPayloadLiveRankStoredSelectData
            rankData selectData).selectQueryCosted target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · exact
      (RankSelectDirectory.ofPayloadLiveRankStoredSelectData
        rankData selectData).auxPayload_length
  · constructor
    · intro target pos
      let directory :=
        RankSelectDirectory.ofPayloadLiveRankStoredSelectData
          rankData selectData
      exact ⟨directory.rankQueryCosted_cost_le target pos,
        directory.rankQueryCosted_erase target pos⟩
    · intro target occurrence
      let directory :=
        RankSelectDirectory.ofPayloadLiveRankStoredSelectData
          rankData selectData
      exact ⟨directory.selectQueryCosted_cost_le target occurrence,
        directory.selectQueryCosted_erase target occurrence⟩

/--
Combined faithful stored-word rank/select directory.

Rank uses the clamped valid-prefix adapter; select uses the occurrence-locator
and word-select path.  Both operations are bounded by three modeled primitive
steps and erase to the reference list-level semantics.
-/
def RankSelectDirectory.ofStoredWordData
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : StoredWordRankData bits rankOverhead)
    (selectData : StoredWordSelectData bits selectOverhead) :
    RankSelectDirectory bits (rankOverhead + selectOverhead) 3 where
  Aux := Unit
  buildAux := ()
  encodeAux _ := rankData.encodeAux ++ selectData.encodeAux
  rankCosted _ target pos := rankData.rankCostedClamped target pos
  selectCosted _ target occurrence := selectData.selectCosted target occurrence
  aux_length_eq := by
    simp [rankData.aux_length_eq, selectData.aux_length_eq]
  rank_cost_le := by
    intro target pos
    exact rankData.rankCostedClamped_cost_le_three target pos
  select_cost_le := by
    intro target occurrence
    exact selectData.selectCosted_cost_le_three target occurrence
  rank_exact := by
    intro target pos
    exact rankData.rankCostedClamped_exact target pos
  select_exact := by
    intro target occurrence
    exact selectData.selectCosted_exact target occurrence

theorem RankSelectDirectory.ofStoredWordData_profile
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : StoredWordRankData bits rankOverhead)
    (selectData : StoredWordSelectData bits selectOverhead) :
    ((RankSelectDirectory.ofStoredWordData rankData selectData).auxPayload.length =
        rankOverhead + selectOverhead) /\
      (forall target pos,
        ((RankSelectDirectory.ofStoredWordData rankData selectData).rankQueryCosted
            target pos).cost <= 3 /\
          ((RankSelectDirectory.ofStoredWordData rankData selectData).rankQueryCosted
            target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((RankSelectDirectory.ofStoredWordData rankData selectData).selectQueryCosted
            target occurrence).cost <= 3 /\
          ((RankSelectDirectory.ofStoredWordData rankData selectData).selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · exact (RankSelectDirectory.ofStoredWordData rankData selectData).auxPayload_length
  · constructor
    · intro target pos
      let directory :=
        RankSelectDirectory.ofStoredWordData rankData selectData
      exact ⟨directory.rankQueryCosted_cost_le target pos,
        directory.rankQueryCosted_erase target pos⟩
    · intro target occurrence
      let directory :=
        RankSelectDirectory.ofStoredWordData rankData selectData
      exact ⟨directory.selectQueryCosted_cost_le target occurrence,
        directory.selectQueryCosted_erase target occurrence⟩

/--
Payload-backed stored rank data.

The `StoredWordRankData` fields provide the operational read path and semantic
certificates.  This wrapper records that the stored words and rank samples are
decoded from the counted auxiliary payload rather than existing only as
proof-side fields.
-/
structure PayloadBackedStoredWordRankData
    (bits : List Bool) (overhead : Nat) where
  data : StoredWordRankData bits overhead
  payload : List Bool
  payload_eq_encodeAux : payload = data.encodeAux
  decodeWords : List Bool -> TableModel.IndexedSeq (List Bool)
  decodeTrueSamples : List Bool -> TableModel.IndexedSeq Nat
  decodeFalseSamples : List Bool -> TableModel.IndexedSeq Nat
  words_eq_decode : decodeWords payload = data.words
  trueSamples_eq_decode : decodeTrueSamples payload = data.trueSamples
  falseSamples_eq_decode : decodeFalseSamples payload = data.falseSamples

namespace PayloadBackedStoredWordRankData

theorem payload_length_eq
    {bits : List Bool} {overhead : Nat}
    (backed : PayloadBackedStoredWordRankData bits overhead) :
    backed.payload.length = overhead := by
  rw [backed.payload_eq_encodeAux]
  exact backed.data.aux_length_eq

theorem rankCosted_profile
    {bits : List Bool} {overhead : Nat}
    (backed : PayloadBackedStoredWordRankData bits overhead) :
    backed.payload.length = overhead /\
      backed.decodeWords backed.payload = backed.data.words /\
      backed.decodeTrueSamples backed.payload = backed.data.trueSamples /\
      backed.decodeFalseSamples backed.payload = backed.data.falseSamples /\
      forall target pos,
        (backed.data.rankCostedClamped target pos).cost <= 3 /\
          (backed.data.rankCostedClamped target pos).erase =
            Succinct.rankPrefix target bits pos := by
  constructor
  · exact backed.payload_length_eq
  · constructor
    · exact backed.words_eq_decode
    · constructor
      · exact backed.trueSamples_eq_decode
      · constructor
        · exact backed.falseSamples_eq_decode
        · intro target pos
          exact ⟨backed.data.rankCostedClamped_cost_le_three target pos,
            backed.data.rankCostedClamped_exact target pos⟩

end PayloadBackedStoredWordRankData

/--
Payload-backed stored select data, tying occurrence locators and payload words
to the counted auxiliary payload through explicit decoders.
-/
structure PayloadBackedStoredWordSelectData
    (bits : List Bool) (overhead : Nat) where
  data : StoredWordSelectData bits overhead
  payload : List Bool
  payload_eq_encodeAux : payload = data.encodeAux
  decodeWords : List Bool -> TableModel.IndexedSeq (List Bool)
  decodeTrueSamples :
    List Bool -> TableModel.IndexedSeq (Option StoredWordSelectSample)
  decodeFalseSamples :
    List Bool -> TableModel.IndexedSeq (Option StoredWordSelectSample)
  words_eq_decode : decodeWords payload = data.words
  trueSamples_eq_decode : decodeTrueSamples payload = data.trueSamples
  falseSamples_eq_decode : decodeFalseSamples payload = data.falseSamples

namespace PayloadBackedStoredWordSelectData

theorem payload_length_eq
    {bits : List Bool} {overhead : Nat}
    (backed : PayloadBackedStoredWordSelectData bits overhead) :
    backed.payload.length = overhead := by
  rw [backed.payload_eq_encodeAux]
  exact backed.data.aux_length_eq

theorem selectCosted_profile
    {bits : List Bool} {overhead : Nat}
    (backed : PayloadBackedStoredWordSelectData bits overhead) :
    backed.payload.length = overhead /\
      backed.decodeWords backed.payload = backed.data.words /\
      backed.decodeTrueSamples backed.payload = backed.data.trueSamples /\
      backed.decodeFalseSamples backed.payload = backed.data.falseSamples /\
      forall target occurrence,
        (backed.data.selectCosted target occurrence).cost <= 3 /\
          (backed.data.selectCosted target occurrence).erase =
            Succinct.select target bits occurrence := by
  constructor
  · exact backed.payload_length_eq
  · constructor
    · exact backed.words_eq_decode
    · constructor
      · exact backed.trueSamples_eq_decode
      · constructor
        · exact backed.falseSamples_eq_decode
        · intro target occurrence
          exact ⟨backed.data.selectCosted_cost_le_three target occurrence,
            backed.data.selectCosted_exact target occurrence⟩

end PayloadBackedStoredWordSelectData

/-- Payload-backed combined stored-word rank/select component. -/
structure PayloadBackedStoredWordRankSelectData
    (bits : List Bool) (rankOverhead selectOverhead : Nat) where
  rank : PayloadBackedStoredWordRankData bits rankOverhead
  select : PayloadBackedStoredWordSelectData bits selectOverhead

namespace PayloadBackedStoredWordRankSelectData

def payload
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData bits rankOverhead selectOverhead) :
    List Bool :=
  backed.rank.payload ++ backed.select.payload

def toRankSelectDirectory
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData bits rankOverhead selectOverhead) :
    RankSelectDirectory bits (rankOverhead + selectOverhead) 3 :=
  RankSelectDirectory.ofStoredWordData backed.rank.data backed.select.data

theorem payload_length_eq
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData bits rankOverhead selectOverhead) :
    backed.payload.length = rankOverhead + selectOverhead := by
  simp [payload, backed.rank.payload_length_eq,
    backed.select.payload_length_eq]

theorem directory_auxPayload_eq_payload
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData bits rankOverhead selectOverhead) :
    backed.toRankSelectDirectory.auxPayload = backed.payload := by
  simp [toRankSelectDirectory, RankSelectDirectory.ofStoredWordData,
    RankSelectDirectory.auxPayload, payload,
    ← backed.rank.payload_eq_encodeAux,
    ← backed.select.payload_eq_encodeAux]

theorem directory_profile
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData bits rankOverhead selectOverhead) :
    backed.payload.length = rankOverhead + selectOverhead /\
      backed.toRankSelectDirectory.auxPayload = backed.payload /\
      (forall target pos,
        (backed.toRankSelectDirectory.rankQueryCosted target pos).cost <= 3 /\
          (backed.toRankSelectDirectory.rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (backed.toRankSelectDirectory.selectQueryCosted target occurrence).cost <=
            3 /\
          (backed.toRankSelectDirectory.selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · exact backed.payload_length_eq
  · constructor
    · exact backed.directory_auxPayload_eq_payload
    · constructor
      · intro target pos
        exact ⟨backed.toRankSelectDirectory.rankQueryCosted_cost_le target pos,
          backed.toRankSelectDirectory.rankQueryCosted_erase target pos⟩
      · intro target occurrence
        exact ⟨
          backed.toRankSelectDirectory.selectQueryCosted_cost_le
            target occurrence,
          backed.toRankSelectDirectory.selectQueryCosted_erase
            target occurrence⟩

end PayloadBackedStoredWordRankSelectData

/-- Family of payload-backed stored-word rank/select components. -/
structure PayloadBackedStoredWordRankSelectFamily
    (rankOverhead selectOverhead : Nat -> Nat) where
  component :
    forall bits : List Bool,
      PayloadBackedStoredWordRankSelectData bits
        (rankOverhead bits.length) (selectOverhead bits.length)
  rank_littleO : LittleOLinear rankOverhead
  select_littleO : LittleOLinear selectOverhead

namespace PayloadBackedStoredWordRankSelectFamily

def overhead
    {rankOverhead selectOverhead : Nat -> Nat}
    (_family :
      PayloadBackedStoredWordRankSelectFamily rankOverhead selectOverhead) :
    Nat -> Nat :=
  fun n => rankOverhead n + selectOverhead n

theorem overhead_littleO
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadBackedStoredWordRankSelectFamily rankOverhead selectOverhead) :
    LittleOLinear family.overhead := by
  exact family.rank_littleO.add family.select_littleO

def toRankSelectFamily
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadBackedStoredWordRankSelectFamily rankOverhead selectOverhead) :
    RankSelectFamily family.overhead 3 where
  directory bits := (family.component bits).toRankSelectDirectory
  overhead_littleO := family.overhead_littleO

theorem constant_query_profile
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadBackedStoredWordRankSelectFamily rankOverhead selectOverhead) :
    LittleOLinear family.overhead /\
      forall bits : List Bool,
        ((family.component bits).payload.length =
          rankOverhead bits.length + selectOverhead bits.length) /\
          (((family.toRankSelectFamily).directory bits).auxPayload =
            (family.component bits).payload) /\
          (forall target pos,
            (((family.toRankSelectFamily).directory bits).rankQueryCosted
                target pos).cost <= 3 /\
              (((family.toRankSelectFamily).directory bits).rankQueryCosted
                target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (((family.toRankSelectFamily).directory bits).selectQueryCosted
                target occurrence).cost <= 3 /\
              (((family.toRankSelectFamily).directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    have hprofile := (family.component bits).directory_profile
    exact hprofile

end PayloadBackedStoredWordRankSelectFamily

end SuccinctSpace

end RMQ
