import RMQ.Core.SuccinctSelect.TwoLevel.ClarkSource

/-!
# Payload-live two-level select data

Split implementation layer for two-level select and rank/select helpers.
Public declarations stay in the historical `RMQ.SuccinctSelect`
namespace.
-/

namespace RMQ
namespace SuccinctSelect
open SuccinctSpace

/-!
## Two-level select target

The older sampled wrapper below is useful migration scaffolding, but the final
word-RAM select story needs the same discipline as the rank side: payload words
must be machine-word bounded, and the query must be forced through counted
coarse-locator, local-delta, payload-word, and word-select operations.
-/

structure TwoLevelPayloadLiveStoredWordSelectData
    (bits : List Bool)
    (superOverhead blockOverhead queryCost : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  wordSize_le_machine :
    wordSize <= SuccinctRank.machineWordBits bits.length
  occurrencesPerSuper : Nat
  occurrencesPerSuper_pos : 0 < occurrencesPerSuper
  /--
  Address used for the local locator table.  This is deliberately independent
  of the queried occurrence, so a concrete dense/sparse select codec is not
  forced to materialize one local table word at every occurrence index.
  -/
  blockIndex : Bool -> Nat -> Nat
  superFieldWidth : Nat
  blockFieldWidth : Nat
  superTrueEntries :
    List (Option SuccinctSpace.StoredWordSelectSample)
  superFalseEntries :
    List (Option SuccinctSpace.StoredWordSelectSample)
  blockTrueEntries :
    List (Option SuccinctSpace.StoredWordSelectSample)
  blockFalseEntries :
    List (Option SuccinctSpace.StoredWordSelectSample)
  superTables :
    SuccinctSpace.FixedWidthSelectSampleTables
      superTrueEntries superFalseEntries superFieldWidth
  blockTables :
    SuccinctSpace.FixedWidthSelectSampleTables
      blockTrueEntries blockFalseEntries blockFieldWidth
  bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize
  superPayload_length : superTables.payload.length = superOverhead
  blockPayload_length : blockTables.payload.length = blockOverhead
  queryCost_ge_four : 4 <= queryCost
  super_entry_present :
    forall (target : Bool) (occurrence : Nat),
      occurrence <= bits.length ->
      exists entry : Option SuccinctSpace.StoredWordSelectSample,
        (superTables.entries target)[occurrence / occurrencesPerSuper]? =
          some entry
  block_entry_present :
    forall (target : Bool) (occurrence : Nat),
      occurrence <= bits.length ->
      exists entry : Option SuccinctSpace.StoredWordSelectSample,
        (blockTables.entries target)[blockIndex target occurrence]? =
          some entry
  word_present_of_sample :
    forall (target : Bool) (occurrence : Nat)
        (super delta : SuccinctSpace.StoredWordSelectSample),
      occurrence <= bits.length ->
      (superTables.entries target)[occurrence / occurrencesPerSuper]? =
          some (some super) ->
      (blockTables.entries target)[blockIndex target occurrence]? =
          some (some delta) ->
        exists word,
          bitWords.store.words[(addSelectSample super delta).wordIndex]? =
            some word
  select_some_exact :
    forall (target : Bool) (occurrence : Nat)
        (super delta : SuccinctSpace.StoredWordSelectSample)
        (word : List Bool),
      occurrence <= bits.length ->
      (superTables.entries target)[occurrence / occurrencesPerSuper]? =
          some (some super) ->
      (blockTables.entries target)[blockIndex target occurrence]? =
          some (some delta) ->
      bitWords.store.words[(addSelectSample super delta).wordIndex]? =
          some word ->
        (RMQ.RAM.boolSelectInWord target word
            (occurrence - (addSelectSample super delta).rankBefore)).map
            (fun offset =>
              (addSelectSample super delta).wordStart + offset) =
          RMQ.Succinct.select target bits occurrence
  select_none_exact_of_super :
    forall (target : Bool) (occurrence : Nat),
      occurrence <= bits.length ->
      (superTables.entries target)[occurrence / occurrencesPerSuper]? =
          some (none : Option SuccinctSpace.StoredWordSelectSample) ->
        RMQ.Succinct.select target bits occurrence = none
  select_none_exact_of_block :
    forall (target : Bool) (occurrence : Nat)
        (super : SuccinctSpace.StoredWordSelectSample),
      occurrence <= bits.length ->
      (superTables.entries target)[occurrence / occurrencesPerSuper]? =
          some (some super) ->
      (blockTables.entries target)[blockIndex target occurrence]? =
          some (none : Option SuccinctSpace.StoredWordSelectSample) ->
        RMQ.Succinct.select target bits occurrence = none

namespace TwoLevelPayloadLiveStoredWordSelectData

def queryOccurrence
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (_data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (occurrence : Nat) : Nat :=
  Nat.min occurrence bits.length

def superIndex
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (occurrence : Nat) : Nat :=
  data.queryOccurrence occurrence / data.occurrencesPerSuper

def superPayload
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost) :
    List Bool :=
  data.superTables.payload

def blockPayload
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost) :
    List Bool :=
  data.blockTables.payload

def auxPayload
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost) :
    List Bool :=
  data.superPayload ++ data.blockPayload

def selectCosted
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (occurrence : Nat) :
    RMQ.Costed (Option Nat) :=
  RMQ.Costed.bind
    (data.superTables.sampleCosted target (data.superIndex occurrence))
    fun super? =>
      RMQ.Costed.bind
        (data.blockTables.sampleCosted target
          (data.blockIndex target (data.queryOccurrence occurrence)))
        fun delta? =>
          match super?, delta? with
          | some (some super), some (some delta) =>
              let sample := addSelectSample super delta
              RMQ.Costed.bind
                (data.bitWords.store.readWordCosted sample.wordIndex)
                fun word? =>
                  match word? with
                  | none => RMQ.Costed.pure none
                  | some word =>
                      RMQ.Costed.map
                        (fun (local? : Option Nat) =>
                          local?.map fun offset =>
                            sample.wordStart + offset)
                        (RMQ.RAM.selectBoolWord target word
                          (data.queryOccurrence occurrence -
                            sample.rankBefore)).toCosted
          | _, _ => RMQ.Costed.pure none

theorem auxPayload_length
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost) :
    data.auxPayload.length = superOverhead + blockOverhead := by
  simp [auxPayload, superPayload, blockPayload,
    data.superPayload_length, data.blockPayload_length]

theorem payload_words_erase
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost) :
    SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        bits := by
  exact data.bitWords.erases

set_option linter.unusedSimpArgs false in
theorem selectCosted_cost_le_four
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= 4 := by
  unfold selectCosted
  cases hsuper :
      (data.superTables.sampleCosted
        target (data.superIndex occurrence)).value <;>
    cases hdelta :
      (data.blockTables.sampleCosted
        target (data.blockIndex target
          (data.queryOccurrence occurrence))).value <;>
    try
      simp [RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
        hsuper, hdelta]
  case some.some superEntry deltaEntry =>
    cases superEntry <;> cases deltaEntry <;>
      try
        simp [RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
          hsuper, hdelta]
    case some.some super delta =>
      cases hword :
          (data.bitWords.store.readWordCosted
            (addSelectSample super delta).wordIndex).value <;>
        simp [RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
          hsuper, hdelta, hword]

theorem selectCosted_cost_le
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= queryCost := by
  exact Nat.le_trans
    (data.selectCosted_cost_le_four target occurrence)
    data.queryCost_ge_four

theorem selectCosted_exact
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      RMQ.Succinct.select target bits occurrence := by
  have hq : data.queryOccurrence occurrence <= bits.length := by
    exact Nat.min_le_right occurrence bits.length
  have hclamp :
      RMQ.Succinct.select target bits (data.queryOccurrence occurrence) =
        RMQ.Succinct.select target bits occurrence := by
    unfold queryOccurrence
    exact RMQ.Succinct.select_min_length_eq target bits occurrence
  rcases data.super_entry_present
      target (data.queryOccurrence occurrence) hq with
    ⟨superEntry, hsuper⟩
  rcases data.block_entry_present
      target (data.queryOccurrence occurrence) hq with
    ⟨deltaEntry, hdelta⟩
  have hsuperValue :
      (data.superTables.sampleCosted
        target (data.superIndex occurrence)).value = some superEntry := by
    have h :=
      data.superTables.sampleCosted_erase
        target (data.superIndex occurrence)
    change
      (data.superTables.sampleCosted
        target (data.superIndex occurrence)).value =
          (data.superTables.entries target)[data.superIndex occurrence]? at h
    rw [show data.superIndex occurrence =
        data.queryOccurrence occurrence / data.occurrencesPerSuper by rfl] at h
    rw [hsuper] at h
    exact h
  have hdeltaValue :
      (data.blockTables.sampleCosted
        target (data.blockIndex target
          (data.queryOccurrence occurrence))).value =
        some deltaEntry := by
    have h :=
      data.blockTables.sampleCosted_erase
        target (data.blockIndex target
          (data.queryOccurrence occurrence))
    change
      (data.blockTables.sampleCosted
        target (data.blockIndex target
          (data.queryOccurrence occurrence))).value =
        (data.blockTables.entries target)[
          data.blockIndex target (data.queryOccurrence occurrence)]? at h
    rw [hdelta] at h
    exact h
  cases superEntry with
  | none =>
      have hnoneQ :=
        data.select_none_exact_of_super
          target (data.queryOccurrence occurrence) hq hsuper
      have hnone :
          RMQ.Succinct.select target bits occurrence = none := by
        exact hclamp ▸ hnoneQ
      unfold selectCosted
      simp [RMQ.Costed.bind, RMQ.Costed.pure, RMQ.Costed.erase,
        hsuperValue, hdeltaValue, hnone]
  | some super =>
      cases deltaEntry with
      | none =>
          have hnoneQ :=
            data.select_none_exact_of_block
              target (data.queryOccurrence occurrence) super
              hq hsuper hdelta
          have hnone :
              RMQ.Succinct.select target bits occurrence = none := by
            exact hclamp ▸ hnoneQ
          unfold selectCosted
          simp [RMQ.Costed.bind, RMQ.Costed.pure, RMQ.Costed.erase,
            hsuperValue, hdeltaValue, hnone]
      | some delta =>
          rcases data.word_present_of_sample
              target (data.queryOccurrence occurrence) super delta
              hq hsuper hdelta with
            ⟨word, hword⟩
          have hwordValue :
              (data.bitWords.store.readWordCosted
                (addSelectSample super delta).wordIndex).value =
                  some word := by
            have hread :=
              data.bitWords.store.readWordCosted_erase
                (addSelectSample super delta).wordIndex
            change
              (data.bitWords.store.readWordCosted
                (addSelectSample super delta).wordIndex).value =
                  data.bitWords.store.words[
                    (addSelectSample super delta).wordIndex]? at hread
            rw [hword] at hread
            exact hread
          have hexact :=
            data.select_some_exact
              target (data.queryOccurrence occurrence) super delta word
              hq hsuper hdelta hword
          unfold selectCosted
          simp [RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
            RMQ.Costed.erase, hsuperValue, hdeltaValue, hwordValue,
            hexact, hclamp]

theorem selected_position_in_read_word_of_sample
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    {target : Bool} {occurrence pos : Nat}
    {super delta : SuccinctSpace.StoredWordSelectSample}
    {word : List Bool}
    (hocc : occurrence <= bits.length)
    (hsuper :
      (data.superTables.entries target)[occurrence / data.occurrencesPerSuper]? =
        some (some super))
    (hdelta :
      (data.blockTables.entries target)[data.blockIndex target occurrence]? =
        some (some delta))
    (hword :
      data.bitWords.store.words[(addSelectSample super delta).wordIndex]? =
        some word)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos) :
    (addSelectSample super delta).wordStart <= pos /\
      pos < (addSelectSample super delta).wordStart + word.length := by
  have hexact :
      SelectSampleWordExact target bits occurrence
        (addSelectSample super delta) word :=
    data.select_some_exact target occurrence super delta word
      hocc hsuper hdelta hword
  exact
    SelectSampleWordExact.selected_position_in_read_word
      hexact hselect

theorem selected_wordIndex_eq_of_sample
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    {target : Bool} {occurrence pos : Nat}
    {super delta : SuccinctSpace.StoredWordSelectSample}
    {word : List Bool}
    (hocc : occurrence <= bits.length)
    (hsuper :
      (data.superTables.entries target)[occurrence / data.occurrencesPerSuper]? =
        some (some super))
    (hdelta :
      (data.blockTables.entries target)[data.blockIndex target occurrence]? =
        some (some delta))
    (hword :
      data.bitWords.store.words[(addSelectSample super delta).wordIndex]? =
        some word)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hstart :
      (addSelectSample super delta).wordStart =
        (addSelectSample super delta).wordIndex * data.wordSize) :
    pos / data.wordSize = (addSelectSample super delta).wordIndex := by
  have hexact :
      SelectSampleWordExact target bits occurrence
        (addSelectSample super delta) word :=
    data.select_some_exact target occurrence super delta word
      hocc hsuper hdelta hword
  have hlist :
      data.bitWords.store.words.toList[
          (addSelectSample super delta).wordIndex]? = some word := by
    simpa [Array.getElem?_toList] using hword
  have hwordLen : word.length <= data.wordSize :=
    data.bitWords.word_length_le (List.mem_of_getElem? hlist)
  exact
    SelectSampleWordExact.selected_wordIndex_eq_of_aligned_read_word
      data.wordSize_pos hexact hselect hstart hwordLen

/--
If the two-level select query reads the same super locator, the same local
locator, and therefore the same aligned payload word for two successful
occurrences, both selected positions must lie in the same payload chunk.

Consequently a compact descriptor that shares one local entry across a sampled
run must read charged descriptor payload that can choose the final payload word;
the current shared-aligned-locator path cannot be the witness.
-/
theorem shared_local_locator_forces_same_selected_wordIndex
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    {target : Bool} {occurrenceA occurrenceB posA posB : Nat}
    {super delta : SuccinctSpace.StoredWordSelectSample}
    {word : List Bool}
    (hoccA : occurrenceA <= bits.length)
    (hoccB : occurrenceB <= bits.length)
    (hsuperA :
      (data.superTables.entries target)[
          occurrenceA / data.occurrencesPerSuper]? =
        some (some super))
    (hsuperB :
      (data.superTables.entries target)[
          occurrenceB / data.occurrencesPerSuper]? =
        some (some super))
    (hdeltaA :
      (data.blockTables.entries target)[
          data.blockIndex target occurrenceA]? =
        some (some delta))
    (hdeltaB :
      (data.blockTables.entries target)[
          data.blockIndex target occurrenceB]? =
        some (some delta))
    (hword :
      data.bitWords.store.words[(addSelectSample super delta).wordIndex]? =
        some word)
    (hselectA :
      RMQ.Succinct.select target bits occurrenceA = some posA)
    (hselectB :
      RMQ.Succinct.select target bits occurrenceB = some posB)
    (hstart :
      (addSelectSample super delta).wordStart =
        (addSelectSample super delta).wordIndex * data.wordSize) :
    posA / data.wordSize = posB / data.wordSize := by
  have hA :
      posA / data.wordSize =
        (addSelectSample super delta).wordIndex :=
    data.selected_wordIndex_eq_of_sample
      hoccA hsuperA hdeltaA hword hselectA hstart
  have hB :
      posB / data.wordSize =
        (addSelectSample super delta).wordIndex :=
    data.selected_wordIndex_eq_of_sample
      hoccB hsuperB hdeltaB hword hselectB hstart
  exact hA.trans hB.symm

theorem shared_local_locator_contradicts_distinct_selected_wordIndex
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    {target : Bool} {occurrenceA occurrenceB posA posB : Nat}
    {super delta : SuccinctSpace.StoredWordSelectSample}
    {word : List Bool}
    (hoccA : occurrenceA <= bits.length)
    (hoccB : occurrenceB <= bits.length)
    (hsuperA :
      (data.superTables.entries target)[
          occurrenceA / data.occurrencesPerSuper]? =
        some (some super))
    (hsuperB :
      (data.superTables.entries target)[
          occurrenceB / data.occurrencesPerSuper]? =
        some (some super))
    (hdeltaA :
      (data.blockTables.entries target)[
          data.blockIndex target occurrenceA]? =
        some (some delta))
    (hdeltaB :
      (data.blockTables.entries target)[
          data.blockIndex target occurrenceB]? =
        some (some delta))
    (hword :
      data.bitWords.store.words[(addSelectSample super delta).wordIndex]? =
        some word)
    (hselectA :
      RMQ.Succinct.select target bits occurrenceA = some posA)
    (hselectB :
      RMQ.Succinct.select target bits occurrenceB = some posB)
    (hstart :
      (addSelectSample super delta).wordStart =
        (addSelectSample super delta).wordIndex * data.wordSize)
    (hdistinct :
      posA / data.wordSize = posB / data.wordSize -> False) :
    False := by
  exact hdistinct
    (data.shared_local_locator_forces_same_selected_wordIndex
      hoccA hoccB hsuperA hsuperB hdeltaA hdeltaB hword
      hselectA hselectB hstart)

theorem payload_word_length_le_machine
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    {word : List Bool}
    (hmem : List.Mem word data.bitWords.store.words.toList) :
    word.length <= SuccinctRank.machineWordBits bits.length := by
  exact Nat.le_trans
    (data.bitWords.word_length_le hmem)
    data.wordSize_le_machine

theorem profile
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost) :
    data.auxPayload.length = superOverhead + blockOverhead /\
      data.wordSize <= SuccinctRank.machineWordBits bits.length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        bits /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <= SuccinctRank.machineWordBits bits.length) /\
      forall target occurrence,
        (data.selectCosted target occurrence).cost <= queryCost /\
          (data.selectCosted target occurrence).erase =
            RMQ.Succinct.select target bits occurrence := by
  constructor
  · exact data.auxPayload_length
  · constructor
    · exact data.wordSize_le_machine
    · constructor
      · exact data.payload_words_erase
      · constructor
        · intro word hmem
          exact data.payload_word_length_le_machine hmem
        · intro target occurrence
          exact ⟨data.selectCosted_cost_le target occurrence,
            data.selectCosted_exact target occurrence⟩

end TwoLevelPayloadLiveStoredWordSelectData

def canonicalTwoLevelSelectData
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (hquery : 4 <= queryCost)
    (bridge :
      CanonicalSelectWordBridge bits wordSize occurrencesPerSuper bitWords) :
    TwoLevelPayloadLiveStoredWordSelectData bits
      ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper superFieldWidth
          hsuperBits).payload.length)
      ((canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper blockFieldWidth
          hblockBits).payload.length)
      queryCost where
  wordSize := wordSize
  wordSize_pos := hwordSize
  wordSize_le_machine := hwordMachine
  occurrencesPerSuper := occurrencesPerSuper
  occurrencesPerSuper_pos := hoccurrences
  blockIndex := fun _ occurrence => occurrence
  superFieldWidth := superFieldWidth
  blockFieldWidth := blockFieldWidth
  superTrueEntries :=
    selectSuperSampleEntries true bits wordSize occurrencesPerSuper
      (canonicalSelectSuperCount bits occurrencesPerSuper)
  superFalseEntries :=
    selectSuperSampleEntries false bits wordSize occurrencesPerSuper
      (canonicalSelectSuperCount bits occurrencesPerSuper)
  blockTrueEntries :=
    selectBlockDeltaEntries true bits wordSize occurrencesPerSuper
      (canonicalSelectBlockCount bits)
  blockFalseEntries :=
    selectBlockDeltaEntries false bits wordSize occurrencesPerSuper
      (canonicalSelectBlockCount bits)
  superTables :=
    canonicalSelectSuperTablesFinite
      bits wordSize occurrencesPerSuper superFieldWidth hsuperBits
  blockTables :=
    canonicalSelectBlockTablesFinite
      bits wordSize occurrencesPerSuper blockFieldWidth hblockBits
  bitWords := bitWords
  superPayload_length := rfl
  blockPayload_length := rfl
  queryCost_ge_four := hquery
  super_entry_present := by
    intro target occurrence hocc
    exact canonicalSelectSuperTablesFinite_present
      (bits := bits) (wordSize := wordSize)
      (occurrencesPerSuper := occurrencesPerSuper)
      (fieldWidth := superFieldWidth) hsuperBits target hocc
  block_entry_present := by
    intro target occurrence hocc
    exact canonicalSelectBlockTablesFinite_present
      (bits := bits) (wordSize := wordSize)
      (occurrencesPerSuper := occurrencesPerSuper)
      (fieldWidth := blockFieldWidth) hblockBits target hocc
  word_present_of_sample := by
    intro target occurrence super delta hocc hsuper hdelta
    have hbase :
        selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
          (occurrence / occurrencesPerSuper) = some super := by
      exact
        (canonicalSelectSuperTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := superFieldWidth)
          (i := occurrence / occurrencesPerSuper)
          (target := target) (entry := some super)
          (hbits := hsuperBits) hsuper).symm
    have hblock :
        selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
          occurrence = some delta := by
      exact
        (canonicalSelectBlockTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := blockFieldWidth)
          (occurrence := occurrence)
          (target := target) (entry := some delta)
          (hbits := hblockBits) hdelta).symm
    rcases
        selectBlockDeltaEntry?_some_fields_of_super hbase hblock with
      ⟨exact, hexact, _hdeltaEq⟩
    rcases bridge.sample_ordered
        target occurrence super exact hocc hbase hexact with
      ⟨hwordIndex, hwordStart, hrankBefore⟩
    have hadd :
        addSelectSample super delta = exact :=
      selectBlockDeltaEntry?_add_exact_of_le hbase hexact hblock
        hwordIndex hwordStart hrankBefore
    rcases bridge.word_present
        target occurrence exact hocc hexact with
      ⟨word, hword⟩
    exact Exists.intro word (by simpa [hadd] using hword)
  select_some_exact := by
    intro target occurrence super delta word hocc hsuper hdelta hword
    have hbase :
        selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
          (occurrence / occurrencesPerSuper) = some super := by
      exact
        (canonicalSelectSuperTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := superFieldWidth)
          (i := occurrence / occurrencesPerSuper)
          (target := target) (entry := some super)
          (hbits := hsuperBits) hsuper).symm
    have hblock :
        selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
          occurrence = some delta := by
      exact
        (canonicalSelectBlockTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := blockFieldWidth)
          (occurrence := occurrence)
          (target := target) (entry := some delta)
          (hbits := hblockBits) hdelta).symm
    rcases
        selectBlockDeltaEntry?_some_fields_of_super hbase hblock with
      ⟨exact, hexact, _hdeltaEq⟩
    rcases bridge.sample_ordered
        target occurrence super exact hocc hbase hexact with
      ⟨hwordIndex, hwordStart, hrankBefore⟩
    have hadd :
        addSelectSample super delta = exact :=
      selectBlockDeltaEntry?_add_exact_of_le hbase hexact hblock
        hwordIndex hwordStart hrankBefore
    have hwordExactIndex :
        bitWords.store.words[exact.wordIndex]? = some word := by
      simpa [hadd] using hword
    have hwordExact :
        SelectSampleWordExact target bits occurrence exact word :=
      bridge.word_exact
        target occurrence exact word hocc hexact hwordExactIndex
    exact
      selectBlockDeltaEntry?_select_some_exact_of_word
        hbase hexact hblock hwordIndex hwordStart hrankBefore hwordExact
  select_none_exact_of_super := by
    intro target occurrence hocc hsuper
    have hentry :
        selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
          (occurrence / occurrencesPerSuper) = none := by
      exact
        (canonicalSelectSuperTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := superFieldWidth)
          (i := occurrence / occurrencesPerSuper)
          (target := target)
          (entry := (none :
            Option SuccinctSpace.StoredWordSelectSample))
          (hbits := hsuperBits) hsuper).symm
    exact selectSuperSampleEntry?_none_exact_of_occurrence hentry
  select_none_exact_of_block := by
    intro target occurrence super hocc hsuper hdelta
    have hbase :
        selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
          (occurrence / occurrencesPerSuper) = some super := by
      exact
        (canonicalSelectSuperTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := superFieldWidth)
          (i := occurrence / occurrencesPerSuper)
          (target := target) (entry := some super)
          (hbits := hsuperBits) hsuper).symm
    have hblock :
        selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
          occurrence = none := by
      exact
        (canonicalSelectBlockTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := blockFieldWidth)
          (occurrence := occurrence)
          (target := target)
          (entry := (none :
            Option SuccinctSpace.StoredWordSelectSample))
          (hbits := hblockBits) hdelta).symm
    exact selectBlockDeltaEntry?_none_exact_of_super hbase hblock

theorem canonicalTwoLevelSelectData_selectCosted_profile
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (hquery : 4 <= queryCost)
    (bridge :
      CanonicalSelectWordBridge bits wordSize occurrencesPerSuper bitWords)
    (target : Bool) (occurrence : Nat) :
    ((canonicalTwoLevelSelectData bits hwordSize hwordMachine hoccurrences
        hsuperBits hblockBits bitWords hquery bridge).selectCosted
        target occurrence).cost <= queryCost /\
      ((canonicalTwoLevelSelectData bits hwordSize hwordMachine hoccurrences
        hsuperBits hblockBits bitWords hquery bridge).selectCosted
        target occurrence).erase =
        RMQ.Succinct.select target bits occurrence := by
  let data :=
    canonicalTwoLevelSelectData bits hwordSize hwordMachine hoccurrences
      hsuperBits hblockBits bitWords hquery bridge
  exact And.intro
    (data.selectCosted_cost_le target occurrence)
    (data.selectCosted_exact target occurrence)

def canonicalTwoLevelSelectDataOfLocal
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (hquery : 4 <= queryCost)
    (hwordPresent :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
          exists word,
            bitWords.store.words[exact.wordIndex]? = some word)
    (hwordExact :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample) (word : List Bool),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
        bitWords.store.words[exact.wordIndex]? = some word ->
          SelectSampleWordExact target bits occurrence exact word) :
    TwoLevelPayloadLiveStoredWordSelectData bits
      ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper superFieldWidth
          hsuperBits).payload.length)
      ((canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper blockFieldWidth
          hblockBits).payload.length)
      queryCost :=
  canonicalTwoLevelSelectData bits hwordSize hwordMachine hoccurrences
    hsuperBits hblockBits bitWords hquery
    (CanonicalSelectWordBridge.ofLocal hwordPresent hwordExact)

theorem canonicalTwoLevelSelectDataOfLocal_selectCosted_profile
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (hquery : 4 <= queryCost)
    (hwordPresent :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
          exists word,
            bitWords.store.words[exact.wordIndex]? = some word)
    (hwordExact :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample) (word : List Bool),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
        bitWords.store.words[exact.wordIndex]? = some word ->
          SelectSampleWordExact target bits occurrence exact word)
    (target : Bool) (occurrence : Nat) :
    ((canonicalTwoLevelSelectDataOfLocal bits hwordSize hwordMachine
        hoccurrences hsuperBits hblockBits bitWords hquery
        hwordPresent hwordExact).selectCosted target occurrence).cost <=
        queryCost /\
      ((canonicalTwoLevelSelectDataOfLocal bits hwordSize hwordMachine
        hoccurrences hsuperBits hblockBits bitWords hquery
        hwordPresent hwordExact).selectCosted target occurrence).erase =
        RMQ.Succinct.select target bits occurrence := by
  exact
    canonicalTwoLevelSelectData_selectCosted_profile bits hwordSize
      hwordMachine hoccurrences hsuperBits hblockBits bitWords hquery
      (CanonicalSelectWordBridge.ofLocal hwordPresent hwordExact)
      target occurrence

def canonicalTwoLevelSelectDataOfChunks
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (hquery : 4 <= queryCost)
    (hwordExact :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample) (word : List Bool),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
        (SuccinctSpace.BoundedPayloadWordStore.ofChunks
            bits hwordSize).store.words[exact.wordIndex]? = some word ->
          SelectSampleWordExact target bits occurrence exact word) :
    TwoLevelPayloadLiveStoredWordSelectData bits
      ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper superFieldWidth
          hsuperBits).payload.length)
      ((canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper blockFieldWidth
          hblockBits).payload.length)
      queryCost :=
  canonicalTwoLevelSelectData bits hwordSize hwordMachine hoccurrences
    hsuperBits hblockBits
    (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hwordSize)
    hquery
    (CanonicalSelectWordBridge.ofChunks hwordSize hwordExact)

theorem canonicalTwoLevelSelectDataOfChunks_selectCosted_profile
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (hquery : 4 <= queryCost)
    (hwordExact :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample) (word : List Bool),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
        (SuccinctSpace.BoundedPayloadWordStore.ofChunks
            bits hwordSize).store.words[exact.wordIndex]? = some word ->
          SelectSampleWordExact target bits occurrence exact word)
    (target : Bool) (occurrence : Nat) :
    ((canonicalTwoLevelSelectDataOfChunks bits hwordSize hwordMachine
        hoccurrences hsuperBits hblockBits hquery hwordExact).selectCosted
        target occurrence).cost <= queryCost /\
      ((canonicalTwoLevelSelectDataOfChunks bits hwordSize hwordMachine
        hoccurrences hsuperBits hblockBits hquery hwordExact).selectCosted
        target occurrence).erase =
        RMQ.Succinct.select target bits occurrence := by
  exact
    canonicalTwoLevelSelectData_selectCosted_profile bits hwordSize
      hwordMachine hoccurrences hsuperBits hblockBits
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hwordSize)
      hquery (CanonicalSelectWordBridge.ofChunks hwordSize hwordExact)
      target occurrence

def canonicalTwoLevelSelectDataOfChunksExact
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (hquery : 4 <= queryCost) :
    TwoLevelPayloadLiveStoredWordSelectData bits
      ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper superFieldWidth
          hsuperBits).payload.length)
      ((canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper blockFieldWidth
          hblockBits).payload.length)
      queryCost :=
  canonicalTwoLevelSelectData bits hwordSize hwordMachine hoccurrences
    hsuperBits hblockBits
    (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hwordSize)
    hquery
    (CanonicalSelectWordBridge.ofChunksExact hwordSize)

theorem canonicalTwoLevelSelectDataOfChunksExact_selectCosted_profile
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (hquery : 4 <= queryCost)
    (target : Bool) (occurrence : Nat) :
    ((canonicalTwoLevelSelectDataOfChunksExact bits hwordSize hwordMachine
        hoccurrences hsuperBits hblockBits hquery).selectCosted
        target occurrence).cost <= queryCost /\
      ((canonicalTwoLevelSelectDataOfChunksExact bits hwordSize hwordMachine
        hoccurrences hsuperBits hblockBits hquery).selectCosted
        target occurrence).erase =
        RMQ.Succinct.select target bits occurrence := by
  exact
    canonicalTwoLevelSelectData_selectCosted_profile bits hwordSize
      hwordMachine hoccurrences hsuperBits hblockBits
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hwordSize)
      hquery (CanonicalSelectWordBridge.ofChunksExact hwordSize)
      target occurrence

structure TwoLevelPayloadLiveStoredWordSelectFamily
    (super block : Nat -> Nat) (queryCost : Nat) where
  component :
    forall bits : List Bool,
      TwoLevelPayloadLiveStoredWordSelectData
        bits (super bits.length) (block bits.length) queryCost
  super_littleO : SuccinctSpace.LittleOLinear super
  block_littleO : SuccinctSpace.LittleOLinear block

namespace TwoLevelPayloadLiveStoredWordSelectFamily

def overhead
    {super block : Nat -> Nat} {queryCost : Nat}
    (_family :
      TwoLevelPayloadLiveStoredWordSelectFamily
        super block queryCost) : Nat -> Nat :=
  twoLevelSelectOverhead super block

theorem overhead_littleO
    {super block : Nat -> Nat} {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordSelectFamily
        super block queryCost) :
    SuccinctSpace.LittleOLinear family.overhead := by
  exact
    twoLevelSelectOverhead_littleO
      family.super_littleO family.block_littleO

theorem constant_query_profile
    {super block : Nat -> Nat} {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordSelectFamily
        super block queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall bits : List Bool,
        ((family.component bits).auxPayload.length =
          family.overhead bits.length) /\
        ((family.component bits).wordSize <=
          SuccinctRank.machineWordBits bits.length) /\
        SuccinctSpace.flattenPayloadWords
            (family.component bits).bitWords.store.words.toList = bits /\
        (forall {word : List Bool},
          List.Mem word
              (family.component bits).bitWords.store.words.toList ->
            word.length <=
              SuccinctRank.machineWordBits bits.length) /\
        forall target occurrence,
          ((family.component bits).selectCosted target occurrence).cost <=
              queryCost /\
            ((family.component bits).selectCosted target occurrence).erase =
              RMQ.Succinct.select target bits occurrence := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    exact (family.component bits).profile

end TwoLevelPayloadLiveStoredWordSelectFamily

end SuccinctSelect
end RMQ

