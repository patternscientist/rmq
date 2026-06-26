import RMQ.Core.SuccinctSelect

/-!
Archived select-side obstruction witnesses.

The old four-field `SparseDenseFalseSelectCloseData` locator island has been
physically pruned. This archive keeps only the smaller obstruction witnesses
that are still useful design evidence for why a shared sampled locator cannot
serve all constant-time select queries.
-/

namespace RMQ.Archive.SelectObstructions

theorem shared_aligned_read_word_forces_same_wordIndex
    {target : Bool} {bits word : List Bool}
    {occurrenceA occurrenceB posA posB wordSize : Nat}
    {sample : SuccinctSpace.StoredWordSelectSample}
    (hwordSize : 0 < wordSize)
    (hexactA :
      RMQ.SuccinctSelect.SelectSampleWordExact
        target bits occurrenceA sample word)
    (hexactB :
      RMQ.SuccinctSelect.SelectSampleWordExact
        target bits occurrenceB sample word)
    (hselectA : RMQ.Succinct.select target bits occurrenceA = some posA)
    (hselectB : RMQ.Succinct.select target bits occurrenceB = some posB)
    (hstart : sample.wordStart = sample.wordIndex * wordSize)
    (hwordLen : word.length <= wordSize) :
    posA / wordSize = posB / wordSize :=
  RMQ.SuccinctSelect.SelectSampleWordExact.shared_aligned_read_word_forces_same_wordIndex
    hwordSize hexactA hexactB hselectA hselectB hstart hwordLen

theorem shared_local_locator_forces_same_selected_wordIndex
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      RMQ.SuccinctSelect.TwoLevelPayloadLiveStoredWordSelectData
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
      data.bitWords.store.words[(RMQ.SuccinctSelect.addSelectSample
          super delta).wordIndex]? =
        some word)
    (hselectA :
      RMQ.Succinct.select target bits occurrenceA = some posA)
    (hselectB :
      RMQ.Succinct.select target bits occurrenceB = some posB)
    (hstart :
      (RMQ.SuccinctSelect.addSelectSample super delta).wordStart =
        (RMQ.SuccinctSelect.addSelectSample super delta).wordIndex *
          data.wordSize) :
    posA / data.wordSize = posB / data.wordSize :=
  data.shared_local_locator_forces_same_selected_wordIndex
    hoccA hoccB hsuperA hsuperB hdeltaA hdeltaB hword
    hselectA hselectB hstart

theorem shared_local_locator_contradicts_distinct_selected_wordIndex
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      RMQ.SuccinctSelect.TwoLevelPayloadLiveStoredWordSelectData
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
      data.bitWords.store.words[(RMQ.SuccinctSelect.addSelectSample
          super delta).wordIndex]? =
        some word)
    (hselectA :
      RMQ.Succinct.select target bits occurrenceA = some posA)
    (hselectB :
      RMQ.Succinct.select target bits occurrenceB = some posB)
    (hstart :
      (RMQ.SuccinctSelect.addSelectSample super delta).wordStart =
        (RMQ.SuccinctSelect.addSelectSample super delta).wordIndex *
          data.wordSize)
    (hdistinct :
      posA / data.wordSize = posB / data.wordSize -> False) :
    False :=
  data.shared_local_locator_contradicts_distinct_selected_wordIndex
    hoccA hoccB hsuperA hsuperB hdeltaA hdeltaB hword
    hselectA hselectB hstart hdistinct

end RMQ.Archive.SelectObstructions
