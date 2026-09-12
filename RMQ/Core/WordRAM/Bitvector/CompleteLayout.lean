import RMQ.Core.WordRAM.Bitvector.CompleteReadStore
import RMQ.Core.WordRAM.Bitvector.RankLayout
import RMQ.Core.WordRAM.Bitvector.ReaderGeometry
import RMQ.Core.WordRAM.Bitvector.AllocationFacts

/-! # Exact regular views of every segment in the complete allocation

The rank raw view has extra empty sentinels but the same counted raw payload.
All other present views are actual components of the single serialized body.
-/

namespace RMQ.PackedBitvector.Allocation

open SuccinctSpace SuccinctRank GenericSelect
open SuccinctFinal.PackedWordRAM

def activeSegment (segment : Nat) : Prop := segment < 23 ∧ segment ≠ 20

instance (segment : Nat) : Decidable (activeSegment segment) :=
  inferInstanceAs (Decidable (segment < 23 ∧ segment ≠ 20))

def physicalComponent (target : Bool) (segment : Nat) : Nat :=
  if segment = 17 then if target then 36 else 35
  else if segment = 18 then if target then 38 else 37
  else if segment = 19 then 0
  else componentIndex target segment

theorem physicalComponent_lt (target : Bool) (segment : Nat) :
    physicalComponent target segment < 39 := by
  unfold physicalComponent componentIndex
  repeat first | split | cases target | omega

theorem allSegments_get_old (bits : List Bool) (index : Nat) (hi : index < 35) :
    (allSegments bits)[index]'(by simp; omega) =
      (Experiment.allSegments bits)[index]'(by simpa using hi) := by
  exact List.getElem_append_left (by simpa using hi)

theorem allSegments_regular (bits : List Bool) (words : Array (List Bool))
    (hs : words ∈ allSegments bits) : RegularWords words := by
  rcases List.mem_append.mp hs with hs | hs
  · exact RMQ.PackedBitvector.allSegments_regular bits words hs
  · exact jacobson_samples_regular bits words hs

theorem allSegments_word_length_lt (bits : List Bool) (words : Array (List Bool))
    (hs : words ∈ allSegments bits) (word : List Bool) (hw : word ∈ words.toList) :
    word.length < Experiment.width bits.length := by
  rcases List.mem_append.mp hs with hs | hs
  · exact RMQ.PackedBitvector.allSegments_word_length_lt bits words hs word hw
  · have h := jacobson_sample_word_length_le bits words hs word hw
    unfold Experiment.width
    omega

theorem allSegments_firstLength_lt (bits : List Bool) (words : Array (List Bool))
    (hs : words ∈ allSegments bits) : firstLength words < Experiment.width bits.length := by
  cases hg : words[0]? with
  | none => simpa [firstLength, hg] using width_pos bits.length
  | some word =>
    have hm : word ∈ words.toList := List.mem_of_getElem? (by simpa using hg)
    simpa [firstLength, hg] using allSegments_word_length_lt bits words hs word hm

theorem logicalWords_component (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : activeSegment segment) (hraw : segment ≠ 19) :
    logicalWords bits target segment =
      (allSegments bits)[physicalComponent target segment]'(by
        simpa using physicalComponent_lt target segment) := by
  by_cases h17 : segment = 17
  · subst segment
    cases target <;>
      simp [logicalWords, physicalComponent, allSegments, rankSegments,
        TwoLevelPayloadLiveStoredWordRankData.superSampleWords]
  · by_cases h18 : segment = 18
    · subst segment
      cases target <;>
        simp [logicalWords, physicalComponent, allSegments, rankSegments,
          TwoLevelPayloadLiveStoredWordRankData.blockSampleWords]
    · have hp : presentSegment segment := by unfold activeSegment at hs; unfold presentSegment; omega
      simp only [logicalWords, physicalComponent, if_neg h17, if_neg h18, if_neg hraw]
      rw [allSegments_get_old bits _ (componentIndex_lt target segment hp)]
      exact selectedWords_present bits target segment hp

theorem logicalWords_raw (bits : List Bool) (target : Bool) :
    logicalWords bits target 19 = (jacobsonRankData bits).bitWords.store.words := by
  simp [logicalWords]

theorem logicalWords_view (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : activeSegment segment) :
    Experiment.segmentBits (logicalWords bits target segment) =
      Experiment.segmentBits ((allSegments bits)[physicalComponent target segment]'(by
        simpa using physicalComponent_lt target segment)) := by
  by_cases hraw : segment = 19
  · subst segment
    rw [logicalWords_raw]
    simp only [physicalComponent, Nat.reduceEqDiff, if_false, if_true]
    rw [allSegments_get_old bits 0 (by decide)]
    change Experiment.segmentBits (jacobsonRankData bits).bitWords.store.words =
      Experiment.segmentBits (sparseExceptionSelectData bits false).bitWords.store.words
    simp only [segmentBits_payload]
  · rw [logicalWords_component bits target segment hs hraw]

theorem logicalWords_regular (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : activeSegment segment) : RegularWords (logicalWords bits target segment) := by
  by_cases hraw : segment = 19
  · subst segment
    rw [logicalWords_raw]
    exact jacobson_raw_regular bits
  · rw [logicalWords_component bits target segment hs hraw]
    exact allSegments_regular bits _ (List.getElem_mem _)

theorem logicalWords_firstLength_lt (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : activeSegment segment) :
    firstLength (logicalWords bits target segment) < Experiment.width bits.length := by
  by_cases hraw : segment = 19
  · subst segment
    rw [logicalWords_raw]
    cases hg : (jacobsonRankData bits).bitWords.store.words[0]? with
    | none => simpa [firstLength, hg] using width_pos bits.length
    | some word =>
      have hm : word ∈ (jacobsonRankData bits).bitWords.store.words.toList :=
        List.mem_of_getElem? (by simpa using hg)
      have hb := jacobson_raw_word_length_le bits word hm
      have hw := machineWordBits_lt_width bits.length
      simpa [firstLength, hg] using Nat.lt_of_le_of_lt hb hw
  · rw [logicalWords_component bits target segment hs hraw]
    exact allSegments_firstLength_lt bits _ (List.getElem_mem _)

theorem bankDescriptor_active (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : activeSegment segment) :
    bankDescriptor bits target segment =
      Experiment.descriptor (207 * Experiment.width bits.length +
        Experiment.componentOffset (allSegments bits) (physicalComponent target segment))
          (logicalWords bits target segment) := by
  by_cases hraw : segment = 19
  · subst segment
    rw [bankDescriptor_raw_alias, logicalWords_raw]
    simp [physicalComponent, Experiment.componentOffset]
  · rw [logicalWords_component bits target segment hs hraw]
    rw [← allDescriptors_getElem! bits _ (physicalComponent_lt target segment)]
    rw [bankDescriptor_eq_selected bits target segment hs.1]
    unfold selectedDescriptor physicalComponent componentIndex
    by_cases h0 : segment = 0
    · simp [h0]
    · by_cases h17 : segment < 17
      · have hn17 : segment ≠ 17 := by omega
        have hn18 : segment ≠ 18 := by omega
        simp [h0, h17, hn17, hn18, hraw]
      · have ht : segment = 17 ∨ segment = 18 ∨ segment = 21 ∨ segment = 22 := by
          unfold activeSegment at hs
          omega
        rcases ht with rfl | rfl | rfl | rfl <;> simp

theorem logicalWords_inactive (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : ¬ activeSegment segment) : logicalWords bits target segment = #[] := by
  have h17 : segment ≠ 17 := by unfold activeSegment at hs; omega
  have h18 : segment ≠ 18 := by unfold activeSegment at hs; omega
  have h19 : segment ≠ 19 := by unfold activeSegment at hs; omega
  have hp : ¬ presentSegment segment := by unfold activeSegment at hs; unfold presentSegment; omega
  simp [logicalWords, h17, h18, h19, selectedWords, hp]

theorem decode_logicalWords (bits : List Bool) (target : Bool) (segment index : Nat)
    (hs : activeSegment segment) (hi : index < (logicalWords bits target segment).size) :
    let words := logicalWords bits target segment
    let stride := firstLength words
    decodeSpanNat (Experiment.width bits.length)
      (207 * Experiment.width bits.length +
        Experiment.componentOffset (allSegments bits) (physicalComponent target segment) + index * stride)
      (min stride ((Experiment.segmentBits words).length - index * stride)) (memory bits) =
        some (bitsToNatLE words[index]) := by
  have h := decode_serialized_view (header bits) (Experiment.width bits.length)
    (allSegments bits) (physicalComponent target segment) index
    (by simpa using physicalComponent_lt target segment) (logicalWords bits target segment)
    (logicalWords_view bits target segment hs) hi (width_pos bits.length)
    (logicalWords_regular bits target segment hs)
    (Nat.le_of_lt (logicalWords_firstLength_lt bits target segment hs))
  simpa only [header_length, memory, body] using h

end RMQ.PackedBitvector.Allocation
