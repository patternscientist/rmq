import RMQ.Core.WordRAM.Bitvector.CanonicalLimits

/-! # Bounds on every reply of the complete logical specification -/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank GenericSelect
open SuccinctFinal.PackedWordRAM

theorem canonical_select_small_length (bits : List Bool) (target : Bool) (segment index : Nat)
    (hs : segment < 17) :
    logicalLength ((Allocation.readStore bits target).readWord? segment index) ≤
      machineWordBits bits.length := by
  rw [Allocation.readStore_select_agrees bits target segment index (Or.inl hs)]
  by_cases hz : segment = 0
  · simp only [genericReadStore, genericLogicalWord, if_pos hz]
    rw [show logicalLength (((sparseExceptionSelectData bits target).bitWords.store.words[index]?).map
      (normalize target)) = logicalLength (sparseExceptionSelectData bits target).bitWords.store.words[index]?
      from normalize_optional_length target _]
    apply optional_length_le
    intro word hw
    exact Nat.le_trans ((sparseExceptionSelectData bits target).bitWords.word_length_le hw)
      (sparseExceptionSelectData bits target).wordSize_le_machine
  · simp only [genericReadStore, genericLogicalWord, if_neg hz, if_pos hs]
    apply optional_length_le
    intro word hw
    cases hg : (Experiment.directorySegments (sparseExceptionSelectData bits target))[segment-1]? with
    | none => simp [hg] at hw
    | some words =>
      have hm : words ∈ Experiment.directorySegments (sparseExceptionSelectData bits target) :=
        List.mem_of_getElem? hg
      exact directorySegments_word_length _ words hm word (by simpa [hg] using hw)

theorem canonical_rank_raw_length (bits : List Bool) (target : Bool) (index : Nat) :
    logicalLength ((Allocation.readStore bits target).readWord? 19 index) ≤
      machineWordBits bits.length := by
  change logicalLength (normalizedSegmentWord target 19
    ((Allocation.logicalWords bits target 19)[index]?)) ≤ _
  rw [normalizedSegmentWord_length, Allocation.logicalWords_raw]
  exact optional_length_le _ _ index (jacobson_raw_word_length_le bits)

theorem canonical_directory_length (bits : List Bool) (target : Bool) (segment index : Nat)
    (h21 : segment ≠ 21) (h22 : segment ≠ 22) :
    logicalLength ((Allocation.readStore bits target).readWord? segment index) ≤
      2 * machineWordBits bits.length + 3 := by
  by_cases hsmall : segment < 17
  · have h := canonical_select_small_length bits target segment index hsmall
    omega
  · by_cases h17 : segment = 17
    · subst segment
      change logicalLength (normalizedSegmentWord target 17
        ((Allocation.logicalWords bits target 17)[index]?)) ≤ _
      rw [normalizedSegmentWord_length]
      simp only [Allocation.logicalWords, if_true]
      apply optional_length_le
      intro word hw
      apply jacobson_sample_word_length_le bits _ ?_ word hw
      cases target <;> simp [jacobsonSampleArrays,
        TwoLevelPayloadLiveStoredWordRankData.superSampleWords]
    · by_cases h18 : segment = 18
      · subst segment
        change logicalLength (normalizedSegmentWord target 18
          ((Allocation.logicalWords bits target 18)[index]?)) ≤ _
        rw [normalizedSegmentWord_length]
        simp only [Allocation.logicalWords, Nat.reduceEqDiff, if_false, if_true]
        apply optional_length_le
        intro word hw
        apply jacobson_sample_word_length_le bits _ ?_ word hw
        cases target <;> simp [jacobsonSampleArrays,
          TwoLevelPayloadLiveStoredWordRankData.blockSampleWords]
      · by_cases h19 : segment = 19
        · subst segment
          have h := canonical_rank_raw_length bits target index
          omega
        · have hinactive : ¬Allocation.activeSegment segment := by
            unfold Allocation.activeSegment
            omega
          simp [Allocation.readStore, Allocation.logicalWord,
            Allocation.logicalWords_inactive bits target segment hinactive,
            normalizedSegmentWord, logicalLength]

theorem canonical_table_length (bits : List Bool) (target : Bool) (segment index : Nat)
    (hs : segment = 21 ∨ segment = 22) :
    logicalLength ((Allocation.readStore bits target).readWord? segment index) ≤
      machineWordBits bits.length + 8 := by
  rcases hs with rfl | rfl
  · rw [Allocation.readStore_select_agrees bits target 21 index (Or.inr (Or.inl rfl))]
    apply optional_length_le
    intro word hw
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
    have hl := (SuccinctClose.bpFringeChunkTable
      (SuccinctClose.bpFringeChunkBits (2*bits.length))).word_length_of_get? (by simpa using hi)
    rw [hl]
    exact chunkTable_width_le bits.length
  · rw [Allocation.readStore_select_agrees bits target 22 index (Or.inr (Or.inr rfl))]
    apply optional_length_le
    intro word hw
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
    have hl := (SuccinctClose.bpChunkSelectTable
      (SuccinctClose.bpFringeChunkBits (2*bits.length)) false).word_length_of_get? (by simpa using hi)
    have hb := SuccinctClose.bpChunkSelectEntryWidth_le
      (SuccinctClose.bpFringeChunkBits (2*bits.length))
    have hc := chunkBits_le_machine bits.length
    omega

theorem canonical_directory_packet (bits : List Bool) (target : Bool) (segment index : Nat)
    (h21 : segment ≠ 21) (h22 : segment ≠ 22) :
    logicalPacket ((Allocation.readStore bits target).readWord? segment index) ≤
      (canonicalLimits bits.length).directoryBound :=
  logicalPacket_le_of_length _ _ (canonical_directory_length bits target segment index h21 h22)

theorem canonical_table_packet (bits : List Bool) (target : Bool) (segment index : Nat)
    (hs : segment = 21 ∨ segment = 22) :
    logicalPacket ((Allocation.readStore bits target).readWord? segment index) ≤
      (canonicalLimits bits.length).tableBound :=
  logicalPacket_le_of_length _ _ (canonical_table_length bits target segment index hs)

theorem canonical_raw_length (bits : List Bool) (target : Bool) (segment index : Nat)
    (hs : segment = 0 ∨ segment = 11 ∨ segment = 15) :
    logicalLength ((Allocation.readStore bits target).readWord? segment index) ≤
      (canonicalLimits bits.length).rawWidth :=
  canonical_select_small_length bits target segment index (by omega)

end RMQ.PackedBitvector
