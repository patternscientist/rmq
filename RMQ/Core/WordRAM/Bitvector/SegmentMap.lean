import RMQ.Core.WordRAM.Bitvector.MemoryLayout
import RMQ.Core.WordRAM.Bitvector.ReaderInterface

/-! # The selected descriptor and logical word refer to the same component -/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank GenericSelect Experiment
open SuccinctFinal.PackedWordRAM

def presentSegment (segment : Nat) : Prop := segment < 17 ∨ segment = 21 ∨ segment = 22

instance (segment : Nat) : Decidable (presentSegment segment) :=
  inferInstanceAs (Decidable (segment < 17 ∨ segment = 21 ∨ segment = 22))

def componentIndex (target : Bool) (segment : Nat) : Nat :=
  if segment = 0 then 0
  else if segment < 17 then if target then 16 + segment else segment
  else if segment = 21 then 33 else 34

theorem componentIndex_lt (target : Bool) (segment : Nat) (_hs : presentSegment segment) :
    componentIndex target segment < 35 := by
  unfold componentIndex presentSegment at *
  split
  · omega
  · split
    · cases target <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
    · split <;> omega

def selectedWords (bits : List Bool) (target : Bool) (segment : Nat) : Array (List Bool) :=
  if presentSegment segment then
    ((allSegments bits)[componentIndex target segment]?).getD #[]
  else #[]

theorem selectedWords_present (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : presentSegment segment) :
    selectedWords bits target segment =
      (allSegments bits)[componentIndex target segment]'(by simpa using componentIndex_lt target segment hs) := by
  have hb : componentIndex target segment < (allSegments bits).length := by
    simpa using componentIndex_lt target segment hs
  simp only [selectedWords, if_pos hs,
    List.getElem?_eq_getElem hb, Option.getD_some]

theorem selectedWords_mem (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : presentSegment segment) : selectedWords bits target segment ∈ allSegments bits := by
  rw [selectedWords_present bits target segment hs]
  exact List.getElem_mem _

theorem bankDescriptor_present (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : presentSegment segment) :
    bankDescriptor bits target segment =
      descriptor (207 * width bits.length + componentOffset (allSegments bits) (componentIndex target segment))
        (selectedWords bits target segment) := by
  have hs23 : segment < 23 := by unfold presentSegment at hs; omega
  rw [bankDescriptor_eq_selected bits target segment hs23, selectedWords_present bits target segment hs]
  rw [← allDescriptors_getElem! bits _ (componentIndex_lt target segment hs)]
  unfold selectedDescriptor componentIndex
  by_cases hz : segment = 0
  · simp [hz]
  · by_cases hl : segment < 17
    · simp [hz, hl]
    · have ht : segment = 21 ∨ segment = 22 := by unfold presentSegment at hs; omega
      rcases ht with rfl | rfl <;> simp

theorem bankDescriptor_absent (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : segment < 23) (ha : ¬presentSegment segment) :
    bankDescriptor bits target segment = [0, 0, 0, 0] := by
  rw [bankDescriptor_eq_selected bits target segment hs]
  have hz : segment ≠ 0 := by unfold presentSegment at ha; omega
  have hl : ¬segment < 17 := by unfold presentSegment at ha; omega
  have h21 : segment ≠ 21 := by unfold presentSegment at ha; omega
  have h22 : segment ≠ 22 := by unfold presentSegment at ha; omega
  simp [selectedDescriptor, hz, hl, h21, h22]

theorem allSegments_raw (bits : List Bool) :
    (allSegments bits)[0]? = some (sparseExceptionSelectData bits false).bitWords.store.words := by
  rfl

theorem allSegments_directory_false (bits : List Bool) (index : Nat) (hi : index < 16) :
    (allSegments bits)[1 + index]? = (directorySegments (sparseExceptionSelectData bits false))[index]? := by
  unfold allSegments
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_right (by simp), List.length_singleton]
  simp

theorem allSegments_directory_true (bits : List Bool) (index : Nat) (hi : index < 16) :
    (allSegments bits)[17 + index]? = (directorySegments (sparseExceptionSelectData bits true))[index]? := by
  unfold allSegments
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem allSegments_rankTable (bits : List Bool) :
    (allSegments bits)[33]? = some
      (SuccinctClose.bpFringeChunkTable (SuccinctClose.bpFringeChunkBits (2 * bits.length))).store.words := by
  simp [allSegments, directorySegments]

theorem allSegments_selectTable (bits : List Bool) :
    (allSegments bits)[34]? = some
      (SuccinctClose.bpChunkSelectTable (SuccinctClose.bpFringeChunkBits (2 * bits.length)) false).store.words := by
  simp [allSegments, directorySegments]

theorem rawWords_target_eq (bits : List Bool) (target : Bool) :
    (sparseExceptionSelectData bits target).bitWords.store.words =
      (sparseExceptionSelectData bits false).bitWords.store.words := by rfl

theorem selectedWords_raw (bits : List Bool) (target : Bool) :
    selectedWords bits target 0 = (sparseExceptionSelectData bits false).bitWords.store.words := by
  unfold selectedWords
  rw [if_pos (show presentSegment 0 from Or.inl (by decide))]
  change ((allSegments bits)[0]?).getD #[] = _
  rw [allSegments_raw]
  rfl

theorem selectedWords_rankTable (bits : List Bool) (target : Bool) :
    selectedWords bits target 21 =
      (SuccinctClose.bpFringeChunkTable (SuccinctClose.bpFringeChunkBits (2 * bits.length))).store.words := by
  unfold selectedWords
  rw [if_pos (show presentSegment 21 from Or.inr (Or.inl rfl))]
  change ((allSegments bits)[33]?).getD #[] = _
  rw [allSegments_rankTable]
  rfl

theorem selectedWords_selectTable (bits : List Bool) (target : Bool) :
    selectedWords bits target 22 =
      (SuccinctClose.bpChunkSelectTable (SuccinctClose.bpFringeChunkBits (2 * bits.length)) false).store.words := by
  unfold selectedWords
  rw [if_pos (show presentSegment 22 from Or.inr (Or.inr rfl))]
  change ((allSegments bits)[34]?).getD #[] = _
  rw [allSegments_selectTable]
  rfl

theorem genericLogicalWord_selected (bits : List Bool) (target : Bool) (segment index : Nat) :
    genericLogicalWord bits target segment index =
      if segment = 0 then ((selectedWords bits target segment)[index]?).map (normalize target)
      else (selectedWords bits target segment)[index]? := by
  by_cases hz : segment = 0
  · subst segment
    simp [genericLogicalWord, selectedWords_raw, rawWords_target_eq]
  · by_cases hl : segment < 17
    · have hp : presentSegment segment := Or.inl hl
      have hi : segment - 1 < 16 := by omega
      have hfalse := allSegments_directory_false bits (segment - 1) hi
      have htrue := allSegments_directory_true bits (segment - 1) hi
      rw [show 1 + (segment - 1) = segment by omega] at hfalse
      rw [show 17 + (segment - 1) = 16 + segment by omega] at htrue
      cases target <;>
        simp [genericLogicalWord, selectedWords, if_pos hp, componentIndex, hz, hl,
          hfalse, htrue]
    · by_cases h21 : segment = 21
      · subst segment
        simp [genericLogicalWord, selectedWords_rankTable]
      · by_cases h22 : segment = 22
        · subst segment
          simp [genericLogicalWord, selectedWords_selectTable]
        · have hp : ¬presentSegment segment := by simp [presentSegment, hl, h21, h22]
          simp [genericLogicalWord, selectedWords, hp, hz, hl, h21, h22]

end RMQ.PackedBitvector
