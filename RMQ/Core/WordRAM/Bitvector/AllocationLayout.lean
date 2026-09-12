import RMQ.Core.WordRAM.Bitvector.Allocation
import RMQ.Core.WordRAM.Bitvector.SegmentMap

/-! # Descriptor positions in the complete shared allocation -/

namespace RMQ.PackedBitvector.Allocation

open SuccinctSpace SuccinctRank GenericSelect
open SuccinctFinal.PackedWordRAM

theorem descriptorsFrom_append (position : Nat) (first second : List (Array (List Bool))) :
    Experiment.descriptorsFrom position (first ++ second) =
      Experiment.descriptorsFrom position first ++
        Experiment.descriptorsFrom
          (position + (first.flatMap Experiment.segmentBits).length) second := by
  induction first generalizing position with
  | nil => simp [Experiment.descriptorsFrom]
  | cons words rest ih =>
    simp [Experiment.descriptorsFrom, ih, Nat.add_assoc]

theorem allDescriptors_get_old (bits : List Bool) (index : Nat) (hi : index < 35) :
    (allDescriptors bits)[index]? = (Experiment.allDescriptors bits)[index]? := by
  unfold allDescriptors allSegments
  rw [descriptorsFrom_append]
  exact List.getElem?_append_left (by simpa using hi)

theorem allDescriptors_getElem!_old (bits : List Bool) (index : Nat) (hi : index < 35) :
    (allDescriptors bits)[index]! = (Experiment.allDescriptors bits)[index]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
    allDescriptors_get_old bits index hi]

theorem allDescriptors_get_length (bits : List Bool) (index : Nat) (hi : index < 39) :
    ((allDescriptors bits)[index]!).length = 4 := by
  have hb : index < (allDescriptors bits).length := by simpa using hi
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hb]
  exact Experiment.descriptorsFrom_member_length _ _ _ (List.getElem_mem hb)

theorem descriptorBank_member_length (bits : List Bool) (target : Bool)
    (entry : List Nat) (h : entry ∈ descriptorBank bits target) : entry.length = 4 := by
  simp only [descriptorBank, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with ((rfl | h) | (rfl | rfl | rfl | rfl)) | (rfl | rfl)
  · exact allDescriptors_get_length bits 0 (by decide)
  · exact Experiment.descriptorsFrom_member_length _ _ _
      (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact allDescriptors_get_length bits _ (by cases target <;> decide)
  · exact allDescriptors_get_length bits _ (by cases target <;> decide)
  · exact Experiment.descriptor_length _ _
  · decide
  · exact allDescriptors_get_length bits 33 (by decide)
  · exact allDescriptors_get_length bits 34 (by decide)

@[simp] theorem descriptorBank_flatten_length (bits : List Bool) (target : Bool) :
    (descriptorBank bits target).flatten.length = 92 := by
  rw [Experiment.flatten_length_four _ (descriptorBank_member_length bits target)]
  simp

@[simp] theorem header_length (bits : List Bool) : (header bits).length = 207 := by
  simp only [header, List.length_append, scalarHeader_length, descriptorBank_flatten_length]

def bankDescriptor (bits : List Bool) (target : Bool) (segment : Nat) : List Nat :=
  ((descriptorBank bits target)[segment]?).getD []

theorem bankDescriptor_length (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : segment < 23) : (bankDescriptor bits target segment).length = 4 := by
  have hb : segment < (descriptorBank bits target).length := by simpa using hs
  simp only [bankDescriptor, List.getElem?_eq_getElem hb, Option.getD_some]
  exact descriptorBank_member_length bits target _ (List.getElem_mem hb)

theorem bank_flatten_field (bits : List Bool) (target : Bool) (segment field : Nat)
    (hs : segment < 23) (hf : field < 4) :
    (descriptorBank bits target).flatten[segment * 4 + field]? =
      (bankDescriptor bits target segment)[field]? := by
  have hb : segment < (descriptorBank bits target).length := by simpa using hs
  apply Experiment.flatten_get_field _ 4 (descriptorBank_member_length bits target)
    segment (bankDescriptor bits target segment) ?_ field hf
  simp only [bankDescriptor, List.getElem?_eq_getElem hb, Option.getD_some]

theorem memory_descriptor_field (bits : List Bool) (target : Bool) (segment field : Nat)
    (hs : segment < 23) (hf : field < 4) :
    (memory bits)[23 + target.toNat * 92 + segment * 4 + field]? =
      (bankDescriptor bits target segment)[field]? := by
  have h := Experiment.twoBank_lookup (scalarHeader bits) (descriptorBank bits false).flatten
    (descriptorBank bits true).flatten (denseWords (Experiment.width bits.length) (body bits))
    (scalarHeader_length bits) (descriptorBank_flatten_length bits false)
    (descriptorBank_flatten_length bits true) target (segment * 4 + field) (by omega)
  change (scalarHeader bits ++ (descriptorBank bits false).flatten ++
    (descriptorBank bits true).flatten ++ denseWords (Experiment.width bits.length) (body bits))[_]? = _
  rw [Nat.add_assoc (23 + target.toNat * 92), h]
  cases target <;> exact bank_flatten_field bits _ segment field hs hf

theorem memory_descriptor_present (bits : List Bool) (target : Bool) (segment field : Nat)
    (hs : segment < 23) (hf : field < 4) :
    (memory bits)[23 + target.toNat * 92 + segment * 4 + field]? =
      some ((bankDescriptor bits target segment)[field]?.getD 0) := by
  rw [memory_descriptor_field bits target segment field hs hf]
  rw [List.getElem?_eq_getElem (by simpa only [bankDescriptor_length bits target segment hs] using hf)]
  rfl

def selectedDescriptor (bits : List Bool) (target : Bool) (segment : Nat) : List Nat :=
  let desc := allDescriptors bits
  if segment = 0 then desc[0]!
  else if segment < 17 then desc[if target then 16 + segment else segment]!
  else if segment = 17 then desc[if target then 36 else 35]!
  else if segment = 18 then desc[if target then 38 else 37]!
  else if segment = 19 then
    Experiment.descriptor (207 * Experiment.width bits.length)
      (jacobsonRankData bits).bitWords.store.words
  else if segment = 21 then desc[33]!
  else if segment = 22 then desc[34]!
  else [0, 0, 0, 0]

theorem bankDescriptor_eq_selected (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : segment < 23) : bankDescriptor bits target segment = selectedDescriptor bits target segment := by
  by_cases hz : segment = 0
  · subst segment
    simp [bankDescriptor, descriptorBank, selectedDescriptor]
  · by_cases hd : segment < 17
    · obtain ⟨index, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
      have hi16 : index < 16 := by omega
      have hi17 : index + 1 < 17 := by omega
      cases target <;>
        simp [bankDescriptor, descriptorBank, selectedDescriptor, List.getElem?_append,
          List.getElem!_eq_getElem?_getD, Nat.add_assoc, Nat.add_comm, hi16, hi17]
      all_goals rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
    · have he : segment = 17 ∨ segment = 18 ∨ segment = 19 ∨ segment = 20 ∨
          segment = 21 ∨ segment = 22 := by omega
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> cases target <;>
        simp [bankDescriptor, descriptorBank, selectedDescriptor]

/-- Adding the rank directories does not change any select descriptor. -/
theorem bankDescriptor_select_agrees (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : presentSegment segment) :
    bankDescriptor bits target segment = Experiment.bankDescriptor bits target segment := by
  have h23 : segment < 23 := by unfold presentSegment at hs; omega
  rw [bankDescriptor_eq_selected bits target segment h23,
    Experiment.bankDescriptor_eq_selected bits target segment h23]
  by_cases hz : segment = 0
  · simp only [selectedDescriptor, Experiment.selectedDescriptor, if_pos hz]
    exact allDescriptors_getElem!_old bits 0 (by decide)
  · by_cases hl : segment < 17
    · simp only [selectedDescriptor, Experiment.selectedDescriptor, if_neg hz, if_pos hl]
      exact allDescriptors_getElem!_old bits _ (by cases target <;> simp <;> omega)
    · have htail : segment = 21 ∨ segment = 22 := by unfold presentSegment at hs; omega
      rcases htail with rfl | rfl <;>
        simp only [selectedDescriptor, Experiment.selectedDescriptor,
          Nat.reduceEqDiff, Nat.reduceLT, if_false, if_true]
      · exact allDescriptors_getElem!_old bits 33 (by decide)
      · exact allDescriptors_getElem!_old bits 34 (by decide)

theorem bankDescriptor_raw_alias (bits : List Bool) (target : Bool) :
    bankDescriptor bits target 19 =
      Experiment.descriptor (207 * Experiment.width bits.length)
        (jacobsonRankData bits).bitWords.store.words := by
  rw [bankDescriptor_eq_selected bits target 19 (by decide)]
  simp [selectedDescriptor]

theorem allDescriptors_getElem! (bits : List Bool) (index : Nat) (hi : index < 39) :
    (allDescriptors bits)[index]! =
      Experiment.descriptor
        (207 * Experiment.width bits.length + Experiment.componentOffset (allSegments bits) index)
        (allSegments bits)[index] := by
  have ha : index < (allSegments bits).length := by simpa using hi
  have hd : index < (allDescriptors bits).length := by simpa using hi
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hd]
  exact Experiment.descriptorsFrom_getElem _ _ _ ha

end RMQ.PackedBitvector.Allocation
