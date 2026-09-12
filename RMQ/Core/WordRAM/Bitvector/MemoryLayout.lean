import RMQ.Core.WordRAM.Bitvector.SelectExperiment

/-! # Exact serialization identities for the generic bitvector allocation

These names expose the existing executable allocation by definitional equality.
Descriptors identify actual component positions; no regular-word or semantic
correctness property is assumed by the serialization lemmas.
-/

namespace RMQ.PackedBitvector.Experiment

open SuccinctSpace SuccinctRank GenericSelect
open SuccinctFinal.PackedWordRAM

def allSegments (bits : List Bool) : List (Array (List Bool)) :=
  let df := sparseExceptionSelectData bits false
  let dt := sparseExceptionSelectData bits true
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  [df.bitWords.store.words] ++ directorySegments df ++ directorySegments dt ++
    [(SuccinctClose.bpFringeChunkTable c).store.words,
     (SuccinctClose.bpChunkSelectTable c false).store.words]

def allDescriptors (bits : List Bool) : List (List Nat) :=
  descriptorsFrom (207 * width bits.length) (allSegments bits)

def descriptorBank (bits : List Bool) (target : Bool) : List (List Nat) :=
  let desc := allDescriptors bits
  [desc[0]!] ++ (desc.drop (if target then 17 else 1)).take 16 ++
    List.replicate 4 [0, 0, 0, 0] ++ [desc[33]!, desc[34]!]

def scalarHeader (bits : List Bool) : List Nat :=
  let df := sparseExceptionSelectData bits false
  let dt := sparseExceptionSelectData bits true
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  [occurrenceCount bits false, occurrenceCount bits true, bits.length,
    0, 0, 0, width bits.length, 0, df.wordSize, df.superStride,
    df.localStride, df.localSlotsPerSuper] ++ flagScalars df ++
    [df.wordSize, 0, c] ++ flagScalars dt

def header (bits : List Bool) : List Nat :=
  scalarHeader bits ++ (descriptorBank bits false).flatten ++
    (descriptorBank bits true).flatten

def body (bits : List Bool) : List Bool := (allSegments bits).flatMap segmentBits

theorem memory_eq (bits : List Bool) :
    memory bits = header bits ++ denseWords (width bits.length) (body bits) := by
  rfl

@[simp] theorem directorySegments_length {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) :
    (directorySegments d).length = 16 := by simp [directorySegments]

@[simp] theorem allSegments_length (bits : List Bool) : (allSegments bits).length = 35 := by
  simp [allSegments]

@[simp] theorem descriptorsFrom_length (position : Nat) (segments : List (Array (List Bool))) :
    (descriptorsFrom position segments).length = segments.length := by
  induction segments generalizing position with
  | nil => rfl
  | cons words rest ih => simp [descriptorsFrom, ih]

@[simp] theorem allDescriptors_length (bits : List Bool) : (allDescriptors bits).length = 35 := by
  simp [allDescriptors]

@[simp] theorem descriptor_length (position : Nat) (words : Array (List Bool)) :
    (descriptor position words).length = 4 := by simp [descriptor]

theorem descriptorsFrom_member_length (position : Nat) (segments : List (Array (List Bool)))
    (entry : List Nat) (h : entry ∈ descriptorsFrom position segments) : entry.length = 4 := by
  induction segments generalizing position with
  | nil => simp [descriptorsFrom] at h
  | cons words rest ih =>
    simp only [descriptorsFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact descriptor_length _ _
    · exact ih _ h

@[simp] theorem descriptorBank_length (bits : List Bool) (target : Bool) :
    (descriptorBank bits target).length = 23 := by
  cases target <;> simp [descriptorBank]

theorem allDescriptors_get_length (bits : List Bool) (index : Nat)
    (hi : index < 35) : ((allDescriptors bits)[index]!).length = 4 := by
  have hb : index < (allDescriptors bits).length := by simpa using hi
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hb]
  exact descriptorsFrom_member_length _ _ _ (List.getElem_mem hb)

theorem descriptorBank_member_length (bits : List Bool) (target : Bool)
    (entry : List Nat) (h : entry ∈ descriptorBank bits target) : entry.length = 4 := by
  simp only [descriptorBank, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_replicate] at h
  rcases h with ((rfl | h) | ⟨_, rfl⟩) | (rfl | rfl)
  · exact allDescriptors_get_length bits 0 (by omega)
  · exact descriptorsFrom_member_length _ _ _
      (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · decide
  · exact allDescriptors_get_length bits 33 (by omega)
  · exact allDescriptors_get_length bits 34 (by omega)

@[simp] theorem scalarHeader_length (bits : List Bool) : (scalarHeader bits).length = 23 := by
  simp [scalarHeader, flagScalars]

theorem flatten_length_four (entries : List (List Nat))
    (h : ∀ entry ∈ entries, entry.length = 4) : entries.flatten.length = entries.length * 4 := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
    have he := h entry (by simp)
    have ht := ih (fun e hm => h e (by simp [hm]))
    simp [he, ht, Nat.add_mul, Nat.add_comm]

@[simp] theorem descriptorBank_flatten_length (bits : List Bool) (target : Bool) :
    (descriptorBank bits target).flatten.length = 92 := by
  rw [flatten_length_four _ (descriptorBank_member_length bits target)]
  simp

@[simp] theorem header_length (bits : List Bool) : (header bits).length = 207 := by
  simp only [header, List.length_append, scalarHeader_length, descriptorBank_flatten_length]

/-- Exact descriptor position as the bit length of the preceding components. -/
theorem descriptorsFrom_getElem (position : Nat) (segments : List (Array (List Bool)))
    (index : Nat) (hi : index < segments.length) :
    (descriptorsFrom position segments)[index]'(by simpa using hi) =
      descriptor (position + ((segments.take index).flatMap segmentBits).length)
        (segments[index]) := by
  induction segments generalizing position index with
  | nil => simp at hi
  | cons words rest ih =>
    cases index with
    | zero => simp [descriptorsFrom]
    | succ index =>
      have hi' : index < rest.length := by simpa using hi
      simpa [descriptorsFrom, Nat.add_assoc] using
        ih (position + (segmentBits words).length) index hi'

theorem descriptorsFrom_getElem? (position : Nat) (segments : List (Array (List Bool)))
    (index : Nat) :
    (descriptorsFrom position segments)[index]? =
      (segments[index]?).map (fun words =>
        descriptor (position + ((segments.take index).flatMap segmentBits).length) words) := by
  by_cases hi : index < segments.length
  · rw [List.getElem?_eq_getElem (by simpa using hi), List.getElem?_eq_getElem hi]
    simp only [Option.map_some]
    exact congrArg some (descriptorsFrom_getElem position segments index hi)
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi),
      List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    rfl

theorem flatten_get_field (entries : List (List Nat)) (count : Nat)
    (hlen : ∀ entry ∈ entries, entry.length = count)
    (index : Nat) (entry : List Nat) (he : entries[index]? = some entry)
    (field : Nat) (hf : field < count) :
    entries.flatten[index * count + field]? = entry[field]? := by
  have hs := SuccinctSpace.List.flatMap_drop_mul_take_of_constant_length
    entries id count hlen he
  have hv := congrArg (fun xs : List Nat => xs[field]?) hs
  simpa only [List.flatMap_id, List.getElem?_take_of_lt hf, List.getElem?_drop] using hv

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
  apply flatten_get_field _ 4 (descriptorBank_member_length bits target)
    segment (bankDescriptor bits target segment) ?_ field hf
  simp only [bankDescriptor, List.getElem?_eq_getElem hb, Option.getD_some]

theorem twoBank_lookup (scalars bankFalse bankTrue tail : List Nat)
    (hs : scalars.length = 23) (hf : bankFalse.length = 92) (ht : bankTrue.length = 92)
    (target : Bool) (index : Nat) (hi : index < 92) :
    (scalars ++ bankFalse ++ bankTrue ++ tail)[23 + target.toNat * 92 + index]? =
      (if target then bankTrue else bankFalse)[index]? := by
  have htotal : (scalars ++ bankFalse ++ bankTrue).length = 207 := by
    simp only [List.length_append, hs, hf, ht]
  cases target
  · change (scalars ++ bankFalse ++ bankTrue ++ tail)[23 + index]? = bankFalse[index]?
    rw [List.getElem?_append_left (by omega)]
    rw [List.getElem?_append_left (by simp only [List.length_append, hs, hf]; omega)]
    rw [List.getElem?_append_right (by omega), hs]
    simp
  · change (scalars ++ bankFalse ++ bankTrue ++ tail)[23 + 92 + index]? = bankTrue[index]?
    rw [List.getElem?_append_left (by omega)]
    rw [List.getElem?_append_right (by simp only [List.length_append, hs, hf]; omega)]
    simp only [List.length_append, hs, hf, Nat.add_sub_cancel_left]

/-- Every descriptor field is an actual lookup into the same executable memory. -/
theorem memory_descriptor_field (bits : List Bool) (target : Bool) (segment field : Nat)
    (hs : segment < 23) (hf : field < 4) :
    (memory bits)[23 + target.toNat * 92 + segment * 4 + field]? =
      (bankDescriptor bits target segment)[field]? := by
  have h := twoBank_lookup (scalarHeader bits) (descriptorBank bits false).flatten
    (descriptorBank bits true).flatten (denseWords (width bits.length) (body bits))
    (scalarHeader_length bits) (descriptorBank_flatten_length bits false)
    (descriptorBank_flatten_length bits true) target (segment * 4 + field) (by omega)
  rw [memory_eq]
  change (scalarHeader bits ++ (descriptorBank bits false).flatten ++
    (descriptorBank bits true).flatten ++ denseWords (width bits.length) (body bits))[_]? = _
  rw [Nat.add_assoc (23 + target.toNat * 92), h]
  cases target <;> exact bank_flatten_field bits _ segment field hs hf

theorem memory_descriptor_present (bits : List Bool) (target : Bool) (segment field : Nat)
    (hs : segment < 23) (hf : field < 4) :
    (memory bits)[23 + target.toNat * 92 + segment * 4 + field]? =
      some ((bankDescriptor bits target segment)[field]?.getD 0) := by
  rw [memory_descriptor_field bits target segment field hs hf]
  rw [List.getElem?_eq_getElem (by simpa only [bankDescriptor_length bits target segment hs] using hf)]
  rfl

def componentOffset (segments : List (Array (List Bool))) (index : Nat) : Nat :=
  ((segments.take index).flatMap segmentBits).length

theorem components_decompose (segments : List (Array (List Bool))) (index : Nat)
    (hi : index < segments.length) :
    segments.flatMap segmentBits =
      (segments.take index).flatMap segmentBits ++ segmentBits segments[index] ++
        (segments.drop (index + 1)).flatMap segmentBits := by
  induction segments generalizing index with
  | nil => simp at hi
  | cons words rest ih =>
    cases index with
    | zero => simp
    | succ index =>
      have hi' : index < rest.length := by simpa using hi
      simpa only [List.flatMap_cons, List.take_succ_cons, List.drop_succ_cons,
        List.getElem_cons_succ, List.append_assoc] using
        congrArg (fun xs => segmentBits words ++ xs) (ih index hi')

theorem component_slice (segments : List (Array (List Bool))) (index position len : Nat)
    (hi : index < segments.length)
    (hb : position + len ≤ (segmentBits segments[index]).length ∨ len = 0) :
    ((segments.flatMap segmentBits).drop (componentOffset segments index + position)).take len =
      ((segmentBits segments[index]).drop position).take len := by
  by_cases hz : len = 0
  · simp [hz]
  have hb' := hb.resolve_right hz
  rw [components_decompose segments index hi]
  unfold componentOffset
  rw [List.append_assoc, SuccinctSpace.List.drop_append_length_add,
    List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

theorem component_span_bound (segments : List (Array (List Bool))) (index position len : Nat)
    (hi : index < segments.length)
    (hb : position + len ≤ (segmentBits segments[index]).length ∨ len = 0) :
    componentOffset segments index + position + len ≤ (segments.flatMap segmentBits).length ∨
      len = 0 := by
  rcases hb with hb | hz
  · left
    have h := congrArg List.length (components_decompose segments index hi)
    simp only [List.length_append] at h
    unfold componentOffset
    omega
  · exact Or.inr hz

def selectedDescriptor (bits : List Bool) (target : Bool) (segment : Nat) : List Nat :=
  let desc := allDescriptors bits
  if segment = 0 then desc[0]!
  else if segment < 17 then desc[if target then 16 + segment else segment]!
  else if segment = 21 then desc[33]!
  else if segment = 22 then desc[34]!
  else [0, 0, 0, 0]

theorem bankDescriptor_eq_selected (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : segment < 23) : bankDescriptor bits target segment = selectedDescriptor bits target segment := by
  by_cases hz : segment = 0
  · subst segment
    simp [bankDescriptor, descriptorBank, selectedDescriptor]
  · by_cases hd : segment < 17
    · have hlo : 1 ≤ segment := by omega
      obtain ⟨index, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
      have hi16 : index < 16 := by omega
      have hi17 : index + 1 < 17 := by omega
      cases target <;>
        simp [bankDescriptor, descriptorBank, selectedDescriptor,
          List.getElem?_append,
          List.getElem!_eq_getElem?_getD, Nat.add_assoc, Nat.add_comm, hi16, hi17]
      all_goals rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
    · by_cases hl : segment < 21
      · have he : segment = 17 ∨ segment = 18 ∨ segment = 19 ∨ segment = 20 := by omega
        rcases he with rfl | rfl | rfl | rfl <;> cases target <;>
          simp [bankDescriptor, descriptorBank, selectedDescriptor]
      · have he : segment = 21 ∨ segment = 22 := by omega
        rcases he with rfl | rfl <;> cases target <;>
          simp [bankDescriptor, descriptorBank, selectedDescriptor]

theorem allDescriptors_getElem! (bits : List Bool) (index : Nat) (hi : index < 35) :
    (allDescriptors bits)[index]! =
      descriptor (207 * width bits.length + componentOffset (allSegments bits) index)
        (allSegments bits)[index] := by
  have ha : index < (allSegments bits).length := by simpa using hi
  have hd : index < (allDescriptors bits).length := by simpa using hi
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hd]
  exact descriptorsFrom_getElem _ _ _ ha

end RMQ.PackedBitvector.Experiment
