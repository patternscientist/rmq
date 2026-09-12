import RMQ.Core.WordRAM.Native.Limbs

/-!
# Bounded byte framing for native images

Scalars use minimal little-endian base-256 digits. Their byte count is framed
by that many marker bytes1, a delimiter0, and the digits. Array lengths are
scalars. Every declared length is checked against available bytes before a
count-driven loop or slice. These are executable list parsers; ByteArray
adaptation and temporary allocation costs are stated at the image interface.
-/

namespace RMQ.SuccinctFinal.PackedNative.BinaryCodec

open LimbWord

abbrev Bytes := List UInt8

def digitCount (value : Nat) : Nat := value.log2 / 8 + 1

def scalar (value : Nat) : Bytes :=
  List.replicate (digitCount value) 1 ++ 0 :: encodeList (digitCount value) value

def readPrefix : Bytes → Option (Nat × Bytes)
  | [] => none
  | b :: rest =>
      if b = 0 then some (0, rest)
      else if b = 1 then do
        let (count, tail) ← readPrefix rest
        pure (count + 1, tail)
      else none

def readScalar (bytes : Bytes) : Option (Nat × Bytes) := do
  let (count, rest) ← readPrefix bytes
  if 0 < count ∧ count ≤ rest.length then
    let value := decodeList (rest.take count)
    if digitCount value = count then some (value, rest.drop count) else none
  else none

theorem digitCount_pos (value : Nat) : 0 < digitCount value := by
  unfold digitCount
  omega

theorem digitCount_capacity (value : Nat) : value < 256 ^ digitCount value := by
  rw [byte_capacity]
  by_cases hv : value = 0
  · subst value
    exact Nat.pow_pos (by decide)
  · apply (Nat.log2_lt hv).1
    unfold digitCount
    omega

theorem digitCount_minimal (value : Nat) (h : value ≠ 0) :
    256 ^ (digitCount value - 1) ≤ value := by
  rw [byte_capacity]
  apply (Nat.le_log2 h).1
  unfold digitCount
  omega

theorem readPrefix_frame (count : Nat) (tail : Bytes) :
    readPrefix (List.replicate count 1 ++ 0 :: tail) = some (count, tail) := by
  induction count with
  | zero => simp [readPrefix]
  | succ count ih => simp [List.replicate_succ, readPrefix, ih]

theorem readPrefix_sound (bytes : Bytes) (count : Nat) (tail : Bytes)
    (h : readPrefix bytes = some (count, tail)) :
    bytes = List.replicate count 1 ++ 0 :: tail := by
  induction bytes generalizing count with
  | nil => simp [readPrefix] at h
  | cons byte bytes ih =>
      unfold readPrefix at h
      split at h
      · cases h
        simp_all
      · split at h
        · cases hs : readPrefix bytes with
          | none => simp [hs] at h
          | some pair =>
              rcases pair with ⟨n, rest⟩
              simp only [hs, bind, Option.bind] at h
              rcases h with ⟨rfl, rfl⟩
              simp_all [List.replicate_succ, ih n hs]
        · contradiction

@[simp] theorem scalar_length (value : Nat) :
    (scalar value).length = 2 * digitCount value + 1 := by
  simp [scalar]
  omega

theorem scalar_nonempty (value : Nat) : 0 < (scalar value).length := by
  rw [scalar_length]
  omega

theorem readScalar_append (value : Nat) (tail : Bytes) :
    readScalar (scalar value ++ tail) = some (value, tail) := by
  have hb := digitCount_capacity value
  have hp := digitCount_pos value
  simp only [scalar, List.append_assoc, List.cons_append]
  rw [readScalar, readPrefix_frame]
  simp [hp, encodeList_length, decodeList_encodeList _ _ hb]

theorem readScalar_sound (bytes : Bytes) (value : Nat) (tail : Bytes)
    (h : readScalar bytes = some (value, tail)) : bytes = scalar value ++ tail := by
  unfold readScalar at h
  cases hs : readPrefix bytes with
  | none => simp [hs] at h
  | some pair =>
      rcases pair with ⟨count, rest⟩
      simp only [hs, bind, Option.bind] at h
      split at h <;> try contradiction
      rename_i hc
      split at h <;> try contradiction
      rename_i hd
      cases h
      have he : encodeList count (decodeList (rest.take count)) = rest.take count := by
        have hl : (rest.take count).length = count := by simp [hc.2]
        simpa only [hl] using encodeList_decodeList (rest.take count)
      rw [readPrefix_sound bytes count rest hs]
      simp only [scalar, hd, he, List.append_assoc, List.cons_append]
      rw [List.take_append_drop]

def word (value : Word) : Bytes := scalar value.size ++ value.toList

def readWord (bytes : Bytes) : Option (Word × Bytes) := do
  let (count, rest) ← readScalar bytes
  if count ≤ rest.length then some ((rest.take count).toArray, rest.drop count)
  else none

@[simp] theorem word_length (value : Word) :
    (word value).length = (scalar value.size).length + value.size := by
  simp [word]

theorem word_nonempty (value : Word) : 0 < (word value).length := by
  have := scalar_nonempty value.size
  rw [word_length]
  omega

theorem readWord_append (value : Word) (tail : Bytes) :
    readWord (word value ++ tail) = some (value, tail) := by
  simp only [word, List.append_assoc]
  rw [readWord, readScalar_append]
  simp

theorem readWord_sound (bytes : Bytes) (value : Word) (tail : Bytes)
    (h : readWord bytes = some (value, tail)) : bytes = word value ++ tail := by
  unfold readWord at h
  cases hs : readScalar bytes with
  | none => simp [hs] at h
  | some pair =>
      rcases pair with ⟨count, rest⟩
      simp only [hs, bind, Option.bind] at h
      split at h <;> try contradiction
      rename_i hc
      cases h
      rw [readScalar_sound bytes count rest hs]
      simp [word, hc, List.append_assoc]

def array (emit : α → Bytes) (values : Array α) : Bytes :=
  scalar values.size ++ values.toList.flatMap emit

def readMany (parse : Bytes → Option (α × Bytes)) : Nat → Bytes →
    Option (List α × Bytes)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes => do
      let (value, rest) ← parse bytes
      let (values, tail) ← readMany parse count rest
      pure (value :: values, tail)

/-- The byte bound is checked before the count-recursive parser is called. -/
def readArray (parse : Bytes → Option (α × Bytes)) (bytes : Bytes) :
    Option (Array α × Bytes) := do
  let (count, rest) ← readScalar bytes
  if count ≤ rest.length then
    let (values, tail) ← readMany parse count rest
    pure (values.toArray, tail)
  else none

theorem readMany_append (emit : α → Bytes) (parse : Bytes → Option (α × Bytes))
    (h : ∀ value tail, parse (emit value ++ tail) = some (value, tail))
    (values : List α) (tail : Bytes) :
    readMany parse values.length (values.flatMap emit ++ tail) = some (values, tail) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [readMany, List.append_assoc, h, ih]

theorem readMany_append_of_mem (emit : α → Bytes) (parse : Bytes → Option (α × Bytes))
    (values : List α)
    (h : ∀ value ∈ values, ∀ tail, parse (emit value ++ tail) = some (value, tail))
    (tail : Bytes) :
    readMany parse values.length (values.flatMap emit ++ tail) = some (values, tail) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      have hv := h value (by simp)
      have ht : ∀ value ∈ values, ∀ tail, parse (emit value ++ tail) = some (value, tail) :=
        fun value hm => h value (by simp [hm])
      simp [readMany, List.append_assoc, hv, ih ht]

theorem readMany_sound (emit : α → Bytes) (parse : Bytes → Option (α × Bytes))
    (hp : ∀ bytes value tail, parse bytes = some (value, tail) → bytes = emit value ++ tail)
    (count : Nat) (bytes : Bytes) (values : List α) (tail : Bytes)
    (h : readMany parse count bytes = some (values, tail)) :
    values.length = count ∧ bytes = values.flatMap emit ++ tail := by
  induction count generalizing bytes values tail with
  | zero => cases h; simp
  | succ count ih =>
      unfold readMany at h
      cases hs : parse bytes with
      | none => simp [hs] at h
      | some pair =>
          rcases pair with ⟨value, rest⟩
          simp only [hs, bind, Option.bind] at h
          cases ht : readMany parse count rest with
          | none => simp [ht] at h
          | some pair =>
              rcases pair with ⟨vs, more⟩
              simp only [ht] at h
              rcases h with ⟨rfl, rfl⟩
              obtain ⟨hl, he⟩ := ih rest vs tail ht
              exact ⟨by simp [hl], by simpa [List.append_assoc] using (hp bytes value rest hs).trans (congrArg (emit value ++ ·) he)⟩

theorem list_length_le_flatMap (emit : α → Bytes)
    (h : ∀ value, 0 < (emit value).length) (values : List α) :
    values.length ≤ (values.flatMap emit).length := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have := h value
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

theorem readArray_append (emit : α → Bytes) (parse : Bytes → Option (α × Bytes))
    (h : ∀ value tail, parse (emit value ++ tail) = some (value, tail))
    (hp : ∀ value, 0 < (emit value).length) (values : Array α) (tail : Bytes) :
    readArray parse (array emit values ++ tail) = some (values, tail) := by
  have hb := list_length_le_flatMap emit hp values.toList
  simp only [array, List.append_assoc]
  rw [readArray, readScalar_append]
  have hb' : values.size ≤ (values.toList.flatMap emit ++ tail).length := by
    simp only [Array.length_toList, List.length_append] at *
    omega
  simp only [bind, Option.bind]
  rw [if_pos hb']
  simp [← Array.length_toList, readMany_append emit parse h]

theorem readArray_append_of_mem (emit : α → Bytes) (parse : Bytes → Option (α × Bytes))
    (hp : ∀ value, 0 < (emit value).length) (values : Array α)
    (h : ∀ value ∈ values.toList, ∀ tail, parse (emit value ++ tail) = some (value, tail))
    (tail : Bytes) :
    readArray parse (array emit values ++ tail) = some (values, tail) := by
  have hb := list_length_le_flatMap emit hp values.toList
  simp only [array, List.append_assoc]
  rw [readArray, readScalar_append]
  have hb' : values.size ≤ (values.toList.flatMap emit ++ tail).length := by
    simp only [Array.length_toList, List.length_append] at *
    omega
  simp only [bind, Option.bind]
  rw [if_pos hb']
  simp [← Array.length_toList, readMany_append_of_mem emit parse values.toList h]

theorem readArray_sound (emit : α → Bytes) (parse : Bytes → Option (α × Bytes))
    (hp : ∀ bytes value tail, parse bytes = some (value, tail) → bytes = emit value ++ tail)
    (bytes : Bytes) (values : Array α) (tail : Bytes)
    (h : readArray parse bytes = some (values, tail)) : bytes = array emit values ++ tail := by
  unfold readArray at h
  cases hs : readScalar bytes with
  | none => simp [hs] at h
  | some pair =>
      rcases pair with ⟨count, rest⟩
      simp only [hs, bind, Option.bind] at h
      split at h <;> try contradiction
      cases ht : readMany parse count rest with
      | none => simp [ht] at h
      | some pair =>
          rcases pair with ⟨vs, more⟩
          simp only [ht] at h
          rcases h with ⟨rfl, rfl⟩
          obtain ⟨hl, he⟩ := readMany_sound emit parse hp count rest vs tail ht
          rw [readScalar_sound bytes count rest hs, he]
          simp [array, hl, List.append_assoc]

@[simp] theorem array_length (emit : α → Bytes) (values : Array α) :
    (array emit values).length = (scalar values.size).length +
      (values.toList.map (fun value => (emit value).length)).sum := by
  simp [array, List.length_flatMap]

theorem array_nonempty (emit : α → Bytes) (values : Array α) :
    0 < (array emit values).length := by
  have := scalar_nonempty values.size
  rw [array_length]
  omega

theorem readWord_length_bound (bytes : Bytes) (value : Word) (tail : Bytes)
    (h : readWord bytes = some (value, tail)) : value.size ≤ bytes.length := by
  rw [readWord_sound bytes value tail h]
  simp only [List.length_append, word_length]
  omega

/-- Extra supported-host cap, checked before the existing byte slice allocates. -/
def readWordBound (limit : Nat) (bytes : Bytes) : Option (Word × Bytes) := do
  let (count, _) ← readScalar bytes
  if count ≤ limit then readWord bytes else none

/-- Extra supported-host count cap, checked before any element parser runs. -/
def readArrayBound (limit : Nat) (parse : Bytes → Option (α × Bytes))
    (bytes : Bytes) : Option (Array α × Bytes) := do
  let (count, _) ← readScalar bytes
  if count ≤ limit then readArray parse bytes else none

theorem readWordBound_append (limit : Nat) (value : Word) (hl : value.size ≤ limit)
    (tail : Bytes) : readWordBound limit (word value ++ tail) = some (value, tail) := by
  have hs : readScalar (word value ++ tail) = some (value.size, value.toList ++ tail) := by
    simpa [word, List.append_assoc] using readScalar_append value.size (value.toList ++ tail)
  simp [readWordBound, hs, hl, readWord_append]

theorem readArrayBound_append (limit : Nat) (emit : α → Bytes)
    (parse : Bytes → Option (α × Bytes)) (hp : ∀ value, 0 < (emit value).length)
    (values : Array α) (hl : values.size ≤ limit)
    (h : ∀ value ∈ values.toList, ∀ tail, parse (emit value ++ tail) = some (value, tail))
    (tail : Bytes) :
    readArrayBound limit parse (array emit values ++ tail) = some (values, tail) := by
  have hs : readScalar (array emit values ++ tail) =
      some (values.size, values.toList.flatMap emit ++ tail) := by
    simpa [array, List.append_assoc] using
      readScalar_append values.size (values.toList.flatMap emit ++ tail)
  simp [readArrayBound, hs, hl, readArray_append_of_mem emit parse hp values h]

theorem readWordBound_to_readWord (limit : Nat) (bytes : Bytes) (value : Word) (tail : Bytes)
    (h : readWordBound limit bytes = some (value, tail)) :
    readWord bytes = some (value, tail) := by
  unfold readWordBound at h
  cases hs : readScalar bytes with
  | none => simp [hs] at h
  | some pair =>
      rcases pair with ⟨count, rest⟩
      simp only [hs, bind, Option.bind] at h
      split at h <;> simp_all

theorem readArrayBound_to_readArray (limit : Nat) (parse : Bytes → Option (α × Bytes))
    (bytes : Bytes) (values : Array α) (tail : Bytes)
    (h : readArrayBound limit parse bytes = some (values, tail)) :
    readArray parse bytes = some (values, tail) := by
  unfold readArrayBound at h
  cases hs : readScalar bytes with
  | none => simp [hs] at h
  | some pair =>
      rcases pair with ⟨count, rest⟩
      simp only [hs, bind, Option.bind] at h
      split at h <;> simp_all

theorem readMany_refines (p q : Bytes → Option (α × Bytes))
    (hp : ∀ bytes value tail, p bytes = some (value, tail) → q bytes = some (value, tail))
    (count : Nat) (bytes : Bytes) (values : List α) (tail : Bytes)
    (h : readMany p count bytes = some (values, tail)) :
    readMany q count bytes = some (values, tail) := by
  induction count generalizing bytes values tail with
  | zero => exact h
  | succ count ih =>
      unfold readMany at h ⊢
      cases hs : p bytes with
      | none => simp [hs] at h
      | some pair =>
          rcases pair with ⟨value, rest⟩
          simp only [hs, bind, Option.bind] at h
          cases ht : readMany p count rest with
          | none => simp [ht] at h
          | some pair =>
              rcases pair with ⟨vs, more⟩
              simp only [ht] at h
              rcases h with ⟨rfl, rfl⟩
              simp [hp bytes value rest hs, ih rest vs tail ht]

theorem readArray_refines (p q : Bytes → Option (α × Bytes))
    (hp : ∀ bytes value tail, p bytes = some (value, tail) → q bytes = some (value, tail))
    (bytes : Bytes) (values : Array α) (tail : Bytes)
    (h : readArray p bytes = some (values, tail)) :
    readArray q bytes = some (values, tail) := by
  unfold readArray at h ⊢
  cases hs : readScalar bytes with
  | none => simp [hs] at h
  | some pair =>
      rcases pair with ⟨count, rest⟩
      simp only [hs, bind, Option.bind] at h ⊢
      split at h <;> try contradiction
      rename_i hb
      rw [if_pos hb]
      cases ht : readMany p count rest with
      | none => simp [ht] at h
      | some pair =>
          rcases pair with ⟨vs, more⟩
          simp only [ht] at h
          rcases h with ⟨rfl, rfl⟩
          simp [readMany_refines p q hp count rest vs tail ht]

end RMQ.SuccinctFinal.PackedNative.BinaryCodec
