import RMQ.Core.WordRAM.Native.Binary.Cursor.Core
import RMQ.Core.WordRAM.Native.Binary.Bounds

/-! Resource-capped native decoder; implementation follows the checked byte cursor. -/

namespace RMQ.SuccinctFinal.PackedNative.BinaryCursor

open LimbWord BinaryCodec

/-- The count cap precedes digit accumulation, including on malformed input. -/
def readScalarDigits (maxDigits : Nat) : Parser Nat := fun bytes pos => do
  let (count, start) ← readPrefix bytes pos
  if 0 < count ∧ count ≤ bytes.size - start ∧ count ≤ maxDigits then
    let value := digitsAux bytes start count 0
    if digitCount value = count then some (value, start + count) else none
  else none

/-- Numeric host caps are converted to digit caps before scalar accumulation. -/
def readScalarLimit (limit : Nat) : Parser Nat := fun bytes pos => do
  let (value, next) ← readScalarDigits (digitCount limit) bytes pos
  if value ≤ limit then some (value, next) else none

theorem readScalarDigits_reject_count (maxDigits : Nat) (bytes : ByteArray)
    (pos count start : Nat) (hp : readPrefix bytes pos = some (count, start))
    (hc : maxDigits < count) : readScalarDigits maxDigits bytes pos = none := by
  have hn : ¬ count ≤ maxDigits := by omega
  simp [readScalarDigits, hp, hn]

theorem readScalarLimit_reject_count (limit : Nat) (bytes : ByteArray)
    (pos count start : Nat) (hp : readPrefix bytes pos = some (count, start))
    (hc : digitCount limit < count) : readScalarLimit limit bytes pos = none := by
  simp [readScalarLimit, readScalarDigits_reject_count _ _ _ _ _ hp hc]

theorem readScalarDigits_eq (maxDigits : Nat) (bytes : ByteArray) (pos : Nat) :
    readScalarDigits maxDigits bytes pos =
      (readScalar bytes pos).filter (fun result => decide (digitCount result.1 ≤ maxDigits)) := by
  unfold readScalarDigits readScalar
  cases hp : readPrefix bytes pos with
  | none => rfl
  | some pair =>
      rcases pair with ⟨count, start⟩
      simp only [bind, Option.bind]
      by_cases hc : 0 < count ∧ count ≤ bytes.size - start
      · by_cases hd : digitCount (digitsAux bytes start count 0) = count
        · by_cases hm : count ≤ maxDigits <;> simp [hc.1, hc.2, hd, hm, Option.filter_some]
        · simp [hc.1, hc.2, hd, Option.filter_some]
      · simp only [hc, if_false, Option.filter_none]
        have hn : ¬ (0 < count ∧ count ≤ bytes.size - start ∧ count ≤ maxDigits) :=
          fun h => hc ⟨h.1, h.2.1⟩
        simp [hn]

theorem readScalarLimit_eq (limit : Nat) (bytes : ByteArray) (pos : Nat) :
    readScalarLimit limit bytes pos =
      (readScalar bytes pos).filter (fun result => decide (result.1 ≤ limit)) := by
  unfold readScalarLimit
  rw [readScalarDigits_eq]
  cases hp : readScalar bytes pos with
  | none => rfl
  | some pair =>
      rcases pair with ⟨value, next⟩
      by_cases hl : value ≤ limit
      · have hd := digitCount_mono value limit hl
        simp [hl, hd, Option.filter_some]
      · by_cases hd : digitCount value ≤ digitCount limit <;> simp [hl, hd, Option.filter_some]

def readWordCapped (limit : Nat) : Parser Word := fun bytes pos => do
  let (count, start) ← readScalarLimit limit bytes pos
  if count ≤ bytes.size - start then readMany readByte count bytes start else none

def readArrayCapped (limit : Nat) (parse : Parser α) : Parser (Array α) := fun bytes pos => do
  let (count, start) ← readScalarLimit limit bytes pos
  if count ≤ bytes.size - start then readMany parse count bytes start else none

theorem readWordCapped_eq (limit : Nat) : readWordCapped limit = readWordBound limit := by
  funext bytes pos
  unfold readWordCapped readWordBound
  rw [readScalarLimit_eq]
  cases hp : readScalar bytes pos with
  | none => rfl
  | some pair =>
      rcases pair with ⟨count, start⟩
      by_cases hl : count ≤ limit <;> simp [hl, Option.filter_some]

theorem readArrayCapped_eq (limit : Nat) (parse : Parser α) :
    readArrayCapped limit parse = readArrayBound limit parse := by
  funext bytes pos
  unfold readArrayCapped readArrayBound
  rw [readScalarLimit_eq]
  cases hp : readScalar bytes pos with
  | none => rfl
  | some pair =>
      rcases pair with ⟨count, start⟩
      by_cases hl : count ≤ limit <;> simp [hl, Option.filter_some]

def readInstructionCapped (width : Nat) : Parser (Array Word) :=
  readArrayCapped 5 (readWordCapped (limbCount width))

theorem readInstructionCapped_eq (width : Nat) :
    readInstructionCapped width = readInstructionBound width := by
  simp [readInstructionCapped, readInstructionBound, readArrayCapped_eq, readWordCapped_eq]

def readBodyCapped (limits : StorageImage.Limits) : Parser StorageImage :=
  andThen (readScalarLimit limits.maxWidth) fun width =>
  andThen (readScalarDigits (max 1 (limbCount width))) fun inputLength =>
  andThen (readScalarLimit limits.maxRegisters) fun registerCount =>
  andThen (readArrayCapped limits.maxInstructions (readInstructionCapped width)) fun code =>
  andThen (readArrayCapped limits.maxMemoryWords (readWordCapped (limbCount width))) fun memory =>
  pureValue ⟨width, inputLength, registerCount, code, memory⟩

theorem readBodyCapped_eq (limits : StorageImage.Limits) (bytes : ByteArray) (pos : Nat) :
    readBodyCapped limits bytes pos =
      (readBodySupported limits bytes pos).filter (fun result =>
        decide (digitCount result.1.inputLength ≤ max 1 (limbCount result.1.width))) := by
  simp only [readBodyCapped, readBodySupported, andThen, readScalarLimit_eq,
    readScalarDigits_eq, readArrayCapped_eq, readWordCapped_eq, readInstructionCapped_eq]
  cases hw : readScalar bytes pos with
  | none => simp
  | some pair =>
      rcases pair with ⟨width, afterWidth⟩
      cases hn : readScalar bytes afterWidth with
      | none =>
          by_cases hwcap : width ≤ limits.maxWidth <;>
            simp [hw, hn, hwcap, Option.filter_some]
      | some pair =>
          rcases pair with ⟨inputLength, afterInput⟩
          cases hr : readScalar bytes afterInput with
          | none =>
              by_cases hwcap : width ≤ limits.maxWidth <;>
                by_cases hncap : digitCount inputLength ≤ max 1 (limbCount width) <;>
                  simp [hw, hn, hr, hwcap, hncap, Option.filter_some]
          | some pair =>
              rcases pair with ⟨registerCount, afterRegisters⟩
              by_cases hwcap : width ≤ limits.maxWidth
              · by_cases hrcap : registerCount ≤ limits.maxRegisters
                · by_cases hncap : digitCount inputLength ≤ max 1 (limbCount width)
                  · simp only [hw, hn, hr, Option.filter_some, hwcap, hrcap, hncap, decide_true,
                      if_true, and_self, bind, Option.bind]
                    cases hc : readArrayBound limits.maxInstructions
                        (readInstructionBound width) bytes afterRegisters with
                    | none => simp [BinaryCursor.andThen, hc]
                    | some pair =>
                        rcases pair with ⟨code, afterCode⟩
                        cases hm : readArrayBound limits.maxMemoryWords
                            (readWordBound (limbCount width)) bytes afterCode with
                        | none => simp [BinaryCursor.andThen, hc, hm]
                        | some pair =>
                            rcases pair with ⟨memory, afterMemory⟩
                            simp [BinaryCursor.andThen, hc, hm, pureValue, hncap, Option.filter_some]
                  · simp only [hw, hn, hr, Option.filter_some, hwcap, hrcap, hncap, decide_true,
                      decide_false, if_false, if_true, and_self, bind, Option.bind]
                    cases hc : readArrayBound limits.maxInstructions
                        (readInstructionBound width) bytes afterRegisters with
                    | none => simp [BinaryCursor.andThen, hc]
                    | some pair =>
                        rcases pair with ⟨code, afterCode⟩
                        cases hm : readArrayBound limits.maxMemoryWords
                            (readWordBound (limbCount width)) bytes afterCode with
                        | none => simp [BinaryCursor.andThen, hc, hm]
                        | some pair =>
                            rcases pair with ⟨memory, afterMemory⟩
                            simp [BinaryCursor.andThen, hc, hm, pureValue, hncap, Option.filter_some]
                · simp [hw, hn, hr, hwcap, hrcap, Option.filter_some, failure]
              · simp [hw, hn, hr, hwcap, Option.filter_some, failure]

def decodeSupported (limits : StorageImage.Limits) (bytes : ByteArray) : Option StorageImage :=
  if bytes.size ≤ limits.maxFileBytes then
    if hasMagic bytes then do
      let (image, next) ← readBodyCapped limits bytes StorageImage.magic.length
      if next = bytes.size ∧ image.valid = true then some image else none
    else none
  else none

theorem decodeSupported_eq (limits : StorageImage.Limits) (bytes : ByteArray) :
    decodeSupported limits bytes = StorageImage.decodeSupported limits bytes := by
  rw [← decodeByteBounded_eq]
  unfold decodeSupported decodeByteBounded
  rw [readBodyCapped_eq]
  by_cases hf : bytes.size ≤ limits.maxFileBytes
  · simp only [hf, if_true]
    by_cases hm : hasMagic bytes = true
    · simp only [hm, if_true]
      cases hr : readBodySupported limits bytes StorageImage.magic.length with
      | none => rfl
      | some pair =>
          rcases pair with ⟨image, next⟩
          by_cases hv : image.valid = true
          · have hn := (StorageImage.valid_iff image).1 hv
            have hd := digitCount_lt_pow image.width image.inputLength hn.2.1
            simp [hd, hv, Option.filter_some]
          · by_cases hd : digitCount image.inputLength ≤ max 1 (limbCount image.width)
            <;> simp [hv, hd, Option.filter_some]
    · simp [hm]
  · simp [hf]

theorem decodeSupported_iff (limits : StorageImage.Limits) (bytes : ByteArray)
    (image : StorageImage) :
    decodeSupported limits bytes = some image ↔
      bytes = image.encode ∧ image.Valid ∧ image.Supported limits := by
  rw [decodeSupported_eq]
  exact StorageImage.decodeSupported_iff limits bytes image

theorem decodeSupported_reject_unsupported (limits : StorageImage.Limits)
    (image : StorageImage) (hs : ¬ image.Supported limits) :
    decodeSupported limits image.encode = none := by
  cases hd : decodeSupported limits image.encode with
  | none => rfl
  | some result =>
      have hr := (decodeSupported_iff limits image.encode result).1 hd
      have he := StorageImage.raw_encode_injective image result hr.1
      subst result
      exact False.elim (hs hr.2.2)

end RMQ.SuccinctFinal.PackedNative.BinaryCursor
