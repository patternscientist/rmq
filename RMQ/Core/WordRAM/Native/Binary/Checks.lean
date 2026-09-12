import RMQ.Core.WordRAM.Native.Binary.Bounds

/-! Independent expected-type consumers and small kernel-checked image controls.
These do not execute the canonical large PQ1 fixture or replace native replay. -/

namespace RMQ.SuccinctFinal.PackedNative.BinaryChecks

open PackedWordRAM LimbWord BinaryCodec

theorem checkedImageRoundtrip : ∀ image : StorageImage,
    image.Valid → StorageImage.decode image.encode = some image :=
  StorageImage.decode_encode

theorem checkedImageInjectivity : ∀ x y : StorageImage,
    x.Valid → y.Valid → x.encode = y.encode → x = y :=
  StorageImage.encode_injective

theorem checkedRawInjectivity : ∀ x y : StorageImage, x.encode = y.encode → x = y :=
  StorageImage.raw_encode_injective

theorem checkedImageSoundness : ∀ (bytes : ByteArray) (image : StorageImage),
    StorageImage.decode bytes = some image → bytes = image.encode ∧ image.Valid := by
  intro bytes image h
  exact (StorageImage.decode_iff bytes image).1 h

theorem checkedImageValidity : ∀ image : StorageImage, image.Valid ↔
    0 < image.width ∧ image.inputLength < 2 ^ image.width ∧
    image.registerCount < 2 ^ image.width ∧
    (∀ fields ∈ image.code.toList, fields.size ≤ 5 ∧
      (∀ value ∈ fields.toList, value.size = limbCount image.width ∧
        LimbWord.decode value < 2 ^ image.width) ∧
      ∃ instruction, parseInstruction (fields.toList.map LimbWord.decode) = .ok instruction) ∧
    (∀ value ∈ image.memory.toList, value.size = limbCount image.width ∧
      LimbWord.decode value < 2 ^ image.width) := by
  intro image
  simpa only [Canonical] using StorageImage.valid_iff image

theorem checkedImageFields : ∀ image : StorageImage, image.Valid →
    (StorageImage.decode image.encode).map StorageImage.width = some image.width ∧
    (StorageImage.decode image.encode).map StorageImage.inputLength = some image.inputLength ∧
    (StorageImage.decode image.encode).map StorageImage.registerCount = some image.registerCount ∧
    (StorageImage.decode image.encode).map StorageImage.code = some image.code ∧
    (StorageImage.decode image.encode).map StorageImage.memory = some image.memory :=
  StorageImage.decoded_fields

theorem checkedImageTruncation : ∀ (image : StorageImage) (initial suffix : List UInt8),
    initial ++ suffix = image.encodeList → suffix ≠ [] →
    StorageImage.decode ⟨initial.toArray⟩ = none :=
  StorageImage.decode_truncated

theorem checkedSupportedRoundtrip : ∀ (limits : StorageImage.Limits) (image : StorageImage),
    image.Valid → image.Supported limits → StorageImage.decodeSupported limits image.encode = some image :=
  StorageImage.decodeSupported_encode

theorem checkedSupportedRefinement : ∀ (limits : StorageImage.Limits)
    (bytes : ByteArray) (image : StorageImage),
    StorageImage.decodeSupported limits bytes = some image →
    StorageImage.decode bytes = some image := StorageImage.decodeSupported_refines

theorem checkedReferenceImage : ∀ (width n registers : Nat) (program : Program)
    (memory : PackedWordRAM.Memory), 0 < width → n < 2 ^ width → registers < 2 ^ width →
    (∀ i ∈ program, i.Fits width) → (∀ value ∈ memory, value < 2 ^ width) →
    (StorageImage.mk width n registers (LimbMachine.encodeCode width program)
      (LimbMachine.encodeMemory width memory)).Valid := StorageImage.fromReference_valid

theorem checkedImageFraming : ∀ image : StorageImage,
    image.encode.size = image.framingBytes + image.storedByteCount := StorageImage.encode_size

theorem checkedImageBits : ∀ image : StorageImage, image.Valid →
    8 * image.encode.size = image.wordCount * image.width +
      image.wordCount * (8 * limbCount image.width - image.width) +
      8 * image.framingBytes := StorageImage.encoded_bit_accounting

def wideImage : StorageImage :=
  StorageImage.fromReference 176 12 4 [.halt 0] [2 ^ 175 + 41, 17]

def smallLimits : StorageImage.Limits := ⟨4096, 256, 32, 16, 16⟩

private theorem digitCount_small (value : Nat) (h : value < 256) : digitCount value = 1 := by
  have hb := digitCount_lt_pow 8 value h
  have hp := digitCount_pos value
  simp only [limbCount] at hb
  omega

private theorem scalar_small (value : Nat) (h : value < 256) :
    scalar value = [1, 0, UInt8.ofNat value] := by
  simp [scalar, digitCount_small value h, LimbWord.encodeList]

private theorem invalidImageRejected (image : StorageImage) (h : ¬ image.Valid) :
    StorageImage.decode image.encode = none := by
  cases hd : StorageImage.decode image.encode with
  | none => rfl
  | some other =>
      have hi := StorageImage.raw_encode_injective image other (StorageImage.decode_sound _ _ hd)
      subst other
      exact False.elim (h (StorageImage.decode_valid _ _ hd))

private theorem unsupportedImageRejected (limits : StorageImage.Limits) (image : StorageImage)
    (h : ¬ image.Supported limits) : StorageImage.decodeSupported limits image.encode = none := by
  cases hd : StorageImage.decodeSupported limits image.encode with
  | none => rfl
  | some other =>
      have hi := StorageImage.raw_encode_injective image other (StorageImage.decodeSupported_sound _ _ _ hd)
      subst other
      exact False.elim (h (StorageImage.decodeSupported_supported _ _ _ hd))

theorem wideImageValid : wideImage.Valid := by
  apply StorageImage.fromReference_valid
  all_goals simp [Instruction.Fits, Instruction.encoding] <;> decide

theorem wideImageRoundtrip : StorageImage.decode wideImage.encode = some wideImage :=
  checkedImageRoundtrip wideImage wideImageValid

theorem wideImageSupported : wideImage.Supported smallLimits := by
  simp [StorageImage.Supported, StorageImage.encode_size, StorageImage.framingBytes,
    StorageImage.storedByteCount, wideImage, smallLimits, StorageImage.fromReference,
    LimbMachine.encodeCode, LimbMachine.encodeInstruction, LimbMachine.encodeMemory,
    Instruction.encoding, Instruction.operands, digitCount_small, limbCount]

theorem wideImageSupportedRoundtrip :
    StorageImage.decodeSupported smallLimits wideImage.encode = some wideImage :=
  checkedSupportedRoundtrip smallLimits wideImage wideImageValid wideImageSupported

theorem scalarBeyondU64 :
    readScalar (scalar (2 ^ 128 + 19)) = some (2 ^ 128 + 19, []) := by
  simpa using readScalar_append (2 ^ 128 + 19) []

theorem scalarMinimalWidth : ∀ value : Nat, value ≠ 0 →
    256 ^ (digitCount value - 1) ≤ value ∧ value < 256 ^ digitCount value := by
  intro value hv
  exact ⟨digitCount_minimal value hv, digitCount_capacity value⟩

theorem goldenImageBytes :
    (StorageImage.fromReference 8 5 2 [.halt 1] [41]).encodeList =
      [82, 77, 81, 78, 1, 1, 0, 8, 1, 0, 5, 1, 0, 2,
        1, 0, 1, 1, 0, 2, 1, 0, 1, 8, 1, 0, 1, 1,
        1, 0, 1, 1, 0, 1, 41] := by
  simp [StorageImage.fromReference, StorageImage.encodeList, StorageImage.bodyBytes,
    StorageImage.magic, StorageImage.instructionBytes, array, word,
    LimbMachine.encodeCode, LimbMachine.encodeInstruction, LimbMachine.encodeMemory,
    Instruction.encoding, Instruction.operands, LimbWord.encode, limbCount, scalar_small,
    LimbWord.encodeList]

theorem scalarZeroByteLengthRejected : readScalar [0] = none := by decide

theorem scalarNonminimalRejected : readScalar [1, 1, 0, 0, 0] = none := by
  simp [readScalar, readPrefix, LimbWord.decodeList, digitCount_small]

theorem scalarInvalidMarkerRejected : readScalar [2, 0, 0] = none := by decide

theorem scalarTruncatedDigitsRejected : readScalar [1, 1, 0, 7] = none := by decide

theorem wordDeclaredLengthRejected : readWord (scalar 1000000 ++ [7]) = none := by
  simp [readWord, readScalar_append]

theorem imageBadMagicRejected :
    StorageImage.decode ⟨([83, 77, 81, 78, 1] ++ wideImage.bodyBytes).toArray⟩ = none := by decide

theorem imageBadVersionRejected :
    StorageImage.decode ⟨([82, 77, 81, 78, 2] ++ wideImage.bodyBytes).toArray⟩ = none := by decide

theorem imageTrailingByteRejected :
    StorageImage.decode ⟨(wideImage.encodeList ++ [0]).toArray⟩ = none := by
  simp [StorageImage.decode, StorageImage.read_append]

theorem imageZeroWidthRejected :
    StorageImage.decode (StorageImage.mk 0 0 0 #[] #[]).encode = none := by
  apply invalidImageRejected
  intro h
  exact Nat.lt_irrefl 0 ((StorageImage.valid_iff _).1 h).1

theorem imageMalformedTagRejected :
    StorageImage.decode
      (StorageImage.mk 8 0 4 #[#[LimbWord.encode 8 99, LimbWord.encode 8 0]] #[]).encode = none := by
  apply invalidImageRejected
  intro h
  have valid := (StorageImage.valid_iff
    (StorageImage.mk 8 0 4 #[#[LimbWord.encode 8 99, LimbWord.encode 8 0]] #[])).1 h
  have hc := valid.2.2.2.1 #[LimbWord.encode 8 99, LimbWord.encode 8 0]
    (by exact List.mem_cons_self)
  obtain ⟨instruction, hp⟩ := hc.2.2
  have hd := LimbWord.decode_encode 8 99 (by decide)
  have hz := LimbWord.decode_encode 8 0 (by decide)
  have rejected : parseInstruction [99, 0] = .error "instruction shape" := rfl
  have hp' : parseInstruction [99, 0] = .ok instruction := by
    simpa only [List.toList_toArray, List.map_cons, List.map_nil, hd, hz] using hp
  have bad := rejected.symm.trans hp'
  cases bad

theorem imageWrongWordLengthRejected :
    StorageImage.decode
      (StorageImage.mk 168 0 4 (LimbMachine.encodeCode 168 [.halt 0]) #[#[0]]).encode = none := by
  apply invalidImageRejected
  intro h
  have hm := ((StorageImage.valid_iff _).1 h).2.2.2.2 #[0] (by simp)
  have hs := hm.1
  simp [limbCount] at hs

theorem imageHighPaddingRejected :
    StorageImage.decode
      (StorageImage.mk 9 0 4 (LimbMachine.encodeCode 9 [.halt 0])
        #[(LimbWord.encodeList 2 (2 ^ 9)).toArray]).encode = none := by
  apply invalidImageRejected
  intro h
  have hm := ((StorageImage.valid_iff _).1 h).2.2.2.2
    (LimbWord.encodeList 2 (2 ^ 9)).toArray (by simp)
  have hd : LimbWord.decode (LimbWord.encodeList 2 (2 ^ 9)).toArray = 2 ^ 9 := by
    simpa only [LimbWord.decode, List.toList_toArray] using
      LimbWord.decodeList_encodeList 2 (2 ^ 9) (by decide)
  have hv := hm.2
  rw [hd] at hv
  exact Nat.lt_irrefl _ hv

theorem imageHugeInstructionCountRejected :
    StorageImage.decode ⟨(StorageImage.magic ++ scalar 168 ++ scalar 12 ++ scalar 4 ++
      scalar (2 ^ 128)).toArray⟩ = none := by
  have hs : readScalar (scalar (2 ^ 128)) = some (2 ^ 128, []) := by
    simpa using readScalar_append (2 ^ 128) []
  simp [StorageImage.decode, StorageImage.read, StorageImage.readBody,
    List.append_assoc, readScalar_append, readArray, hs]

theorem imageFileLimitRejected :
    StorageImage.decodeSupported { smallLimits with maxFileBytes := 0 } wideImage.encode = none := by
  apply unsupportedImageRejected
  intro h
  have hf := h.1
  change wideImage.encode.size ≤ 0 at hf
  rw [StorageImage.encode_size] at hf
  have hb : 5 ≤ wideImage.framingBytes := by unfold StorageImage.framingBytes; omega
  omega

theorem imageWidthLimitRejected :
    StorageImage.decodeSupported { smallLimits with maxWidth := 64 } wideImage.encode = none := by
  apply unsupportedImageRejected
  intro h
  have hw := h.2.1
  change 176 ≤ 64 at hw
  omega

theorem imageRegisterLimitRejected :
    StorageImage.decodeSupported { smallLimits with maxRegisters := 3 } wideImage.encode = none := by
  apply unsupportedImageRejected
  intro h
  have hr := h.2.2.1
  change 4 ≤ 3 at hr
  omega

theorem imageInstructionLimitRejected :
    StorageImage.decodeSupported { smallLimits with maxInstructions := 0 } wideImage.encode = none := by
  apply unsupportedImageRejected
  intro h
  have hc := h.2.2.2.1
  change 1 ≤ 0 at hc
  omega

theorem imageMemoryLimitRejected :
    StorageImage.decodeSupported { smallLimits with maxMemoryWords := 0 } wideImage.encode = none := by
  apply unsupportedImageRejected
  intro h
  have hm := h.2.2.2.2
  change 2 ≤ 0 at hm
  omega

#print axioms checkedImageRoundtrip
#print axioms checkedImageInjectivity
#print axioms checkedRawInjectivity
#print axioms checkedImageSoundness
#print axioms checkedImageValidity
#print axioms checkedImageFields
#print axioms checkedImageTruncation
#print axioms checkedSupportedRoundtrip
#print axioms checkedSupportedRefinement
#print axioms checkedReferenceImage
#print axioms checkedImageFraming
#print axioms checkedImageBits
#print axioms scalarMinimalWidth

end RMQ.SuccinctFinal.PackedNative.BinaryChecks
