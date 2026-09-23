import RMQ.Core.WordRAM.Native.Binary

/-! Successful supported decoding enforces every explicit host cap.
This proof-only layer leaves the all-Nat reference codec unchanged. -/

namespace RMQ.SuccinctFinal.PackedNative.BinaryCodec

theorem digitCount_mono (a b : Nat) (h : a ≤ b) : digitCount a ≤ digitCount b := by
  by_cases ha : a = 0
  · subst a
    simp [digitCount]
  · have hb : b ≠ 0 := by omega
    have hl : a.log2 ≤ b.log2 :=
      (Nat.le_log2 hb).2 (Nat.le_trans (Nat.log2_self_le ha) h)
    unfold digitCount
    omega

theorem digitCount_lt_pow (width value : Nat) (h : value < 2 ^ width) :
    digitCount value ≤ max 1 (LimbWord.limbCount width) := by
  by_cases hv : value = 0
  · subst value
    simpa [digitCount] using Nat.le_max_left 1 (LimbWord.limbCount width)
  · have hl : value.log2 < width := (Nat.log2_lt hv).2 h
    have hc : digitCount value ≤ LimbWord.limbCount width := by
      unfold digitCount LimbWord.limbCount
      omega
    exact Nat.le_trans hc (Nat.le_max_right _ _)

theorem readMany_length (parse : Bytes → Option (α × Bytes)) (count : Nat)
    (bytes : Bytes) (values : List α) (tail : Bytes)
    (h : readMany parse count bytes = some (values, tail)) : values.length = count := by
  induction count generalizing bytes values tail with
  | zero =>
      simp only [readMany, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
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
              simp [ih rest vs tail ht]

theorem readArrayBound_limit (limit : Nat) (parse : Bytes → Option (α × Bytes))
    (bytes : Bytes) (values : Array α) (tail : Bytes)
    (h : readArrayBound limit parse bytes = some (values, tail)) : values.size ≤ limit := by
  unfold readArrayBound at h
  cases hs : readScalar bytes with
  | none => simp [hs] at h
  | some pair =>
      rcases pair with ⟨count, rest⟩
      simp only [hs, bind, Option.bind] at h
      split at h <;> try contradiction
      rename_i hcap
      unfold readArray at h
      simp only [hs, bind, Option.bind] at h
      split at h <;> try contradiction
      cases ht : readMany parse count rest with
      | none => simp [ht] at h
      | some pair =>
          rcases pair with ⟨vs, more⟩
          simp only [ht] at h
          rcases h with ⟨rfl, rfl⟩
          simpa [readMany_length parse count rest vs tail ht] using hcap

end RMQ.SuccinctFinal.PackedNative.BinaryCodec

namespace RMQ.SuccinctFinal.PackedNative.StorageImage

open BinaryCodec LimbWord

theorem readBodySupported_bounds (limits : Limits) (bytes : Bytes)
    (image : StorageImage) (tail : Bytes)
    (h : readBodySupported limits bytes = some (image, tail)) :
    image.width ≤ limits.maxWidth ∧ image.registerCount ≤ limits.maxRegisters ∧
    image.code.size ≤ limits.maxInstructions ∧ image.memory.size ≤ limits.maxMemoryWords := by
  unfold readBodySupported at h
  cases hw : readScalar bytes with
  | none => simp [hw] at h
  | some pair =>
    rcases pair with ⟨width, afterWidth⟩
    simp only [hw, bind, Option.bind] at h
    cases hn : readScalar afterWidth with
    | none => simp [hn] at h
    | some pair =>
      rcases pair with ⟨inputLength, afterInput⟩
      simp only [hn] at h
      cases hr : readScalar afterInput with
      | none => simp [hr] at h
      | some pair =>
        rcases pair with ⟨registerCount, afterRegisters⟩
        simp only [hr] at h
        split at h <;> try contradiction
        rename_i hcap
        cases hc : readArrayBound limits.maxInstructions (readInstructionBound width) afterRegisters with
        | none => simp [hc] at h
        | some pair =>
          rcases pair with ⟨code, afterCode⟩
          simp only [hc] at h
          cases hm : readArrayBound limits.maxMemoryWords (readWordBound (limbCount width)) afterCode with
          | none => simp [hm] at h
          | some pair =>
            rcases pair with ⟨memory, afterMemory⟩
            simp only [hm] at h
            cases h
            exact ⟨hcap.1, hcap.2,
              readArrayBound_limit _ _ _ _ _ hc, readArrayBound_limit _ _ _ _ _ hm⟩

theorem decodeSupported_supported (limits : Limits) (bytes : ByteArray) (image : StorageImage)
    (h : decodeSupported limits bytes = some image) : image.Supported limits := by
  have he := decodeSupported_sound limits bytes image h
  unfold decodeSupported at h
  split at h <;> try contradiction
  rename_i hfile
  dsimp only at h
  split at h <;> try contradiction
  cases hr : readBodySupported limits (bytes.data.toList.drop magic.length) with
  | none => simp [hr] at h
  | some pair =>
      rcases pair with ⟨result, rest⟩
      simp only [hr, bind, Option.bind] at h
      split at h <;> try contradiction
      cases h
      refine ⟨?_, readBodySupported_bounds limits _ _ _ hr⟩
      rw [← he]
      exact hfile

theorem decodeSupported_iff (limits : Limits) (bytes : ByteArray) (image : StorageImage) :
    decodeSupported limits bytes = some image ↔
      bytes = image.encode ∧ image.Valid ∧ image.Supported limits := by
  constructor
  · intro h
    exact ⟨decodeSupported_sound _ _ _ h, decodeSupported_valid _ _ _ h,
      decodeSupported_supported _ _ _ h⟩
  · rintro ⟨rfl, hv, hs⟩
    exact decodeSupported_encode limits image hv hs

end RMQ.SuccinctFinal.PackedNative.StorageImage

namespace RMQ.SuccinctFinal.PackedNative.BinaryChecks

theorem checkedSupportedCaps : ∀ (limits : StorageImage.Limits)
    (bytes : ByteArray) (image : StorageImage),
    StorageImage.decodeSupported limits bytes = some image →
      image.encode.size ≤ limits.maxFileBytes ∧ image.width ≤ limits.maxWidth ∧
      image.registerCount ≤ limits.maxRegisters ∧ image.code.size ≤ limits.maxInstructions ∧
      image.memory.size ≤ limits.maxMemoryWords := StorageImage.decodeSupported_supported

theorem checkedSupportedExactDomain : ∀ (limits : StorageImage.Limits)
    (bytes : ByteArray) (image : StorageImage),
    StorageImage.decodeSupported limits bytes = some image ↔
      bytes = image.encode ∧ image.Valid ∧ image.Supported limits := StorageImage.decodeSupported_iff

#print axioms checkedSupportedCaps
#print axioms checkedSupportedExactDomain
#print axioms BinaryCodec.digitCount_mono
#print axioms BinaryCodec.digitCount_lt_pow

end RMQ.SuccinctFinal.PackedNative.BinaryChecks
