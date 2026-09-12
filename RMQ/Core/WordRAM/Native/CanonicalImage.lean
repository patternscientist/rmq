import RMQ.Core.WordRAM.Native.Canonical
import RMQ.Core.WordRAM.Native.Runtime

/-! # Canonical images use the allocation counted by the accepted theorem -/

namespace RMQ.SuccinctFinal.PackedNative
open PackedWordRAM

def canonicalImage (xs : List Int) : StorageImage :=
  StorageImage.fromReference (wordWidth xs.length) xs.length queryRegisterCount
    queryProgram (buildMemory xs)

theorem canonical_register_count_fits (n : Nat) : queryRegisterCount < 2 ^ wordWidth n := by
  have hw : 32 ≤ wordWidth n := by unfold wordWidth; omega
  exact Nat.lt_of_lt_of_le (by rw [queryRegisterCount_eq]; decide)
    (Nat.pow_le_pow_right (by decide : 0 < 2) hw)

theorem canonical_image_valid (xs : List Int) : (canonicalImage xs).Valid :=
  StorageImage.fromReference_valid (wordWidth xs.length) xs.length queryRegisterCount
    queryProgram (buildMemory xs) (wordWidth_pos xs.length) (size_lt_wordCapacity xs.length)
    (canonical_register_count_fits xs.length) (queryProgram_fits xs.length) (buildMemory_words_fit xs)

theorem canonical_image_roundtrip (xs : List Int) :
    StorageImage.decode (canonicalImage xs).encode = some (canonicalImage xs) :=
  StorageImage.decode_encode _ (canonical_image_valid xs)

theorem canonical_loaded_cells (xs : List Int) :
    (StorageImage.decode (canonicalImage xs).encode).map StorageImage.memory =
      some (LimbMachine.encodeMemory (wordWidth xs.length) (buildMemory xs)) ∧
    (StorageImage.decode (canonicalImage xs).encode).map StorageImage.code =
      some (LimbMachine.encodeCode (wordWidth xs.length) queryProgram) := by
  rw [canonical_image_roundtrip]
  exact ⟨rfl, rfl⟩

theorem canonical_image_word_count (xs : List Int) :
    (canonicalImage xs).wordCount = (buildMemory xs).length +
      (queryProgram.map Instruction.encoding).flatten.length := by
  simp [canonicalImage, StorageImage.fromReference, StorageImage.wordCount,
    LimbMachine.encodeCode, LimbMachine.encodeInstruction, LimbMachine.encodeMemory,
    List.length_flatten, List.map_map, Function.comp_def, Nat.add_comm]

/-- Numeric data/code bits plus the accepted register/PC/status scratch use the
same complete allocation bound. Image framing and byte rounding are additional. -/
theorem canonical_complete_numeric_bits (xs : List Int) :
    (canonicalImage xs).wordCount * (canonicalImage xs).width +
      (queryRegisterCount + 3) * (canonicalImage xs).width ≤
        2 * xs.length + queryCompleteRho xs.length := by
  rw [canonical_image_word_count]
  simpa [canonicalImage, StorageImage.fromReference, Nat.add_mul] using
    fullyChargedPackedQueryCapstone_holds.completeCapacity xs

theorem canonical_image_file_bits (xs : List Int) :
    8 * (canonicalImage xs).encode.size =
      ((buildMemory xs).length + (queryProgram.map Instruction.encoding).flatten.length) *
        wordWidth xs.length +
      ((buildMemory xs).length + (queryProgram.map Instruction.encoding).flatten.length) *
        (8 * LimbWord.limbCount (wordWidth xs.length) - wordWidth xs.length) +
      8 * (canonicalImage xs).framingBytes := by
  have h := StorageImage.encoded_bit_accounting _ (canonical_image_valid xs)
  rw [canonical_image_word_count] at h
  exact h

theorem canonical_initial_words (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    nativeInitialState (canonicalImage xs)
      (LimbWord.encode (wordWidth xs.length) left) (LimbWord.encode (wordWidth xs.length) right) =
      LimbMachine.State.encode (wordWidth xs.length) queryRegisterCount
        (initialState xs.length left right) := by
  simp only [nativeInitialState, canonicalImage, StorageImage.fromReference,
    LimbWord.decode_encode _ _ hl, LimbWord.decode_encode _ _ hr]
  rfl

theorem canonical_native_core (xs : List Int) (left right fuel : Nat) (observeReads : Bool)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    let output := nativeCore (canonicalImage xs)
      (LimbWord.encode (wordWidth xs.length) left) (LimbWord.encode (wordWidth xs.length) right)
      fuel observeReads
    (output.1.decode, output.2) =
      observeRun observeReads
        (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)) {} := by
  simp only [nativeCore, canonical_initial_words xs left right hl hr]
  exact canonical_limb_thin xs left right fuel observeReads hl hr

theorem canonical_supported_roundtrip (xs : List Int) (limits : StorageImage.Limits)
    (hs : (canonicalImage xs).Supported limits) :
    StorageImage.decodeSupported limits (canonicalImage xs).encode = some (canonicalImage xs) :=
  StorageImage.decodeSupported_encode _ _ (canonical_image_valid xs) hs

end RMQ.SuccinctFinal.PackedNative
