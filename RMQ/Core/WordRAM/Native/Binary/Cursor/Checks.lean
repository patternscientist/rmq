import RMQ.Core.WordRAM.Native.Binary.Cursor

/-! Independent exact parser correspondence and direct indexed-loader controls. -/

namespace RMQ.SuccinctFinal.PackedNative.BinaryCursor.Checks

example (limits : StorageImage.Limits) (bytes : ByteArray) :
    BinaryCursor.decodeSupported limits bytes = StorageImage.decodeSupported limits bytes :=
  decodeSupported_eq limits bytes

example (limits : StorageImage.Limits) (image : StorageImage)
    (hv : image.Valid) (hs : image.Supported limits) :
    BinaryCursor.decodeSupported limits image.encode = some image := by
  rw [decodeSupported_eq]
  exact StorageImage.decodeSupported_encode limits image hv hs

example (limits : StorageImage.Limits) (bytes : ByteArray) (image : StorageImage)
    (h : BinaryCursor.decodeSupported limits bytes = some image) :
    bytes = image.encode ∧ image.Valid := by
  rw [decodeSupported_eq] at h
  exact ⟨StorageImage.decodeSupported_sound limits bytes image h,
    StorageImage.decodeSupported_valid limits bytes image h⟩

example (limits : StorageImage.Limits) (input : ByteArray) (image : StorageImage)
    (h : BinaryCursor.decodeSupported limits input = some image) :
    input.size ≤ limits.maxFileBytes ∧ image.width ≤ limits.maxWidth ∧
      image.registerCount ≤ limits.maxRegisters ∧ image.code.size ≤ limits.maxInstructions ∧
      image.memory.size ≤ limits.maxMemoryWords := by
  have he := (BinaryCursor.decodeSupported_iff limits input image).1 h
  rw [he.1]
  exact he.2.2

example (bytes : ByteArray) (pos : Nat) (hp : pos ≤ bytes.size) :
    (BinaryCursor.readScalar bytes pos).map (fun result => (result.1, bytes.data.toList.drop result.2)) =
      BinaryCodec.readScalar (bytes.data.toList.drop pos) :=
  readScalar_correct.result bytes pos hp

example (limit : Nat) (bytes : ByteArray) (pos : Nat) (hp : pos ≤ bytes.size) :
    (BinaryCursor.readWordCapped limit bytes pos).map
      (fun result => (result.1, bytes.data.toList.drop result.2)) =
      BinaryCodec.readWordBound limit (bytes.data.toList.drop pos) := by
  rw [readWordCapped_eq]
  exact (readWordBound_correct limit).result bytes pos hp

example (limit : Nat) (input : ByteArray) (pos : Nat) :
    BinaryCursor.readScalarLimit limit input pos =
      (BinaryCursor.readScalar input pos).filter (fun result => decide (result.1 ≤ limit)) :=
  readScalarLimit_eq limit input pos

def bytes (values : List UInt8) : ByteArray := ⟨values.toArray⟩
example : BinaryCursor.readScalar (bytes [1,0,0]) 0 = some (0,3) := by
  change (if BinaryCodec.digitCount 0 = 1 then some (0,3) else none) = some (0,3)
  simp [BinaryCodec.digitCount]
example : BinaryCursor.readScalar (bytes [1,0,255]) 0 = some (255,3) := by
  change (if BinaryCodec.digitCount 255 = 1 then some (255,3) else none) = some (255,3)
  simp +decide [BinaryCodec.digitCount, Nat.log2]
example : BinaryCursor.readScalar (bytes [1,1,0,0,1]) 0 = some (256,5) := by
  change (if BinaryCodec.digitCount 256 = 2 then some (256,5) else none) = some (256,5)
  simp +decide [BinaryCodec.digitCount, Nat.log2]
example : BinaryCursor.readScalar (bytes [0]) 0 = none := by rfl
example : BinaryCursor.readScalar (bytes [2]) 0 = none := by rfl
example : BinaryCursor.readScalar (bytes [1,1]) 0 = none := by rfl
example : BinaryCursor.readScalar (bytes [1,1,0,1,0]) 0 = none := by
  change (if BinaryCodec.digitCount 1 = 2 then some (1,5) else none) = none
  simp +decide [BinaryCodec.digitCount, Nat.log2]
example : BinaryCursor.readWordCapped 1 (bytes [1,0,2,17,19]) 0 = none := by
  have hs : readScalar (bytes [1,0,2,17,19]) 0 = some (2,3) := by
    change (if BinaryCodec.digitCount 2 = 1 then some (2,3) else none) = some (2,3)
    simp +decide [BinaryCodec.digitCount, Nat.log2]
  rw [readWordCapped_eq]
  simp only [readWordBound, hs]
  rfl
example : BinaryCursor.readWordCapped 2 (bytes [1,0,2,17,19]) 0 = some (#[17,19],5) := by
  have hs : readScalar (bytes [1,0,2,17,19]) 0 = some (2,3) := by
    change (if BinaryCodec.digitCount 2 = 1 then some (2,3) else none) = some (2,3)
    simp +decide [BinaryCodec.digitCount, Nat.log2]
  rw [readWordCapped_eq]
  simp only [readWordBound, hs]
  rfl
example : BinaryCursor.readWordCapped 2 (bytes [1,0,2,17]) 0 = none := by
  have hs : readScalar (bytes [1,0,2,17]) 0 = some (2,3) := by
    change (if BinaryCodec.digitCount 2 = 1 then some (2,3) else none) = some (2,3)
    simp +decide [BinaryCodec.digitCount, Nat.log2]
  rw [readWordCapped_eq]
  simp only [readWordBound, hs]
  rfl

def limits : StorageImage.Limits := ⟨4096,32,16,16,16⟩
def sample : StorageImage := StorageImage.fromReference 8 0 2
  [.constant 0 9, .halt 0] [23]

theorem sampleValid : sample.Valid := by
  apply StorageImage.fromReference_valid
  all_goals simp [PackedWordRAM.Instruction.Fits, PackedWordRAM.Instruction.encoding] <;> decide

theorem sampleSize : sample.encode.size = 50 := by
  simp +decide [sample, StorageImage.fromReference, StorageImage.encode,
    StorageImage.encodeList, StorageImage.bodyBytes, StorageImage.instructionBytes,
    StorageImage.magic, BinaryCodec.array, BinaryCodec.word, BinaryCodec.scalar,
    BinaryCodec.digitCount, Nat.log2, LimbMachine.encodeCode,
    LimbMachine.encodeInstruction, LimbMachine.encodeMemory, LimbWord.encode,
    LimbWord.encodeList, LimbWord.limbCount, PackedWordRAM.Instruction.encoding,
    PackedWordRAM.Instruction.operands, ByteArray.size]

theorem sampleSupported : sample.Supported limits := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  rw [sampleSize]
  decide

example : BinaryCursor.decodeSupported limits sample.encode = some sample := by
  rw [decodeSupported_eq]
  exact StorageImage.decodeSupported_encode limits sample sampleValid sampleSupported
example : BinaryCursor.decodeSupported limits (bytes [82,77,81,78,1]) = none := by rfl
example : BinaryCursor.decodeSupported limits (bytes [82,77,81,78,2]) = none := by rfl
example : BinaryCursor.decodeSupported ⟨0,32,16,16,16⟩ sample.encode = none := by
  apply decodeSupported_reject_unsupported
  intro hs
  have hf := hs.1
  rw [sampleSize] at hf
  change 50 ≤ 0 at hf
  omega
example : BinaryCursor.decodeSupported ⟨4096,7,16,16,16⟩ sample.encode = none := by
  apply decodeSupported_reject_unsupported
  intro hs
  have hw : 8 ≤ 7 := hs.2.1
  omega
example : BinaryCursor.decodeSupported ⟨4096,32,1,16,16⟩ sample.encode = none := by
  apply decodeSupported_reject_unsupported
  intro hs
  have hr : 2 ≤ 1 := hs.2.2.1
  omega
example : BinaryCursor.decodeSupported ⟨4096,32,16,1,16⟩ sample.encode = none := by
  apply decodeSupported_reject_unsupported
  intro hs
  have hc : 2 ≤ 1 := hs.2.2.2.1
  omega
example : BinaryCursor.decodeSupported ⟨4096,32,16,16,0⟩ sample.encode = none := by
  apply decodeSupported_reject_unsupported
  intro hs
  have hm : 1 ≤ 0 := hs.2.2.2.2
  omega

example (maxDigits : Nat) (input : ByteArray) (pos count start : Nat)
    (hp : readPrefix input pos = some (count, start)) (hc : maxDigits < count) :
    readScalarDigits maxDigits input pos = none :=
  readScalarDigits_reject_count maxDigits input pos count start hp hc

example : readScalarDigits 1 (bytes [1,1,0,0,1]) 0 = none := by rfl
example : readScalarLimit 4096 (bytes [1,1,1,0,255,255,255]) 0 = none := by
  apply readScalarLimit_reject_count 4096 _ 0 3 4 rfl
  simp +decide [BinaryCodec.digitCount, Nat.log2]

example : max 1 (LimbWord.limbCount 4096) = 512 := rfl

#print axioms readByte_correct
#print axioms readPrefix_correct
#print axioms digitsAux_result
#print axioms readScalar_correct
#print axioms readWordBound_correct
#print axioms readArrayBound_correct
#print axioms readBodySupported_correct
#print axioms decodeSupported_eq
#print axioms readScalarDigits_reject_count
#print axioms decodeSupported_iff

end RMQ.SuccinctFinal.PackedNative.BinaryCursor.Checks
