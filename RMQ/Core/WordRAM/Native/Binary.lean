import RMQ.Core.WordRAM.Native.Binary.Codec
import RMQ.Core.WordRAM.Native.Machine

/-!
# Version1 native storage images

The image stores the exact limb-machine Code and Memory arrays. Bytes are
little-endian inside each word. Scalar framing supports all natural values;
finite host limits are a separate checked interface. List/Array/ByteArray
conversion and parser temporaries are runtime storage, not numeric payload.
-/

namespace RMQ.SuccinctFinal.PackedNative

open PackedWordRAM LimbWord

structure StorageImage where
  width : Nat
  inputLength : Nat
  registerCount : Nat
  code : LimbMachine.Code
  memory : LimbMachine.Memory
deriving Repr, DecidableEq

namespace StorageImage

open BinaryCodec

def magic : Bytes := [82, 77, 81, 78, 1]

def instructionBytes (fields : Array Word) : Bytes := BinaryCodec.array word fields

def readInstructionBytes : Bytes → Option (Array Word × Bytes) := readArray readWord

theorem readInstructionBytes_append (fields : Array Word) (tail : Bytes) :
    readInstructionBytes (instructionBytes fields ++ tail) = some (fields, tail) :=
  readArray_append word readWord readWord_append word_nonempty fields tail

theorem readInstructionBytes_sound (bytes : Bytes) (fields : Array Word) (tail : Bytes)
    (h : readInstructionBytes bytes = some (fields, tail)) :
    bytes = instructionBytes fields ++ tail :=
  readArray_sound word readWord readWord_sound bytes fields tail h

def bodyBytes (image : StorageImage) : Bytes :=
  scalar image.width ++ scalar image.inputLength ++ scalar image.registerCount ++
  BinaryCodec.array instructionBytes image.code ++ BinaryCodec.array word image.memory

def encodeList (image : StorageImage) : Bytes := magic ++ image.bodyBytes

def encode (image : StorageImage) : ByteArray := ⟨image.encodeList.toArray⟩

def readBody (bytes : Bytes) : Option (StorageImage × Bytes) := do
  let (width, rest) ← readScalar bytes
  let (inputLength, rest) ← readScalar rest
  let (registerCount, rest) ← readScalar rest
  let (code, rest) ← readArray readInstructionBytes rest
  let (memory, rest) ← readArray readWord rest
  pure (⟨width, inputLength, registerCount, code, memory⟩, rest)

def read (bytes : Bytes) : Option (StorageImage × Bytes) :=
  if bytes.take magic.length = magic then readBody (bytes.drop magic.length) else none

theorem readBody_append (image : StorageImage) (tail : Bytes) :
    readBody (image.bodyBytes ++ tail) = some (image, tail) := by
  cases image
  simp [bodyBytes, readBody, List.append_assoc, readScalar_append,
    readArray_append instructionBytes readInstructionBytes readInstructionBytes_append
      (array_nonempty word), readArray_append word readWord readWord_append word_nonempty]

theorem readBody_sound (bytes : Bytes) (image : StorageImage) (tail : Bytes)
    (h : readBody bytes = some (image, tail)) : bytes = image.bodyBytes ++ tail := by
  unfold readBody at h
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
        cases hc : readArray readInstructionBytes afterRegisters with
        | none => simp [hc] at h
        | some pair =>
          rcases pair with ⟨code, afterCode⟩
          simp only [hc] at h
          cases hm : readArray readWord afterCode with
          | none => simp [hm] at h
          | some pair =>
            rcases pair with ⟨memory, afterMemory⟩
            simp only [hm] at h
            have he : bytes =
                (StorageImage.mk width inputLength registerCount code memory).bodyBytes ++
                  afterMemory := by
              rw [readScalar_sound _ _ _ hw, readScalar_sound _ _ _ hn,
                readScalar_sound _ _ _ hr,
                readArray_sound instructionBytes readInstructionBytes readInstructionBytes_sound _ _ _ hc,
                readArray_sound word readWord readWord_sound _ _ _ hm]
              simp [bodyBytes, List.append_assoc]
            cases h
            exact he

theorem read_append (image : StorageImage) (tail : Bytes) :
    read (image.encodeList ++ tail) = some (image, tail) := by
  simp [read, encodeList, List.append_assoc, readBody_append]

theorem read_sound (bytes : Bytes) (image : StorageImage) (tail : Bytes)
    (h : read bytes = some (image, tail)) : bytes = image.encodeList ++ tail := by
  unfold read at h
  split at h <;> try contradiction
  rename_i hm
  have hb := readBody_sound _ _ _ h
  have he := List.take_append_drop magic.length bytes
  rw [hm, hb] at he
  simpa [encodeList, List.append_assoc] using he.symm

/-- Avoid allocating 2^width merely to validate a hostile scalar header. -/
def fits (width value : Nat) : Bool := decide (value = 0 ∨ value.log2 < width)

theorem fits_iff (width value : Nat) : fits width value = true ↔ value < 2 ^ width := by
  simp only [fits, decide_eq_true_eq]
  by_cases hv : value = 0
  · simp [hv, Nat.pow_pos (by decide : 0 < 2)]
  · simp [hv, Nat.log2_lt hv]

def canonicalWord (width : Nat) (value : Word) : Bool :=
  decide (value.size = limbCount width) && fits width (LimbWord.decode value)

theorem canonicalWord_iff (width : Nat) (value : Word) :
    canonicalWord width value = true ↔ Canonical width value := by
  simp [canonicalWord, fits_iff, Canonical]

def validInstruction (width : Nat) (fields : Array Word) : Bool :=
  decide (fields.size ≤ 5) && fields.toList.all (canonicalWord width) &&
    match parseInstruction (fields.toList.map LimbWord.decode) with
    | .ok _ => true
    | .error _ => false

theorem validInstruction_iff (width : Nat) (fields : Array Word) :
    validInstruction width fields = true ↔ fields.size ≤ 5 ∧
      (∀ value ∈ fields.toList, Canonical width value) ∧
      ∃ instruction, parseInstruction (fields.toList.map LimbWord.decode) = .ok instruction := by
  unfold validInstruction
  cases hp : parseInstruction (fields.toList.map LimbWord.decode) <;>
    simp [canonicalWord_iff, List.all_eq_true, and_assoc, -Array.all_toList]

def valid (image : StorageImage) : Bool :=
  decide (0 < image.width) && fits image.width image.inputLength &&
  fits image.width image.registerCount && image.code.toList.all (validInstruction image.width) &&
  image.memory.toList.all (canonicalWord image.width)

def Valid (image : StorageImage) : Prop := image.valid = true

theorem valid_iff (image : StorageImage) : image.Valid ↔
    0 < image.width ∧ image.inputLength < 2 ^ image.width ∧
    image.registerCount < 2 ^ image.width ∧
    (∀ fields ∈ image.code.toList, fields.size ≤ 5 ∧
      (∀ value ∈ fields.toList, Canonical image.width value) ∧
      ∃ instruction, parseInstruction (fields.toList.map LimbWord.decode) = .ok instruction) ∧
    (∀ value ∈ image.memory.toList, Canonical image.width value) := by
  simp [Valid, valid, fits_iff, validInstruction_iff, canonicalWord_iff,
    List.all_eq_true, and_assoc, -Array.all_toList]

theorem validInstruction_encoded (width : Nat) (instruction : Instruction)
    (h : instruction.Fits width) :
    validInstruction width (LimbMachine.encodeInstruction width instruction) = true := by
  have hs : (LimbMachine.encodeInstruction width instruction).size ≤ 5 := by
    simpa [LimbMachine.encodeInstruction] using LimbMachine.instruction_length instruction
  have hc : ∀ value ∈ (LimbMachine.encodeInstruction width instruction).toList,
      Canonical width value := by
    simp only [LimbMachine.encodeInstruction, List.toList_toArray, List.mem_map]
    intro value hv
    obtain ⟨number, hn, rfl⟩ := hv
    exact canonical_encode width number (h number hn)
  refine (validInstruction_iff _ _).2 ⟨hs, hc, instruction, ?_⟩
  have hd := LimbMachine.decodeInstruction_encode width instruction h
  have ha : (LimbMachine.encodeInstruction width instruction).toList.all
      (fun value => decide (Canonical width value)) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hc
  unfold LimbMachine.decodeInstruction at hd
  rw [if_pos hs, if_pos ha] at hd
  exact hd

/-- This is the machine's own finite code/store encoding, with no sibling data. -/
def fromReference (width inputLength registerCount : Nat) (program : Program)
    (memory : PackedWordRAM.Memory) : StorageImage :=
  ⟨width, inputLength, registerCount, LimbMachine.encodeCode width program,
    LimbMachine.encodeMemory width memory⟩

theorem fromReference_valid (width inputLength registerCount : Nat) (program : Program)
    (memory : PackedWordRAM.Memory) (hw : 0 < width)
    (hn : inputLength < 2 ^ width) (hr : registerCount < 2 ^ width)
    (hp : ∀ instruction ∈ program, instruction.Fits width)
    (hm : ∀ value ∈ memory, value < 2 ^ width) :
    (fromReference width inputLength registerCount program memory).Valid := by
  have hc : ∀ fields ∈ (LimbMachine.encodeCode width program).toList,
      validInstruction width fields = true := by
    simp only [LimbMachine.encodeCode, List.toList_toArray, List.mem_map]
    intro fields hf
    obtain ⟨instruction, hi, rfl⟩ := hf
    exact validInstruction_encoded width instruction (hp instruction hi)
  have hmem : ∀ value ∈ (LimbMachine.encodeMemory width memory).toList,
      canonicalWord width value = true := by
    simp only [LimbMachine.encodeMemory, List.toList_toArray, List.mem_map]
    intro value hv
    obtain ⟨number, hi, rfl⟩ := hv
    exact (canonicalWord_iff _ _).2 (canonical_encode _ _ (hm number hi))
  simp only [fromReference, Valid, valid, Bool.and_eq_true, decide_eq_true_eq,
    fits_iff, List.all_eq_true, and_assoc]
  exact ⟨hw, hn, hr, hc, hmem⟩

def decode (bytes : ByteArray) : Option StorageImage := do
  let (image, rest) ← read bytes.data.toList
  if rest.isEmpty && image.valid then some image else none

theorem decode_encode (image : StorageImage) (h : image.Valid) :
    decode (encode image) = some image := by
  have hr : read image.encodeList = some (image, []) := by simpa using read_append image []
  have hv : image.valid = true := h
  simp [decode, encode, hr, hv]

theorem encode_injective (x y : StorageImage) (hx : x.Valid) (hy : y.Valid)
    (h : encode x = encode y) : x = y := by
  have := congrArg decode h
  simpa [decode_encode x hx, decode_encode y hy] using this

/-- Framing itself is injective even before semantic image validation. -/
theorem raw_encode_injective (x y : StorageImage) (h : encode x = encode y) : x = y := by
  have hx : read x.encodeList = some (x, []) := by simpa using read_append x []
  have hy : read y.encodeList = some (y, []) := by simpa using read_append y []
  have he := congrArg (fun bytes : ByteArray => read bytes.data.toList) h
  simpa [encode, hx, hy] using he

theorem decode_valid (bytes : ByteArray) (image : StorageImage)
    (h : decode bytes = some image) : image.Valid := by
  unfold decode at h
  cases hr : read bytes.data.toList with
  | none => simp [hr] at h
  | some pair =>
      rcases pair with ⟨result, rest⟩
      simp only [hr, bind, Option.bind] at h
      split at h <;> try contradiction
      rename_i hv
      cases h
      exact (Bool.and_eq_true_iff.mp hv).2

theorem decode_sound (bytes : ByteArray) (image : StorageImage)
    (h : decode bytes = some image) : bytes = image.encode := by
  unfold decode at h
  cases hr : read bytes.data.toList with
  | none => simp [hr] at h
  | some pair =>
      rcases pair with ⟨result, rest⟩
      simp only [hr, bind, Option.bind] at h
      split at h <;> try contradiction
      rename_i hv
      have hempty : rest = [] := by simpa using (Bool.and_eq_true_iff.mp hv).1
      subst rest
      cases h
      have he := read_sound _ _ _ hr
      have ha := congrArg List.toArray he
      cases bytes
      simpa [encode] using congrArg ByteArray.mk ha

theorem decode_iff (bytes : ByteArray) (image : StorageImage) :
    decode bytes = some image ↔ bytes = image.encode ∧ image.Valid := by
  constructor
  · intro h
    exact ⟨decode_sound _ _ h, decode_valid _ _ h⟩
  · rintro ⟨rfl, hv⟩
    exact decode_encode image hv

theorem decode_bad_magic (bytes : ByteArray)
    (h : bytes.data.toList.take magic.length ≠ magic) : decode bytes = none := by
  simp [decode, read, h]

theorem decode_truncated (image : StorageImage) (initial suffix : Bytes)
    (h : initial ++ suffix = image.encodeList) (hn : suffix ≠ []) :
    decode ⟨initial.toArray⟩ = none := by
  cases hd : decode ⟨initial.toArray⟩ with
  | none => rfl
  | some other =>
      have he := decode_sound _ _ hd
      have hp : initial = other.encodeList := by
        have := congrArg (fun bytes : ByteArray => bytes.data.toList) he
        simpa [encode] using this
      have ha := read_append other suffix
      have hb := read_append image []
      rw [← hp, h] at ha
      simp only [List.append_nil] at hb
      rw [hb] at ha
      have hh := (Prod.mk.inj (Option.some.inj ha)).2
      exact False.elim (hn hh.symm)

theorem decoded_fields (image : StorageImage) (h : image.Valid) :
    (decode (encode image)).map StorageImage.width = some image.width ∧
    (decode (encode image)).map StorageImage.inputLength = some image.inputLength ∧
    (decode (encode image)).map StorageImage.registerCount = some image.registerCount ∧
    (decode (encode image)).map StorageImage.code = some image.code ∧
    (decode (encode image)).map StorageImage.memory = some image.memory := by
  rw [decode_encode image h]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

structure Limits where
  maxFileBytes : Nat
  maxWidth : Nat
  maxRegisters : Nat
  maxInstructions : Nat
  maxMemoryWords : Nat
deriving Repr, DecidableEq

def Supported (limits : Limits) (image : StorageImage) : Prop :=
  image.encode.size ≤ limits.maxFileBytes ∧ image.width ≤ limits.maxWidth ∧
  image.registerCount ≤ limits.maxRegisters ∧ image.code.size ≤ limits.maxInstructions ∧
  image.memory.size ≤ limits.maxMemoryWords

def readInstructionBound (width : Nat) : Bytes → Option (Array Word × Bytes) :=
  readArrayBound 5 (readWordBound (limbCount width))

/-- Width/register caps precede body parsing. Instruction, memory, field and
word-byte caps precede their corresponding allocations and element loops. -/
def readBodySupported (limits : Limits) (bytes : Bytes) : Option (StorageImage × Bytes) := do
  let (width, rest) ← readScalar bytes
  let (inputLength, rest) ← readScalar rest
  let (registerCount, rest) ← readScalar rest
  if width ≤ limits.maxWidth ∧ registerCount ≤ limits.maxRegisters then
    let (code, rest) ← readArrayBound limits.maxInstructions (readInstructionBound width) rest
    let (memory, rest) ← readArrayBound limits.maxMemoryWords (readWordBound (limbCount width)) rest
    pure (⟨width, inputLength, registerCount, code, memory⟩, rest)
  else none

def decodeSupported (limits : Limits) (bytes : ByteArray) : Option StorageImage :=
  if bytes.size ≤ limits.maxFileBytes then
    let raw := bytes.data.toList
    if raw.take magic.length = magic then do
      let (image, rest) ← readBodySupported limits (raw.drop magic.length)
      if rest.isEmpty && image.valid then some image else none
    else none
  else none

theorem readInstructionBound_append (width : Nat) (fields : Array Word)
    (hl : fields.size ≤ 5) (hw : ∀ value ∈ fields.toList, Canonical width value)
    (tail : Bytes) :
    readInstructionBound width (instructionBytes fields ++ tail) = some (fields, tail) := by
  apply readArrayBound_append 5 word (readWordBound (limbCount width)) word_nonempty fields hl
  intro value hv rest
  exact readWordBound_append _ _ (Nat.le_of_eq (hw value hv).1) rest

theorem readBodySupported_append (limits : Limits) (image : StorageImage)
    (hv : image.Valid) (hs : image.Supported limits) (tail : Bytes) :
    readBodySupported limits (image.bodyBytes ++ tail) = some (image, tail) := by
  obtain ⟨_, _, _, hc, hm⟩ := (valid_iff image).1 hv
  obtain ⟨_, hwidth, hregisters, hcode, hmemory⟩ := hs
  have hcodeRead : ∀ tail,
      readArrayBound limits.maxInstructions (readInstructionBound image.width)
        (BinaryCodec.array instructionBytes image.code ++ tail) = some (image.code, tail) := by
    apply readArrayBound_append limits.maxInstructions instructionBytes
      (readInstructionBound image.width) (array_nonempty word) image.code hcode
    intro fields hf tail
    exact readInstructionBound_append image.width fields (hc fields hf).1 (hc fields hf).2.1 tail
  have hmemoryRead : ∀ tail,
      readArrayBound limits.maxMemoryWords (readWordBound (limbCount image.width))
        (BinaryCodec.array word image.memory ++ tail) = some (image.memory, tail) := by
    apply readArrayBound_append limits.maxMemoryWords word
      (readWordBound (limbCount image.width)) word_nonempty image.memory hmemory
    intro value hv tail
    exact readWordBound_append _ _ (Nat.le_of_eq (hm value hv).1) tail
  cases image
  simp_all [readBodySupported, bodyBytes, List.append_assoc, readScalar_append]

theorem decodeSupported_encode (limits : Limits) (image : StorageImage)
    (hv : image.Valid) (hs : image.Supported limits) :
    decodeSupported limits image.encode = some image := by
  have hr : readBodySupported limits image.bodyBytes = some (image, []) := by
    simpa using readBodySupported_append limits image hv hs []
  have hsize := hs.1
  have hvalid : image.valid = true := hv
  unfold decodeSupported
  rw [if_pos hsize]
  simp [encode, encodeList, hr, hvalid]

theorem readInstructionBound_refines (width : Nat) (bytes : Bytes)
    (fields : Array Word) (tail : Bytes)
    (h : readInstructionBound width bytes = some (fields, tail)) :
    readInstructionBytes bytes = some (fields, tail) := by
  apply readArray_refines (readWordBound (limbCount width)) readWord
    (readWordBound_to_readWord (limbCount width))
  exact readArrayBound_to_readArray _ _ _ _ _ h

theorem readBodySupported_refines (limits : Limits) (bytes : Bytes)
    (image : StorageImage) (tail : Bytes)
    (h : readBodySupported limits bytes = some (image, tail)) :
    readBody bytes = some (image, tail) := by
  unfold readBodySupported at h
  unfold readBody
  cases hw : readScalar bytes with
  | none => simp [hw] at h
  | some pair =>
    rcases pair with ⟨width, afterWidth⟩
    simp only [hw, bind, Option.bind] at h ⊢
    cases hn : readScalar afterWidth with
    | none => simp [hn] at h
    | some pair =>
      rcases pair with ⟨inputLength, afterInput⟩
      simp only [hn] at h ⊢
      cases hr : readScalar afterInput with
      | none => simp [hr] at h
      | some pair =>
        rcases pair with ⟨registerCount, afterRegisters⟩
        simp only [hr] at h ⊢
        split at h <;> try contradiction
        cases hc : readArrayBound limits.maxInstructions (readInstructionBound width) afterRegisters with
        | none => simp [hc] at h
        | some pair =>
          rcases pair with ⟨code, afterCode⟩
          simp only [hc] at h
          have hcr := readArray_refines (readInstructionBound width) readInstructionBytes
            (readInstructionBound_refines width) afterRegisters code afterCode
            (readArrayBound_to_readArray _ _ _ _ _ hc)
          simp only [hcr]
          cases hm : readArrayBound limits.maxMemoryWords (readWordBound (limbCount width)) afterCode with
          | none => simp [hm] at h
          | some pair =>
            rcases pair with ⟨memory, afterMemory⟩
            simp only [hm] at h
            have hmr := readArray_refines (readWordBound (limbCount width)) readWord
              (readWordBound_to_readWord (limbCount width)) afterCode memory afterMemory
              (readArrayBound_to_readArray _ _ _ _ _ hm)
            simpa only [hmr] using h

theorem decodeSupported_refines (limits : Limits) (bytes : ByteArray) (image : StorageImage)
    (h : decodeSupported limits bytes = some image) : decode bytes = some image := by
  unfold decodeSupported at h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  rename_i hmagic
  cases hr : readBodySupported limits (bytes.data.toList.drop magic.length) with
  | none => simp [hr] at h
  | some pair =>
      rcases pair with ⟨result, rest⟩
      have href := readBodySupported_refines limits _ _ _ hr
      simpa [decode, read, hmagic, href, hr] using h

theorem decodeSupported_valid (limits : Limits) (bytes : ByteArray) (image : StorageImage)
    (h : decodeSupported limits bytes = some image) : image.Valid :=
  decode_valid bytes image (decodeSupported_refines limits bytes image h)

theorem decodeSupported_sound (limits : Limits) (bytes : ByteArray) (image : StorageImage)
    (h : decodeSupported limits bytes = some image) : bytes = image.encode :=
  decode_sound bytes image (decodeSupported_refines limits bytes image h)

theorem decodeSupported_oversized_file (limits : Limits) (bytes : ByteArray)
    (h : limits.maxFileBytes < bytes.size) : decodeSupported limits bytes = none := by
  simp [decodeSupported, show ¬ bytes.size ≤ limits.maxFileBytes by omega]

/-- Frame bytes exclude stored Word bytes and include every scalar length. -/
def framingBytes (image : StorageImage) : Nat :=
  5 + (scalar image.width).length + (scalar image.inputLength).length +
  (scalar image.registerCount).length + (scalar image.code.size).length +
  (scalar image.memory.size).length +
  (image.code.toList.map (fun fields => (scalar fields.size).length +
    (fields.toList.map (fun value => (scalar value.size).length)).sum)).sum +
  (image.memory.toList.map (fun value => (scalar value.size).length)).sum

def storedByteCount (image : StorageImage) : Nat :=
  (image.code.toList.map (fun fields => (fields.toList.map Array.size).sum)).sum +
  (image.memory.toList.map Array.size).sum

theorem sum_map_add (values : List α) (f g : α → Nat) :
    (values.map (fun value => f value + g value)).sum =
      (values.map f).sum + (values.map g).sum := by
  induction values with
  | nil => simp
  | cons value values ih => simp [ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem encodeList_length (image : StorageImage) :
    image.encodeList.length = image.framingBytes + image.storedByteCount := by
  simp only [encodeList, bodyBytes, List.length_append, magic, List.length_cons,
    List.length_nil, array_length, instructionBytes, word_length, sum_map_add,
    framingBytes, storedByteCount]
  omega

theorem encode_size (image : StorageImage) :
    image.encode.size = image.framingBytes + image.storedByteCount := by
  simpa [encode, ByteArray.size] using encodeList_length image

def wordCount (image : StorageImage) : Nat :=
  (image.code.toList.map Array.size).sum + image.memory.size

theorem sum_map_constant_of_mem (values : List α) (f : α → Nat) (constant : Nat)
    (h : ∀ value ∈ values, f value = constant) :
    (values.map f).sum = values.length * constant := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have hv := h value (by simp)
      have ht : ∀ value ∈ values, f value = constant := fun v hm => h v (by simp [hm])
      simp [hv, ih ht, Nat.add_mul, Nat.add_comm]

theorem sum_map_mul (values : List α) (f : α → Nat) (constant : Nat) :
    (values.map (fun value => f value * constant)).sum = (values.map f).sum * constant := by
  induction values with
  | nil => simp
  | cons value values ih => simp [ih, Nat.add_mul]

theorem storedByteCount_canonical (image : StorageImage) (h : image.Valid) :
    image.storedByteCount = image.wordCount * limbCount image.width := by
  obtain ⟨_, _, _, hc, hm⟩ := (valid_iff image).1 h
  have hmem : (image.memory.toList.map Array.size).sum =
      image.memory.size * limbCount image.width := by
    simpa using sum_map_constant_of_mem image.memory.toList Array.size (limbCount image.width)
      (fun value hv => (hm value hv).1)
  have hfields : ∀ fields ∈ image.code.toList,
      (fields.toList.map Array.size).sum = fields.size * limbCount image.width := by
    intro fields hf
    simpa using sum_map_constant_of_mem fields.toList Array.size (limbCount image.width)
      (fun value hv => ((hc fields hf).2.1 value hv).1)
  have hcode : (image.code.toList.map (fun fields => (fields.toList.map Array.size).sum)).sum =
      (image.code.toList.map Array.size).sum * limbCount image.width := by
    rw [← sum_map_mul]
    congr 1
    exact List.map_congr_left hfields
  simp [storedByteCount, wordCount, hcode, hmem, Nat.add_mul]

/-- Exact file bits = numeric word bits + byte rounding + explicit framing.
Array objects, ByteArray conversion, parser temporaries and runtime allocation
are separate costs; this equation does not count their physical memory. -/
theorem encoded_bit_accounting (image : StorageImage) (h : image.Valid) :
    8 * image.encode.size = image.wordCount * image.width +
      image.wordCount * (8 * limbCount image.width - image.width) +
      8 * image.framingBytes := by
  have hw := (rounded_width image.width).1
  have he : image.width + (8 * limbCount image.width - image.width) =
      8 * limbCount image.width := by omega
  rw [encode_size, storedByteCount_canonical image h]
  rw [← Nat.mul_add image.wordCount, he]
  simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]

end StorageImage
end RMQ.SuccinctFinal.PackedNative
