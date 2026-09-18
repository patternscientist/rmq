import RMQ.Core.WordRAM.Native.Binary

/-!
# Indexed, tail-recursive native image loader

Runtime parsers use ByteArray.size/get and offsets. List suffixes below are proof
views only. In particular, no per-byte ByteArray.data conversion is performed.
-/

namespace RMQ.SuccinctFinal.PackedNative.BinaryCursor

open LimbWord BinaryCodec

abbrev Parser (α : Type) := ByteArray → Nat → Option (α × Nat)

def suffix (bytes : ByteArray) (pos : Nat) : Bytes := bytes.data.toList.drop pos

@[simp] theorem suffix_length (bytes : ByteArray) (pos : Nat) :
    (suffix bytes pos).length = bytes.size - pos := by
  simp [suffix, ByteArray.size]

theorem suffix_cons (bytes : ByteArray) (pos : Nat) (hp : pos < bytes.size) :
    suffix bytes pos = bytes[pos] :: suffix bytes (pos + 1) := by
  unfold suffix
  rw [List.drop_eq_getElem_cons (by simpa [ByteArray.size] using hp)]
  rfl

theorem suffix_nil (bytes : ByteArray) (pos : Nat) (hp : bytes.size ≤ pos) :
    suffix bytes pos = [] := by
  apply List.drop_eq_nil_iff.mpr
  simpa only [Array.length_toList] using hp

def observe (bytes : ByteArray) (result : α × Nat) : α × Bytes :=
  (result.1, suffix bytes result.2)

structure Correct (fast : Parser α) (slow : Bytes → Option (α × Bytes)) : Prop where
  result : ∀ bytes pos, pos ≤ bytes.size →
    (fast bytes pos).map (observe bytes) = slow (suffix bytes pos)
  bounds : ∀ bytes pos value next, pos ≤ bytes.size → fast bytes pos = some (value, next) →
    pos ≤ next ∧ next ≤ bytes.size

def readByte : Parser UInt8 := fun bytes pos =>
  if hp : pos < bytes.size then some (bytes[pos], pos + 1) else none

def readByteList : Bytes → Option (UInt8 × Bytes)
  | [] => none
  | byte :: rest => some (byte, rest)

theorem readByte_correct : Correct readByte readByteList := by
  constructor
  · intro bytes pos hp
    by_cases hl : pos < bytes.size
    · simp [readByte, hl, observe, suffix_cons bytes pos hl, readByteList]
    · simp [readByte, hl, suffix_nil bytes pos (by omega), readByteList]
  · intro bytes pos value next hp h
    unfold readByte at h
    split at h <;> try contradiction
    cases h
    omega

/-- Fuel is remaining bytes; both prefix count and offset are tail accumulators. -/
def prefixAux (bytes : ByteArray) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | fuel + 1, pos, count =>
      match readByte bytes pos with
      | none => none
      | some (byte, next) =>
          if byte = 0 then some (count, next)
          else if byte = 1 then prefixAux bytes fuel next (count + 1)
          else none

def readPrefix : Parser Nat := fun bytes pos => prefixAux bytes (bytes.size - pos) pos 0

/-- Each counted loop pushes one result and tail-calls; no list trace is built. -/
def manyAux (parse : Parser α) (bytes : ByteArray) :
    Nat → Nat → Array α → Option (Array α × Nat)
  | 0, pos, acc => some (acc, pos)
  | count + 1, pos, acc =>
      match parse bytes pos with
      | none => none
      | some (value, next) => manyAux parse bytes count next (acc.push value)

def readMany (parse : Parser α) (count : Nat) : Parser (Array α) :=
  fun bytes pos => manyAux parse bytes count pos #[]

/-- Bounds are checked by the caller before this digit loop. The fallback is
total but is unreachable in the successful scalar parser. -/
def byteAt (bytes : ByteArray) (pos : Nat) : UInt8 :=
  if hp : pos < bytes.size then bytes[pos] else 0

/-- Read highest digit first, accumulate downward; the recursive call is tail. -/
def digitsAux (bytes : ByteArray) (start : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | count + 1, acc =>
      digitsAux bytes start count ((byteAt bytes (start + count)).toNat + 256 * acc)

def readScalar : Parser Nat := fun bytes pos => do
  let (count, start) ← readPrefix bytes pos
  if 0 < count ∧ count ≤ bytes.size - start then
    let value := digitsAux bytes start count 0
    if digitCount value = count then some (value, start + count) else none
  else none

def readWordBound (limit : Nat) : Parser Word := fun bytes pos => do
  let (count, start) ← readScalar bytes pos
  if count ≤ limit ∧ count ≤ bytes.size - start then
    readMany readByte count bytes start
  else none

def readArrayBound (limit : Nat) (parse : Parser α) : Parser (Array α) := fun bytes pos => do
  let (count, start) ← readScalar bytes pos
  if count ≤ limit ∧ count ≤ bytes.size - start then
    readMany parse count bytes start
  else none

theorem manyAux_bounds (fast : Parser α) (slow : Bytes → Option (α × Bytes))
    (hc : Correct fast slow) (bytes : ByteArray) (count pos : Nat) (acc : Array α)
    (hp : pos ≤ bytes.size) (values : Array α) (next : Nat)
    (h : manyAux fast bytes count pos acc = some (values, next)) :
    pos ≤ next ∧ next ≤ bytes.size := by
  induction count generalizing pos acc with
  | zero => cases h; exact ⟨Nat.le_refl _, hp⟩
  | succ count ih =>
      unfold manyAux at h
      cases hf : fast bytes pos with
      | none => simp [hf] at h
      | some pair =>
          rcases pair with ⟨value, middle⟩
          have hb := hc.bounds bytes pos value middle hp hf
          simp only [hf] at h
          have hr := ih middle (acc.push value) hb.2 h
          exact ⟨Nat.le_trans hb.1 hr.1, hr.2⟩

theorem manyAux_result (fast : Parser α) (slow : Bytes → Option (α × Bytes))
    (hc : Correct fast slow) (bytes : ByteArray) (count pos : Nat) (acc : Array α)
    (hp : pos ≤ bytes.size) :
    (manyAux fast bytes count pos acc).map (observe bytes) =
      (BinaryCodec.readMany slow count (suffix bytes pos)).map
        (fun result => (acc ++ result.1.toArray, result.2)) := by
  induction count generalizing pos acc with
  | zero => simp [manyAux, BinaryCodec.readMany, observe]
  | succ count ih =>
      cases hf : fast bytes pos with
      | none =>
          have hs := hc.result bytes pos hp
          simp only [hf, Option.map_none] at hs
          simp [manyAux, hf, BinaryCodec.readMany, ← hs]
      | some pair =>
          rcases pair with ⟨value, middle⟩
          have hb := hc.bounds bytes pos value middle hp hf
          have hs := hc.result bytes pos hp
          simp only [hf, Option.map_some, observe] at hs
          simp only [manyAux, hf, BinaryCodec.readMany, ← hs, bind, Option.bind]
          rw [ih middle (acc.push value) hb.2]
          cases hr : BinaryCodec.readMany slow count (suffix bytes middle) with
          | none => simp
          | some pair =>
              rcases pair with ⟨values, tail⟩
              simp

theorem readMany_result (fast : Parser α) (slow : Bytes → Option (α × Bytes))
    (hc : Correct fast slow) (bytes : ByteArray) (count pos : Nat) (hp : pos ≤ bytes.size) :
    (readMany fast count bytes pos).map (observe bytes) =
      (BinaryCodec.readMany slow count (suffix bytes pos)).map
        (fun result => (result.1.toArray, result.2)) := by
  simpa [readMany] using manyAux_result fast slow hc bytes count pos #[] hp

theorem readMany_bounds (fast : Parser α) (slow : Bytes → Option (α × Bytes))
    (hc : Correct fast slow) (bytes : ByteArray) (count pos : Nat) (hp : pos ≤ bytes.size)
    (values : Array α) (next : Nat) (h : readMany fast count bytes pos = some (values, next)) :
    pos ≤ next ∧ next ≤ bytes.size := manyAux_bounds fast slow hc bytes count pos #[] hp values next h

theorem prefixAux_bounds (bytes : ByteArray) (fuel pos count value next : Nat)
    (hp : pos ≤ bytes.size) (hf : fuel = bytes.size - pos)
    (h : prefixAux bytes fuel pos count = some (value, next)) :
    pos < next ∧ next ≤ bytes.size := by
  induction fuel generalizing pos count with
  | zero => simp [prefixAux] at h
  | succ fuel ih =>
      have hl : pos < bytes.size := by omega
      simp only [prefixAux, readByte, dif_pos hl] at h
      split at h
      · cases h; omega
      · split at h <;> try contradiction
        have hr := ih (pos + 1) (count + 1) (by omega) (by omega) h
        omega

theorem prefixAux_result (bytes : ByteArray) (fuel pos count : Nat)
    (hp : pos ≤ bytes.size) (hf : fuel = bytes.size - pos) :
    (prefixAux bytes fuel pos count).map (observe bytes) =
      (BinaryCodec.readPrefix (suffix bytes pos)).map (fun result => (count + result.1, result.2)) := by
  induction fuel generalizing pos count with
  | zero =>
      have hl : bytes.size ≤ pos := by omega
      simp [prefixAux, suffix_nil bytes pos hl, BinaryCodec.readPrefix]
  | succ fuel ih =>
      have hl : pos < bytes.size := by omega
      rw [suffix_cons bytes pos hl]
      simp only [prefixAux, readByte, dif_pos hl, BinaryCodec.readPrefix]
      by_cases hzero : bytes[pos] = 0
      · simp [hzero, observe]
      · by_cases hone : bytes[pos] = 1
        · simp only [hzero, hone, show ¬(1 : UInt8) = 0 from by decide, if_false, if_true]
          rw [ih (pos + 1) (count + 1) (by omega) (by omega)]
          cases hr : BinaryCodec.readPrefix (suffix bytes (pos + 1)) with
          | none => simp
          | some pair => rcases pair with ⟨n, tail⟩; simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · simp [hzero, hone]

theorem readPrefix_correct : Correct readPrefix BinaryCodec.readPrefix := by
  constructor
  · intro bytes pos hp
    simpa [readPrefix] using prefixAux_result bytes (bytes.size - pos) pos 0 hp rfl
  · intro bytes pos value next hp h
    have hr := prefixAux_bounds bytes (bytes.size - pos) pos 0 value next hp rfl h
    exact ⟨Nat.le_of_lt hr.1, hr.2⟩

theorem decodeList_append (xs ys : Bytes) :
    LimbWord.decodeList (xs ++ ys) = LimbWord.decodeList xs + 256 ^ xs.length * LimbWord.decodeList ys := by
  induction xs with
  | nil => simp [LimbWord.decodeList]
  | cons x xs ih =>
      simp [LimbWord.decodeList, ih, Nat.pow_succ, Nat.mul_add, Nat.mul_assoc,
        Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem digitsAux_result (bytes : ByteArray) (start count acc : Nat)
    (hb : start + count ≤ bytes.size) :
    digitsAux bytes start count acc =
      LimbWord.decodeList ((suffix bytes start).take count) + 256 ^ count * acc := by
  induction count generalizing acc with
  | zero => simp [digitsAux, LimbWord.decodeList]
  | succ count ih =>
      have hi : start + count < bytes.size := by omega
      have hc : count < (suffix bytes start).length := by rw [suffix_length]; omega
      have he : (suffix bytes start)[count] = bytes[start + count] := by
        simp only [suffix, List.getElem_drop, Array.getElem_toList]
        rfl
      rw [digitsAux, ih _ (by omega), List.take_succ_eq_append_getElem hc,
        decodeList_append]
      simp only [byteAt, dif_pos hi, he, List.length_take, suffix_length]
      have hmin : min count (bytes.size - start) = count := by omega
      rw [hmin]
      simp [LimbWord.decodeList, Nat.pow_succ, Nat.mul_add, Nat.mul_assoc,
        Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem suffix_drop (bytes : ByteArray) (start count : Nat) :
    (suffix bytes start).drop count = suffix bytes (start + count) := by
  simp [suffix, List.drop_drop, Nat.add_comm]

theorem readScalar_correct : Correct readScalar BinaryCodec.readScalar := by
  constructor
  · intro bytes pos hp
    have href := readPrefix_correct.result bytes pos hp
    cases hr : readPrefix bytes pos with
    | none =>
        simp only [hr, Option.map_none] at href
        simp [readScalar, hr, BinaryCodec.readScalar, ← href]
    | some pair =>
        rcases pair with ⟨count, start⟩
        have hb := readPrefix_correct.bounds bytes pos count start hp hr
        simp only [hr, Option.map_some, observe] at href
        simp only [readScalar, hr, BinaryCodec.readScalar, ← href, bind, Option.bind, suffix_length]
        by_cases hc : 0 < count ∧ count ≤ bytes.size - start
        · rw [if_pos hc, if_pos hc, digitsAux_result bytes start count 0 (by omega)]
          simp only [Nat.mul_zero, Nat.add_zero]
          by_cases hd : digitCount (LimbWord.decodeList ((suffix bytes start).take count)) = count
          · simp [hd, observe, suffix_drop]
          · simp [hd]
        · simp [hc]
  · intro bytes pos value next hp h
    unfold readScalar at h
    cases hr : readPrefix bytes pos with
    | none => simp [hr] at h
    | some pair =>
        rcases pair with ⟨count, start⟩
        have hb := readPrefix_correct.bounds bytes pos count start hp hr
        simp only [hr, bind, Option.bind] at h
        split at h <;> try contradiction
        rename_i hc
        split at h <;> try contradiction
        cases h
        omega

theorem readManyByte_reference (count : Nat) (bytes : Bytes) (hb : count ≤ bytes.length) :
    BinaryCodec.readMany readByteList count bytes = some (bytes.take count, bytes.drop count) := by
  induction count generalizing bytes with
  | zero => simp [BinaryCodec.readMany]
  | succ count ih =>
      cases bytes with
      | nil => simp at hb
      | cons byte bytes =>
          have hb' : count ≤ bytes.length := by simp only [List.length_cons] at hb; omega
          simp [BinaryCodec.readMany, readByteList, ih bytes hb']

theorem readWordBound_correct (limit : Nat) : Correct (readWordBound limit) (BinaryCodec.readWordBound limit) := by
  constructor
  · intro bytes pos hp
    have href := readScalar_correct.result bytes pos hp
    cases hr : readScalar bytes pos with
    | none =>
        simp only [hr, Option.map_none] at href
        simp [readWordBound, hr, BinaryCodec.readWordBound, ← href]
    | some pair =>
        rcases pair with ⟨count, start⟩
        have hb := readScalar_correct.bounds bytes pos count start hp hr
        simp only [hr, Option.map_some, observe] at href
        simp only [readWordBound, hr, BinaryCodec.readWordBound, BinaryCodec.readWord,
          ← href, bind, Option.bind, suffix_length]
        by_cases hl : count ≤ limit
        · by_cases hc : count ≤ bytes.size - start
          · simp only [hl, hc, and_self, if_true]
            rw [readMany_result readByte readByteList readByte_correct bytes count start hb.2,
              readManyByte_reference count (suffix bytes start) (by simpa using hc)]
            rfl
          · simp [hl, hc]
        · simp [hl]
  · intro bytes pos value next hp h
    unfold readWordBound at h
    cases hr : readScalar bytes pos with
    | none => simp [hr] at h
    | some pair =>
        rcases pair with ⟨count, start⟩
        have hb := readScalar_correct.bounds bytes pos count start hp hr
        simp only [hr, bind, Option.bind] at h
        split at h <;> try contradiction
        have hm := readMany_bounds readByte readByteList readByte_correct bytes count start hb.2 value next h
        exact ⟨Nat.le_trans hb.1 hm.1, hm.2⟩

theorem readArrayBound_correct (limit : Nat) (fast : Parser α)
    (slow : Bytes → Option (α × Bytes)) (hc : Correct fast slow) :
    Correct (readArrayBound limit fast) (BinaryCodec.readArrayBound limit slow) := by
  constructor
  · intro bytes pos hp
    have href := readScalar_correct.result bytes pos hp
    cases hr : readScalar bytes pos with
    | none =>
        simp only [hr, Option.map_none] at href
        simp [readArrayBound, hr, BinaryCodec.readArrayBound, ← href]
    | some pair =>
        rcases pair with ⟨count, start⟩
        have hb := readScalar_correct.bounds bytes pos count start hp hr
        simp only [hr, Option.map_some, observe] at href
        simp only [readArrayBound, hr, BinaryCodec.readArrayBound, BinaryCodec.readArray,
          ← href, bind, Option.bind, suffix_length]
        by_cases hl : count ≤ limit
        · by_cases hn : count ≤ bytes.size - start
          · simp only [hl, hn, and_self, if_true]
            rw [readMany_result fast slow hc bytes count start hb.2]
            cases BinaryCodec.readMany slow count (suffix bytes start) <;> rfl
          · simp [hl, hn]
        · simp [hl]
  · intro bytes pos value next hp h
    unfold readArrayBound at h
    cases hr : readScalar bytes pos with
    | none => simp [hr] at h
    | some pair =>
        rcases pair with ⟨count, start⟩
        have hb := readScalar_correct.bounds bytes pos count start hp hr
        simp only [hr, bind, Option.bind] at h
        split at h <;> try contradiction
        have hm := readMany_bounds fast slow hc bytes count start hb.2 value next h
        exact ⟨Nat.le_trans hb.1 hm.1, hm.2⟩

def andThen (parse : Parser α) (next : α → Parser β) : Parser β := fun bytes pos => do
  let (value, middle) ← parse bytes pos
  next value bytes middle

def pureValue (value : α) : Parser α := fun _ pos => some (value, pos)
def failure : Parser α := fun _ _ => none

theorem pureValue_correct (value : α) :
    Correct (pureValue value) (fun bytes => some (value, bytes)) := by
  constructor
  · intro bytes pos hp; rfl
  · intro bytes pos result next hp h
    cases h
    exact ⟨Nat.le_refl _, hp⟩

theorem failure_correct : Correct (failure : Parser α) (fun _ => none) := by
  constructor
  · intro bytes pos hp; rfl
  · intro bytes pos result next hp h; cases h

theorem Correct.andThen (fast : Parser α) (slow : Bytes → Option (α × Bytes))
    (hf : Correct fast slow) (fastNext : α → Parser β)
    (slowNext : α → Bytes → Option (β × Bytes))
    (hn : ∀ value, Correct (fastNext value) (slowNext value)) :
    Correct (BinaryCursor.andThen fast fastNext) (fun bytes => do
      let (value, rest) ← slow bytes
      slowNext value rest) := by
  constructor
  · intro bytes pos hp
    have hs := hf.result bytes pos hp
    cases hr : fast bytes pos with
    | none =>
        simp only [hr, Option.map_none] at hs
        simp [BinaryCursor.andThen, hr, ← hs]
    | some pair =>
        rcases pair with ⟨value, middle⟩
        have hb := hf.bounds bytes pos value middle hp hr
        simp only [hr, Option.map_some, observe] at hs
        simpa [BinaryCursor.andThen, hr, ← hs] using (hn value).result bytes middle hb.2
  · intro bytes pos result next hp h
    unfold BinaryCursor.andThen at h
    cases hr : fast bytes pos with
    | none => simp [hr] at h
    | some pair =>
        rcases pair with ⟨value, middle⟩
        have hb := hf.bounds bytes pos value middle hp hr
        simp only [hr, bind, Option.bind] at h
        have hh := (hn value).bounds bytes middle result next hb.2 h
        exact ⟨Nat.le_trans hb.1 hh.1, hh.2⟩

def readInstructionBound (width : Nat) : Parser (Array Word) :=
  readArrayBound 5 (readWordBound (limbCount width))

theorem readInstructionBound_correct (width : Nat) :
    Correct (readInstructionBound width) (StorageImage.readInstructionBound width) :=
  readArrayBound_correct _ _ _ (readWordBound_correct _)

def readBodySupported (limits : StorageImage.Limits) : Parser StorageImage :=
  andThen readScalar fun width =>
  andThen readScalar fun inputLength =>
  andThen readScalar fun registerCount =>
  if width ≤ limits.maxWidth ∧ registerCount ≤ limits.maxRegisters then
    andThen (readArrayBound limits.maxInstructions (readInstructionBound width)) fun code =>
    andThen (readArrayBound limits.maxMemoryWords (readWordBound (limbCount width))) fun memory =>
    pureValue ⟨width, inputLength, registerCount, code, memory⟩
  else failure

theorem readBodySupported_correct (limits : StorageImage.Limits) :
    Correct (readBodySupported limits) (StorageImage.readBodySupported limits) := by
  let parseMemory := fun width inputLength registerCount code bytes => do
    let (memory, rest) ← BinaryCodec.readArrayBound limits.maxMemoryWords
      (BinaryCodec.readWordBound (limbCount width)) bytes
    some ((⟨width, inputLength, registerCount, code, memory⟩ : StorageImage), rest)
  let parseCode := fun width inputLength registerCount bytes => do
    let (code, rest) ← BinaryCodec.readArrayBound limits.maxInstructions
      (StorageImage.readInstructionBound width) bytes
    parseMemory width inputLength registerCount code rest
  let parseRegisters := fun width inputLength bytes => do
    let (registerCount, rest) ← BinaryCodec.readScalar bytes
    if width ≤ limits.maxWidth ∧ registerCount ≤ limits.maxRegisters then
      parseCode width inputLength registerCount rest
    else none
  let parseInput := fun width bytes => do
    let (inputLength, rest) ← BinaryCodec.readScalar bytes
    parseRegisters width inputLength rest
  unfold readBodySupported StorageImage.readBodySupported
  refine Correct.andThen readScalar BinaryCodec.readScalar readScalar_correct _ parseInput ?_
  intro width
  refine Correct.andThen readScalar BinaryCodec.readScalar readScalar_correct _
    (parseRegisters width) ?_
  intro inputLength
  refine Correct.andThen readScalar BinaryCodec.readScalar readScalar_correct _
    (fun registerCount rest =>
      if width ≤ limits.maxWidth ∧ registerCount ≤ limits.maxRegisters then
        parseCode width inputLength registerCount rest else none) ?_
  intro registerCount
  by_cases hl : width ≤ limits.maxWidth ∧ registerCount ≤ limits.maxRegisters
  · simp only [hl, and_self, if_true]
    refine Correct.andThen _ _ (readArrayBound_correct _ _ _ (readInstructionBound_correct width)) _
      (parseMemory width inputLength registerCount) ?_
    intro code
    refine Correct.andThen _ _ (readArrayBound_correct _ _ _ (readWordBound_correct _)) _
      (fun memory rest => some ((⟨width, inputLength, registerCount, code, memory⟩ : StorageImage), rest)) ?_
    intro memory
    exact pureValue_correct _
  · simp only [hl, if_false]
    exact failure_correct

/-- Only the constant-size magic slice is converted to a list. -/
def hasMagic (bytes : ByteArray) : Bool :=
  decide ((bytes.extract 0 StorageImage.magic.length).data.toList = StorageImage.magic)

theorem hasMagic_eq (bytes : ByteArray) :
    hasMagic bytes = decide (bytes.data.toList.take StorageImage.magic.length = StorageImage.magic) := by
  simp [hasMagic, ByteArray.extract, ByteArray.copySlice, ByteArray.empty,
    ByteArray.emptyWithCapacity, Array.toList_extract]

/-- Actual native decoder: file cap first, indexed parser, exact end, valid image. -/
def decodeByteBounded (limits : StorageImage.Limits) (bytes : ByteArray) : Option StorageImage :=
  if bytes.size ≤ limits.maxFileBytes then
    if hasMagic bytes then do
      let (image, next) ← readBodySupported limits bytes StorageImage.magic.length
      if next = bytes.size ∧ image.valid = true then some image else none
    else none
  else none

theorem decodeByteBounded_eq (limits : StorageImage.Limits) (bytes : ByteArray) :
    decodeByteBounded limits bytes = StorageImage.decodeSupported limits bytes := by
  unfold decodeByteBounded StorageImage.decodeSupported
  by_cases hf : bytes.size ≤ limits.maxFileBytes
  · simp only [hf, if_true, hasMagic_eq, decide_eq_true_eq]
    by_cases hm : bytes.data.toList.take StorageImage.magic.length = StorageImage.magic
    · simp only [hm, if_true]
      have hp : StorageImage.magic.length ≤ bytes.size := by
        have he := congrArg List.length hm
        simp only [List.length_take, Array.length_toList] at he
        change StorageImage.magic.length ≤ bytes.data.size
        omega
      have hr := (readBodySupported_correct limits).result bytes StorageImage.magic.length hp
      cases hd : readBodySupported limits bytes StorageImage.magic.length with
      | none =>
          simp only [hd, Option.map_none] at hr
          change none = StorageImage.readBodySupported limits
            (bytes.data.toList.drop StorageImage.magic.length) at hr
          simp [← hr]
      | some pair =>
          rcases pair with ⟨image, next⟩
          have hb := (readBodySupported_correct limits).bounds bytes StorageImage.magic.length image next hp hd
          simp only [hd, Option.map_some, observe] at hr
          change some (image, suffix bytes next) = StorageImage.readBodySupported limits
            (bytes.data.toList.drop StorageImage.magic.length) at hr
          have hempty : suffix bytes next = [] ↔ next = bytes.size := by
            rw [← List.length_eq_zero_iff, suffix_length]
            omega
          simp only [← hr, bind, Option.bind, Bool.and_eq_true, List.isEmpty_iff, hempty]
    · simp [hm]
  · simp [hf]

end RMQ.SuccinctFinal.PackedNative.BinaryCursor
