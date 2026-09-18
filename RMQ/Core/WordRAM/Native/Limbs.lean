import RMQ.Core.WordRAM.Packed.Primitive

/-!
# Canonical byte limbs and checked scalar operations

Stored words contain only little-endian UInt8 limbs. Arithmetic decodes temporary
Nat values, performs the existing primitive operation, and re-encodes the result.
These conversions and BigNat temporaries have runtime costs beyond model ticks.
-/

namespace RMQ.SuccinctFinal.PackedNative.LimbWord

open PackedWordRAM

abbrev Word := Array UInt8

def limbCount (width : Nat) : Nat := (width + 7) / 8

def encodeList : Nat → Nat → List UInt8
  | 0, _ => []
  | count + 1, value => UInt8.ofNat value :: encodeList count (value / 256)

def decodeList : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * decodeList rest

def encode (width value : Nat) : Word := (encodeList (limbCount width) value).toArray

def decode (word : Word) : Nat := decodeList word.toList

def Canonical (width : Nat) (word : Word) : Prop :=
  word.size = limbCount width ∧ decode word < 2 ^ width

instance (width : Nat) (word : Word) : Decidable (Canonical width word) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem encodeList_length (count value : Nat) :
    (encodeList count value).length = count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => simp [encodeList, ih]

theorem decodeList_encodeList (count value : Nat) (h : value < 256 ^ count) :
    decodeList (encodeList count value) = value := by
  induction count generalizing value with
  | zero =>
      simp only [Nat.pow_zero] at h
      have : value = 0 := by omega
      simp [this, encodeList, decodeList]
  | succ count ih =>
      have hd : value / 256 < 256 ^ count := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).2
        simpa [Nat.pow_succ] using h
      simp only [encodeList, decodeList, UInt8.toNat_ofNat', Nat.reducePow, ih _ hd]
      exact Nat.mod_add_div value 256

theorem encodeList_decodeList (bytes : List UInt8) :
    encodeList bytes.length (decodeList bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
      have hb : b.toNat < 256 := b.toNat_lt_size
      have hm : (b.toNat + 256 * decodeList bs) % 256 = b.toNat := by omega
      have hd : (b.toNat + 256 * decodeList bs) / 256 = decodeList bs := by omega
      simp only [List.length_cons, decodeList, encodeList, hd, ih]
      congr 1
      apply UInt8.toNat_inj.1
      simpa only [UInt8.toNat_ofNat', Nat.reducePow] using hm

theorem rounded_width (width : Nat) :
    width ≤ 8 * limbCount width ∧ 8 * limbCount width < width + 8 := by
  unfold limbCount
  omega

theorem byte_capacity (count : Nat) : 256 ^ count = 2 ^ (8 * count) := by
  rw [Nat.pow_mul]

@[simp] theorem encode_size (width value : Nat) :
    (encode width value).size = limbCount width := by simp [encode]

theorem decode_encode (width value : Nat) (h : value < 2 ^ width) :
    decode (encode width value) = value := by
  simp only [decode, encode, List.toList_toArray]
  apply decodeList_encodeList
  rw [byte_capacity]
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (rounded_width width).1)

theorem encode_decode (width : Nat) (word : Word)
    (h : word.size = limbCount width) : encode width (decode word) = word := by
  unfold encode decode
  rw [← h, ← Array.length_toList, encodeList_decodeList]

theorem canonical_encode (width value : Nat) (h : value < 2 ^ width) :
    Canonical width (encode width value) := by
  exact ⟨encode_size _ _, by rw [decode_encode _ _ h]; exact h⟩

theorem encode_injective (width x y : Nat) (hx : x < 2 ^ width) (hy : y < 2 ^ width)
    (h : encode width x = encode width y) : x = y := by
  have := congrArg decode h
  simpa [decode_encode _ _ hx, decode_encode _ _ hy] using this

theorem decode_injective (width : Nat) (x y : Word)
    (hx : x.size = limbCount width) (hy : y.size = limbCount width)
    (h : decode x = decode y) : x = y := by
  rw [← encode_decode width x hx, ← encode_decode width y hy, h]

/-- Whole extra high bits are zero: the decoded value divided by 2^width is zero. -/
theorem canonical_padding (width : Nat) (word : Word) (h : Canonical width word) :
    decode word / 2 ^ width = 0 := Nat.div_eq_of_lt h.2

inductive WordFault where
  | malformedWord | underflow | zeroDivisor | oversizedShift | overflow
  | addressLimit | negativeInput
deriving Repr, DecidableEq

/-- Exactly the arithmetic-specific clauses of the reference Instruction.Safe. -/
def ArithmeticSafe (width : Nat) (op : Arithmetic) (x y : Nat) : Prop :=
  op.eval x y < 2 ^ width ∧
  (op = .sub → y ≤ x) ∧
  (op = .div ∨ op = .mod → 0 < y) ∧
  (op = .shl ∨ op = .shr → y < width)

/-- Operand checks precede evaluation, especially shifts with hostile counts. -/
def checkedNatArithmetic (width : Nat) (op : Arithmetic) (x y : Nat) :
    Except WordFault Word :=
  if op = .sub ∧ x < y then .error .underflow
  else if (op = .div ∨ op = .mod) ∧ y = 0 then .error .zeroDivisor
  else if (op = .shl ∨ op = .shr) ∧ width ≤ y then .error .oversizedShift
  else let result := op.eval x y
       if result < 2 ^ width then .ok (encode width result)
       else .error .overflow

def checkedArithmetic (width : Nat) (op : Arithmetic) (x y : Word) :
    Except WordFault Word :=
  if Canonical width x ∧ Canonical width y then
    checkedNatArithmetic width op (decode x) (decode y)
  else .error .malformedWord

theorem checkedNatArithmetic_of_safe (width : Nat) (op : Arithmetic) (x y : Nat)
    (h : ArithmeticSafe width op x y) :
    checkedNatArithmetic width op x y = .ok (encode width (op.eval x y)) := by
  rcases h with ⟨hr, hs, hd, hh⟩
  have hs' : ¬ (op = .sub ∧ x < y) := by rintro ⟨ho, hx⟩; have := hs ho; omega
  have hd' : ¬ ((op = .div ∨ op = .mod) ∧ y = 0) := by
    rintro ⟨ho, hx⟩; have := hd ho; omega
  have hh' : ¬ ((op = .shl ∨ op = .shr) ∧ width ≤ y) := by
    rintro ⟨ho, hx⟩; have := hh ho; omega
  simp [checkedNatArithmetic, hs', hd', hh', hr]

theorem checkedArithmetic_of_safe (width : Nat) (op : Arithmetic) (x y : Word)
    (hx : Canonical width x) (hy : Canonical width y)
    (h : ArithmeticSafe width op (decode x) (decode y)) :
    checkedArithmetic width op x y = .ok (encode width (op.eval (decode x) (decode y))) := by
  simp [checkedArithmetic, hx, hy, checkedNatArithmetic_of_safe _ _ _ _ h]

theorem checkedNatArithmetic_success (width : Nat) (op : Arithmetic) (x y : Nat)
    (result : Word) (h : checkedNatArithmetic width op x y = .ok result) :
    ArithmeticSafe width op x y ∧ Canonical width result ∧
    decode result = op.eval x y := by
  unfold checkedNatArithmetic at h
  split at h <;> try contradiction
  rename_i hs
  split at h <;> try contradiction
  rename_i hd
  split at h <;> try contradiction
  rename_i hh
  dsimp only at h
  split at h <;> try contradiction
  rename_i hr
  cases h
  refine ⟨⟨hr, ?_, ?_, ?_⟩, canonical_encode _ _ hr, decode_encode _ _ hr⟩
  · intro ho
    have : ¬ x < y := fun hxy => hs ⟨ho, hxy⟩
    omega
  · intro ho
    have : y ≠ 0 := fun hy => hd ⟨ho, hy⟩
    omega
  · intro ho
    have : ¬ width ≤ y := fun hy => hh ⟨ho, hy⟩
    omega

theorem checkedArithmetic_success (width : Nat) (op : Arithmetic) (x y result : Word)
    (h : checkedArithmetic width op x y = .ok result) :
    Canonical width x ∧ Canonical width y ∧
    ArithmeticSafe width op (decode x) (decode y) ∧
    Canonical width result ∧ decode result = op.eval (decode x) (decode y) := by
  unfold checkedArithmetic at h
  split at h <;> try contradiction
  rename_i hc
  exact ⟨hc.1, hc.2, checkedNatArithmetic_success _ _ _ _ _ h⟩

def checkedNat (width value : Nat) : Except WordFault Word :=
  if value < 2 ^ width then .ok (encode width value) else .error .overflow

theorem checkedNat_of_lt (width value : Nat) (h : value < 2 ^ width) :
    checkedNat width value = .ok (encode width value) := by simp [checkedNat, h]

theorem checkedNat_success (width value : Nat) (result : Word)
    (h : checkedNat width value = .ok result) :
    Canonical width result ∧ decode result = value := by
  unfold checkedNat at h
  split at h <;> try contradiction
  rename_i hv
  cases h
  exact ⟨canonical_encode _ _ hv, decode_encode _ _ hv⟩

def checkedComparison (width : Nat) (op : Comparison) (x y : Word) :
    Except WordFault Word :=
  if Canonical width x ∧ Canonical width y then
    checkedNat width (op.eval (decode x) (decode y))
  else .error .malformedWord

theorem comparison_lt (width : Nat) (op : Comparison) (x y : Nat) (hw : 0 < width) :
    op.eval x y < 2 ^ width := by
  have hp : 2 ≤ 2 ^ width := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ width by omega))
  cases op <;> simp only [Comparison.eval] <;> split <;> omega

theorem checkedComparison_of_canonical (width : Nat) (op : Comparison) (x y : Word)
    (hw : 0 < width) (hx : Canonical width x) (hy : Canonical width y) :
    checkedComparison width op x y = .ok (encode width (op.eval (decode x) (decode y))) := by
  simp [checkedComparison, hx, hy, checkedNat_of_lt _ _ (comparison_lt _ _ _ _ hw)]

theorem checkedComparison_success (width : Nat) (op : Comparison) (x y result : Word)
    (h : checkedComparison width op x y = .ok result) :
    Canonical width x ∧ Canonical width y ∧ Canonical width result ∧
    decode result = op.eval (decode x) (decode y) := by
  unfold checkedComparison at h
  split at h <;> try contradiction
  rename_i hc
  exact ⟨hc.1, hc.2, checkedNat_success _ _ _ h⟩

/-- The explicit host-address support check is separate from abstract words. -/
def checkedAddress (width limit : Nat) (word : Word) : Except WordFault USize :=
  if Canonical width word then
    if decode word < limit ∧ decode word < USize.size then
      .ok (USize.ofNat (decode word))
    else .error .addressLimit
  else .error .malformedWord

theorem checkedAddress_of_supported (width limit : Nat) (word : Word)
    (hc : Canonical width word) (hl : decode word < limit) (hs : decode word < USize.size) :
    checkedAddress width limit word = .ok (USize.ofNat (decode word)) := by
  simp [checkedAddress, hc, hl, hs]

theorem checkedAddress_success (width limit : Nat) (word : Word) (address : USize)
    (h : checkedAddress width limit word = .ok address) :
    Canonical width word ∧ address.toNat = decode word ∧ address.toNat < limit := by
  unfold checkedAddress at h
  split at h <;> try contradiction
  rename_i hc
  split at h <;> try contradiction
  rename_i hs
  cases h
  exact ⟨hc, USize.toNat_ofNat_of_lt' hs.2, by rw [USize.toNat_ofNat_of_lt' hs.2]; exact hs.1⟩

/-- Signed frontend inputs are accepted only as nonnegative representatives. -/
def checkedInt (width : Nat) (value : Int) : Except WordFault Word :=
  if 0 ≤ value then checkedNat width value.toNat else .error .negativeInput

theorem checkedInt_success (width : Nat) (value : Int) (result : Word)
    (h : checkedInt width value = .ok result) :
    0 ≤ value ∧ Canonical width result ∧ (decode result : Int) = value := by
  unfold checkedInt at h
  split at h <;> try contradiction
  rename_i hv
  obtain ⟨hc, hd⟩ := checkedNat_success _ _ _ h
  exact ⟨hv, hc, by rw [hd]; exact Int.toNat_of_nonneg hv⟩

theorem checkedArithmetic_accepts_iff (width : Nat) (op : Arithmetic) (x y : Word) :
    (∃ result, checkedArithmetic width op x y = .ok result) ↔
    Canonical width x ∧ Canonical width y ∧
    ArithmeticSafe width op (decode x) (decode y) := by
  constructor
  · rintro ⟨result, h⟩
    obtain ⟨hx, hy, hs, _⟩ := checkedArithmetic_success _ _ _ _ _ h
    exact ⟨hx, hy, hs⟩
  · rintro ⟨hx, hy, hs⟩
    exact ⟨_, checkedArithmetic_of_safe _ _ _ _ hx hy hs⟩

theorem checkedInt_of_supported (width : Nat) (value : Int)
    (hn : 0 ≤ value) (hw : value.toNat < 2 ^ width) :
    checkedInt width value = .ok (encode width value.toNat) := by
  simp [checkedInt, hn, checkedNat_of_lt _ _ hw]

theorem checkedNatArithmetic_underflow (width x y : Nat) (h : x < y) :
    checkedNatArithmetic width .sub x y = .error .underflow := by
  simp [checkedNatArithmetic, h]

theorem checkedNatArithmetic_zero_divisor (width x : Nat) :
    checkedNatArithmetic width .div x 0 = .error .zeroDivisor ∧
    checkedNatArithmetic width .mod x 0 = .error .zeroDivisor := by
  simp [checkedNatArithmetic]

theorem checkedNatArithmetic_oversized_shift (width x y : Nat) (h : width ≤ y) :
    checkedNatArithmetic width .shl x y = .error .oversizedShift ∧
    checkedNatArithmetic width .shr x y = .error .oversizedShift := by
  simp [checkedNatArithmetic, h]

theorem checkedNat_overflow (width value : Nat) (h : 2 ^ width ≤ value) :
    checkedNat width value = .error .overflow := by
  simp [checkedNat, show ¬ value < 2 ^ width by omega]

theorem checkedArithmetic_malformed (width : Nat) (op : Arithmetic) (x y : Word)
    (h : ¬ (Canonical width x ∧ Canonical width y)) :
    checkedArithmetic width op x y = .error .malformedWord := by
  simp [checkedArithmetic, h]

theorem checkedInt_negative (width : Nat) (value : Int) (h : value < 0) :
    checkedInt width value = .error .negativeInput := by
  simp [checkedInt, show ¬ 0 ≤ value by omega]

/-- Numeric width and allocated byte bits differ by fewer than eight bits.
This does not include Array objects, allocator overhead, or temporary Nats. -/
theorem encoded_payload_bits (width value : Nat) :
    8 * (encode width value).size = 8 * limbCount width ∧
    width ≤ 8 * (encode width value).size ∧
    8 * (encode width value).size < width + 8 := by
  rw [encode_size]
  exact ⟨rfl, rounded_width width⟩

theorem arithmeticSafe_of_instructionSafe (width : Nat) (s : State) (op : Arithmetic)
    (dst lhs rhs : Nat) (h : Instruction.Safe width s (.arithmetic op dst lhs rhs)) :
    ArithmeticSafe width op (s.regs lhs) (s.regs rhs) := h.2.2

theorem checkedArithmetic_encode_of_safe (width : Nat) (op : Arithmetic) (x y : Nat)
    (hx : x < 2 ^ width) (hy : y < 2 ^ width) (h : ArithmeticSafe width op x y) :
    checkedArithmetic width op (encode width x) (encode width y) =
      .ok (encode width (op.eval x y)) := by
  have hs : ArithmeticSafe width op (decode (encode width x)) (decode (encode width y)) := by
    simpa [decode_encode _ _ hx, decode_encode _ _ hy] using h
  simpa [decode_encode _ _ hx, decode_encode _ _ hy] using
    checkedArithmetic_of_safe width op _ _ (canonical_encode _ _ hx) (canonical_encode _ _ hy) hs

theorem decodeList_lt (bytes : List UInt8) : decodeList bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => decide
  | cons b bs ih =>
      have hb : b.toNat < 256 := b.toNat_lt_size
      simp only [decodeList, List.length_cons, Nat.pow_succ]
      omega

theorem encodeList_getElem (count value i : Nat) (hi : i < count) :
    (encodeList count value)[i]'(by simpa using hi) = UInt8.ofNat (value / 256 ^ i) := by
  induction count generalizing value i with
  | zero => omega
  | succ count ih =>
      cases i with
      | zero => simp [encodeList]
      | succ i =>
          simp only [encodeList, List.getElem_cons_succ]
          rw [ih (value / 256) i (by omega)]
          congr 1
          rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

end RMQ.SuccinctFinal.PackedNative.LimbWord
