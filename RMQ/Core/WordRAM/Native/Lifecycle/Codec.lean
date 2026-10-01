import RMQ.Core.WordRAM.Native.Limbs

/-! # Lifecycle signed magnitude and endpoint codecs

Magnitude bytes are little endian. Leading zero bytes at the high end are
allowed; the native input format requires at least one byte and forbids a
negative sign on zero. Arithmetic in this module is arbitrary precision.
The size ceilings in `SignedFormat` describe host admission, not the model's
word domain. Foreign pointer validity and the 0/1 sign flag are C obligations.
-/

namespace RMQ.SuccinctFinal.PackedNative.Lifecycle

def maxMagnitudeBytes : Nat := 4096

def decodeMagnitude (bytes : ByteArray) : Nat := LimbWord.decode bytes.data

def decodeSigned (negative : Bool) (bytes : ByteArray) : Int :=
  if negative then -(decodeMagnitude bytes : Int) else (decodeMagnitude bytes : Int)

def encodeMagnitude (count value : Nat) : ByteArray :=
  ⟨(LimbWord.encodeList count value).toArray⟩

def signedNegative (value : Int) : Bool := decide (value < 0)

def encodeSigned (count : Nat) (value : Int) : ByteArray :=
  encodeMagnitude count value.natAbs

/-- A host input may have high zero padding, but has a unique sign for zero. -/
def SignedFormat (negative : Bool) (bytes : ByteArray) : Prop :=
  0 < bytes.size ∧ bytes.size ≤ maxMagnitudeBytes ∧
    (negative = true → decodeMagnitude bytes ≠ 0)

instance (negative : Bool) (bytes : ByteArray) : Decidable (SignedFormat negative bytes) :=
  inferInstanceAs (Decidable (_ ∧ _))

def signedFormat (negative : Bool) (bytes : ByteArray) : Bool :=
  decide (SignedFormat negative bytes)

theorem signedFormat_iff (negative : Bool) (bytes : ByteArray) :
    signedFormat negative bytes = true ↔ SignedFormat negative bytes := by
  simp [signedFormat]

theorem decodeSigned_magnitude (negative : Bool) (bytes : ByteArray) :
    (decodeSigned negative bytes).natAbs = decodeMagnitude bytes := by
  cases negative <;> simp [decodeSigned]

theorem decodeSigned_sign (negative : Bool) (bytes : ByteArray)
    (format : SignedFormat negative bytes) :
    signedNegative (decodeSigned negative bytes) = negative := by
  cases negative with
  | false => simp [signedNegative, decodeSigned]
  | true =>
      have positive : 0 < decodeMagnitude bytes := by
        have nonzero := format.2.2 rfl
        omega
      simp [signedNegative, decodeSigned, positive]

@[simp] theorem encodeMagnitude_size (count value : Nat) :
    (encodeMagnitude count value).size = count := by
  simp [encodeMagnitude, ByteArray.size]

theorem decodeMagnitude_encodeMagnitude (count value : Nat)
    (fits : value < 256 ^ count) :
    decodeMagnitude (encodeMagnitude count value) = value := by
  simpa [decodeMagnitude, encodeMagnitude, LimbWord.decode] using
    LimbWord.decodeList_encodeList count value fits

/-- Diagnostic naturals have an independent, nonempty magnitude buffer. -/
def encodeNatural (value : Nat) : ByteArray :=
  encodeMagnitude (value.log2 / 8 + 1) value

theorem encodeNatural_exact (value : Nat) :
    0 < (encodeNatural value).size ∧
      (encodeNatural value).size = value.log2 / 8 + 1 ∧
      decodeMagnitude (encodeNatural value) = value := by
  refine ⟨by simp [encodeNatural], by simp [encodeNatural], ?_⟩
  apply decodeMagnitude_encodeMagnitude
  rw [LimbWord.byte_capacity]
  exact Nat.lt_of_lt_of_le Nat.lt_log2_self
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))

theorem decodeSigned_encodeSigned (count : Nat) (value : Int)
    (fits : value.natAbs < 256 ^ count) :
    decodeSigned (signedNegative value) (encodeSigned count value) = value := by
  unfold decodeSigned encodeSigned
  rw [decodeMagnitude_encodeMagnitude count value.natAbs fits]
  cases value with
  | ofNat n =>
      change (if decide ((n : Int) < 0) then -(n : Int) else (n : Int)) = (n : Int)
      have nonnegative : ¬ ((n : Int) < 0) := by omega
      simp [nonnegative]
  | negSucc n =>
      change (if decide (Int.negSucc n < 0) then -((n + 1 : Nat) : Int)
        else ((n + 1 : Nat) : Int)) = Int.negSucc n
      simp only [Int.negSucc_lt_zero, decide_true, ↓reduceIte] <;> rfl

theorem encoded_signed_format (count : Nat) (value : Int)
    (positive : 0 < count) (bounded : count ≤ maxMagnitudeBytes)
    (fits : value.natAbs < 256 ^ count) :
    SignedFormat (signedNegative value) (encodeSigned count value) := by
  refine ⟨by simpa [encodeSigned] using positive,
    by simpa [encodeSigned] using bounded, ?_⟩
  intro negative
  rw [encodeSigned, decodeMagnitude_encodeMagnitude count value.natAbs fits]
  have hneg : value < 0 := by simpa [signedNegative] using negative
  cases value with
  | ofNat n => omega
  | negSucc n => simp

/-- Every finite integer has an exact sign/magnitude representation. The
chosen count here is an existence witness, not an allocation policy. -/
theorem signed_representation_exists (value : Int) :
    ∃ count, 0 < count ∧
      decodeSigned (signedNegative value) (encodeSigned count value) = value := by
  refine ⟨value.natAbs + 1, by omega, decodeSigned_encodeSigned _ _ ?_⟩
  have hlarge : value.natAbs < 2 ^ (value.natAbs + 1) := by
    have := Nat.lt_two_pow_self (n := value.natAbs + 1)
    omega
  exact Nat.lt_of_lt_of_le hlarge
    (Nat.pow_le_pow_left (by decide : 2 ≤ 256) (value.natAbs + 1))

theorem decodeSigned_nonnegative_zero (bytes : ByteArray)
    (zero : decodeMagnitude bytes = 0) : decodeSigned false bytes = 0 := by
  simp [decodeSigned, zero]

theorem signedFormat_rejects_negative_zero (bytes : ByteArray)
    (zero : decodeMagnitude bytes = 0) : signedFormat true bytes = false := by
  simp [signedFormat, SignedFormat, zero]

/-- Endpoint encoding is fixed width and separate from signed key encoding. -/
def encodeEndpoint (width value : Nat) : ByteArray := ⟨LimbWord.encode width value⟩

theorem encodeEndpoint_canonical (width value : Nat) (fits : value < 2 ^ width) :
    LimbWord.Canonical width (encodeEndpoint width value).data ∧
      decodeMagnitude (encodeEndpoint width value) = value :=
  ⟨LimbWord.canonical_encode width value fits, LimbWord.decode_encode width value fits⟩

theorem endpoint_roundtrip (width : Nat) (bytes : ByteArray)
    (canonical : LimbWord.Canonical width bytes.data) :
    (encodeEndpoint width (decodeMagnitude bytes)).data = bytes.data :=
  LimbWord.encode_decode width bytes.data canonical.1

/-- Kernel controls for permitted padding, canonical zero sign, and a negative
input beyond 128 bits. These are codec facts, not native execution evidence. -/
theorem signed_codec_boundaries :
    decodeSigned true ⟨#[5, 0]⟩ = -5 ∧
      signedFormat true ⟨#[5, 0]⟩ = true ∧
      signedFormat false ⟨#[0, 0]⟩ = true ∧
      signedFormat true ⟨#[0, 0]⟩ = false ∧
      decodeSigned true ⟨#[7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]⟩ =
        -((2 ^ 130 + 7 : Nat) : Int) := by
  decide

end RMQ.SuccinctFinal.PackedNative.Lifecycle
