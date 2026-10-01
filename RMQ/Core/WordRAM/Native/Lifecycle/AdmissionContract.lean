import RMQ.Core.WordRAM.Native.Lifecycle.Admission

/-! # Independent expected-type admission consumer

These clients state their expected clauses directly. In particular, the wire
limits, actual count and endpoint bounds are not inferred from the current
producer declaration. Mutation replay first compiles the producer, then this
client; native parser correctness remains a separate foreign-code obligation.
-/

namespace RMQ.SuccinctFinal.PackedNative.Lifecycle.AdmissionContract

open PackedLifecycle (InputModel)
open PackedWordRAM (wordWidth)

theorem model_selection :
    modelOfComparison false = InputModel.word ∧
      modelOfComparison true = InputModel.comparison :=
  ⟨modelOfComparison_false, modelOfComparison_true⟩

theorem signed_roundtrip (count : Nat) (value : Int)
    (fits : value.natAbs < 256 ^ count) :
    decodeSigned (signedNegative value) (encodeSigned count value) = value :=
  decodeSigned_encodeSigned count value fits

theorem finite_integer_representation (value : Int) :
    ∃ count, 0 < count ∧
      decodeSigned (signedNegative value) (encodeSigned count value) = value :=
  signed_representation_exists value

theorem natural_serialization (value : Nat) :
    0 < (encodeNatural value).size ∧
      (encodeNatural value).size = value.log2 / 8 + 1 ∧
      decodeMagnitude (encodeNatural value) = value :=
  encodeNatural_exact value

theorem signed_format (count : Nat) (value : Int)
    (positive : 0 < count) (bounded : count ≤ 4096)
    (fits : value.natAbs < 256 ^ count) :
    0 < (encodeSigned count value).size ∧
      (encodeSigned count value).size ≤ 4096 ∧
      (signedNegative value = true →
        decodeMagnitude (encodeSigned count value) ≠ 0) :=
  encoded_signed_format count value positive bounded fits

theorem signed_format_check (negative : Bool) (bytes : ByteArray) :
    signedFormat negative bytes = true ↔
      0 < bytes.size ∧ bytes.size ≤ 4096 ∧
        (negative = true → decodeMagnitude bytes ≠ 0) :=
  signedFormat_iff negative bytes

theorem decoded_signed_fields (negative : Bool) (bytes : ByteArray)
    (positive : 0 < bytes.size) (bounded : bytes.size ≤ 4096)
    (nonzero : negative = true → decodeMagnitude bytes ≠ 0) :
    (decodeSigned negative bytes).natAbs = decodeMagnitude bytes ∧
      signedNegative (decodeSigned negative bytes) = negative :=
  ⟨decodeSigned_magnitude negative bytes,
    decodeSigned_sign negative bytes ⟨positive, bounded, nonzero⟩⟩

theorem count_conversion (count : Nat) (bounded : count ≤ 4096) :
    (USize.ofNat count).toNat = count := nativeCount_toUSize_exact count bounded

theorem actual_profile_alignment (count : Nat) : wordWidth count % 8 = 0 :=
  word_profile_byte_aligned count

theorem signed_sequence (count : Nat) (xs : List Int)
    (fits : ∀ value ∈ xs, value.natAbs < 256 ^ count) :
    decodeInputs (xs.map (fun value =>
      (⟨signedNegative value, encodeSigned count value⟩ : SignedBytes))) = xs :=
  decodeInputs_encoded count xs fits

theorem actual_count (inputs : List SignedBytes) :
    (decodeInputs inputs).length = inputs.length := decodeInputs_length inputs

theorem actual_input_at (inputs : List SignedBytes) (i : Nat) :
    (decodeInputs inputs)[i]? =
      (inputs[i]?).map (fun input => decodeSigned input.negative input.magnitude) :=
  decodeInputs_getElem? inputs i

theorem endpoint_projection (width : Nat) (left right : ByteArray)
    (accepted : queryAdmission width left right = true) :
    left.size = LimbWord.limbCount width ∧ right.size = LimbWord.limbCount width ∧
      decodeMagnitude left < 2 ^ width ∧ decodeMagnitude right < 2 ^ width :=
  queryAdmission_success width left right accepted

theorem endpoint_admission_check (width : Nat) (left right : ByteArray) :
    queryAdmission width left right = true ↔
      (left.data.size = LimbWord.limbCount width ∧ LimbWord.decode left.data < 2 ^ width) ∧
      (right.data.size = LimbWord.limbCount width ∧ LimbWord.decode right.data < 2 ^ width) :=
  queryAdmission_iff width left right

theorem endpoint_roundtrip_projection (width : Nat) (bytes : ByteArray)
    (length : bytes.data.size = LimbWord.limbCount width)
    (bound : LimbWord.decode bytes.data < 2 ^ width) :
    (encodeEndpoint width (decodeMagnitude bytes)).data = bytes.data :=
  endpoint_roundtrip width bytes ⟨length, bound⟩

/-- Invalid represented ranges still pass admission. The lifecycle itself
must establish the ordinary None packet; admission does not synthesize it. -/
theorem represented_invalid_range (width n left right : Nat)
    (hl : left < 2 ^ width) (hr : right < 2 ^ width)
    (_invalid : ¬ (left < right ∧ right ≤ n)) :
    queryAdmission width (encodeEndpoint width left) (encodeEndpoint width right) = true ∧
      decodeMagnitude (encodeEndpoint width left) = left ∧
      decodeMagnitude (encodeEndpoint width right) = right :=
  ⟨queryAdmission_encoded width left right hl hr,
    (encodeEndpoint_canonical width left hl).2,
    (encodeEndpoint_canonical width right hr).2⟩

theorem word_admission (xs : List Int) (count : Nat) (left right : ByteArray)
    (accepted : buildAdmission .word xs count left right = true) :
    count = xs.length ∧ xs.length ≤ 4096 ∧
      PackedConstruction.InputFits (wordWidth xs.length) xs ∧
      left.size = LimbWord.limbCount (wordWidth xs.length) ∧
      right.size = LimbWord.limbCount (wordWidth xs.length) ∧
      decodeMagnitude left < 2 ^ wordWidth xs.length ∧
      decodeMagnitude right < 2 ^ wordWidth xs.length :=
  buildAdmission_success .word xs count left right accepted

theorem word_bias (xs : List Int) (count : Nat) (left right : ByteArray)
    (accepted : buildAdmission .word xs count left right = true) :
    ∀ value ∈ xs, (PackedConstruction.encodeInt (wordWidth xs.length) value : Int) =
      value + ((2 ^ (wordWidth xs.length - 1) : Nat) : Int) :=
  buildAdmission_word_bias xs count left right accepted

theorem word_domain_failure (xs : List Int) (count : Nat) (left right : ByteArray)
    (outside : ¬ PackedConstruction.InputFits (wordWidth xs.length) xs) :
    buildAdmission .word xs count left right = false :=
  buildAdmission_word_rejects xs count left right outside

theorem comparison_domain (xs : List Int) : inputDomainCheck .comparison xs = true :=
  (inputDomainCheck_iff .comparison xs).2 True.intro

theorem build_admission_check (model : InputModel) (xs : List Int) (count : Nat)
    (left right : ByteArray) :
    buildAdmission model xs count left right = true ↔
      count = xs.length ∧ xs.length ≤ 4096 ∧ PackedLifecycle.InputDomain model xs ∧
      (left.data.size = LimbWord.limbCount (wordWidth xs.length) ∧
        LimbWord.decode left.data < 2 ^ wordWidth xs.length) ∧
      (right.data.size = LimbWord.limbCount (wordWidth xs.length) ∧
        LimbWord.decode right.data < 2 ^ wordWidth xs.length) :=
  buildAdmission_iff model xs count left right

theorem full_wire_admission (model : InputModel) (inputs : List SignedBytes)
    (left right : ByteArray)
    (accepted : encodedBuildAdmission model inputs left right = true) :
    inputs.length ≤ 4096 ∧
      (∀ input ∈ inputs, 0 < input.magnitude.size ∧ input.magnitude.size ≤ 4096 ∧
        (input.negative = true → decodeMagnitude input.magnitude ≠ 0)) ∧
      (inputs.map fun input => input.magnitude.size).sum ≤ 16777216 ∧
      (decodeInputs inputs).length = inputs.length ∧
      PackedLifecycle.InputDomain model (decodeInputs inputs) ∧
      (left.data.size = LimbWord.limbCount (wordWidth inputs.length) ∧
        LimbWord.decode left.data < 2 ^ wordWidth inputs.length) ∧
      (right.data.size = LimbWord.limbCount (wordWidth inputs.length) ∧
        LimbWord.decode right.data < 2 ^ wordWidth inputs.length) :=
  encodedBuildAdmission_success model inputs left right accepted

theorem full_wire_converse (model : InputModel) (inputs : List SignedBytes)
    (left right : ByteArray)
    (count : inputs.length ≤ 4096)
    (keys : ∀ input ∈ inputs, 0 < input.magnitude.size ∧ input.magnitude.size ≤ 4096 ∧
      (input.negative = true → decodeMagnitude input.magnitude ≠ 0))
    (total : (inputs.map fun input => input.magnitude.size).sum ≤ 16777216)
    (domain : PackedLifecycle.InputDomain model (decodeInputs inputs))
    (leftLength : left.data.size = LimbWord.limbCount (wordWidth inputs.length))
    (leftBound : LimbWord.decode left.data < 2 ^ wordWidth inputs.length)
    (rightLength : right.data.size = LimbWord.limbCount (wordWidth inputs.length))
    (rightBound : LimbWord.decode right.data < 2 ^ wordWidth inputs.length) :
    encodedBuildAdmission model inputs left right = true :=
  (encodedBuildAdmission_iff model inputs left right).2
    ⟨⟨count, keys, total⟩, domain, ⟨leftLength, leftBound⟩, ⟨rightLength, rightBound⟩⟩

end RMQ.SuccinctFinal.PackedNative.Lifecycle.AdmissionContract
