import RMQ.Core.WordRAM.Native.Limbs

/-! Independently stated consumer types and exact finite-word boundary checks. -/

namespace RMQ.SuccinctFinal.PackedNative.LimbWord.Checks

open PackedWordRAM

example (width value : Nat) (h : value < 2 ^ width) :
    decode (encode width value) = value := decode_encode width value h

example (width value : Nat) :
    (encode width value).size = (width + 7) / 8 := encode_size width value

example (width x y : Nat) (hx : x < 2 ^ width) (hy : y < 2 ^ width)
    (h : encode width x = encode width y) : x = y := encode_injective width x y hx hy h

example (width : Nat) (op : Arithmetic) (x y result : Word)
    (h : checkedArithmetic width op x y = .ok result) :
    (x.size = (width + 7) / 8 ∧ decode x < 2 ^ width) ∧
    (y.size = (width + 7) / 8 ∧ decode y < 2 ^ width) ∧
    (op.eval (decode x) (decode y) < 2 ^ width ∧
      (op = .sub → decode y ≤ decode x) ∧
      (op = .div ∨ op = .mod → 0 < decode y) ∧
      (op = .shl ∨ op = .shr → decode y < width)) ∧
    (result.size = (width + 7) / 8 ∧ decode result < 2 ^ width) ∧
    decode result = op.eval (decode x) (decode y) :=
  checkedArithmetic_success width op x y result h

example (width : Nat) (op : Arithmetic) (x y : Word)
    (hx : x.size = (width + 7) / 8 ∧ decode x < 2 ^ width)
    (hy : y.size = (width + 7) / 8 ∧ decode y < 2 ^ width)
    (h : op.eval (decode x) (decode y) < 2 ^ width ∧
      (op = .sub → decode y ≤ decode x) ∧
      (op = .div ∨ op = .mod → 0 < decode y) ∧
      (op = .shl ∨ op = .shr → decode y < width)) :
    checkedArithmetic width op x y =
      .ok (encode width (op.eval (decode x) (decode y))) :=
  checkedArithmetic_of_safe width op x y hx hy h

example (width : Nat) (op : Comparison) (x y result : Word)
    (h : checkedComparison width op x y = .ok result) :
    Canonical width x ∧ Canonical width y ∧ Canonical width result ∧
    decode result = op.eval (decode x) (decode y) :=
  checkedComparison_success width op x y result h

example (width limit : Nat) (word : Word) (address : USize)
    (h : checkedAddress width limit word = .ok address) :
    Canonical width word ∧ address.toNat = decode word ∧ address.toNat < limit :=
  checkedAddress_success width limit word address h

example (width : Nat) (value : Int) (result : Word)
    (h : checkedInt width value = .ok result) :
    0 ≤ value ∧ Canonical width result ∧ (decode result : Int) = value :=
  checkedInt_success width value result h

-- Each concrete result below is the independently calculated reference result.
example : checkedArithmetic 8 .add (encode 8 17) (encode 8 19) = .ok (encode 8 36) := by rfl
example : checkedArithmetic 8 .sub (encode 8 19) (encode 8 17) = .ok (encode 8 2) := by rfl
example : checkedArithmetic 8 .mul (encode 8 13) (encode 8 17) = .ok (encode 8 221) := by rfl
example : checkedArithmetic 8 .div (encode 8 221) (encode 8 17) = .ok (encode 8 13) := by rfl
example : checkedArithmetic 8 .mod (encode 8 222) (encode 8 17) = .ok (encode 8 1) := by rfl
example : checkedArithmetic 8 .shl (encode 8 3) (encode 8 4) = .ok (encode 8 48) := by rfl
example : checkedArithmetic 8 .shr (encode 8 49) (encode 8 4) = .ok (encode 8 3) := by rfl
example : checkedArithmetic 8 .band (encode 8 12) (encode 8 10) = .ok (encode 8 8) := by rfl
example : checkedArithmetic 8 .bor (encode 8 12) (encode 8 10) = .ok (encode 8 14) := by rfl
example : checkedArithmetic 8 .bxor (encode 8 12) (encode 8 10) = .ok (encode 8 6) := by rfl

example : decode (encode 168 (2 ^ 167 + 19)) = 2 ^ 167 + 19 :=
  decode_encode _ _ (by decide)
example : decode (encode 176 (2 ^ 175 + 37)) = 2 ^ 175 + 37 :=
  decode_encode _ _ (by decide)
example : (encode 168 0).size = 21 ∧ (encode 176 0).size = 22 := by decide
example : Canonical 0 #[] := by decide
example : ¬ Canonical 1 #[2] := by decide
example : checkedArithmetic 8 .add #[] (encode 8 1) = .error .malformedWord := by rfl
example : checkedArithmetic 8 .add (encode 8 255) (encode 8 1) = .error .overflow := by rfl
example : checkedArithmetic 8 .sub (encode 8 0) (encode 8 1) = .error .underflow := by rfl
example : checkedArithmetic 8 .div (encode 8 17) (encode 8 0) = .error .zeroDivisor := by rfl
example : checkedArithmetic 8 .mod (encode 8 17) (encode 8 0) = .error .zeroDivisor := by rfl
example : checkedArithmetic 8 .shl (encode 8 1) (encode 8 8) = .error .oversizedShift := by rfl
example : checkedArithmetic 8 .shr (encode 8 1) (encode 8 8) = .error .oversizedShift := by rfl
example : checkedComparison 8 .lt (encode 8 17) (encode 8 19) = .ok (encode 8 1) := by rfl
example : checkedComparison 8 .le (encode 8 19) (encode 8 19) = .ok (encode 8 1) := by rfl
example : checkedComparison 8 .eq (encode 8 17) (encode 8 19) = .ok (encode 8 0) := by rfl
example : checkedAddress 8 17 (encode 8 17) = .error .addressLimit := by rfl
example : checkedInt 8 (-1) = .error .negativeInput := by rfl
example : checkedInt 8 256 = .error .overflow := by rfl
example : checkedInt 8 255 = .ok (encode 8 255) := by rfl

#print axioms decode_encode
#print axioms encode_decode
#print axioms encode_injective
#print axioms decode_injective
#print axioms canonical_padding
#print axioms encoded_payload_bits
#print axioms encodeList_getElem
#print axioms checkedArithmetic_of_safe
#print axioms checkedArithmetic_success
#print axioms checkedArithmetic_accepts_iff
#print axioms arithmeticSafe_of_instructionSafe
#print axioms checkedComparison_success
#print axioms checkedAddress_success
#print axioms checkedInt_success

end RMQ.SuccinctFinal.PackedNative.LimbWord.Checks
