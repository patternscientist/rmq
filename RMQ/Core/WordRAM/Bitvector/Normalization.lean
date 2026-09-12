import RMQ.Core.Succinct
import RMQ.Core.SuccinctSpace.WordStore

/-!
# Selected-bit normalization

These semantic and numeric identities let a false-bit reader serve either
Boolean value. A physical client must derive the normalized numeric word from
its charged raw reply; these identities make no execution or storage claim.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace

/-- Preserve positions and map the requested Boolean value to `false`. -/
def normalize (target : Bool) (bits : List Bool) : List Bool :=
  bits.map (fun bit => bit != target)

@[simp] theorem normalize_eq_map (target : Bool) (bits : List Bool) :
    normalize target bits = bits.map (fun bit => bit != target) := rfl

@[simp] theorem normalize_length (target : Bool) (bits : List Bool) :
    (normalize target bits).length = bits.length := by
  simp [normalize]

@[simp] theorem normalize_nil (target : Bool) : normalize target [] = [] := rfl

@[simp] theorem normalize_cons (target bit : Bool) (bits : List Bool) :
    normalize target (bit :: bits) = (bit != target) :: normalize target bits := rfl

@[simp] theorem normalize_bit_eq_false (target bit : Bool) :
    (bit != target) = false ↔ bit = target := by
  cases target <;> cases bit <;> decide

@[simp] theorem normalize_bit_involutive (target bit : Bool) :
    ((bit != target) != target) = bit := by
  cases target <;> cases bit <;> rfl

@[simp] theorem normalize_false (bits : List Bool) : normalize false bits = bits := by
  simp [normalize]

@[simp] theorem normalize_involutive (target : Bool) (bits : List Bool) :
    normalize target (normalize target bits) = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp only [normalize_cons, normalize_bit_involutive, ih]

theorem normalize_getElem? (target : Bool) (bits : List Bool) (index : Nat) :
    (normalize target bits)[index]? =
      (bits[index]?).map (fun bit => bit != target) := by
  simp [normalize]

theorem normalize_take (target : Bool) (bits : List Bool) (limit : Nat) :
    normalize target (bits.take limit) = (normalize target bits).take limit := by
  simp [normalize, List.map_take]

theorem normalize_drop (target : Bool) (bits : List Bool) (start : Nat) :
    normalize target (bits.drop start) = (normalize target bits).drop start := by
  simp [normalize, List.map_drop]

/-- Prefix counts transport for every natural prefix, including saturation. -/
theorem rankPrefix_normalize (target : Bool) (bits : List Bool) (limit : Nat) :
    Succinct.rankPrefix false (normalize target bits) limit =
      Succinct.rankPrefix target bits limit := by
  induction bits generalizing limit with
  | nil => simp [Succinct.rankPrefix_nil]
  | cons bit bits ih =>
      cases limit with
      | zero => rfl
      | succ limit =>
          simp only [normalize_cons, Succinct.rankPrefix, normalize_bit_eq_false, ih]

/-- The selected position is unchanged, with arbitrary starting offset. -/
theorem selectFrom_normalize (target : Bool) (bits : List Bool)
    (base occurrence : Nat) :
    Succinct.selectFrom false (normalize target bits) base occurrence =
      Succinct.selectFrom target bits base occurrence := by
  induction bits generalizing base occurrence with
  | nil => rfl
  | cons bit bits ih =>
      simp only [normalize_cons, Succinct.selectFrom, normalize_bit_eq_false, ih]

/-- Zero-based select transports even when the occurrence is absent. -/
theorem select_normalize (target : Bool) (bits : List Bool) (occurrence : Nat) :
    Succinct.select false (normalize target bits) occurrence =
      Succinct.select target bits occurrence := by
  exact selectFrom_normalize target bits 0 occurrence

/-- Complementing a finite little-endian word complements precisely its bits. -/
theorem normalize_true_numeric_sum (bits : List Bool) :
    bitsToNatLE (normalize true bits) + bitsToNatLE bits + 1 =
      2 ^ bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;>
        simp [normalize, bitsToNatLE, bitToNat, Nat.pow_succ] at * <;> omega

/-- A normalized word can be computed from its numeric reply and its length. -/
theorem normalize_numeric (target : Bool) (bits : List Bool) :
    bitsToNatLE (normalize target bits) =
      if target then 2 ^ bits.length - 1 - bitsToNatLE bits
      else bitsToNatLE bits := by
  cases target with
  | false => simp
  | true =>
      have h := normalize_true_numeric_sum bits
      change bitsToNatLE (normalize true bits) =
        2 ^ bits.length - 1 - bitsToNatLE bits
      omega

/-- The existing reader's one-based presence packet also has a scalar formula. -/
theorem normalize_numeric_packet (target : Bool) (bits : List Bool) :
    bitsToNatLE (normalize target bits) + 1 =
      if target then 2 ^ bits.length - bitsToNatLE bits
      else bitsToNatLE bits + 1 := by
  cases target with
  | false => simp
  | true =>
      have h := normalize_true_numeric_sum bits
      change bitsToNatLE (normalize true bits) + 1 =
        2 ^ bits.length - bitsToNatLE bits
      omega

/-- Preserve absence before applying the scalar formula to a present packet. -/
theorem normalize_optional_numeric_packet (target : Bool) (word : Option (List Bool)) :
    ((word.map (normalize target)).map (fun bits => bitsToNatLE bits + 1)).getD 0 =
      let packet := (word.map (fun bits => bitsToNatLE bits + 1)).getD 0
      let len := (word.map List.length).getD 0
      if packet = 0 then 0 else if target then 2 ^ len + 1 - packet else packet := by
  cases word with
  | none => rfl
  | some bits =>
      simp only [Option.map_some, Option.getD_some]
      have hp : bitsToNatLE bits + 1 ≠ 0 := by omega
      rw [if_neg hp, normalize_numeric_packet]
      cases target <;> simp

theorem normalize_optional_length (target : Bool) (word : Option (List Bool)) :
    ((word.map (normalize target)).map List.length).getD 0 =
      (word.map List.length).getD 0 := by
  cases word <;> simp

/-- Exact-type semantic consumer over the same input and every API argument. -/
theorem normalization_semantics (target : Bool) (bits : List Bool) :
    (normalize target bits).length = bits.length ∧
    (∀ limit : Nat,
      Succinct.rankPrefix false (normalize target bits) limit =
        Succinct.rankPrefix target bits limit) ∧
    (∀ occurrence : Nat,
      Succinct.select false (normalize target bits) occurrence =
        Succinct.select target bits occurrence) :=
  ⟨normalize_length target bits, rankPrefix_normalize target bits,
    select_normalize target bits⟩

-- Kernel-checked semantic controls. These are not physical-program validation.
example : Succinct.select false (normalize true []) 0 = none := by decide
example : Succinct.select false (normalize true [true]) 0 = some 0 := by decide
example : Succinct.select false (normalize false [true]) 0 = none := by decide
example : Succinct.rankPrefix false (normalize true [false, true]) 3 = 1 := by decide
example : Succinct.select false (normalize true [false, true]) 1 = none := by decide
example : Succinct.select false (normalize false [true, false]) 0 = some 1 := by decide
example : normalize true [true, false, true, false] = [false, true, false, true] := by decide
example : bitsToNatLE (normalize true [true, false, true]) = 2 := by decide

/-- Omitting normalization cannot meet the universal rank transport contract. -/
theorem identity_rank_transport_fails :
    ¬ (∀ (target : Bool) (bits : List Bool) (limit : Nat),
      Succinct.rankPrefix false bits limit = Succinct.rankPrefix target bits limit) := by
  intro h
  have bad := h true [true] 1
  simp [Succinct.rankPrefix] at bad

/-- The same omitted-normalization mutation also fails the select contract. -/
theorem identity_select_transport_fails :
    ¬ (∀ (target : Bool) (bits : List Bool) (occurrence : Nat),
      Succinct.select false bits occurrence = Succinct.select target bits occurrence) := by
  intro h
  have bad := h true [true] 0
  simp [Succinct.select, Succinct.selectFrom] at bad

end RMQ.PackedBitvector
