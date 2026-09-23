import Std

/-! # Pointwise input contract for packed construction

This module specifies the supplied input representation. Cell zero contains an
unsigned length; cell `i + 1` contains only the biased signed encoding of key
`i`. It neither constructs an RMQ allocation nor claims that evaluating the
specification is a charged machine execution. Input materialization, reads and
comparisons are obligations of the later construction machine.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

/-- Numeric input cells, with absence distinct from a stored zero. -/
abbrev InputMemory := Nat → Option Nat

/-- A signed key fits the half-open signed interval of a positive word width. -/
def SignedFits (width : Nat) (x : Int) : Prop :=
  0 < width ∧ -((2 ^ (width - 1) : Nat) : Int) ≤ x ∧
    x < ((2 ^ (width - 1) : Nat) : Int)

/-- Biasing maps the signed interval monotonically to unsigned word values. -/
def encodeInt (width : Nat) (x : Int) : Nat :=
  (x + ((2 ^ (width - 1) : Nat) : Int)).toNat

/-- The header is unsigned. Key representability remains a separate premise. -/
def InputFits (width : Nat) (xs : List Int) : Prop :=
  0 < width ∧ xs.length < 2 ^ width ∧ ∀ x ∈ xs, SignedFits width x

/-- A specification of pre-supplied input, not an uncharged conversion step. -/
def encodeInput (width : Nat) (xs : List Int) : InputMemory :=
  fun address => if address = 0 then some xs.length
    else (xs[address - 1]?).map (encodeInt width)

/-- Exactly one header cell and one cell per input key are retained. -/
def inputCellCount (xs : List Int) : Nat := xs.length + 1

private theorem input_capacity_eq_twice_half {width : Nat} (hw : 0 < width) :
    2 ^ width = 2 ^ (width - 1) * 2 := by
  calc
    2 ^ width = 2 ^ (width - 1 + 1) := congrArg (fun n => 2 ^ n) (by omega)
    _ = 2 ^ (width - 1) * 2 := Nat.pow_succ _ _

/-- No information is lost by the `toNat` conversion on representable keys. -/
theorem encodeInt_asInt {width : Nat} {x : Int} (hx : SignedFits width x) :
    (encodeInt width x : Int) = x + ((2 ^ (width - 1) : Nat) : Int) := by
  apply Int.toNat_of_nonneg
  rcases hx with ⟨_, hlo, _⟩
  omega

theorem encodeInt_lt_capacity {width : Nat} {x : Int} (hx : SignedFits width x) :
    encodeInt width x < 2 ^ width := by
  have hvalue := encodeInt_asInt hx
  have hcapacity := input_capacity_eq_twice_half hx.1
  rcases hx with ⟨_, hlo, hhi⟩
  omega

/-- Unsigned comparison of encoded keys refines ordinary integer order. -/
theorem encodeInt_le_iff {width : Nat} {x y : Int}
    (hx : SignedFits width x) (hy : SignedFits width y) :
    encodeInt width x ≤ encodeInt width y ↔ x ≤ y := by
  have hx' := encodeInt_asInt hx
  have hy' := encodeInt_asInt hy
  omega

theorem encodeInt_lt_iff {width : Nat} {x y : Int}
    (hx : SignedFits width x) (hy : SignedFits width y) :
    encodeInt width x < encodeInt width y ↔ x < y := by
  have hx' := encodeInt_asInt hx
  have hy' := encodeInt_asInt hy
  omega

theorem encodeInt_eq_iff {width : Nat} {x y : Int}
    (hx : SignedFits width x) (hy : SignedFits width y) :
    encodeInt width x = encodeInt width y ↔ x = y := by
  have hx' := encodeInt_asInt hx
  have hy' := encodeInt_asInt hy
  omega

@[simp] theorem encodeInput_header (width : Nat) (xs : List Int) :
    encodeInput width xs 0 = some xs.length := by
  simp [encodeInput]

/-- Every key cell depends only on the corresponding key and the fixed width. -/
@[simp] theorem encodeInput_succ (width : Nat) (xs : List Int) (i : Nat) :
    encodeInput width xs (i + 1) = (xs[i]?).map (encodeInt width) := by
  simp [encodeInput]

theorem encodeInput_key {width : Nat} {xs : List Int} {i : Nat} {x : Int}
    (hx : xs[i]? = some x) :
    encodeInput width xs (i + 1) = some (encodeInt width x) := by
  simp [hx]

/-- The extent is exact, including the empty input's sole header cell. -/
theorem encodeInput_eq_none_iff (width : Nat) (xs : List Int) (address : Nat) :
    encodeInput width xs address = none ↔ xs.length < address := by
  cases address with
  | zero => simp
  | succ i =>
      simp only [encodeInput_succ, Option.map_eq_none_iff, List.getElem?_eq_none_iff]
      omega

theorem encodeInput_word_fits {width : Nat} {xs : List Int}
    (hfit : InputFits width xs) {address value : Nat}
    (hread : encodeInput width xs address = some value) : value < 2 ^ width := by
  cases address with
  | zero =>
      have heq : xs.length = value := by simpa using hread
      rw [← heq]
      exact hfit.2.1
  | succ i =>
      rw [encodeInput_succ] at hread
      obtain ⟨x, hx, heq⟩ := Option.map_eq_some_iff.mp hread
      rw [← heq]
      exact encodeInt_lt_capacity (hfit.2.2 x (List.mem_of_getElem? hx))

/-- All present input addresses fit the header's declared capacity. This does
not assert a bound for a later machine's one-past-end sentinel. -/
theorem encodeInput_address_fits {width : Nat} {xs : List Int}
    (hfit : InputFits width xs) {address value : Nat}
    (hread : encodeInput width xs address = some value) : address < 2 ^ width := by
  have hbound : address ≤ xs.length := by
    by_cases h : address ≤ xs.length
    · exact h
    · have hnone := (encodeInput_eq_none_iff width xs address).2 (by omega)
      rw [hread] at hnone
      contradiction
  exact Nat.lt_of_le_of_lt hbound hfit.2.1

/-- Same-length inputs with the same key at an address have the same cell. -/
theorem encodeInput_pointwise {width : Nat} {xs ys : List Int}
    (hlen : xs.length = ys.length) (address : Nat)
    (hkey : address ≠ 0 → xs[address - 1]? = ys[address - 1]?) :
    encodeInput width xs address = encodeInput width ys address := by
  by_cases hzero : address = 0
  · simp [encodeInput, hzero, hlen]
  · simp [encodeInput, hzero, hkey hzero]

/-- Replacing a key leaves every other cell, including the header, unchanged. -/
theorem encodeInput_set_other (width : Nat) (xs : List Int) (i : Nat) (x : Int)
    (address : Nat) (hne : address ≠ i + 1) :
    encodeInput width (xs.set i x) address = encodeInput width xs address := by
  apply encodeInput_pointwise (by simp)
  intro hzero
  exact List.getElem?_set_ne (by omega)

theorem encodeInput_set_self (width : Nat) (xs : List Int) (i : Nat) (x : Int)
    (hi : i < xs.length) :
    encodeInput width (xs.set i x) (i + 1) = some (encodeInt width x) := by
  simp [List.getElem?_set_self hi]

/-- Zero is representable at every positive signed width. -/
theorem zero_signedFits {width : Nat} (hw : 0 < width) : SignedFits width 0 := by
  have hhalf := Nat.two_pow_pos (width - 1)
  exact ⟨hw, by omega, by omega⟩

/-- Every size has a nonempty admissible input family whenever its unsigned
header fits. This statement makes no assumption about a PQ1-specific width. -/
theorem zero_inputFits {width n : Nat} (hw : 0 < width) (hn : n < 2 ^ width) :
    InputFits width (List.replicate n (0 : Int)) := by
  refine ⟨hw, by simpa using hn, ?_⟩
  intro x hx
  have heq : x = 0 := List.eq_of_mem_replicate hx
  subst x
  exact zero_signedFits hw

/-- A simple all-size witness; logarithmic width and complete machine capacity
remain obligations of the composed construction theorem. -/
theorem inputFits_all_sizes (n : Nat) :
    InputFits (n + 2) (List.replicate n (0 : Int)) := by
  apply zero_inputFits (by omega)
  have hlarge : n + 2 < 2 ^ (n + 2) := Nat.lt_two_pow_self
  omega

end RMQ.SuccinctFinal.PackedConstruction
