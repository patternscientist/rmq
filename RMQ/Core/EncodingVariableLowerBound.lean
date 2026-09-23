import RMQ.Core.EncodingLowerBound

/-!
# Exact RMQ encodings with bounded variable payload length

The payload is an ordinary bit list, whose length is observable. At a fixed
input size `n`, one decoder answers every valid nonempty half-open query from
the payload and the endpoints. A uniform budget `B` bounds every size-`n`
input's payload; no lower bound on each individual input is asserted.

There are exactly `2^(B+1)-1` bit lists of length at most `B`. Exact answers
distinguish Cartesian shapes, so this capacity and the existing cubic-square
Catalan bound imply the coefficient-correct inequality in doubled bits.
The decoder may specialize fixed advice depending on `n`. It receives neither
the original input nor an additional shape or proof argument.
-/

namespace RMQ

namespace EncodingVariableLowerBound

/-- All bit lists of every length from zero through `B`, without padding. -/
def boundedBitStrings : Nat → List (List Bool)
  | 0 => [[]]
  | B + 1 => boundedBitStrings B ++ LowerBound.bitStrings (B + 1)

private theorem length_eq_of_mem_bitStrings
    {bits : List Bool} {n : Nat}
    (hmem : bits ∈ LowerBound.bitStrings n) : bits.length = n := by
  induction n generalizing bits with
  | zero =>
      simpa [LowerBound.bitStrings] using hmem
  | succ n ih =>
      rcases List.mem_flatMap.mp hmem with ⟨tail, htail, hbits⟩
      have hlength := ih htail
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbits
      rcases hbits with rfl | rfl <;> simp [hlength]

private theorem bitStrings_nodup (n : Nat) :
    (LowerBound.bitStrings n).Nodup := by
  induction n with
  | zero => simp [LowerBound.bitStrings]
  | succ n ih =>
      change List.Pairwise (fun a b : List Bool => a ≠ b)
        ((LowerBound.bitStrings n).flatMap fun bits =>
          [false :: bits, true :: bits])
      rw [List.pairwise_flatMap]
      constructor
      · intro bits _
        simp
      · apply List.Pairwise.imp ?_ ih
        intro left right hne a ha b hb hab
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hne (List.cons.inj hab).2
        · cases hab
        · cases hab
        · exact hne (List.cons.inj hab).2

/-- Membership records the whole bounded universe, including the empty list. -/
theorem mem_boundedBitStrings_iff {bits : List Bool} {B : Nat} :
    bits ∈ boundedBitStrings B ↔ bits.length ≤ B := by
  induction B with
  | zero =>
      simp [boundedBitStrings]
  | succ B ih =>
      rw [boundedBitStrings, List.mem_append, ih]
      constructor
      · intro h
        rcases h with h | h
        · omega
        · have hlength := length_eq_of_mem_bitStrings h
          omega
      · intro h
        by_cases hsmall : bits.length ≤ B
        · exact Or.inl hsmall
        · exact Or.inr
            (LowerBound.mem_bitStrings_of_length (by omega))

/-- Arithmetic form avoiding truncated subtraction during the induction. -/
theorem boundedBitStrings_length_add_one (B : Nat) :
    (boundedBitStrings B).length + 1 = 2 ^ (B + 1) := by
  induction B with
  | zero => simp [boundedBitStrings]
  | succ B ih =>
      simp only [boundedBitStrings, List.length_append,
        LowerBound.bitStrings_length]
      rw [Nat.pow_succ 2 (B + 1)]
      omega

/-- Exact size of the variable-length universe when length is observable. -/
theorem boundedBitStrings_length (B : Nat) :
    (boundedBitStrings B).length = 2 ^ (B + 1) - 1 := by
  have h := boundedBitStrings_length_add_one B
  omega

/-- The enumeration has no repetitions, including across different lengths. -/
theorem boundedBitStrings_nodup (B : Nat) :
    (boundedBitStrings B).Nodup := by
  induction B with
  | zero => simp [boundedBitStrings]
  | succ B ih =>
      rw [boundedBitStrings, List.nodup_append]
      refine ⟨ih, bitStrings_nodup (B + 1), ?_⟩
      intro left hleft right hright heq
      have hsmall := mem_boundedBitStrings_iff.mp hleft
      have hlarge := length_eq_of_mem_bitStrings hright
      subst right
      omega

/-- Exact finite-universe certificate; no quotient or prefix-free convention. -/
theorem boundedBitStrings_cardinality (B : Nat) :
    (boundedBitStrings B).Nodup ∧
      (boundedBitStrings B).length = 2 ^ (B + 1) - 1 ∧
      ∀ bits, bits ∈ boundedBitStrings B ↔ bits.length ≤ B :=
  ⟨boundedBitStrings_nodup B, boundedBitStrings_length B,
    fun _ => mem_boundedBitStrings_iff⟩

end EncodingVariableLowerBound

/-- A single payload-only decoder exact on every size-`n` input, with a uniform
maximum payload length `B`. Proof fields constrain executable data and do not
provide executable answers. Invalid queries are outside this generic contract. -/
structure ExactRMQBoundedEncoding (n B : Nat) where
  encode : List Int → List Bool
  query : List Bool → Nat → Nat → Option Nat
  length_le : ∀ xs, xs.length = n → (encode xs).length ≤ B
  query_exact : ∀ xs, xs.length = n →
    ∀ left len, 0 < len → left + len ≤ n →
      query (encode xs) left (left + len) = some (scanWindow xs left len)

namespace ExactRMQBoundedEncoding

variable {n B : Nat}

/-- Equal payloads give equal valid-window answers because the decoder is fixed. -/
theorem sameRMQBehavior_of_encode_eq (E : ExactRMQBoundedEncoding n B)
    {xs ys : List Int} (hxs : xs.length = n) (hys : ys.length = n)
    (hcode : E.encode xs = E.encode ys) :
    Cartesian.SameRMQBehavior xs ys := by
  constructor
  · omega
  · intro left len hlen hbound
    have hn : left + len ≤ n := by omega
    have hx := E.query_exact xs hxs left len hlen hn
    have hy := E.query_exact ys hys left len hlen hn
    rw [hcode, hy] at hx
    exact (Option.some.inj hx).symm

/-- Exact leftmost half-open RMQ answers distinguish Cartesian shapes. -/
theorem shape_eq_of_encode_eq (E : ExactRMQBoundedEncoding n B)
    {xs ys : List Int} (hxs : xs.length = n) (hys : ys.length = n)
    (hcode : E.encode xs = E.encode ys) :
    Cartesian.shape xs = Cartesian.shape ys :=
  Cartesian.shape_eq_of_sameRMQBehavior
    (E.sameRMQBehavior_of_encode_eq hxs hys hcode)

/-- Restrict the actual encoder to the standard computed representative arrays. -/
def shapeEncode (E : ExactRMQBoundedEncoding n B)
    (shape : Cartesian.CartesianShape) : List Bool :=
  E.encode shape.representative

theorem representative_length_eq
    {shape : Cartesian.CartesianShape}
    (hshape : shape ∈ Cartesian.shapesOfSize n) :
    shape.representative.length = n := by
  rw [Cartesian.CartesianShape.representative_length,
    (Cartesian.mem_shapesOfSize_shapeOfSize hshape).size_eq]

theorem shapeEncode_length_le (E : ExactRMQBoundedEncoding n B)
    {shape : Cartesian.CartesianShape}
    (hshape : shape ∈ Cartesian.shapesOfSize n) :
    (E.shapeEncode shape).length ≤ B :=
  E.length_le shape.representative (representative_length_eq hshape)

/-- Shape injection is a consequence of exactness, not a record assumption. -/
theorem shapeEncode_injective_on (E : ExactRMQBoundedEncoding n B)
    {left right : Cartesian.CartesianShape}
    (hleft : left ∈ Cartesian.shapesOfSize n)
    (hright : right ∈ Cartesian.shapesOfSize n)
    (hcode : E.shapeEncode left = E.shapeEncode right) : left = right := by
  have hshape := E.shape_eq_of_encode_eq
    (representative_length_eq hleft) (representative_length_eq hright) hcode
  simpa [Cartesian.CartesianShape.shape_representative] using hshape

/-- All Cartesian shapes must fit in the complete bounded bit-list universe. -/
theorem shapeCount_le (E : ExactRMQBoundedEncoding n B) :
    Cartesian.shapeCount n ≤ 2 ^ (B + 1) - 1 := by
  have hcapacity : (Cartesian.shapesOfSize n).length ≤
      (EncodingVariableLowerBound.boundedBitStrings B).length := by
    apply LowerBound.length_le_of_nodup_injective_into
      (Cartesian.shapesOfSize n)
      (EncodingVariableLowerBound.boundedBitStrings B) E.shapeEncode
      (Cartesian.shapesOfSize_nodup n)
    · intro shape hshape
      exact EncodingVariableLowerBound.mem_boundedBitStrings_iff.mpr
        (E.shapeEncode_length_le hshape)
    · intro left hleft right hright hcode
      exact E.shapeEncode_injective_on hleft hright hcode
  simpa [Cartesian.shapeCount,
    EncodingVariableLowerBound.boundedBitStrings_length] using hcapacity

/-- Coefficient-correct doubled Catalan lower bound on the uniform maximum
payload length. The extra one accounts for observing variable bit-list length. -/
theorem doubledLogSlackLower_le (E : ExactRMQBoundedEncoding n B) :
    EncodingLowerBound.doubledLogSlackLower n ≤ 2 * (B + 1) := by
  have hcapacity : Cartesian.shapeCount n ≤ 2 ^ (B + 1) :=
    Nat.le_trans E.shapeCount_le (Nat.sub_le _ _)
  simpa [EncodingLowerBound.doubledLogSlackLower] using
    (LowerBound.two_mul_bits_lower_of_cubic_square_bound hcapacity
      (EncodingLowerBound.shapeCount_cubic_square_lower n))

/-- The domain quantified by the uniform budget is inhabited for every size. -/
theorem input_domain_nonempty (n : Nat) :
    ∃ xs : List Int, xs.length = n :=
  ⟨List.replicate n 0, by simp⟩

/-- An already exact encoding remains exact when its uniform budget increases. -/
def withBudget (E : ExactRMQBoundedEncoding n B) {C : Nat} (hBC : B ≤ C) :
    ExactRMQBoundedEncoding n C where
  encode := E.encode
  query := E.query
  length_le xs hxs := Nat.le_trans (E.length_le xs hxs) hBC
  query_exact := E.query_exact

/-- Specialize size-only advice once; the resulting decoder still receives only
payload and endpoints. All exactness quantifiers remain over every size-`n` input. -/
def ofSizeAdvice {Advice : Type} (advice : Nat → Advice)
    (encode : List Int → List Bool)
    (decoder : Advice → List Bool → Nat → Nat → Option Nat)
    (length_le : ∀ xs, xs.length = n → (encode xs).length ≤ B)
    (query_exact : ∀ xs, xs.length = n →
      ∀ left len, 0 < len → left + len ≤ n →
        decoder (advice n) (encode xs) left (left + len) =
          some (scanWindow xs left len)) : ExactRMQBoundedEncoding n B where
  encode := encode
  query := decoder (advice n)
  length_le := length_le
  query_exact := query_exact

/-- Empty input needs no payload and has no valid nonempty query. -/
def emptyEncoding : ExactRMQBoundedEncoding 0 0 where
  encode _ := []
  query _ _ _ := none
  length_le := by intros; simp
  query_exact := by
    intro xs hxs left len hlen hbound
    omega

/-- At size one the sole valid answer is zero. This inhabited zero-bit instance
uses the fixed size-only advice `n-1`; it does not retain the singleton value. -/
def singletonEncoding : ExactRMQBoundedEncoding 1 0 :=
  ofSizeAdvice (fun n => n - 1) (fun _ => [])
    (fun advice _ _ _ => some advice)
    (by intros; simp)
    (by
      intro xs hxs left len hlen hbound
      have hleft : left = 0 := by omega
      have hlen' : len = 1 := by omega
      simp [hleft, hlen', scanWindow])

/-- The same exactness field used by the counting theorem excludes null answers. -/
theorem query_ne_none (E : ExactRMQBoundedEncoding n B)
    {xs : List Int} (hxs : xs.length = n) {left len : Nat}
    (hlen : 0 < len) (hbound : left + len ≤ n) :
    E.query (E.encode xs) left (left + len) ≠ none := by
  rw [E.query_exact xs hxs left len hlen hbound]
  intro h
  cases h

/-- A null decoder cannot satisfy this exact encoding contract at a positive size. -/
theorem null_decoder_impossible (E : ExactRMQBoundedEncoding n B)
    (hn : 0 < n)
    (hnull : ∀ bits left right, E.query bits left right = none) : False := by
  exact E.query_ne_none (xs := List.replicate n 0) (by simp)
    (left := 0) (len := 1) (by omega) (by omega) (hnull _ _ _)

/-- Exactness constrains the answer value, in addition to the presence of an answer. -/
theorem wrong_answer_impossible (E : ExactRMQBoundedEncoding n B)
    {xs : List Int} (hxs : xs.length = n) {left len answer : Nat}
    (hlen : 0 < len) (hbound : left + len ≤ n)
    (hwrong : E.query (E.encode xs) left (left + len) = some answer)
    (hne : answer ≠ scanWindow xs left len) : False := by
  rw [E.query_exact xs hxs left len hlen hbound] at hwrong
  exact hne (Option.some.inj hwrong).symm

/-- A concrete equal-key control observes the leftmost tie policy. -/
theorem equal_key_leftmost (E : ExactRMQBoundedEncoding 2 B) :
    E.query (E.encode [7, 7]) 0 2 = some 0 := by
  simpa [scanWindow, betterIndex] using
    E.query_exact [7, 7] (by rfl) 0 2 (by decide) (by decide)

/-- Distinct answers on the same valid window forbid payload collisions. A fixed
decoder, including any fixed size-only advice, must distinguish these inputs. -/
theorem two_input_codes_ne (E : ExactRMQBoundedEncoding 2 B) :
    E.encode [0, 1] ≠ E.encode [1, 0] := by
  intro hcode
  have hleft := E.query_exact [0, 1] (by rfl) 0 2 (by decide) (by decide)
  have hright := E.query_exact [1, 0] (by rfl) 0 2 (by decide) (by decide)
  rw [hcode, hright] at hleft
  simp [scanWindow, betterIndex] at hleft

/-- Removing exactness would allow a constant empty payload; retaining this same
contract rules it out already at size two. -/
theorem zero_budget_two_impossible (E : ExactRMQBoundedEncoding 2 0) : False := by
  have hleft := E.length_le [0, 1] (by rfl)
  have hright := E.length_le [1, 0] (by rfl)
  have hleft_nil : E.encode [0, 1] = [] := List.length_eq_zero_iff.mp (by omega)
  have hright_nil : E.encode [1, 0] = [] := List.length_eq_zero_iff.mp (by omega)
  exact E.two_input_codes_ne (hleft_nil.trans hright_nil.symm)

/-- Universal fixed-decoder rejection at the actual exactness proposition for a
constant empty payload. An input- or shape-dependent side channel cannot be
substituted for this one decoder uniformly over all size-two inputs. -/
theorem constant_payload_exactness_impossible
    (query : List Bool → Nat → Nat → Option Nat)
    (hexact : ∀ xs : List Int, xs.length = 2 →
      ∀ left len, 0 < len → left + len ≤ 2 →
        query [] left (left + len) = some (scanWindow xs left len)) : False :=
  zero_budget_two_impossible {
    encode := fun _ => []
    query := query
    length_le := by intros; simp
    query_exact := hexact
  }

end ExactRMQBoundedEncoding

end RMQ
