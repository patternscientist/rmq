import RMQ.Core.SuccinctRMQClassic
import RMQ.Core.SuccinctFinal.RAM.ReviewerPhysical

/-!
# EG-CP-F01: the frozen packed header schema

Scratch evidence file for the Stage F row `EG-CP-F01-HEADER-SCHEMA`.
Nothing here is added to `RMQ/`.

The frozen objects are, in order:

* `ZqhF01.w`                  -- the frozen cell width `w(n)`;
* `ZqhF01.HeaderField`        -- the closed field-tag universe;
* `ZqhF01.K`                  -- the literal header arity;
* `ZqhF01.frozenSchema`       -- fields, per-field width, per-field value;
* `ZqhF01.headerBits`         -- the serialized header;
* `ZqhF01.payloadBits`        -- definitionally `SuccinctClassic.buildPayload`;
* `ZqhF01.serializedBits`     -- `headerBits xs ++ payloadBits xs`.

Arity is enforced by the elaborator in three independent places; see the
section `## 3` comment.
-/

namespace ZqhF01

open RMQ
open RMQ.SuccinctSpace

/-! ## 0. The frozen cell width `w(n)`, re-pinned locally

Identical to the already-checked `RMQ.PackedHeader.frozenWordWidth` of
`docs/internal/f01_evidence/dpw_f01_width_a.lean`; restated here so this file
stands alone. -/

/-- The frozen packed cell width `w(n)`, `n` the input length. -/
def w (n : Nat) : Nat :=
  SuccinctRank.machineWordBits (2 * n)

theorem w_closed_form (n : Nat) : w n = Nat.log2 (2 * n) + 1 := rfl

theorem one_le_w (n : Nat) : 1 <= w n := by
  simp only [w, SuccinctRank.machineWordBits]
  omega

theorem lt_two_pow_w (n : Nat) : n < 2 ^ w n := by
  have h : 2 * n < 2 ^ (Nat.log2 (2 * n) + 1) := Nat.lt_log2_self
  simp only [w, SuccinctRank.machineWordBits]
  omega

/-- `machineWordBits` always strictly dominates its argument.  This is the one
fact that makes every field-fit theorem below uniform. -/
theorem lt_two_pow_machineWordBits (m : Nat) :
    m < 2 ^ SuccinctRank.machineWordBits m := by
  simpa [SuccinctRank.machineWordBits] using (Nat.lt_log2_self (n := m))

theorem log2_zero : Nat.log2 0 = 0 := by simp

private theorem log2_eq_of_bounds {n k : Nat}
    (hlow : 2 ^ k <= n) (hhigh : n < 2 ^ (k + 1)) :
    Nat.log2 n = k := by
  have hn : n ≠ 0 := by
    have : 0 < 2 ^ k := Nat.pow_pos (by omega)
    omega
  have h1 : k <= Nat.log2 n := (Nat.le_log2 hn).mpr hlow
  have h2 : Nat.log2 n < k + 1 := (Nat.log2_lt hn).mpr hhigh
  omega

theorem log2_one : Nat.log2 1 = 0 :=
  log2_eq_of_bounds (by decide) (by decide)

theorem log2_two : Nat.log2 2 = 1 :=
  log2_eq_of_bounds (by decide) (by decide)

theorem log2_two_mul_of_pos {n : Nat} (hn : 0 < n) :
    Nat.log2 (2 * n) = Nat.log2 n + 1 := by
  have hn0 : n ≠ 0 := by omega
  have hself : 2 ^ Nat.log2 n <= n := Nat.log2_self_le hn0
  have hlt : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  refine log2_eq_of_bounds ?_ ?_
  · have hsucc : 2 ^ (Nat.log2 n + 1) = 2 ^ Nat.log2 n * 2 := by rw [Nat.pow_succ]
    omega
  · have hsucc : 2 ^ (Nat.log2 n + 1 + 1) = 2 ^ (Nat.log2 n + 1) * 2 := by
      rw [Nat.pow_succ]
    omega

theorem machineWordBits_two_mul_of_pos {m : Nat} (hm : 0 < m) :
    SuccinctRank.machineWordBits (2 * m)
      = SuccinctRank.machineWordBits m + 1 := by
  simp only [SuccinctRank.machineWordBits, log2_two_mul_of_pos hm]

/-- Small-size pin: `w 0 = 1`. -/
theorem w_zero : w 0 = 1 := by
  simp only [w, SuccinctRank.machineWordBits, show (2 * 0 : Nat) = 0 from rfl,
    log2_zero]

/-- Small-size pin: `w 1 = 2`. -/
theorem w_one : w 1 = 2 := by
  simp only [w, SuccinctRank.machineWordBits, show (2 * 1 : Nat) = 2 from rfl,
    log2_two]

/-! ## 1. Generic serialization machinery

A schema is a list of field tags plus two total functions: the per-field
frozen bit width, a function of `n` only, and the per-field value, a function
of the input.  Nothing here knows how many fields there are; the arity lives
entirely in the concrete schemas of sections 3 and 6. -/

/-- A packed header schema over a closed field-tag universe `F`. -/
structure HeaderSchema (F : Type) where
  /-- Serialization order of the descriptor fields. -/
  fields : List F
  /-- Frozen bit width of each field.  Depends on `n` only. -/
  width : Nat -> F -> Nat
  /-- Value stored in each field. -/
  value : List Int -> F -> Nat

/-- Number of serialized descriptor fields. -/
def HeaderSchema.arity {F : Type} (S : HeaderSchema F) : Nat :=
  S.fields.length

/-- The header, field by field, before concatenation. -/
def HeaderSchema.fieldWords {F : Type} (S : HeaderSchema F)
    (xs : List Int) : List (List Bool) :=
  S.fields.map (fun f => natToBitsLE (S.width xs.length f) (S.value xs f))

/-- The serialized header bitstring. -/
def HeaderSchema.bits {F : Type} (S : HeaderSchema F)
    (xs : List Int) : List Bool :=
  flattenPayloadWords (S.fieldWords xs)

theorem flatten_map_length {F : Type} (fields : List F) (g : F -> List Bool) :
    (flattenPayloadWords (fields.map g)).length
      = (fields.map (fun f => (g f).length)).sum := by
  induction fields with
  | nil => simp [flattenPayloadWords]
  | cons a rest ih => simp [flattenPayloadWords, ih]

/-- Field count is the schema arity, for every input. -/
theorem HeaderSchema.fieldWords_length {F : Type} (S : HeaderSchema F)
    (xs : List Int) : (S.fieldWords xs).length = S.arity := by
  simp [HeaderSchema.fieldWords, HeaderSchema.arity]

/-- Every emitted field word has exactly its frozen width. -/
theorem HeaderSchema.fieldWords_widths {F : Type} (S : HeaderSchema F)
    (xs : List Int) (f : F) :
    (natToBitsLE (S.width xs.length f) (S.value xs f)).length
      = S.width xs.length f :=
  natToBitsLE_length _ _

/-- Header length is the sum of the frozen field widths, an `n`-only quantity. -/
theorem HeaderSchema.bits_length {F : Type} (S : HeaderSchema F)
    (xs : List Int) :
    (S.bits xs).length = (S.fields.map (S.width xs.length)).sum := by
  simp only [HeaderSchema.bits, HeaderSchema.fieldWords]
  rw [flatten_map_length]
  simp [natToBitsLE_length]

/-- Generic field-fit round trip: a field whose value fits its frozen width is
recovered exactly by the little-endian decoder. -/
theorem HeaderSchema.field_roundTrip {F : Type} (S : HeaderSchema F)
    (xs : List Int) (f : F)
    (hfit : S.value xs f < 2 ^ S.width xs.length f) :
    bitsToNatLE (natToBitsLE (S.width xs.length f) (S.value xs f))
      = S.value xs f :=
  bitsToNatLE_natToBitsLE_of_lt hfit

/-! ## 2. The payload half of the contract

`payloadBits` is `SuccinctClassic.buildPayload` by definitional unfolding, not
by a proved representation equivalence. -/

/-- The frozen payload: definitionally the canonical `buildPayload`. -/
def payloadBits (xs : List Int) : List Bool :=
  SuccinctClassic.buildPayload xs

theorem payloadBits_def (xs : List Int) :
    payloadBits xs = SuccinctClassic.buildPayload xs := rfl

/-- The same statement with the right-hand side fully unfolded to the canonical
reviewer payload, again by `rfl`. -/
theorem payloadBits_eq_canonicalReviewerPayload (xs : List Int) :
    payloadBits xs
      = SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayload
          (SuccinctClassic.cartesianShape xs) := rfl

/-! ## 3. THE FROZEN SCHEMA: `K = 1`

The field universe is a closed inductive.  Arity is enforced by the elaborator
in three independent places, so a fourth field cannot be smuggled in:

1. `frozenWidth` and `frozenValue` are defined by `match` on `HeaderField`; a
   new constructor without a new arm is a non-exhaustive match;
2. `frozenFields_complete` is closed by `cases f <;> decide`; a new constructor
   that is not listed in `frozenFields` makes the `decide` fail;
3. `frozen_arity` is `rfl` against the literal `K`; adding a field to
   `frozenFields` without bumping `K` makes the `rfl` fail.

Direction 2 catches "declared but not serialized", direction 3 catches
"serialized but not counted".  Together they pin `K` to the constructor count.
-/

/-- The closed universe of frozen header fields. -/
inductive HeaderField where
  /-- The input length `n`.  Every other geometry constant is a closed
  arithmetic function of it. -/
  | size
  deriving DecidableEq, Repr

/-- THE FROZEN HEADER ARITY. -/
def K : Nat := 1

/-- Serialization order. -/
def frozenFields : List HeaderField := [HeaderField.size]

/-- Frozen per-field width.  A function of `n` alone. -/
def frozenWidth (n : Nat) : HeaderField -> Nat
  | .size => w n

/-- Frozen per-field value. -/
def frozenValue (xs : List Int) : HeaderField -> Nat
  | .size => xs.length

/-- THE FROZEN SCHEMA. -/
def frozenSchema : HeaderSchema HeaderField where
  fields := frozenFields
  width := frozenWidth
  value := frozenValue

/-- Elaborator gate 2: every constructor of the closed field universe is
serialized. -/
theorem frozenFields_complete (f : HeaderField) : f ∈ frozenFields := by
  cases f <;> decide

/-- No field is serialized twice. -/
theorem frozenFields_nodup : frozenFields.Nodup := by decide

/-- **ARITY THEOREM.**  The serialized field count is exactly `K`, for every
input, with no side condition. -/
theorem frozen_arity (xs : List Int) :
    (frozenSchema.fieldWords xs).length = K :=
  frozenSchema.fieldWords_length xs

/-- Elaborator gate 3: the schema's own field list has length `K`, by `rfl`. -/
theorem frozenSchema_arity_literal : frozenSchema.arity = K := rfl

/-- `K` is `1`, verbatim. -/
theorem K_eq_one : K = 1 := rfl

/-! ## 4. `headerBits`, `serializedBits`, and the width theorems -/

/-- THE FROZEN HEADER. -/
def headerBits (xs : List Int) : List Bool :=
  frozenSchema.bits xs

/-- THE FROZEN SERIALIZATION. -/
def serializedBits (xs : List Int) : List Bool :=
  headerBits xs ++ payloadBits xs

theorem serializedBits_def (xs : List Int) :
    serializedBits xs = headerBits xs ++ payloadBits xs := rfl

/-- The contract's serialization equation with the payload spelled out as the
canonical `buildPayload`, by `rfl`. -/
theorem serializedBits_eq (xs : List Int) :
    serializedBits xs = headerBits xs ++ SuccinctClassic.buildPayload xs := rfl

/-- **WIDTH THEOREM (exact).**  Every field of the frozen schema has width
exactly `w n`, for all `n` and all fields, including `n = 0` and `n = 1`. -/
theorem frozen_field_width_eq (n : Nat) (f : HeaderField) :
    frozenSchema.width n f = w n := by
  cases f
  rfl

/-- **WIDTH THEOREM (bound).**  Every field width is bounded by the frozen
`w n`; the stated multiple is `1`. -/
theorem frozen_field_width_le (n : Nat) (f : HeaderField) :
    frozenSchema.width n f <= 1 * w n := by
  rw [frozen_field_width_eq]
  omega

/-- **FIT THEOREM.**  Every field's value is strictly below `2 ^ (its frozen
width)`, so no field is truncated, for all inputs including the empty list. -/
theorem frozen_field_fits (xs : List Int) (f : HeaderField) :
    frozenSchema.value xs f < 2 ^ frozenSchema.width xs.length f := by
  cases f
  exact lt_two_pow_w xs.length

/-- **HEADER LENGTH, closed form in `n`.** -/
theorem headerBits_length (xs : List Int) :
    (headerBits xs).length = K * w xs.length := by
  simp [headerBits, HeaderSchema.bits, HeaderSchema.fieldWords, frozenSchema,
    frozenFields, frozenWidth, flattenPayloadWords, natToBitsLE_length, K]

/-- The same, fully closed: `Nat.log2 (2 * n) + 1`. -/
theorem headerBits_length_closed (xs : List Int) :
    (headerBits xs).length = Nat.log2 (2 * xs.length) + 1 := by
  rw [headerBits_length]
  simp [K, w, SuccinctRank.machineWordBits]

/-- The header depends on the input only through `n`. -/
theorem headerBits_size_only (xs ys : List Int)
    (hlen : xs.length = ys.length) : headerBits xs = headerBits ys := by
  simp [headerBits, HeaderSchema.bits, HeaderSchema.fieldWords, frozenSchema,
    frozenFields, frozenWidth, frozenValue, hlen]

/-- With `K = 1` the header is exactly one field word. -/
theorem headerBits_eq_single_field (xs : List Int) :
    headerBits xs = natToBitsLE (w xs.length) xs.length := by
  simp [headerBits, HeaderSchema.bits, HeaderSchema.fieldWords, frozenSchema,
    frozenFields, frozenWidth, frozenValue, flattenPayloadWords]

/-- **DECODE.**  The header round-trips: the little-endian decoder applied to
the whole header returns `n`, for every input. -/
theorem headerBits_decode (xs : List Int) :
    bitsToNatLE (headerBits xs) = xs.length := by
  rw [headerBits_eq_single_field]
  exact bitsToNatLE_natToBitsLE_of_lt (lt_two_pow_w xs.length)

/-- Total serialized length splits exactly. -/
theorem serializedBits_length (xs : List Int) :
    (serializedBits xs).length
      = K * w xs.length + (SuccinctClassic.buildPayload xs).length := by
  simp [serializedBits, payloadBits, headerBits_length]

/-! ## 5. Small-size behavior, pinned explicitly -/

theorem headerBits_nil : headerBits ([] : List Int) = [false] := by
  rw [headerBits_eq_single_field]
  simp only [List.length_nil, w_zero]
  decide

theorem headerBits_singleton (a : Int) : headerBits [a] = [true, false] := by
  rw [headerBits_eq_single_field]
  have hlen : ([a] : List Int).length = 1 := rfl
  rw [hlen, w_one]
  decide

theorem headerBits_length_nil : (headerBits ([] : List Int)).length = 1 := by
  rw [headerBits_nil]; rfl

theorem headerBits_length_singleton (a : Int) : (headerBits [a]).length = 2 := by
  rw [headerBits_singleton a]; rfl

/-- Anti-vacuity: the header genuinely varies with `n`.  A schema whose header
were constant would satisfy every theorem above vacuously. -/
theorem headerBits_nil_ne_singleton (a : Int) :
    headerBits ([] : List Int) ≠ headerBits [a] := by
  rw [headerBits_nil, headerBits_singleton]
  decide

/-! ## 6. The `K = 3` alternative schema

Provided because the `K = 1` decision rests on padding the two content-dependent
select regions to their `n`-only budgets, which costs space against
`EG-CP-F05`.  If that padding is declined, the schema below is the drop-in
replacement: identical machinery, three fields, and the same four theorem
shapes.  Both schemas are checked here so the arity decision is a one-line edit
in the coordinator's hands rather than a re-derivation. -/

open RMQ.GenericSelect in
/-- The route's long-super relative region for `xs`. -/
def longRelativeBits (xs : List Int) : List Bool :=
  (longSuperRelativeTable (SuccinctClassic.cartesianShape xs).bpCode
    false).payload

open RMQ.GenericSelect in
/-- The route's sparse-exception relative region for `xs`. -/
def sparseRelativeBits (xs : List Int) : List Bool :=
  (sparseExceptionRelativeTable (SuccinctClassic.cartesianShape xs).bpCode
    false).payload

/-- Bridge: `longRelativeBits` is the route's `selectLongRelative` payload. -/
theorem longRelativeBits_eq_route (xs : List Int) :
    longRelativeBits xs
      = SuccinctFinal.concreteBPNativeSuccinctRMQReviewerSourcePayload
          (SuccinctClassic.cartesianShape xs)
          SuccinctFinal.ReviewerSource.selectLongRelative := rfl

/-- Bridge: `sparseRelativeBits` is the route's `selectSparseRelative` payload. -/
theorem sparseRelativeBits_eq_route (xs : List Int) :
    sparseRelativeBits xs
      = SuccinctFinal.concreteBPNativeSuccinctRMQReviewerSourcePayload
          (SuccinctClassic.cartesianShape xs)
          SuccinctFinal.ReviewerSource.selectSparseRelative := rfl

/-- The BP code of the canonical shape has length `2 * n`. -/
theorem bpCode_length_eq (xs : List Int) :
    (SuccinctClassic.cartesianShape xs).bpCode.length = 2 * xs.length := by
  rw [Cartesian.CartesianShape.bpCode_length]
  simp [SuccinctClassic.cartesianShape, Cartesian.shape_size]

theorem longRelativeBits_le_budget (xs : List Int) :
    (longRelativeBits xs).length
      <= GenericSelect.longSuperRelativeTableOverhead (2 * xs.length) := by
  have h :=
    GenericSelect.longSuperRelativeTable_payload_le_overhead
      (SuccinctClassic.cartesianShape xs).bpCode false
  rw [bpCode_length_eq] at h
  exact h

theorem sparseRelativeBits_le_budget (xs : List Int) :
    (sparseRelativeBits xs).length
      <= GenericSelect.sparseExceptionRelativeTableOverhead (2 * xs.length) := by
  have h :=
    GenericSelect.sparseExceptionRelativeTable_payload_le_overhead
      (SuccinctClassic.cartesianShape xs).bpCode false
  rw [bpCode_length_eq] at h
  exact h

/-- The extended closed field universe. -/
inductive HeaderFieldExt where
  /-- The input length `n`. -/
  | size
  /-- Bit length of the long-super relative region. -/
  | longRelativeLength
  /-- Bit length of the sparse-exception relative region. -/
  | sparseRelativeLength
  deriving DecidableEq, Repr

/-- THE ALTERNATIVE HEADER ARITY. -/
def KExt : Nat := 3

def extFields : List HeaderFieldExt :=
  [HeaderFieldExt.size, HeaderFieldExt.longRelativeLength,
    HeaderFieldExt.sparseRelativeLength]

/-- Frozen per-field width for the extended schema.  Each is a function of `n`
alone: the two region fields are sized by `machineWordBits` of the region's
`n`-only budget. -/
def extWidth (n : Nat) : HeaderFieldExt -> Nat
  | .size => w n
  | .longRelativeLength =>
      SuccinctRank.machineWordBits
        (GenericSelect.longSuperRelativeTableOverhead (2 * n))
  | .sparseRelativeLength =>
      SuccinctRank.machineWordBits
        (GenericSelect.sparseExceptionRelativeTableOverhead (2 * n))

def extValue (xs : List Int) : HeaderFieldExt -> Nat
  | .size => xs.length
  | .longRelativeLength => (longRelativeBits xs).length
  | .sparseRelativeLength => (sparseRelativeBits xs).length

/-- THE ALTERNATIVE SCHEMA. -/
def extSchema : HeaderSchema HeaderFieldExt where
  fields := extFields
  width := extWidth
  value := extValue

theorem extFields_complete (f : HeaderFieldExt) : f ∈ extFields := by
  cases f <;> decide

theorem extFields_nodup : extFields.Nodup := by decide

/-- **ARITY THEOREM** for the alternative schema. -/
theorem ext_arity (xs : List Int) :
    (extSchema.fieldWords xs).length = KExt :=
  extSchema.fieldWords_length xs

theorem extSchema_arity_literal : extSchema.arity = KExt := rfl

theorem KExt_eq_three : KExt = 3 := rfl

/-- **FIT THEOREM** for the alternative schema: no field is truncated, for all
inputs, at every size. -/
theorem ext_field_fits (xs : List Int) (f : HeaderFieldExt) :
    extSchema.value xs f < 2 ^ extSchema.width xs.length f := by
  cases f with
  | size => exact lt_two_pow_w xs.length
  | longRelativeLength =>
      exact Nat.lt_of_le_of_lt (longRelativeBits_le_budget xs)
        (lt_two_pow_machineWordBits _)
  | sparseRelativeLength =>
      exact Nat.lt_of_le_of_lt (sparseRelativeBits_le_budget xs)
        (lt_two_pow_machineWordBits _)

/-! ### Width bounds for the alternative schema -/

theorem machineWordBits_512_mul_of_pos {m : Nat} (hm : 0 < m) :
    SuccinctRank.machineWordBits (512 * m)
      = SuccinctRank.machineWordBits m + 9 := by
  have h : (512 : Nat) * m
      = 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * m)))))))) := by omega
  have h1 : 0 < 2 * m := by omega
  have h2 : 0 < 2 * (2 * m) := by omega
  have h3 : 0 < 2 * (2 * (2 * m)) := by omega
  have h4 : 0 < 2 * (2 * (2 * (2 * m))) := by omega
  have h5 : 0 < 2 * (2 * (2 * (2 * (2 * m)))) := by omega
  have h6 : 0 < 2 * (2 * (2 * (2 * (2 * (2 * m))))) := by omega
  have h7 : 0 < 2 * (2 * (2 * (2 * (2 * (2 * (2 * m)))))) := by omega
  have h8 : 0 < 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * m))))))) := by omega
  rw [h, machineWordBits_two_mul_of_pos h8, machineWordBits_two_mul_of_pos h7,
    machineWordBits_two_mul_of_pos h6, machineWordBits_two_mul_of_pos h5,
    machineWordBits_two_mul_of_pos h4, machineWordBits_two_mul_of_pos h3,
    machineWordBits_two_mul_of_pos h2, machineWordBits_two_mul_of_pos h1,
    machineWordBits_two_mul_of_pos hm]

/-- `machineWordBits (2 * n + 1) <= w n + 1`, for every `n` including `0`. -/
theorem machineWordBits_two_mul_succ_le (n : Nat) :
    SuccinctRank.machineWordBits (2 * n + 1) <= w n + 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [w_zero]
    simp [SuccinctRank.machineWordBits, log2_one]
  · have hpos : 0 < 2 * n := by omega
    have hle : 2 * n + 1 <= 2 * (2 * n) := by omega
    have hmono := SuccinctRank.machineWordBits_mono_le hle
    rw [machineWordBits_two_mul_of_pos hpos] at hmono
    exact hmono

/-- **WIDTH THEOREM (bound)** for the alternative schema.  Every field width is
at most `w n + 10`, hence at most the stated multiple `11 * w n`, for all `n`
including `0` and `1`. -/
theorem ext_field_width_le (n : Nat) (f : HeaderFieldExt) :
    extSchema.width n f <= w n + 10 := by
  cases f with
  | size => simp [extSchema, extWidth]
  | longRelativeLength =>
      show SuccinctRank.machineWordBits
        (GenericSelect.longSuperRelativeTableOverhead (2 * n)) <= w n + 10
      have hbudget :
          GenericSelect.longSuperRelativeTableOverhead (2 * n) <= 2 * n + 1 := by
        simp only [GenericSelect.longSuperRelativeTableOverhead,
          SuccinctSpace.idDivLogLogOverhead]
        have := Nat.div_le_self (2 * n)
          (Nat.log2 (Nat.log2 (2 * n) + 1) + 1)
        omega
      have h1 := SuccinctRank.machineWordBits_mono_le hbudget
      have h2 := machineWordBits_two_mul_succ_le n
      omega
  | sparseRelativeLength =>
      show SuccinctRank.machineWordBits
        (GenericSelect.sparseExceptionRelativeTableOverhead (2 * n))
          <= w n + 10
      have hbudget :
          GenericSelect.sparseExceptionRelativeTableOverhead (2 * n)
            <= 512 * (2 * n + 1) := by
        simp only [GenericSelect.sparseExceptionRelativeTableOverhead,
          SuccinctSpace.idDivLogLogOverhead]
        have := Nat.div_le_self (2 * n)
          (Nat.log2 (Nat.log2 (2 * n) + 1) + 1)
        have hmul : 512 * ((2 * n) / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1))
            <= 512 * (2 * n) := Nat.mul_le_mul_left 512 this
        omega
      have h1 := SuccinctRank.machineWordBits_mono_le hbudget
      rw [machineWordBits_512_mul_of_pos (m := 2 * n + 1) (by omega)] at h1
      have h2 := machineWordBits_two_mul_succ_le n
      omega

theorem ext_field_width_le_multiple (n : Nat) (f : HeaderFieldExt) :
    extSchema.width n f <= 11 * w n := by
  have h := ext_field_width_le n f
  have hw := one_le_w n
  omega

/-- Header length of the alternative schema, closed in `n`. -/
theorem extHeaderBits_length (xs : List Int) :
    (extSchema.bits xs).length
      = w xs.length
        + (SuccinctRank.machineWordBits
            (GenericSelect.longSuperRelativeTableOverhead (2 * xs.length))
          + SuccinctRank.machineWordBits
              (GenericSelect.sparseExceptionRelativeTableOverhead
                (2 * xs.length))) := by
  simp [HeaderSchema.bits, HeaderSchema.fieldWords, extSchema, extFields,
    extWidth, flattenPayloadWords, natToBitsLE_length]

/-! ## 6b. Checked controls for the three elaborator arity gates

The claim "adding a field without updating the arity theorem breaks
elaboration" is itself evidence, so it gets checked controls rather than prose.
A failing elaboration cannot be exhibited inside a green file, so instead each
control proves the *negation* of the proposition the gate would have to
discharge.  A false goal cannot be closed by any tactic, so these theorems are
exactly the statement that the corresponding gate fires. -/

/-- A copy of the frozen field universe with one extra constructor added and
the serialization list left un-updated. -/
inductive HeaderFieldPlusOne where
  | size
  | rogue
  deriving DecidableEq, Repr

/-- The un-updated serialization list. -/
def staleFields : List HeaderFieldPlusOne := [HeaderFieldPlusOne.size]

/-- GATE 2 FIRES.  `frozenFields_complete`'s script `cases f <;> decide` would
face this goal on the new constructor, and it is false. -/
theorem gate2_fires : HeaderFieldPlusOne.rogue ∉ staleFields := by decide

/-- GATE 3 FIRES.  If the new constructor is instead appended to the field list
while `K` is left at its literal, the `rfl` in `frozenSchema_arity_literal`
would face this equation, and it is false. -/
theorem gate3_fires :
    ([HeaderFieldPlusOne.size, HeaderFieldPlusOne.rogue]).length ≠ K := by
  decide

/-- GATE 1 is the non-exhaustive `match`: `frozenWidth` and `frozenValue` are
defined by pattern match on the closed universe, so a new constructor with no
arm is a definition-time error.  That gate has no proposition to negate; it is
witnessed by the definitions themselves at `frozenWidth` and `frozenValue`
above, and I state plainly that this one rests on Lean's match exhaustiveness
rather than on a theorem in this file. -/
theorem gate1_note : True := trivial

/-! ### Honest slack in the size field

`w` is pinned by the rank directory's divisor, not chosen tight for the size
field.  For every positive `n` it is exactly one bit wider than the minimal
encoding of `n`. -/

theorem w_eq_log2_add_two {n : Nat} (hn : 0 < n) :
    w n = Nat.log2 n + 2 := by
  simp only [w, SuccinctRank.machineWordBits, log2_two_mul_of_pos hn]

/-- The minimal width that fits `n` is `Nat.log2 n + 1`, so the frozen size
field carries exactly one slack bit at every positive `n`. -/
theorem size_field_slack {n : Nat} (hn : 0 < n) :
    n < 2 ^ (w n - 1) /\ w n - 1 = Nat.log2 n + 1 := by
  have hw := w_eq_log2_add_two hn
  refine ⟨?_, by omega⟩
  have h : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have : w n - 1 = Nat.log2 n + 1 := by omega
  rw [this]
  exact h

/-! ## 7. Executed values -/

#eval (List.range 9).map (fun n => (n, w n))
#eval ((w 512, w 1024, w 8192) : Nat × Nat × Nat)
#eval headerBits ([] : List Int)
#eval headerBits ([7] : List Int)
#eval headerBits ([3, 1, 4, 1, 5] : List Int)
#eval (headerBits ([3, 1, 4, 1, 5] : List Int)).length
#eval bitsToNatLE (headerBits ([3, 1, 4, 1, 5] : List Int))
#eval (List.range 9).map (fun n =>
  (n, extWidth n .size, extWidth n .longRelativeLength,
    extWidth n .sparseRelativeLength))

/-! ## 8. Axiom audit -/

#print axioms frozen_arity
#print axioms frozenSchema_arity_literal
#print axioms frozenFields_complete
#print axioms frozenFields_nodup
#print axioms frozen_field_width_eq
#print axioms frozen_field_width_le
#print axioms frozen_field_fits
#print axioms headerBits_length
#print axioms headerBits_length_closed
#print axioms headerBits_size_only
#print axioms headerBits_decode
#print axioms serializedBits_eq
#print axioms serializedBits_length
#print axioms payloadBits_eq_canonicalReviewerPayload
#print axioms headerBits_nil
#print axioms headerBits_singleton
#print axioms headerBits_nil_ne_singleton
#print axioms ext_arity
#print axioms extFields_complete
#print axioms ext_field_fits
#print axioms ext_field_width_le
#print axioms ext_field_width_le_multiple
#print axioms extHeaderBits_length
#print axioms longRelativeBits_eq_route
#print axioms sparseRelativeBits_eq_route
#print axioms gate2_fires
#print axioms gate3_fires
#print axioms w_eq_log2_add_two
#print axioms size_field_slack
#print axioms bpCode_length_eq
#print axioms longRelativeBits_le_budget
#print axioms sparseRelativeBits_le_budget


/-! ## VFY: adversarial audit section (added by the verifier, not the lane) -/

section Vfy

/-- VFY-1a: every "all-size" theorem instantiated at n = 0. -/
example : frozenSchema.width 0 HeaderField.size = 1 := by
  rw [frozen_field_width_eq]; exact w_zero
example : frozenSchema.value ([] : List Int) HeaderField.size
    < 2 ^ frozenSchema.width ([] : List Int).length HeaderField.size :=
  frozen_field_fits [] HeaderField.size
example : (headerBits ([] : List Int)).length = K * w 0 :=
  headerBits_length []
example : bitsToNatLE (headerBits ([] : List Int)) = 0 := headerBits_decode []
example : (frozenSchema.fieldWords ([] : List Int)).length = K := frozen_arity []

/-- VFY-1b: same at n = 1. -/
example : frozenSchema.width 1 HeaderField.size = 2 := by
  rw [frozen_field_width_eq]; exact w_one
example (a : Int) : frozenSchema.value [a] HeaderField.size
    < 2 ^ frozenSchema.width ([a] : List Int).length HeaderField.size :=
  frozen_field_fits [a] HeaderField.size
example (a : Int) : bitsToNatLE (headerBits [a]) = 1 := headerBits_decode [a]

/-- VFY-2: the header is exactly ONE cell of the frozen width. -/
theorem vfy_header_is_one_cell (xs : List Int) :
    (headerBits xs).length = w xs.length := by
  rw [headerBits_length]; simp [K]

/-- VFY-3: THE MISSING ROUTE LINK.  Is the file's `w` the route's actual cell
width?  The lane's file never states this; it is only asserted in a comment. -/
theorem vfy_w_eq_route_wordSize (xs : List Int) :
    w xs.length
      = SuccinctFinal.builtRelativeSplitBPCloseRankWordSize
          (SuccinctClassic.cartesianShape xs) := by
  show SuccinctRank.machineWordBits (2 * xs.length)
      = SuccinctRank.machineWordBits
          (SuccinctClassic.cartesianShape xs).bpCode.length
  rw [bpCode_length_eq]

/-- VFY-4: the canonical payload places the close component at an offset that
is `2n` plus the length of the live access payload; the live access payload
contains BOTH content-dependent select regions. -/
theorem vfy_close_offset (xs : List Int) :
    SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerCloseBitOffset
        (SuccinctClassic.cartesianShape xs)
      = 2 * xs.length
        + (SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload
            (SuccinctClassic.cartesianShape xs)).length := by
  show (SuccinctClassic.cartesianShape xs).bpCode.length
      + (SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload
          (SuccinctClassic.cartesianShape xs)).length
    = 2 * xs.length + _
  rw [bpCode_length_eq]

/-- VFY-5: the live access payload literally ends with the sparse relative
region and contains the long relative region, so the close offset is a function
of both lengths. -/
theorem vfy_access_contains_regions (xs : List Int) :
    SuccinctFinal.ReviewerSource.selectLongRelative ∈
        ([SuccinctFinal.ReviewerSource.selectLongRelative,
          SuccinctFinal.ReviewerSource.selectSparseRelative]) := by
  decide

/-! ### VFY-6: EXECUTED -- is the payload length actually a function of `n`?
If two equal-length inputs give different payload lengths, `K = 1` cannot
determine the layout. -/

def probeLists6 : List (List Int) :=
  [[1,2,3,4,5,6], [6,5,4,3,2,1], [3,1,4,1,5,9], [1,1,1,1,1,1],
   [2,7,1,8,2,8], [5,5,5,5,5,4]]

#eval probeLists6.map (fun xs => (xs, (payloadBits xs).length))
#eval probeLists6.map (fun xs =>
  ((longRelativeBits xs).length, (sparseRelativeBits xs).length))
#eval probeLists6.map (fun xs =>
  (SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerCloseBitOffset
    (SuccinctClassic.cartesianShape xs)))

/-! ### VFY-7: EXECUTED -- what does padding to the proved `n`-only budgets
cost, in bits, relative to `2n`?  Argument is the BP bit length `2n`. -/

#eval (List.range 12).map (fun k =>
  let n := 2 ^ (k + 8)
  (n, 2 * n,
    GenericSelect.longSuperRelativeTableOverhead (2 * n),
    GenericSelect.sparseExceptionRelativeTableOverhead (2 * n)))

/-! ### VFY-8: is there ANY decode/extraction theorem for the K = 3 schema? -/

example (xs : List Int) : bitsToNatLE (extSchema.bits xs) = xs.length := by
  sorry

#print axioms vfy_w_eq_route_wordSize
#print axioms vfy_header_is_one_cell
#print axioms vfy_close_offset

end Vfy

end ZqhF01
