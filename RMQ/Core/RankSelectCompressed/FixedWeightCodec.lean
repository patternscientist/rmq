import RMQ.Core.RankSelectSpec
import RMQ.Core.SuccinctSpace.WordStore

/-!
# Compressed/FID rank-select specification surface

This module adds the fixed-weight bitvector counting layer and the public
compressed rank/select theorem shape.  It is deliberately a spec/profile layer:
the fixed-weight codec and packed-payload spine live here, while the full
compressed/FID construction remains below this interface.
-/

namespace RMQ

namespace RankSelectSpec

/--
Mathlib-free binomial-count recurrence.

`binomialCount n k` counts the number of length-`n` bitvectors with exactly
`k` true bits.  It intentionally avoids depending on `Nat.choose`, which is not
part of the repository's Lean/Std footprint.
-/
def binomialCount : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => binomialCount n 0
  | n + 1, k + 1 => binomialCount n (k + 1) + binomialCount n k

/-- Bitvectors of length `n` with exactly `k` true bits. -/
def fixedWeightBitstrings : Nat -> Nat -> List (List Bool)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, 0 =>
      (fixedWeightBitstrings n 0).map fun bits => false :: bits
  | n + 1, k + 1 =>
      ((fixedWeightBitstrings n (k + 1)).map fun bits => false :: bits) ++
        ((fixedWeightBitstrings n k).map fun bits => true :: bits)

theorem fixedWeightBitstrings_length
    (n k : Nat) :
    (fixedWeightBitstrings n k).length = binomialCount n k := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [fixedWeightBitstrings, binomialCount]
  | succ n ih =>
      cases k with
      | zero =>
          simp [fixedWeightBitstrings, binomialCount, ih]
      | succ k =>
          simp [fixedWeightBitstrings, binomialCount, ih, Nat.add_comm]

@[simp] theorem binomialCount_zero_right (n : Nat) :
    binomialCount n 0 = 1 := by
  induction n with
  | zero =>
      simp [binomialCount]
  | succ n ih =>
      simp [binomialCount, ih]

/--
The fixed-weight universe is bounded by the full Boolean universe.

This deliberately stays with the local `binomialCount` recurrence rather than
importing `Nat.choose`.
-/
theorem binomialCount_le_two_pow (n k : Nat) :
    binomialCount n k <= 2 ^ n := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [binomialCount]
  | succ n ih =>
      cases k with
      | zero =>
          have hcount := ih 0
          have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          simp [binomialCount]
          have hpowPos : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
          omega
      | succ k =>
          have hfalse := ih (k + 1)
          have htrue := ih k
          have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          simp [binomialCount]
          omega

theorem binomialCount_le_add_left (extra n k : Nat) :
    binomialCount n k <= binomialCount (extra + n) k := by
  induction extra with
  | zero =>
      simp
  | succ extra ih =>
      cases k with
      | zero =>
          simp at ih ⊢
      | succ k =>
          have hstep :
              binomialCount (extra + n) (k + 1) <=
                binomialCount ((extra + n) + 1) (k + 1) := by
            simp [binomialCount]
          exact Nat.le_trans ih
            (by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                using hstep)

theorem binomialCount_mul_le_add (n1 k1 n2 k2 : Nat) :
    binomialCount n1 k1 * binomialCount n2 k2 <=
      binomialCount (n1 + n2) (k1 + k2) := by
  induction n1 generalizing k1 with
  | zero =>
      cases k1 with
      | zero =>
          simp [binomialCount]
      | succ k1 =>
          simp [binomialCount]
  | succ n1 ih =>
      cases k1 with
      | zero =>
          simp [binomialCount]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (binomialCount_le_add_left (extra := n1 + 1)
              (n := n2) (k := k2))
      | succ k1 =>
          have hfalse :
              binomialCount n1 (k1 + 1) * binomialCount n2 k2 <=
                binomialCount (n1 + n2) ((k1 + 1) + k2) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              ih (k1 + 1)
          have htrue :
              binomialCount n1 k1 * binomialCount n2 k2 <=
                binomialCount (n1 + n2) (k1 + k2) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              ih k1
          change
            (binomialCount n1 (k1 + 1) + binomialCount n1 k1) *
                binomialCount n2 k2 <=
              binomialCount ((n1 + 1) + n2) ((k1 + 1) + k2)
          rw [Nat.add_mul]
          have htarget :
              binomialCount ((n1 + 1) + n2) ((k1 + 1) + k2) =
                binomialCount (n1 + n2) ((k1 + 1) + k2) +
                  binomialCount (n1 + n2) (k1 + k2) := by
            simp [binomialCount, Nat.add_assoc, Nat.add_comm]
          rw [htarget]
          omega

/-- Number of true bits in a bitvector. -/
def trueCount (bits : List Bool) : Nat :=
  Succinct.rankPrefix true bits bits.length

@[simp] theorem trueCount_nil : trueCount [] = 0 := by
  rfl

@[simp] theorem trueCount_cons_false (bits : List Bool) :
    trueCount (false :: bits) = trueCount bits := by
  simp [trueCount, Succinct.rankPrefix]

@[simp] theorem trueCount_cons_true (bits : List Bool) :
    trueCount (true :: bits) = trueCount bits + 1 := by
  simp [trueCount, Succinct.rankPrefix, Nat.add_comm]

theorem trueCount_append (xs ys : List Bool) :
    trueCount (xs ++ ys) = trueCount xs + trueCount ys := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      cases x
      · simp [ih]
      · simp [ih, Nat.add_comm]
        omega

theorem trueCount_le_length (bits : List Bool) :
    trueCount bits <= bits.length := by
  induction bits with
  | nil =>
      simp
  | cons bit rest ih =>
      cases bit
      · simp
        omega
      · simp
        omega

theorem trueCount_lt_of_length_lt
    {bits : List Bool} {bound : Nat}
    (hlen : bits.length < bound) :
    trueCount bits < bound := by
  have hcount := trueCount_le_length bits
  omega

theorem binomialCount_pos_of_le {n k : Nat}
    (hk : k <= n) : 0 < binomialCount n k := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [binomialCount] at hk ⊢
  | succ n ih =>
      cases k with
      | zero =>
          simp [binomialCount]
      | succ k =>
          have hk' : k <= n := by omega
          have hpos := ih hk'
          simp [binomialCount]
          omega

theorem fixedWeightBitstrings_mem_length_trueCount
    {bits : List Bool} {n k : Nat}
    (hmem : List.Mem bits (fixedWeightBitstrings n k)) :
    bits.length = n /\ trueCount bits = k := by
  induction n generalizing bits k with
  | zero =>
      cases k with
      | zero =>
          cases hmem with
          | head =>
              simp
          | tail _ htail =>
              cases htail
      | succ k =>
          cases hmem
  | succ n ih =>
      cases k with
      | zero =>
          rcases List.mem_map.mp hmem with ⟨tail, htail, rfl⟩
          have htailFacts := ih htail
          simp [htailFacts.1, htailFacts.2]
      | succ k =>
          rcases List.mem_append.mp hmem with hmem | hmem
          · rcases List.mem_map.mp hmem with ⟨tail, htail, rfl⟩
            have htailFacts := ih htail
            simp [htailFacts.1, htailFacts.2]
          · rcases List.mem_map.mp hmem with ⟨tail, htail, rfl⟩
            have htailFacts := ih htail
            simp [htailFacts.1, htailFacts.2]

theorem fixedWeightBitstrings_mem_of_length_trueCount
    {bits : List Bool} {n k : Nat}
    (hlen : bits.length = n) (hcount : trueCount bits = k) :
    List.Mem bits (fixedWeightBitstrings n k) := by
  induction n generalizing bits k with
  | zero =>
      cases bits with
      | nil =>
          cases k with
          | zero =>
              exact List.Mem.head []
          | succ k =>
              simp at hcount
      | cons bit rest =>
          simp at hlen
  | succ n ih =>
      cases bits with
      | nil =>
          simp at hlen
      | cons bit rest =>
          have hrestLen : rest.length = n := by
            simp at hlen
            exact hlen
          cases bit
          case false =>
            cases k with
            | zero =>
                exact
                  List.mem_map.mpr
                    ⟨rest, ih hrestLen (by simpa using hcount), rfl⟩
            | succ k =>
                exact
                  List.mem_append.mpr
                    (Or.inl
                      (List.mem_map.mpr
                        ⟨rest, ih hrestLen (by simpa using hcount), rfl⟩))
          case true =>
            cases k with
            | zero =>
                simp at hcount
            | succ k =>
                have htailCount : trueCount rest = k := by
                  simpa using hcount
                exact
                  List.mem_append.mpr
                    (Or.inr
                      (List.mem_map.mpr
                        ⟨rest, ih hrestLen htailCount, rfl⟩))

theorem fixedWeightBitstrings_mem_iff
    {bits : List Bool} {n k : Nat} :
    List.Mem bits (fixedWeightBitstrings n k) <->
      bits.length = n /\ trueCount bits = k := by
  constructor
  · exact fixedWeightBitstrings_mem_length_trueCount
  · intro h
    exact fixedWeightBitstrings_mem_of_length_trueCount h.1 h.2

private theorem nodup_map_cons_bool
    (head : Bool) {xs : List (List Bool)}
    (hxs : xs.Nodup) :
    (xs.map (fun bits => head :: bits)).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      change ((head :: x) :: xs.map (fun bits => head :: bits)).Nodup
      rw [List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨tail, htail, htailEq⟩
        exact hxs.1 (by
          cases htailEq
          exact htail)
      · exact ih hxs.2

/-- The fixed-weight bitvector universe has no duplicate entries. -/
theorem fixedWeightBitstrings_nodup
    (n k : Nat) :
    (fixedWeightBitstrings n k).Nodup := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [fixedWeightBitstrings]
  | succ n ih =>
      cases k with
      | zero =>
          exact nodup_map_cons_bool false (ih 0)
      | succ k =>
          rw [fixedWeightBitstrings]
          rw [List.nodup_append]
          constructor
          · exact nodup_map_cons_bool false (ih (k + 1))
          · constructor
            · exact nodup_map_cons_bool true (ih k)
            · intro a ha b hb hab
              rw [List.mem_map] at ha
              rw [List.mem_map] at hb
              rcases ha with ⟨tailA, htailA, haEq⟩
              rcases hb with ⟨tailB, htailB, hbEq⟩
              subst a
              subst b
              cases haEq

/--
First index of a value in a list, local to the compressed rank/select codec
spine. This keeps the codec proofs independent of heavier downstream modules.
-/
def listIndexOf? {alpha : Type u} [DecidableEq alpha]
    (target : alpha) : List alpha -> Option Nat
  | [] => none
  | x :: xs =>
      if x = target then
        some 0
      else
        match listIndexOf? target xs with
        | none => none
        | some idx => some (idx + 1)

theorem listIndexOf?_lt_length
    {alpha : Type u} [DecidableEq alpha] {target : alpha} :
    forall {xs : List alpha} {idx : Nat},
      listIndexOf? target xs = some idx -> idx < xs.length
  | [], _, h => by
      simp [listIndexOf?] at h
  | x :: xs, idx, h => by
      unfold listIndexOf? at h
      by_cases hx : x = target
      · simp [hx] at h
        cases h
        simp
      · simp [hx] at h
        cases htail : listIndexOf? target xs with
        | none =>
            simp [htail] at h
        | some tailIdx =>
            simp [htail] at h
            have htail_lt :
                tailIdx < xs.length :=
              listIndexOf?_lt_length (target := target) htail
            cases h
            simp
            omega

theorem listIndexOf?_get?
    {alpha : Type u} [DecidableEq alpha] {target : alpha} :
    forall {xs : List alpha} {idx : Nat},
      listIndexOf? target xs = some idx -> xs[idx]? = some target
  | [], _, h => by
      simp [listIndexOf?] at h
  | x :: xs, idx, h => by
      unfold listIndexOf? at h
      by_cases hx : x = target
      · simp [hx] at h
        cases h
        simp [hx]
      · simp [hx] at h
        cases htail : listIndexOf? target xs with
        | none =>
            simp [htail] at h
        | some tailIdx =>
            simp [htail] at h
            cases h
            have hget :
                xs[tailIdx]? = some target :=
              listIndexOf?_get? (target := target) htail
            simpa using hget

theorem listIndexOf?_mem
    {alpha : Type u} [DecidableEq alpha] {target : alpha}
    {xs : List alpha} {idx : Nat}
    (h : listIndexOf? target xs = some idx) :
    target ∈ xs := by
  exact List.mem_of_getElem? (listIndexOf?_get? h)

theorem listIndexOf?_exists_of_mem
    {alpha : Type u} [DecidableEq alpha] {target : alpha} :
    forall {xs : List alpha},
      target ∈ xs -> exists idx, listIndexOf? target xs = some idx
  | [], hmem => by
      simp at hmem
  | x :: xs, hmem => by
      unfold listIndexOf?
      by_cases hx : x = target
      · exact ⟨0, by simp [hx]⟩
      · have htarget_x : target ≠ x := by
          intro htarget_x
          exact hx htarget_x.symm
        simp [hx, htarget_x] at hmem ⊢
        rcases listIndexOf?_exists_of_mem (target := target) hmem with
          ⟨idx, hidx⟩
        exact ⟨idx + 1, by simp [hidx]⟩

theorem listIndexOf?_eq_of_get?_nodup
    {alpha : Type u} [DecidableEq alpha] {target : alpha}
    {xs : List alpha} {idx : Nat}
    (hnodup : xs.Nodup)
    (hget : xs[idx]? = some target) :
    listIndexOf? target xs = some idx := by
  induction xs generalizing idx with
  | nil =>
      simp at hget
  | cons x xs ih =>
      unfold listIndexOf?
      by_cases hx : x = target
      · simp [hx]
        rw [List.nodup_cons] at hnodup
        cases idx with
        | zero =>
            rfl
        | succ idx =>
            simp [hx] at hget
            have hmemTarget : target ∈ xs :=
              List.mem_of_getElem? hget
            have hmemX : x ∈ xs := by
              simpa [hx] using hmemTarget
            exact False.elim (hnodup.1 hmemX)
      · simp [hx]
        cases idx with
        | zero =>
            simp [hx] at hget
        | succ idx =>
            rw [List.nodup_cons] at hnodup
            have htail :
                listIndexOf? target xs = some idx :=
              ih hnodup.2 (by simpa using hget)
            simp [htail]

/--
Canonical fixed-weight encoder: the first index of `bits` in the finite
fixed-weight universe for its own length and true-count.
-/
def fixedWeightEncode? (bits : List Bool) : Option Nat :=
  listIndexOf? bits (fixedWeightBitstrings bits.length (trueCount bits))

/-- Canonical fixed-weight decoder by indexing the counted universe. -/
def fixedWeightDecode? (n k code : Nat) : Option (List Bool) :=
  (fixedWeightBitstrings n k)[code]?

theorem fixedWeightEncode?_exists (bits : List Bool) :
    exists code, fixedWeightEncode? bits = some code := by
  unfold fixedWeightEncode?
  exact
    listIndexOf?_exists_of_mem
      (target := bits)
      (fixedWeightBitstrings_mem_of_length_trueCount rfl rfl)

theorem fixedWeightEncode?_lt_binomialCount
    {bits : List Bool} {code : Nat}
    (henc : fixedWeightEncode? bits = some code) :
    code < binomialCount bits.length (trueCount bits) := by
  have hlt :
      code <
        (fixedWeightBitstrings bits.length (trueCount bits)).length := by
    exact listIndexOf?_lt_length henc
  simpa [fixedWeightBitstrings_length] using hlt

/-- Total canonical code for a bitvector in its own fixed-weight universe. -/
def fixedWeightCode (bits : List Bool) : Nat :=
  (fixedWeightEncode? bits).getD 0

theorem fixedWeightEncode?_eq_some_fixedWeightCode
    (bits : List Bool) :
    fixedWeightEncode? bits = some (fixedWeightCode bits) := by
  rcases fixedWeightEncode?_exists bits with ⟨code, hcode⟩
  simp [fixedWeightCode, hcode]

theorem fixedWeightCode_lt_binomialCount
    (bits : List Bool) :
    fixedWeightCode bits <
      binomialCount bits.length (trueCount bits) := by
  exact fixedWeightEncode?_lt_binomialCount
    (fixedWeightEncode?_eq_some_fixedWeightCode bits)

theorem fixedWeightDecode?_fixedWeightEncode?
    {bits : List Bool} {code : Nat}
    (henc : fixedWeightEncode? bits = some code) :
    fixedWeightDecode? bits.length (trueCount bits) code = some bits := by
  exact listIndexOf?_get? henc

theorem fixedWeightDecode?_mem_length_trueCount
    {n k code : Nat} {bits : List Bool}
    (hdec : fixedWeightDecode? n k code = some bits) :
    bits.length = n /\ trueCount bits = k := by
  unfold fixedWeightDecode? at hdec
  have hmem : List.Mem bits (fixedWeightBitstrings n k) :=
    List.mem_of_getElem? hdec
  exact fixedWeightBitstrings_mem_length_trueCount hmem

theorem fixedWeightEncode?_fixedWeightDecode?
    {n k code : Nat} {bits : List Bool}
    (hdec : fixedWeightDecode? n k code = some bits) :
    fixedWeightEncode? bits = some code := by
  unfold fixedWeightDecode? at hdec
  have hfacts := fixedWeightBitstrings_mem_length_trueCount
    (List.mem_of_getElem? hdec)
  unfold fixedWeightEncode?
  rw [hfacts.1, hfacts.2]
  exact listIndexOf?_eq_of_get?_nodup
    (fixedWeightBitstrings_nodup n k) hdec

theorem fixedWeightDecode?_eq_some_iff
    {n k code : Nat} {bits : List Bool} :
    fixedWeightDecode? n k code = some bits <->
      bits.length = n /\ trueCount bits = k /\
        fixedWeightEncode? bits = some code := by
  constructor
  · intro hdec
    have hfacts := fixedWeightDecode?_mem_length_trueCount hdec
    exact ⟨hfacts.1, hfacts.2,
      fixedWeightEncode?_fixedWeightDecode? hdec⟩
  · intro h
    have hdec :=
      fixedWeightDecode?_fixedWeightEncode? h.2.2
    simpa [h.1, h.2.1] using hdec

theorem fixedWeightCodec_roundTrip
    (bits : List Bool) :
    exists code,
      fixedWeightEncode? bits = some code /\
        fixedWeightDecode? bits.length (trueCount bits) code = some bits /\
        code < binomialCount bits.length (trueCount bits) := by
  rcases fixedWeightEncode?_exists bits with ⟨code, henc⟩
  exact
    ⟨code, henc, fixedWeightDecode?_fixedWeightEncode? henc,
      fixedWeightEncode?_lt_binomialCount henc⟩

/--
The information-theoretic fixed-weight payload budget used by the compressed
rank/select profile.  The `+ 1` is the usual whole-number ceiling slack for a
binary code over `binomialCount n m` states.
-/
def fixedWeightPayloadBudget (bits : List Bool) : Nat :=
  Nat.log2 (binomialCount bits.length (trueCount bits)) + 1

private theorem log2_le_of_lt_pow_succ {n k : Nat}
    (hlt : n < 2 ^ (k + 1)) :
    Nat.log2 n <= k := by
  by_cases hzero : n = 0
  · simp [hzero]
  · by_cases hle : Nat.log2 n <= k
    · exact hle
    · have hk : k + 1 <= Nat.log2 n := by omega
      have hmono : 2 ^ (k + 1) <= 2 ^ Nat.log2 n :=
        Nat.pow_le_pow_right (by omega : 0 < 2) hk
      have hself : 2 ^ Nat.log2 n <= n := Nat.log2_self_le hzero
      exact False.elim
        (Nat.not_lt_of_ge (Nat.le_trans hmono hself) hlt)

theorem log2_add_le_log2_mul_le {a b c : Nat}
    (ha : 0 < a) (hb : 0 < b) (hle : a * b <= c) :
    Nat.log2 a + Nat.log2 b <= Nat.log2 c := by
  have hpowA : 2 ^ Nat.log2 a <= a :=
    Nat.log2_self_le (by omega)
  have hpowB : 2 ^ Nat.log2 b <= b :=
    Nat.log2_self_le (by omega)
  have hpowMul :
      2 ^ (Nat.log2 a + Nat.log2 b) <= a * b := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul hpowA hpowB
  have hc : c ≠ 0 := by
    intro hzero
    subst c
    have hprod : 0 < a * b := Nat.mul_pos ha hb
    omega
  exact (Nat.le_log2 hc).2 (Nat.le_trans hpowMul hle)

theorem fixedWeightPayloadBudget_le_length_add_one
    (bits : List Bool) :
    fixedWeightPayloadBudget bits <= bits.length + 1 := by
  unfold fixedWeightPayloadBudget
  have hbin :
      binomialCount bits.length (trueCount bits) <=
        2 ^ bits.length :=
    binomialCount_le_two_pow bits.length (trueCount bits)
  have hpow_lt : 2 ^ bits.length < 2 ^ (bits.length + 1) := by
    rw [Nat.pow_succ]
    have hpos : 0 < 2 ^ bits.length :=
      Nat.pow_pos (by omega : 0 < 2)
    omega
  have hcount_lt :
      binomialCount bits.length (trueCount bits) <
        2 ^ (bits.length + 1) :=
    Nat.lt_of_le_of_lt hbin hpow_lt
  have hlog :
      Nat.log2 (binomialCount bits.length (trueCount bits)) <=
        bits.length :=
    log2_le_of_lt_pow_succ hcount_lt
  omega

theorem fixedWeightEncode?_lt_payloadBudgetPow
    {bits : List Bool} {code : Nat}
    (henc : fixedWeightEncode? bits = some code) :
    code < 2 ^ fixedWeightPayloadBudget bits := by
  have hcode :
      code < binomialCount bits.length (trueCount bits) :=
    fixedWeightEncode?_lt_binomialCount henc
  have hcount :
      binomialCount bits.length (trueCount bits) <
        2 ^ (Nat.log2 (binomialCount bits.length (trueCount bits)) + 1) :=
    Nat.lt_log2_self
  exact Nat.lt_trans hcode (by simpa [fixedWeightPayloadBudget] using hcount)

theorem fixedWeightCode_lt_payloadBudgetPow
    (bits : List Bool) :
    fixedWeightCode bits < 2 ^ fixedWeightPayloadBudget bits := by
  exact fixedWeightEncode?_lt_payloadBudgetPow
    (fixedWeightEncode?_eq_some_fixedWeightCode bits)

/--
Packed fixed-weight payload for one bitvector.

This is the concrete bit-level realization of the canonical fixed-weight code:
store `fixedWeightCode bits` in exactly `fixedWeightPayloadBudget bits`
little-endian bits.
-/
def fixedWeightPackedPayload (bits : List Bool) : List Bool :=
  SuccinctSpace.natToBitsLE
    (fixedWeightPayloadBudget bits) (fixedWeightCode bits)

@[simp] theorem fixedWeightPackedPayload_length
    (bits : List Bool) :
    (fixedWeightPackedPayload bits).length =
      fixedWeightPayloadBudget bits := by
  simp [fixedWeightPackedPayload, SuccinctSpace.natToBitsLE_length]

theorem fixedWeightPackedPayload_bitsToNatLE
    (bits : List Bool) :
    SuccinctSpace.bitsToNatLE (fixedWeightPackedPayload bits) =
      fixedWeightCode bits := by
  simpa [fixedWeightPackedPayload] using
    SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt
      (fixedWeightCode_lt_payloadBudgetPow bits)

theorem fixedWeightDecode?_packedPayload
    (bits : List Bool) :
    fixedWeightDecode? bits.length (trueCount bits)
        (SuccinctSpace.bitsToNatLE (fixedWeightPackedPayload bits)) =
      some bits := by
  rw [fixedWeightPackedPayload_bitsToNatLE]
  exact
    fixedWeightDecode?_fixedWeightEncode?
      (fixedWeightEncode?_eq_some_fixedWeightCode bits)

theorem fixedWeightPackedPayload_profile
    (bits : List Bool) :
    (fixedWeightPackedPayload bits).length =
        fixedWeightPayloadBudget bits /\
      SuccinctSpace.bitsToNatLE (fixedWeightPackedPayload bits) =
        fixedWeightCode bits /\
      fixedWeightDecode? bits.length (trueCount bits)
          (SuccinctSpace.bitsToNatLE (fixedWeightPackedPayload bits)) =
        some bits := by
  exact
    ⟨fixedWeightPackedPayload_length bits,
      fixedWeightPackedPayload_bitsToNatLE bits,
      fixedWeightDecode?_packedPayload bits⟩


end RankSelectSpec

end RMQ
