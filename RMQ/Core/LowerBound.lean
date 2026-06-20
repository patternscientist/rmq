/-!
# Generic finite encoding lower-bound helpers

This module is the hub-facing part of the information-theoretic story.  It
does not mention RMQ, Cartesian trees, or shapes.  It only packages:

* fixed-length bitstring universes,
* a finite-domain lossless encoding interface,
* the finite injection/capacity counting step, and
* the arithmetic bridge from a count lower bound to a bit lower bound.
-/

namespace RMQ

namespace LowerBound

/-- All bitstrings of length `n`. -/
def bitStrings : Nat -> List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitStrings n).flatMap fun bits =>
      [false :: bits, true :: bits]

private theorem sum_map_const_nat {alpha : Type} (xs : List alpha) (n : Nat) :
    ((xs.map fun _ => n).sum) = xs.length * n := by
  simp [List.map_const']

theorem bitStrings_length (n : Nat) :
    (bitStrings n).length = 2 ^ n := by
  induction n with
  | zero =>
      simp [bitStrings]
  | succ n ih =>
      simp [bitStrings, List.length_flatMap, sum_map_const_nat]
      rw [ih, Nat.pow_succ]

theorem mem_bitStrings_of_length
    {bits : List Bool} {n : Nat} (hlen : bits.length = n) :
    List.Mem bits (bitStrings n) := by
  induction n generalizing bits with
  | zero =>
      cases bits with
      | nil =>
          exact List.Mem.head []
      | cons _ _ =>
          simp at hlen
  | succ n ih =>
      cases bits with
      | nil =>
          simp at hlen
      | cons b bits =>
          have htail : bits.length = n := by
            simp at hlen
            exact hlen
          have hmem := ih htail
          cases b
          case false =>
            exact List.mem_flatMap.mpr
              (Exists.intro bits
                (And.intro hmem (List.Mem.head _)))
          case true =>
            exact List.mem_flatMap.mpr
              (Exists.intro bits
                (And.intro hmem
                  (List.Mem.tail _ (List.Mem.head _))))

private theorem mem_erase_of_ne_of_mem
    {alpha : Type u} [BEq alpha] [LawfulBEq alpha]
    {a b : alpha} {xs : List alpha}
    (hne : Not (a = b)) (hmem : List.Mem a xs) :
    List.Mem a (xs.erase b) := by
  induction xs with
  | nil =>
      cases hmem
  | cons x xs ih =>
      by_cases hxb : x = b
      case pos =>
        subst x
        rw [List.erase_cons_head]
        have hmem' := List.mem_cons.mp hmem
        rcases hmem' with hmem | hmem
        case inl =>
          exact False.elim (hne hmem)
        case inr =>
          exact hmem
      case neg =>
        have hbeq : Not ((x == b) = true) := by
          intro h
          apply hxb
          exact eq_of_beq h
        rw [List.erase_cons_tail hbeq]
        have hmem' := List.mem_cons.mp hmem
        apply List.mem_cons.mpr
        rcases hmem' with hmem | hmem
        case inl =>
          exact Or.inl hmem
        case inr =>
          exact Or.inr (ih hmem)

theorem length_le_of_nodup_injective_into
    {alpha : Type u} {beta : Type v} [BEq beta] [LawfulBEq beta]
    (xs : List alpha) (ys : List beta) (f : alpha -> beta)
    (hxs : xs.Nodup)
    (hmem : forall x, List.Mem x xs -> List.Mem (f x) ys)
    (hinj :
      forall x, List.Mem x xs ->
        forall y, List.Mem y xs -> f x = f y -> x = y) :
    xs.length <= ys.length := by
  induction xs generalizing ys with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      have hxmem : List.Mem (f x) ys := hmem x (List.Mem.head xs)
      have htail :
          xs.length <= (ys.erase (f x)).length := by
        apply ih
        case hxs =>
          exact hxs.2
        case hmem =>
          intro y hy
          have hymem : List.Mem (f y) ys :=
            hmem y (List.Mem.tail x hy)
          have hne : Not (f y = f x) := by
            intro hEq
            have hyx : y = x :=
              hinj y (List.Mem.tail x hy) x (List.Mem.head xs) hEq
            rw [hyx] at hy
            exact hxs.1 hy
          exact mem_erase_of_ne_of_mem hne hymem
        case hinj =>
          intro y hy z hz hEq
          exact hinj y (List.Mem.tail x hy) z (List.Mem.tail x hz) hEq
      have herase_len := List.length_erase_of_mem hxmem
      have hys_pos : 0 < ys.length := by
        cases ys with
        | nil =>
            cases hxmem
        | cons _ _ =>
            simp
      rw [herase_len] at htail
      change xs.length + 1 <= ys.length
      omega

/-- A fixed-length bit encoding of a finite domain that loses no information. -/
structure LosslessEncoding (domain : List alpha) (bits : Nat) where
  encode : alpha -> List Bool
  length_eq :
    forall {x : alpha}, List.Mem x domain -> (encode x).length = bits
  injective_on :
    forall {left right : alpha},
      List.Mem left domain ->
        List.Mem right domain -> encode left = encode right -> left = right

/-- Capacity bound for fixed-length lossless encodings of a finite domain. -/
theorem domain_length_le_two_pow_of_lossless_encoding
    {domain : List alpha} {bits : Nat}
    (encoding : LosslessEncoding domain bits)
    (hnodup : domain.Nodup) :
    domain.length <= 2 ^ bits := by
  have hle : domain.length <= (bitStrings bits).length := by
    apply length_le_of_nodup_injective_into
    case hxs =>
      exact hnodup
    case hmem =>
      intro x hx
      exact mem_bitStrings_of_length (encoding.length_eq hx)
    case hinj =>
      intro left hleft right hright hcode
      exact encoding.injective_on hleft hright hcode
  simpa [bitStrings_length] using hle

/--
If a domain of size `count` injects into `bits` bits, and a separate counting
argument proves at least `2^lower` distinct states, then `bits >= lower`.
-/
theorem lower_le_bits_of_count_lower_bound
    {count bits lower : Nat}
    (hcapacity : count <= 2 ^ bits)
    (hcount_lower : 2 ^ lower <= count) :
    lower <= bits := by
  have hpow : 2 ^ lower <= 2 ^ bits :=
    Nat.le_trans hcount_lower hcapacity
  exact
    (Nat.pow_le_pow_iff_right
      (a := 2) (n := lower) (m := bits) (by omega)).mp hpow

/--
The square of the odd width `2*n+1` fits in a logarithmic power-of-two budget.
This is the arithmetic slack used by quadratic Catalan-style lower bounds.
-/
theorem odd_square_le_two_pow_log_slack (n : Nat) :
    (2 * n + 1) * (2 * n + 1) <=
      2 ^ (2 * Nat.log2 (2 * n + 1) + 2) := by
  let width := 2 * n + 1
  have hlt : width < 2 ^ (Nat.log2 width + 1) :=
    Nat.lt_log2_self (n := width)
  have hle : width <= 2 ^ (Nat.log2 width + 1) :=
    Nat.le_of_lt hlt
  have hsquare :
      width * width <=
        2 ^ (Nat.log2 width + 1) * 2 ^ (Nat.log2 width + 1) :=
    Nat.mul_le_mul hle hle
  have hpow :
      2 ^ (Nat.log2 width + 1) * 2 ^ (Nat.log2 width + 1) =
        2 ^ (2 * Nat.log2 width + 2) := by
    rw [<- Nat.pow_add]
    congr 1
    omega
  simpa [width, hpow] using hsquare

theorem two_pow_sub_le_of_le_mul_pow
    {total slack count : Nat}
    (hbound : 2 ^ total <= 2 ^ slack * count) :
    2 ^ (total - slack) <= count := by
  by_cases hslack : slack <= total
  case pos =>
    let lower := total - slack
    have hsum : slack + lower = total := by
      unfold lower
      omega
    have hleft : 2 ^ slack * 2 ^ lower = 2 ^ total := by
      rw [<- Nat.pow_add, hsum]
    have hmul : 2 ^ slack * 2 ^ lower <= 2 ^ slack * count := by
      simpa [hleft] using hbound
    exact
      Nat.le_of_mul_le_mul_left hmul
        (Nat.pow_pos (by omega : 0 < 2))
  case neg =>
    have hzero : total - slack = 0 := by
      omega
    rw [hzero]
    have hcount_pos : 0 < count := by
      cases count with
      | zero =>
          have hpos : 0 < 2 ^ total :=
            Nat.pow_pos (by omega : 0 < 2)
          have hle_zero : 2 ^ total <= 0 := by
            exact hbound
          omega
      | succ _ =>
          omega
    exact hcount_pos

/--
Turn a quadratic count lower bound into the logarithmic exponent form used by
succinct RMQ-style lower bounds.
-/
theorem count_log_lower_of_quadratic_bound
    {n count : Nat}
    (hquad :
      2 ^ (2 * n) <=
        ((2 * n + 1) * (2 * n + 1)) * count) :
    2 ^ (2 * n - (2 * Nat.log2 (2 * n + 1) + 2)) <= count := by
  let slack := 2 * Nat.log2 (2 * n + 1) + 2
  have hodd :
      (2 * n + 1) * (2 * n + 1) <= 2 ^ slack := by
    simpa [slack] using odd_square_le_two_pow_log_slack n
  have hbound :
      2 ^ (2 * n) <= 2 ^ slack * count :=
    Nat.le_trans hquad (Nat.mul_le_mul_right count hodd)
  simpa [slack] using
    two_pow_sub_le_of_le_mul_pow
      (total := 2 * n)
      (slack := slack)
      (count := count)
      hbound

end LowerBound

end RMQ
