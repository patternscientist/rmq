import RMQ.Core.Shape

/-!
# RMQ encoding lower-bound scaffolding

This module starts the information-theoretic side of the RMQ story.  The first
layer is deliberately finite and shape-level: any fixed-length bit encoding
that distinguishes all Cartesian shapes of size `n` must have at least
`shapeCount n` distinct codes available.

Later modules can connect this shape-distinguishability premise to exact RMQ
behavior and then combine it with Catalan lower bounds.
-/

namespace RMQ

namespace EncodingLowerBound

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
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
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
    {alpha beta : Type} [BEq beta] [LawfulBEq beta]
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

/--
A fixed-length bit encoding of all Cartesian shapes of size `n` that loses no
shape information.
-/
structure LosslessShapeEncoding (n bits : Nat) where
  encode : Cartesian.CartesianShape -> List Bool
  length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (encode shape).length = bits
  injective_on :
    forall {left right : Cartesian.CartesianShape},
      List.Mem left (Cartesian.shapesOfSize n) ->
        List.Mem right (Cartesian.shapesOfSize n) ->
          encode left = encode right -> left = right

/--
Capacity lower bound for fixed-length lossless Cartesian-shape encodings.

This is the finite pigeonhole step behind the RMQ space lower bound: if an
encoding distinguishes all `shapeCount n` Cartesian shapes using `bits` bits,
then `shapeCount n <= 2^bits`.
-/
theorem shapeCount_le_two_pow_of_lossless_shape_encoding
    {n bits : Nat} (encoding : LosslessShapeEncoding n bits) :
    Cartesian.shapeCount n <= 2 ^ bits := by
  have hle :
      (Cartesian.shapesOfSize n).length <= (bitStrings bits).length := by
    apply length_le_of_nodup_injective_into
    case hxs =>
      exact Cartesian.shapesOfSize_nodup n
    case hmem =>
      intro shape hshape
      have hlen := encoding.length_eq hshape
      exact mem_bitStrings_of_length hlen
    case hinj =>
      intro left hleft right hright hcode
      exact encoding.injective_on hleft hright hcode
  simpa [Cartesian.shapeCount, bitStrings_length] using hle

end EncodingLowerBound

end RMQ
