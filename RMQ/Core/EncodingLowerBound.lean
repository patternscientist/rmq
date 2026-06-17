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
A fixed-length shape encoding equipped with an RMQ query decoder.

The lower-bound reading is: `sample shape` is a representative input whose
Cartesian shape is exactly `shape`; `query` is the operation available after
seeing only the bitstring; and `query_exact` says this operation answers every
nonempty representative-array RMQ query exactly.
-/
structure ExactRMQShapeEncoding (n bits : Nat) where
  encode : Cartesian.CartesianShape -> List Bool
  query : List Bool -> Nat -> Nat -> Option Nat
  sample : Cartesian.CartesianShape -> List Int
  length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (encode shape).length = bits
  sample_length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (sample shape).length = n
  sample_shape_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        Cartesian.shape (sample shape) = shape
  query_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {left len : Nat},
          0 < len ->
            left + len <= n ->
              query (encode shape) left (left + len) =
                some (scanWindow (sample shape) left len)

theorem sameRMQBehavior_of_exactRMQShapeEncoding_eq
    {n bits : Nat} (encoding : ExactRMQShapeEncoding n bits)
    {leftShape rightShape : Cartesian.CartesianShape}
    (hleft : List.Mem leftShape (Cartesian.shapesOfSize n))
    (hright : List.Mem rightShape (Cartesian.shapesOfSize n))
    (hcode : encoding.encode leftShape = encoding.encode rightShape) :
    Cartesian.SameRMQBehavior
      (encoding.sample leftShape) (encoding.sample rightShape) := by
  constructor
  case left =>
    rw [encoding.sample_length_eq hleft, encoding.sample_length_eq hright]
  case right =>
    intro left len hlen hbound
    have hbound_n : left + len <= n := by
      simpa [encoding.sample_length_eq hleft] using hbound
    have hquery_left :
        encoding.query (encoding.encode leftShape) left (left + len) =
          some (scanWindow (encoding.sample leftShape) left len) :=
      encoding.query_exact hleft hlen hbound_n
    have hquery_right :
        encoding.query (encoding.encode rightShape) left (left + len) =
          some (scanWindow (encoding.sample rightShape) left len) :=
      encoding.query_exact hright hlen hbound_n
    rw [hcode] at hquery_left
    rw [hquery_right] at hquery_left
    injection hquery_left with hscan
    exact hscan.symm

/--
Exact RMQ behavior over representative arrays induces a lossless Cartesian-shape
encoding. This is the semantic bridge from a data-structure correctness
contract to the finite shape-count capacity argument.
-/
def losslessShapeEncoding_of_exactRMQShapeEncoding
    {n bits : Nat} (encoding : ExactRMQShapeEncoding n bits) :
    LosslessShapeEncoding n bits where
  encode := encoding.encode
  length_eq := encoding.length_eq
  injective_on := by
    intro leftShape rightShape hleft hright hcode
    have hbehavior :=
      sameRMQBehavior_of_exactRMQShapeEncoding_eq
        encoding hleft hright hcode
    have hshape :=
      Cartesian.shape_eq_of_sameRMQBehavior hbehavior
    rw [encoding.sample_shape_eq hleft,
      encoding.sample_shape_eq hright] at hshape
    exact hshape

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

/--
Capacity lower bound specialized to exact RMQ encodings. If a fixed-length
bitstring plus query decoder can answer every representative-array RMQ query
exactly for every Cartesian shape of size `n`, then the bit universe must hold
at least `shapeCount n` states.
-/
theorem shapeCount_le_two_pow_of_exactRMQShapeEncoding
    {n bits : Nat} (encoding : ExactRMQShapeEncoding n bits) :
    Cartesian.shapeCount n <= 2 ^ bits :=
  shapeCount_le_two_pow_of_lossless_shape_encoding
    (losslessShapeEncoding_of_exactRMQShapeEncoding encoding)

/--
Arithmetic bridge from a Catalan lower bound to a bit lower bound.

Once a separate Catalan theorem supplies `2 ^ lower <= shapeCount n`, the
finite capacity theorem forces every fixed-length lossless shape encoding to
use at least `lower` bits.
-/
theorem lower_le_bits_of_shapeCount_lower_bound
    {n bits lower : Nat} (encoding : LosslessShapeEncoding n bits)
    (hshape_lower : 2 ^ lower <= Cartesian.shapeCount n) :
    lower <= bits := by
  have hcapacity :
      Cartesian.shapeCount n <= 2 ^ bits :=
    shapeCount_le_two_pow_of_lossless_shape_encoding encoding
  have hpow : 2 ^ lower <= 2 ^ bits :=
    Nat.le_trans hshape_lower hcapacity
  exact
    (Nat.pow_le_pow_iff_right
      (a := 2) (n := lower) (m := bits) (by omega)).mp hpow

/--
The same Catalan-to-bits bridge specialized to exact RMQ encodings.
-/
theorem lower_le_bits_of_exactRMQShapeEncoding
    {n bits lower : Nat} (encoding : ExactRMQShapeEncoding n bits)
    (hshape_lower : 2 ^ lower <= Cartesian.shapeCount n) :
    lower <= bits :=
  lower_le_bits_of_shapeCount_lower_bound
    (losslessShapeEncoding_of_exactRMQShapeEncoding encoding)
    hshape_lower

/--
Final-form arithmetic scaffold for the standard RMQ lower-bound headline.

The remaining combinatorial theorem should instantiate `slack` with a
logarithmic function of `n`, proving
`2 ^ (2 * n - slack) <= shapeCount n`; this theorem then turns that Catalan
fact into the corresponding bit lower bound.
-/
theorem two_mul_sub_slack_le_bits_of_exactRMQShapeEncoding
    {n bits slack : Nat} (encoding : ExactRMQShapeEncoding n bits)
    (hshape_lower : 2 ^ (2 * n - slack) <= Cartesian.shapeCount n) :
    2 * n - slack <= bits :=
  lower_le_bits_of_exactRMQShapeEncoding encoding hshape_lower

end EncodingLowerBound

end RMQ
