import RMQ.Core.Shape
import RMQ.Core.TableModel
import RMQ.Core.LowerBound
import RMQ.Core.PayloadLowerBound

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

/-- Compatibility wrapper for the generic fixed-length bitstring universe. -/
abbrev bitStrings : Nat -> List (List Bool) :=
  LowerBound.bitStrings

private theorem sum_map_const_nat {alpha : Type} (xs : List alpha) (n : Nat) :
    ((xs.map fun _ => n).sum) = xs.length * n := by
  simp [List.map_const']

theorem bitStrings_length (n : Nat) :
    (bitStrings n).length = 2 ^ n := by
  exact LowerBound.bitStrings_length n

theorem mem_bitStrings_of_length
    {bits : List Bool} {n : Nat} (hlen : bits.length = n) :
    List.Mem bits (bitStrings n) := by
  exact LowerBound.mem_bitStrings_of_length hlen

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
    {alpha : Type u} {beta : Type v} [BEq beta] [LawfulBEq beta]
    (xs : List alpha) (ys : List beta) (f : alpha -> beta)
    (hxs : xs.Nodup)
    (hmem : forall x, List.Mem x xs -> List.Mem (f x) ys)
    (hinj :
      forall x, List.Mem x xs ->
        forall y, List.Mem y xs -> f x = f y -> x = y) :
    xs.length <= ys.length := by
  exact LowerBound.length_le_of_nodup_injective_into
    xs ys f hxs hmem hinj

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

/--
State-oriented version of `ExactRMQShapeEncoding`.

This is the lower-bound adapter intended for concrete data structures: build a
state from each representative shape, encode that state into exactly `bits`
payload bits, and answer RMQ queries using only the payload.
-/
structure ExactRMQStateEncoding (n bits : Nat) where
  State : Type
  buildState : Cartesian.CartesianShape -> State
  encodeState : State -> List Bool
  queryEncoded : List Bool -> Nat -> Nat -> Option Nat
  sample : Cartesian.CartesianShape -> List Int
  length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (encodeState (buildState shape)).length = bits
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
              queryEncoded (encodeState (buildState shape)) left (left + len) =
                some (scanWindow (sample shape) left len)

/-- Forget the concrete built state and view a state encoding as a shape encoding. -/
def exactRMQShapeEncoding_of_stateEncoding
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits) :
    ExactRMQShapeEncoding n bits where
  encode shape := encoding.encodeState (encoding.buildState shape)
  query := encoding.queryEncoded
  sample := encoding.sample
  length_eq := encoding.length_eq
  sample_length_eq := encoding.sample_length_eq
  sample_shape_eq := encoding.sample_shape_eq
  query_exact := encoding.query_exact

/-- Payload used by the canonical representative state encoding. -/
def canonicalShapePayload
    (shape : Cartesian.CartesianShape) : List Bool :=
  shape.fullCode.tail

/--
Recover the full explicit shape code from a fixed-size payload. For size zero
the only shape is empty, whose full code is `[false]`; for positive sizes the
payload is the tail of a nonempty `true :: ...` full code.
-/
def fullCodeOfPayload (n : Nat) (payload : List Bool) : List Bool :=
  if n = 0 then [false] else true :: payload

/-- Decode a canonical fixed-size shape payload. -/
def decodeShapePayload? (n : Nat) (payload : List Bool) :
    Option Cartesian.CartesianShape :=
  Cartesian.CartesianShape.decodeFullCode? (fullCodeOfPayload n payload)

theorem fullCodeOfPayload_canonicalShapePayload
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : Cartesian.ShapeOfSize n shape) :
    fullCodeOfPayload n (canonicalShapePayload shape) = shape.fullCode := by
  cases hshape with
  | empty =>
      simp [fullCodeOfPayload, Cartesian.CartesianShape.fullCode]
  | node hleft hright =>
      simp [fullCodeOfPayload, canonicalShapePayload,
        Cartesian.CartesianShape.fullCode]

theorem decodeShapePayload?_canonicalShapePayload
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : Cartesian.ShapeOfSize n shape) :
    decodeShapePayload? n (canonicalShapePayload shape) = some shape := by
  unfold decodeShapePayload?
  rw [fullCodeOfPayload_canonicalShapePayload hshape]
  exact Cartesian.CartesianShape.decodeFullCode?_fullCode shape

/-- Query decoder for the canonical representative state encoding. -/
def canonicalRepresentativeStateQuery
    (n : Nat) (payload : List Bool) (left right : Nat) : Option Nat :=
  match decodeShapePayload? n payload with
  | some shape =>
      some (scanWindow shape.representative left (right - left))
  | none => none

/--
Concrete baseline `ExactRMQStateEncoding` instance.

It stores the explicit Cartesian shape payload (`fullCode.tail`) and answers
queries by decoding that payload and scanning the canonical representative
array. This is not a succinct upper bound; it is the first concrete state
encoding that exercises the lower-bound adapter end to end.
-/
def canonicalRepresentativeStateEncoding
    (n : Nat) : ExactRMQStateEncoding n (2 * n) where
  State := Cartesian.CartesianShape
  buildState shape := shape
  encodeState shape := canonicalShapePayload shape
  queryEncoded := canonicalRepresentativeStateQuery n
  sample shape := shape.representative
  length_eq := by
    intro shape hmem
    exact Cartesian.CartesianShape.fullCode_tail_length_of_shapeOfSize
      (Cartesian.mem_shapesOfSize_shapeOfSize hmem)
  sample_length_eq := by
    intro shape hmem
    have hshape := Cartesian.mem_shapesOfSize_shapeOfSize hmem
    rw [Cartesian.CartesianShape.representative_length,
      Cartesian.ShapeOfSize.size_eq hshape]
  sample_shape_eq := by
    intro shape _hmem
    exact Cartesian.CartesianShape.shape_representative shape
  query_exact := by
    intro shape hmem left len _hlen _hbound
    have hshape := Cartesian.mem_shapesOfSize_shapeOfSize hmem
    have hdecode :=
      decodeShapePayload?_canonicalShapePayload hshape
    have hsub : left + len - left = len := by omega
    simp [canonicalRepresentativeStateQuery, hdecode, hsub]

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

namespace ExactRMQStateEncoding

/-- The counted payload produced by building a state for a representative shape. -/
def payloadOf
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits)
    (shape : Cartesian.CartesianShape) : List Bool :=
  encoding.encodeState (encoding.buildState shape)

/-- View a state encoding's concrete states through their serialized payload bits. -/
def payloadView
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits) :
    TableModel.PayloadView encoding.State :=
  TableModel.PayloadView.exact encoding.encodeState

theorem payloadOf_length_eq
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (encoding.payloadOf shape).length = bits := by
  exact encoding.length_eq hshape

theorem sameRMQBehavior_of_payload_eq
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits)
    {leftShape rightShape : Cartesian.CartesianShape}
    (hleft : List.Mem leftShape (Cartesian.shapesOfSize n))
    (hright : List.Mem rightShape (Cartesian.shapesOfSize n))
    (hpayload :
      encoding.payloadOf leftShape = encoding.payloadOf rightShape) :
    Cartesian.SameRMQBehavior
      (encoding.sample leftShape) (encoding.sample rightShape) := by
  exact sameRMQBehavior_of_exactRMQShapeEncoding_eq
    (exactRMQShapeEncoding_of_stateEncoding encoding)
    hleft hright hpayload

theorem shape_eq_of_payload_eq
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits)
    {leftShape rightShape : Cartesian.CartesianShape}
    (hleft : List.Mem leftShape (Cartesian.shapesOfSize n))
    (hright : List.Mem rightShape (Cartesian.shapesOfSize n))
    (hpayload :
      encoding.payloadOf leftShape = encoding.payloadOf rightShape) :
    leftShape = rightShape := by
  have hbehavior :=
    encoding.sameRMQBehavior_of_payload_eq hleft hright hpayload
  have hshape :=
    Cartesian.shape_eq_of_sameRMQBehavior hbehavior
  rw [encoding.sample_shape_eq hleft,
    encoding.sample_shape_eq hright] at hshape
  exact hshape

/--
Payload-accounted lossless shape encoding induced by an exact RMQ state
encoding.

This is the generic hub-facing view: the encoded finite domain is recovered
from the payload bits of the built state, while the RMQ-specific theorem above
proves those payload bits are injective over Cartesian shapes.
-/
def payloadLosslessEncoding
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits) :
    LowerBound.PayloadLosslessEncoding (Cartesian.shapesOfSize n) bits where
  State := encoding.State
  buildState := encoding.buildState
  payloadView := encoding.payloadView
  length_eq := by
    intro shape hshape
    simpa [payloadView, payloadOf] using
      encoding.payloadOf_length_eq hshape
  injective_on := by
    intro leftShape rightShape hleft hright hpayload
    have hpayload' :
        encoding.payloadOf leftShape =
          encoding.payloadOf rightShape := by
      simpa [payloadView, payloadOf] using hpayload
    exact
      encoding.shape_eq_of_payload_eq hleft hright hpayload'

theorem payloadLosslessEncoding_toLosslessEncoding_encode
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits)
    (shape : Cartesian.CartesianShape) :
    ((encoding.payloadLosslessEncoding).toLosslessEncoding).encode shape =
      encoding.payloadOf shape := by
  rfl

theorem payloadBitCount_ge_bits_of_mem
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    bits <=
      (encoding.payloadView).payloadBitCount
        (encoding.buildState shape) := by
  exact
    LowerBound.PayloadLosslessEncoding.payloadBitCount_ge_bits_of_mem
      encoding.payloadLosslessEncoding hshape

theorem payloadBitCount_eq_bits_of_mem
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (encoding.payloadView).payloadBitCount
        (encoding.buildState shape) = bits := by
  simpa [payloadView, payloadOf] using
    encoding.payloadOf_length_eq hshape

/--
Add proof-only or auxiliary data to a state encoding without changing the
counted payload bits or the payload-only query decoder.
-/
def withUnchargedAux
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits)
    (aux : encoding.State -> Type)
    (mkAux :
      forall shape : Cartesian.CartesianShape,
        aux (encoding.buildState shape)) :
    ExactRMQStateEncoding n bits where
  State := Sigma aux
  buildState shape := ⟨encoding.buildState shape, mkAux shape⟩
  encodeState state := encoding.encodeState state.1
  queryEncoded := encoding.queryEncoded
  sample := encoding.sample
  length_eq := by
    intro shape hshape
    exact encoding.length_eq hshape
  sample_length_eq := encoding.sample_length_eq
  sample_shape_eq := encoding.sample_shape_eq
  query_exact := by
    intro shape hshape left len hlen hbound
    exact encoding.query_exact hshape hlen hbound

@[simp] theorem payloadOf_withUnchargedAux
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits)
    (aux : encoding.State -> Type)
    (mkAux :
      forall shape : Cartesian.CartesianShape,
        aux (encoding.buildState shape))
    (shape : Cartesian.CartesianShape) :
    (encoding.withUnchargedAux aux mkAux).payloadOf shape =
      encoding.payloadOf shape := by
  rfl

end ExactRMQStateEncoding

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

/-- Direct lossless shape encoding induced by a state encoding's payload view. -/
def losslessShapeEncoding_of_exactRMQStateEncoding
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits) :
    LosslessShapeEncoding n bits :=
  losslessShapeEncoding_of_exactRMQShapeEncoding
    (exactRMQShapeEncoding_of_stateEncoding encoding)

/--
Capacity lower bound for fixed-length lossless Cartesian-shape encodings.

This is the finite pigeonhole step behind the RMQ space lower bound: if an
encoding distinguishes all `shapeCount n` Cartesian shapes using `bits` bits,
then `shapeCount n <= 2^bits`.
-/
theorem shapeCount_le_two_pow_of_lossless_shape_encoding
    {n bits : Nat} (encoding : LosslessShapeEncoding n bits) :
    Cartesian.shapeCount n <= 2 ^ bits := by
  let generic :
      LowerBound.LosslessEncoding (Cartesian.shapesOfSize n) bits :=
    {
    encode := encoding.encode
    length_eq := encoding.length_eq
    injective_on := encoding.injective_on
    }
  have hcapacity :=
    LowerBound.domain_length_le_two_pow_of_lossless_encoding
      generic (Cartesian.shapesOfSize_nodup n)
  simpa [Cartesian.shapeCount] using hcapacity

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
  exact
    LowerBound.lower_le_bits_of_count_lower_bound
      hcapacity hshape_lower

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

private def rightSpine : Nat -> Cartesian.CartesianShape
  | 0 => Cartesian.CartesianShape.empty
  | n + 1 =>
      Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
        (rightSpine n)

private theorem rightSpine_shapeOfSize (n : Nat) :
    Cartesian.ShapeOfSize n (rightSpine n) := by
  induction n with
  | zero =>
      simp [rightSpine]
      exact Cartesian.ShapeOfSize.empty
  | succ n ih =>
      simpa [rightSpine, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Cartesian.ShapeOfSize.node
          (leftSize := 0)
          (rightSize := n)
          Cartesian.ShapeOfSize.empty ih)

theorem shapeCount_pos (n : Nat) :
    0 < Cartesian.shapeCount n := by
  unfold Cartesian.shapeCount
  exact
    List.length_pos_of_mem
      (Cartesian.shapeOfSize_mem_shapesOfSize (rightSpine_shapeOfSize n))

private theorem shapeOfSize_size (shape : Cartesian.CartesianShape) :
    Cartesian.ShapeOfSize shape.size shape := by
  induction shape with
  | empty =>
      simp [Cartesian.CartesianShape.size]
      exact Cartesian.ShapeOfSize.empty
  | node left right ihleft ihright =>
      simpa [Cartesian.CartesianShape.size] using
        Cartesian.ShapeOfSize.node ihleft ihright

/--
The square of the odd width `2*n+1` fits in a logarithmic power-of-two budget.
This is the arithmetic slack used by the quadratic Catalan lower-bound target.
-/
theorem odd_square_le_two_pow_log_slack (n : Nat) :
    (2 * n + 1) * (2 * n + 1) <=
      2 ^ (2 * Nat.log2 (2 * n + 1) + 2) := by
  exact LowerBound.odd_square_le_two_pow_log_slack n

private theorem two_pow_sub_le_of_le_mul_pow
    {total slack count : Nat}
    (hbound : 2 ^ total <= 2 ^ slack * count) :
    2 ^ (total - slack) <= count := by
  exact LowerBound.two_pow_sub_le_of_le_mul_pow hbound

private def remyPositions : Cartesian.CartesianShape -> List (List Bool)
  | Cartesian.CartesianShape.empty => [[]]
  | Cartesian.CartesianShape.node left right =>
      [] ::
        ((remyPositions left).map fun path => false :: path) ++
          ((remyPositions right).map fun path => true :: path)

private def remyLeaves : Cartesian.CartesianShape -> List (List Bool)
  | Cartesian.CartesianShape.empty => [[]]
  | Cartesian.CartesianShape.node left right =>
      ((remyLeaves left).map fun path => false :: path) ++
        ((remyLeaves right).map fun path => true :: path)

private theorem remyPositions_length (shape : Cartesian.CartesianShape) :
    (remyPositions shape).length = 2 * shape.size + 1 := by
  induction shape with
  | empty =>
      simp [remyPositions, Cartesian.CartesianShape.size]
  | node left right ihleft ihright =>
      simp [remyPositions, Cartesian.CartesianShape.size, ihleft, ihright]
      omega

private theorem remyLeaves_length (shape : Cartesian.CartesianShape) :
    (remyLeaves shape).length = shape.size + 1 := by
  induction shape with
  | empty =>
      simp [remyLeaves, Cartesian.CartesianShape.size]
  | node left right ihleft ihright =>
      simp [remyLeaves, Cartesian.CartesianShape.size, ihleft, ihright]
      omega

private def remyInsert
    (shape : Cartesian.CartesianShape) (path : List Bool) (oldOnLeft : Bool) :
    Cartesian.CartesianShape :=
  match shape, path with
  | shape, [] =>
      if oldOnLeft then
        Cartesian.CartesianShape.node shape Cartesian.CartesianShape.empty
      else
        Cartesian.CartesianShape.node Cartesian.CartesianShape.empty shape
  | Cartesian.CartesianShape.empty, _ :: _ =>
      Cartesian.CartesianShape.empty
  | Cartesian.CartesianShape.node left right, false :: rest =>
      Cartesian.CartesianShape.node (remyInsert left rest oldOnLeft) right
  | Cartesian.CartesianShape.node left right, true :: rest =>
      Cartesian.CartesianShape.node left (remyInsert right rest oldOnLeft)

private def remyNewLeafPath (path : List Bool) (oldOnLeft : Bool) : List Bool :=
  match path with
  | [] => if oldOnLeft then [true] else [false]
  | step :: rest => step :: remyNewLeafPath rest oldOnLeft

private def remyRemoveMarkedLeaf :
    Cartesian.CartesianShape -> List Bool ->
      Option (Prod Cartesian.CartesianShape (Prod (List Bool) Bool))
  | Cartesian.CartesianShape.node old Cartesian.CartesianShape.empty, [true] =>
      some (old, [], true)
  | Cartesian.CartesianShape.node Cartesian.CartesianShape.empty old, [false] =>
      some (old, [], false)
  | Cartesian.CartesianShape.node left right, false :: rest =>
      match remyRemoveMarkedLeaf left rest with
      | some (old, path, oldOnLeft) =>
          some (Cartesian.CartesianShape.node old right,
            false :: path, oldOnLeft)
      | none => none
  | Cartesian.CartesianShape.node left right, true :: rest =>
      match remyRemoveMarkedLeaf right rest with
      | some (old, path, oldOnLeft) =>
          some (Cartesian.CartesianShape.node left old,
            true :: path, oldOnLeft)
      | none => none
  | _, _ => none

private theorem remyInsert_size
    (shape : Cartesian.CartesianShape) {path : List Bool} {oldOnLeft : Bool}
    (hpath : List.Mem path (remyPositions shape)) :
    (remyInsert shape path oldOnLeft).size = shape.size + 1 := by
  induction shape generalizing path with
  | empty =>
      cases hpath with
      | head =>
          cases oldOnLeft <;>
            simp [remyInsert, Cartesian.CartesianShape.size]
      | tail _ htail =>
          cases htail
  | node left right ihleft ihright =>
      cases hpath with
      | head =>
        cases oldOnLeft <;>
          simp [remyInsert, Cartesian.CartesianShape.size] <;> omega
      | tail _ hrest =>
        have hrestOr := List.mem_append.mp hrest
        cases hrestOr with
        | inl hleft =>
            have hleftMap := List.mem_map.mp hleft
            cases hleftMap with
            | intro leftPath hleftRest =>
                cases hleftRest with
                | intro hleftPath hpathEq =>
                    cases hpathEq
                    have hsize := ihleft hleftPath
                    cases oldOnLeft <;>
                      simp [remyInsert, Cartesian.CartesianShape.size, hsize] <;> omega
        | inr hright =>
            have hrightMap := List.mem_map.mp hright
            cases hrightMap with
            | intro rightPath hrightRest =>
                cases hrightRest with
                | intro hrightPath hpathEq =>
                    cases hpathEq
                    have hsize := ihright hrightPath
                    cases oldOnLeft <;>
                      simp [remyInsert, Cartesian.CartesianShape.size, hsize] <;> omega

private theorem remyNewLeaf_mem
    (shape : Cartesian.CartesianShape) {path : List Bool} {oldOnLeft : Bool}
    (hpath : List.Mem path (remyPositions shape)) :
    List.Mem (remyNewLeafPath path oldOnLeft)
      (remyLeaves (remyInsert shape path oldOnLeft)) := by
  induction shape generalizing path with
  | empty =>
      cases hpath with
      | head =>
        cases oldOnLeft
        case false =>
          exact List.Mem.head _
        case true =>
          exact List.Mem.tail _ (List.Mem.head _)
      | tail _ htail =>
          cases htail
  | node left right ihleft ihright =>
      cases hpath with
      | head =>
        cases oldOnLeft
        case false =>
          exact List.Mem.head _
        case true =>
          simp [remyInsert, remyNewLeafPath, remyLeaves]
          exact List.mem_append.mpr
            (Or.inr (List.mem_append.mpr
              (Or.inr (List.Mem.head []))))
      | tail _ hrest =>
        have hrestOr := List.mem_append.mp hrest
        cases hrestOr with
        | inl hleft =>
            have hleftMap := List.mem_map.mp hleft
            cases hleftMap with
            | intro leftPath hleftRest =>
                cases hleftRest with
                | intro hleftPath hpathEq =>
                    cases hpathEq
                    have hmem := ihleft hleftPath
                    exact List.mem_append.mpr
                      (Or.inl (List.mem_map.mpr
                        (Exists.intro (remyNewLeafPath leftPath oldOnLeft)
                          (And.intro hmem rfl))))
        | inr hright =>
            have hrightMap := List.mem_map.mp hright
            cases hrightMap with
            | intro rightPath hrightRest =>
                cases hrightRest with
                | intro hrightPath hpathEq =>
                    cases hpathEq
                    have hmem := ihright hrightPath
                    exact List.mem_append.mpr
                      (Or.inr (List.mem_map.mpr
                        (Exists.intro (remyNewLeafPath rightPath oldOnLeft)
                          (And.intro hmem rfl))))

private theorem remyRemoveMarkedLeaf_insert
    (shape : Cartesian.CartesianShape) {path : List Bool} {oldOnLeft : Bool}
    (hpath : List.Mem path (remyPositions shape)) :
    remyRemoveMarkedLeaf
        (remyInsert shape path oldOnLeft)
        (remyNewLeafPath path oldOnLeft) =
      some (shape, path, oldOnLeft) := by
  induction shape generalizing path with
  | empty =>
      cases hpath with
      | head =>
          cases oldOnLeft <;>
            simp [remyInsert, remyNewLeafPath, remyRemoveMarkedLeaf]
      | tail _ htail =>
          cases htail
  | node left right ihleft ihright =>
      cases hpath with
      | head =>
        cases oldOnLeft <;>
          simp [remyInsert, remyNewLeafPath, remyRemoveMarkedLeaf]
      | tail _ hrest =>
        have hrestOr := List.mem_append.mp hrest
        cases hrestOr with
        | inl hleft =>
            have hleftMap := List.mem_map.mp hleft
            cases hleftMap with
            | intro leftPath hleftRest =>
                cases hleftRest with
                | intro hleftPath hpathEq =>
                    cases hpathEq
                    have hremove := ihleft hleftPath
                    cases leftPath with
                    | nil =>
                        cases oldOnLeft <;>
                          simp [remyInsert, remyNewLeafPath, remyRemoveMarkedLeaf]
                            at hremove <;>
                          simp [remyInsert, remyNewLeafPath, remyRemoveMarkedLeaf] <;>
                          try rw [hremove]
                    | cons step rest =>
                        cases step <;> cases oldOnLeft <;>
                          simp [remyNewLeafPath]
                            at hremove <;>
                          simp [remyInsert, remyNewLeafPath, remyRemoveMarkedLeaf] <;>
                          try rw [hremove]
        | inr hright =>
            have hrightMap := List.mem_map.mp hright
            cases hrightMap with
            | intro rightPath hrightRest =>
                cases hrightRest with
                | intro hrightPath hpathEq =>
                    cases hpathEq
                    have hremove := ihright hrightPath
                    cases rightPath with
                    | nil =>
                        cases oldOnLeft <;>
                          simp [remyInsert, remyNewLeafPath, remyRemoveMarkedLeaf]
                            at hremove <;>
                          simp [remyInsert, remyNewLeafPath, remyRemoveMarkedLeaf] <;>
                          try rw [hremove]
                    | cons step rest =>
                        cases step <;> cases oldOnLeft <;>
                          simp [remyNewLeafPath]
                            at hremove <;>
                          simp [remyInsert, remyNewLeafPath, remyRemoveMarkedLeaf] <;>
                          try rw [hremove]

private theorem nodup_map_injective
    {alpha beta : Type} {xs : List alpha} {f : alpha -> beta}
    (hxs : xs.Nodup)
    (hinj :
      forall {x y : alpha},
        List.Mem x xs -> List.Mem y xs -> f x = f y -> x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      change (f x :: xs.map f).Nodup
      rw [List.nodup_cons]
      constructor
      case left =>
        intro hmem
        rw [List.mem_map] at hmem
        cases hmem with
        | intro y hrest =>
        cases hrest with
        | intro hy hxy =>
        have hyx : y = x :=
          hinj (List.Mem.tail x hy) (List.Mem.head xs) hxy
        exact hxs.1 (by simpa [hyx] using hy)
      case right =>
        apply ih hxs.2
        intro y z hy hz hyz
        exact hinj (List.Mem.tail x hy) (List.Mem.tail x hz) hyz

private theorem nodup_flatMap_of_nodup_disjoint
    {alpha beta : Type} {xs : List alpha} {f : alpha -> List beta}
    (hxs : xs.Nodup)
    (hnodup : forall x, List.Mem x xs -> (f x).Nodup)
    (hdisjoint :
      forall x, List.Mem x xs ->
        forall y, List.Mem y xs -> Not (x = y) ->
          forall a, List.Mem a (f x) ->
            forall b, List.Mem b (f y) -> Not (a = b)) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      simp [List.flatMap]
      rw [List.nodup_append]
      constructor
      case left =>
        exact hnodup x (List.Mem.head xs)
      case right =>
      constructor
      case left =>
        apply ih
        case hxs =>
          exact hxs.2
        case hnodup =>
          intro y hy
          exact hnodup y (List.Mem.tail x hy)
        case hdisjoint =>
          intro y hy z hz hyz a ha b hb
          exact hdisjoint y (List.Mem.tail x hy) z (List.Mem.tail x hz)
            hyz a ha b hb
      case right =>
        intro a ha b hb hab
        change List.Mem b (xs.flatMap f) at hb
        have hbFlat := List.mem_flatMap.mp hb
        cases hbFlat with
        | intro y hrest =>
        cases hrest with
        | intro hy hb =>
        exact hdisjoint x (List.Mem.head xs) y (List.Mem.tail x hy)
          (by
            intro hxy
            subst y
            exact hxs.1 hy)
          a ha b hb hab

private theorem remyPositions_nodup
    (shape : Cartesian.CartesianShape) :
    (remyPositions shape).Nodup := by
  induction shape with
  | empty =>
      simp [remyPositions]
  | node left right ihleft ihright =>
      simp [remyPositions]
      rw [List.nodup_append]
      constructor
      case left =>
        apply nodup_map_injective ihleft
        intro x y hx hy hEq
        injection hEq
      case right =>
        constructor
        case left =>
          apply nodup_map_injective ihright
          intro x y hx hy hEq
          injection hEq
        case right =>
          intro a ha b hb hEq
          have haMap := List.mem_map.mp ha
          have hbMap := List.mem_map.mp hb
          cases haMap with
          | intro leftPath hleftRest =>
          cases hleftRest with
          | intro _hleft haEq =>
          cases hbMap with
          | intro rightPath hrightRest =>
          cases hrightRest with
          | intro _hright hbEq =>
              subst a
              subst b
              cases haEq

private structure RemyInput where
  shape : Cartesian.CartesianShape
  path : List Bool
  oldOnLeft : Bool
deriving DecidableEq

private def remyInputFiber
    (shape : Cartesian.CartesianShape) : List RemyInput :=
  (remyPositions shape).flatMap fun path =>
    [{ shape := shape, path := path, oldOnLeft := false },
      { shape := shape, path := path, oldOnLeft := true }]

private def remyInputList (n : Nat) : List RemyInput :=
  (Cartesian.shapesOfSize n).flatMap remyInputFiber

private def markedLeafCodes (n : Nat) : List (Prod (List Bool) (List Bool)) :=
  (Cartesian.shapesOfSize n).flatMap fun shape =>
    (remyLeaves shape).map fun leaf => (shape.fullCode, leaf)

private theorem sum_map_eq_const_nat
    {alpha : Type} (xs : List alpha) (f : alpha -> Nat) (c : Nat)
    (hconst : forall x, List.Mem x xs -> f x = c) :
    (xs.map f).sum = xs.length * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp
      rw [hconst x (List.Mem.head xs)]
      have htail :
          (List.map f xs).sum = xs.length * c := by
        apply ih
        intro y hy
        exact hconst y (List.Mem.tail x hy)
      rw [htail]
      rw [Nat.succ_mul]
      exact Nat.add_comm c (xs.length * c)

private theorem remyInputFiber_length
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (remyInputFiber shape).length = (2 * n + 1) * 2 := by
  unfold remyInputFiber
  rw [List.length_flatMap]
  have hsum :
      ((remyPositions shape).map
        (fun path =>
          ([{ shape := shape, path := path, oldOnLeft := false },
            { shape := shape, path := path, oldOnLeft := true }] :
            List RemyInput).length)).sum =
        (remyPositions shape).length * 2 := by
    apply sum_map_eq_const_nat
    intro path _hpath
    simp
  rw [hsum, remyPositions_length]
  have hsize :=
    Cartesian.ShapeOfSize.size_eq
      (Cartesian.mem_shapesOfSize_shapeOfSize hshape)
  rw [hsize]

private theorem remyInputList_length (n : Nat) :
    (remyInputList n).length =
      Cartesian.shapeCount n * ((2 * n + 1) * 2) := by
  unfold remyInputList
  rw [List.length_flatMap]
  have hsum :
      ((Cartesian.shapesOfSize n).map
        (fun shape => (remyInputFiber shape).length)).sum =
        (Cartesian.shapesOfSize n).length * ((2 * n + 1) * 2) := by
    apply sum_map_eq_const_nat
    intro shape hshape
    exact remyInputFiber_length hshape
  simpa [Cartesian.shapeCount] using hsum

private theorem markedLeafCodes_length (n : Nat) :
    (markedLeafCodes n).length =
      Cartesian.shapeCount n * (n + 1) := by
  unfold markedLeafCodes
  rw [List.length_flatMap]
  have hsum :
      ((Cartesian.shapesOfSize n).map
        (fun shape => ((remyLeaves shape).map
          fun leaf => (shape.fullCode, leaf)).length)).sum =
        (Cartesian.shapesOfSize n).length * (n + 1) := by
    apply sum_map_eq_const_nat
    intro shape hshape
    rw [List.length_map, remyLeaves_length]
    have hsize :=
      Cartesian.ShapeOfSize.size_eq
        (Cartesian.mem_shapesOfSize_shapeOfSize hshape)
    rw [hsize]
  simpa [Cartesian.shapeCount] using hsum

private def remyEncodeInput (input : RemyInput) :
    Prod (List Bool) (List Bool) :=
  let inserted := remyInsert input.shape input.path input.oldOnLeft
  (inserted.fullCode, remyNewLeafPath input.path input.oldOnLeft)

private theorem remyInputPair_nodup
    (shape : Cartesian.CartesianShape) (path : List Bool) :
    ([{ shape := shape, path := path, oldOnLeft := false },
      { shape := shape, path := path, oldOnLeft := true }] :
      List RemyInput).Nodup := by
  simp

private theorem remyInputPair_mem_path
    {shape : Cartesian.CartesianShape} {path : List Bool}
    {input : RemyInput}
    (hmem :
      List.Mem input
        ([{ shape := shape, path := path, oldOnLeft := false },
          { shape := shape, path := path, oldOnLeft := true }] :
          List RemyInput)) :
    input.path = path := by
  cases hmem with
  | head =>
      rfl
  | tail _ htail =>
      cases htail with
      | head =>
          rfl
      | tail _ hnil =>
          cases hnil

private theorem remyInputFiber_mem_shape
    {shape : Cartesian.CartesianShape} {input : RemyInput}
    (hmem : List.Mem input (remyInputFiber shape)) :
    input.shape = shape := by
  unfold remyInputFiber at hmem
  have hflat := List.mem_flatMap.mp hmem
  cases hflat with
  | intro path hrest =>
      cases hrest with
      | intro _hpath hpair =>
          simp at hpair
          cases hpair with
          | inl hinput =>
              rw [hinput]
          | inr hinput =>
              rw [hinput]

private theorem remyInputFiber_mem_path
    {shape : Cartesian.CartesianShape} {input : RemyInput}
    (hmem : List.Mem input (remyInputFiber shape)) :
    List.Mem input.path (remyPositions shape) := by
  unfold remyInputFiber at hmem
  have hflat := List.mem_flatMap.mp hmem
  cases hflat with
  | intro path hrest =>
      cases hrest with
      | intro hpath hpair =>
          have hinputPath := remyInputPair_mem_path hpair
          rw [hinputPath]
          exact hpath

private theorem remyInputFiber_nodup
    (shape : Cartesian.CartesianShape) :
    (remyInputFiber shape).Nodup := by
  unfold remyInputFiber
  apply nodup_flatMap_of_nodup_disjoint
  case hxs =>
    exact remyPositions_nodup shape
  case hnodup =>
    intro path _hpath
    exact remyInputPair_nodup shape path
  case hdisjoint =>
    intro leftPath _hleftPath rightPath _hrightPath hne a ha b hb hab
    have haPath := remyInputPair_mem_path ha
    have hbPath := remyInputPair_mem_path hb
    have hpathEq : leftPath = rightPath := by
      rw [<- haPath, <- hbPath]
      exact congrArg RemyInput.path hab
    exact hne hpathEq

private theorem remyInputList_nodup (n : Nat) :
    (remyInputList n).Nodup := by
  unfold remyInputList
  apply nodup_flatMap_of_nodup_disjoint
  case hxs =>
    exact Cartesian.shapesOfSize_nodup n
  case hnodup =>
    intro shape _hshape
    exact remyInputFiber_nodup shape
  case hdisjoint =>
    intro leftShape _hleft rightShape _hright hne a ha b hb hab
    have haShape := remyInputFiber_mem_shape ha
    have hbShape := remyInputFiber_mem_shape hb
    have hshapeEq : leftShape = rightShape := by
      rw [<- haShape, <- hbShape]
      exact congrArg RemyInput.shape hab
    exact hne hshapeEq

private theorem remyInputList_mem_shape
    {n : Nat} {input : RemyInput}
    (hmem : List.Mem input (remyInputList n)) :
    List.Mem input.shape (Cartesian.shapesOfSize n) := by
  unfold remyInputList at hmem
  have hflat := List.mem_flatMap.mp hmem
  cases hflat with
  | intro shape hrest =>
      cases hrest with
      | intro hshape hinput =>
          have hshapeEq := remyInputFiber_mem_shape hinput
          rw [hshapeEq]
          exact hshape

private theorem remyInputList_mem_path
    {n : Nat} {input : RemyInput}
    (hmem : List.Mem input (remyInputList n)) :
    List.Mem input.path (remyPositions input.shape) := by
  unfold remyInputList at hmem
  have hflat := List.mem_flatMap.mp hmem
  cases hflat with
  | intro shape hrest =>
      cases hrest with
      | intro _hshape hinput =>
          have hshapeEq := remyInputFiber_mem_shape hinput
          have hpath := remyInputFiber_mem_path hinput
          simpa [hshapeEq] using hpath

private theorem remyEncodeInput_mem_markedLeafCodes
    {n : Nat} {input : RemyInput}
    (hmem : List.Mem input (remyInputList n)) :
    List.Mem (remyEncodeInput input) (markedLeafCodes (n + 1)) := by
  unfold markedLeafCodes
  have hshapeMem := remyInputList_mem_shape hmem
  have hpathMem := remyInputList_mem_path hmem
  let inserted := remyInsert input.shape input.path input.oldOnLeft
  have hinsertShape :
      List.Mem inserted (Cartesian.shapesOfSize (n + 1)) := by
    apply Cartesian.shapeOfSize_mem_shapesOfSize
    have hinsertSize :
        inserted.size = input.shape.size + 1 := by
      simpa [inserted] using
        remyInsert_size input.shape hpathMem
    have hshapeSize :
        input.shape.size = n := by
      exact Cartesian.ShapeOfSize.size_eq
        (Cartesian.mem_shapesOfSize_shapeOfSize hshapeMem)
    simpa [inserted, hinsertSize, hshapeSize] using
      shapeOfSize_size inserted
  have hleaf :
      List.Mem (remyNewLeafPath input.path input.oldOnLeft)
        (remyLeaves inserted) := by
    simpa [inserted] using
      remyNewLeaf_mem input.shape hpathMem
  apply List.mem_flatMap.mpr
  exact Exists.intro inserted
    (And.intro hinsertShape
      (List.mem_map.mpr
        (Exists.intro (remyNewLeafPath input.path input.oldOnLeft)
          (And.intro hleaf (by
            unfold remyEncodeInput
            simp [inserted])))))

private theorem remyEncodeInput_injective_on
    {n : Nat} {left right : RemyInput}
    (hleft : List.Mem left (remyInputList n))
    (hright : List.Mem right (remyInputList n))
    (hcode : remyEncodeInput left = remyEncodeInput right) :
    left = right := by
  have hleftPath := remyInputList_mem_path hleft
  have hrightPath := remyInputList_mem_path hright
  have hfirst :
      (remyInsert left.shape left.path left.oldOnLeft).fullCode =
        (remyInsert right.shape right.path right.oldOnLeft).fullCode := by
    simpa [remyEncodeInput] using congrArg Prod.fst hcode
  have hleaf :
      remyNewLeafPath left.path left.oldOnLeft =
        remyNewLeafPath right.path right.oldOnLeft := by
    simpa [remyEncodeInput] using congrArg Prod.snd hcode
  have hinsert :
      remyInsert left.shape left.path left.oldOnLeft =
        remyInsert right.shape right.path right.oldOnLeft :=
    Cartesian.CartesianShape.fullCode_injective hfirst
  have hremoveLeft :=
    remyRemoveMarkedLeaf_insert
      left.shape
      (path := left.path)
      (oldOnLeft := left.oldOnLeft)
      hleftPath
  have hremoveRight :=
    remyRemoveMarkedLeaf_insert
      right.shape
      (path := right.path)
      (oldOnLeft := right.oldOnLeft)
      hrightPath
  have hsome :
      some (left.shape, left.path, left.oldOnLeft) =
        some (right.shape, right.path, right.oldOnLeft) := by
    rw [<- hremoveLeft, <- hremoveRight, hinsert, hleaf]
  have htuple := Option.some.inj hsome
  have hshapeEq : left.shape = right.shape :=
    congrArg Prod.fst htuple
  have htailEq :
      (left.path, left.oldOnLeft) = (right.path, right.oldOnLeft) :=
    congrArg Prod.snd htuple
  have hpathEq : left.path = right.path :=
    congrArg Prod.fst htailEq
  have holdEq : left.oldOnLeft = right.oldOnLeft :=
    congrArg Prod.snd htailEq
  cases left with
  | mk leftShape leftPath leftOld =>
      cases right with
      | mk rightShape rightPath rightOld =>
          simp at hshapeEq hpathEq holdEq
          subst rightShape
          subst rightPath
          subst rightOld
          rfl

private theorem remyRatio_lower (n : Nat) :
    2 * (2 * n + 1) * Cartesian.shapeCount n <=
      (n + 2) * Cartesian.shapeCount (n + 1) := by
  have hle :
      (remyInputList n).length <=
        (markedLeafCodes (n + 1)).length := by
    apply length_le_of_nodup_injective_into
    case hxs =>
      exact remyInputList_nodup n
    case hmem =>
      intro input hinput
      exact remyEncodeInput_mem_markedLeafCodes hinput
    case hinj =>
      intro left hleft right hright hcode
      exact remyEncodeInput_injective_on hleft hright hcode
  rw [remyInputList_length, markedLeafCodes_length] at hle
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hle

private theorem remyStep_arith (n : Nat) :
    2 * (n + 2) * (2 * n + 1) <=
      (2 * (n + 1) + 1) * (2 * (n + 1) + 1) := by
  have hidentity :
      2 * (n + 2) * (2 * n + 1) + (2 * n + 5) =
        (2 * (n + 1) + 1) * (2 * (n + 1) + 1) := by
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    omega
  rw [<- hidentity]
  omega

private theorem remyStep_cubic_square_arith (n : Nat) :
    4 * (2 * n + 1) * (n + 2) * (n + 2) <=
      (2 * (n + 1) + 1) * (2 * (n + 1) + 1) *
        (2 * (n + 1) + 1) := by
  have hidentity :
      4 * (2 * n + 1) * (n + 2) * (n + 2) + (6 * n + 11) =
        (2 * (n + 1) + 1) * (2 * (n + 1) + 1) *
          (2 * (n + 1) + 1) := by
    have h8 :
        n * (n * 8) = 2 * (n * (n * 4)) := by
      rw [show 8 = 2 * 4 by rfl]
      ac_rfl
    have h16 :
        n * (n * 16) = 4 * (n * (n * 4)) := by
      rw [show 16 = 4 * 4 by rfl]
      ac_rfl
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [h8, h16]
    omega
  rw [<- hidentity]
  omega

private theorem two_pow_two_mul_succ (n : Nat) :
    2 ^ (2 * (n + 1)) = 4 * 2 ^ (2 * n) := by
  rw [show 4 = 2 ^ 2 by rfl]
  rw [<- Nat.pow_add]
  congr 1
  omega

private theorem two_pow_four_mul_succ (n : Nat) :
    2 ^ (4 * (n + 1)) = 16 * 2 ^ (4 * n) := by
  rw [show 16 = 2 ^ 4 by rfl]
  rw [<- Nat.pow_add]
  congr 1
  omega

private theorem remyStep_count_bound (n : Nat) :
    4 * (((2 * n + 1) * (2 * n + 1)) *
        Cartesian.shapeCount n) <=
      ((2 * (n + 1) + 1) * (2 * (n + 1) + 1)) *
        Cartesian.shapeCount (n + 1) := by
  have hratio := remyRatio_lower n
  have hscaledRatio :
      (2 * (2 * n + 1)) *
          (2 * (2 * n + 1) * Cartesian.shapeCount n) <=
        (2 * (2 * n + 1)) *
          ((n + 2) * Cartesian.shapeCount (n + 1)) :=
    Nat.mul_le_mul_left (2 * (2 * n + 1)) hratio
  have harith :
      (2 * (2 * n + 1)) * (n + 2) <=
        (2 * (n + 1) + 1) * (2 * (n + 1) + 1) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      remyStep_arith n
  have hscaledArith :
      (2 * (2 * n + 1)) *
          ((n + 2) * Cartesian.shapeCount (n + 1)) <=
        ((2 * (n + 1) + 1) * (2 * (n + 1) + 1)) *
          Cartesian.shapeCount (n + 1) := by
    have hmul :=
      Nat.mul_le_mul_right (Cartesian.shapeCount (n + 1)) harith
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  have hstep := Nat.le_trans hscaledRatio hscaledArith
  have hreshape :
      4 * (((2 * n + 1) * (2 * n + 1)) *
          Cartesian.shapeCount n) =
        (2 * (2 * n + 1)) *
          (2 * (2 * n + 1) * Cartesian.shapeCount n) := by
    rw [show 4 = 2 * 2 by rfl]
    ac_rfl
  rw [hreshape]
  exact hstep

private theorem remyStep_cubic_square_count_bound (n : Nat) :
    16 * (((2 * n + 1) * (2 * n + 1) * (2 * n + 1)) *
        (Cartesian.shapeCount n * Cartesian.shapeCount n)) <=
      ((2 * (n + 1) + 1) * (2 * (n + 1) + 1) *
          (2 * (n + 1) + 1)) *
        (Cartesian.shapeCount (n + 1) * Cartesian.shapeCount (n + 1)) := by
  let width := 2 * n + 1
  let nextWidth := 2 * (n + 1) + 1
  let count := Cartesian.shapeCount n
  let nextCount := Cartesian.shapeCount (n + 1)
  have hratio :
      2 * width * count <= (n + 2) * nextCount := by
    simpa [width, count, nextCount, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using remyRatio_lower n
  have hsquareRaw :
      (2 * width * count) * (2 * width * count) <=
        ((n + 2) * nextCount) * ((n + 2) * nextCount) :=
    Nat.mul_le_mul hratio hratio
  have hsquare :
      4 * (width * width) * (count * count) <=
        ((n + 2) * (n + 2)) * (nextCount * nextCount) := by
    have hleft :
        (2 * width * count) * (2 * width * count) =
          4 * (width * width) * (count * count) := by
      rw [show 4 = 2 * 2 by rfl]
      ac_rfl
    have hright :
        ((n + 2) * nextCount) * ((n + 2) * nextCount) =
          ((n + 2) * (n + 2)) * (nextCount * nextCount) := by
      ac_rfl
    simpa [hleft, hright] using hsquareRaw
  have hscaledRatio :
      16 * ((width * width * width) * (count * count)) <=
        (4 * width * (n + 2) * (n + 2)) *
          (nextCount * nextCount) := by
    have hmul := Nat.mul_le_mul_left (4 * width) hsquare
    have hleft :
        (4 * width) * (4 * (width * width) * (count * count)) =
          16 * ((width * width * width) * (count * count)) := by
      rw [show 16 = 4 * 4 by rfl]
      ac_rfl
    have hright :
        (4 * width) *
            (((n + 2) * (n + 2)) * (nextCount * nextCount)) =
          (4 * width * (n + 2) * (n + 2)) *
            (nextCount * nextCount) := by
      ac_rfl
    simpa [hleft, hright] using hmul
  have harith :
      4 * width * (n + 2) * (n + 2) <=
        nextWidth * nextWidth * nextWidth := by
    simpa [width, nextWidth, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using remyStep_cubic_square_arith n
  have hscaledArith :
      (4 * width * (n + 2) * (n + 2)) *
          (nextCount * nextCount) <=
        (nextWidth * nextWidth * nextWidth) *
          (nextCount * nextCount) := by
    exact Nat.mul_le_mul_right (nextCount * nextCount) harith
  have hstep := Nat.le_trans hscaledRatio hscaledArith
  simpa [width, nextWidth, count, nextCount, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using hstep

/--
Quadratic-form Catalan lower bound for the explicit Cartesian-shape count.

This is the Mathlib-free counting theorem behind the logarithmic-slack RMQ
space lower bound: `shapeCount n` is large enough that multiplying by the
quadratic slack `(2*n+1)^2` covers the full `2^(2*n)` universe.
-/
theorem shapeCount_quadratic_lower (n : Nat) :
    2 ^ (2 * n) <=
      ((2 * n + 1) * (2 * n + 1)) * Cartesian.shapeCount n := by
  induction n with
  | zero =>
      simp [Cartesian.shapeCount, Cartesian.shapesOfSize]
  | succ n ih =>
      rw [two_pow_two_mul_succ]
      exact Nat.le_trans
        (Nat.mul_le_mul_left 4 ih)
        (remyStep_count_bound n)

/--
Cubic-square Catalan lower bound for the explicit Cartesian-shape count.

This strengthens the quadratic count into the squared form
`2^(4*n) <= (2*n+1)^3 * shapeCount n^2`, matching the integer-arithmetic
surrogate for the `3/2 * log n` Catalan slack.
-/
theorem shapeCount_cubic_square_lower (n : Nat) :
    2 ^ (4 * n) <=
      ((2 * n + 1) * (2 * n + 1) * (2 * n + 1)) *
        (Cartesian.shapeCount n * Cartesian.shapeCount n) := by
  induction n with
  | zero =>
      simp [Cartesian.shapeCount, Cartesian.shapesOfSize]
  | succ n ih =>
      rw [two_pow_four_mul_succ]
      exact Nat.le_trans
        (Nat.mul_le_mul_left 16 ih)
        (remyStep_cubic_square_count_bound n)

/--
Turn a quadratic Catalan lower-bound target into the logarithmic exponent form
needed by `two_mul_sub_slack_le_bits_of_exactRMQShapeEncoding`.

The remaining combinatorial theorem is the premise:
`2^(2*n) <= (2*n+1)^2 * shapeCount n`.
-/
theorem shapeCount_log_lower_of_quadratic_bound
    {n : Nat}
    (hquad :
      2 ^ (2 * n) <=
        ((2 * n + 1) * (2 * n + 1)) * Cartesian.shapeCount n) :
    2 ^ (2 * n - (2 * Nat.log2 (2 * n + 1) + 2)) <=
      Cartesian.shapeCount n := by
  exact LowerBound.count_log_lower_of_quadratic_bound hquad

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

/--
End-to-end logarithmic-slack bit lower bound from an externally supplied
quadratic Catalan counting inequality.
-/
theorem two_mul_sub_log_slack_le_bits_of_exactRMQShapeEncoding_of_quadratic_bound
    {n bits : Nat} (encoding : ExactRMQShapeEncoding n bits)
    (hquad :
      2 ^ (2 * n) <=
        ((2 * n + 1) * (2 * n + 1)) * Cartesian.shapeCount n) :
    2 * n - (2 * Nat.log2 (2 * n + 1) + 2) <= bits :=
  two_mul_sub_slack_le_bits_of_exactRMQShapeEncoding
    encoding
    (shapeCount_log_lower_of_quadratic_bound hquad)

/--
End-to-end logarithmic-slack bit lower bound for exact fixed-length RMQ
shape encodings.

The combinatorial Catalan count is discharged by
`shapeCount_quadratic_lower`, so the theorem has no remaining counting
premise.
-/
theorem two_mul_sub_log_slack_le_bits_of_exactRMQShapeEncoding
    {n bits : Nat} (encoding : ExactRMQShapeEncoding n bits) :
    2 * n - (2 * Nat.log2 (2 * n + 1) + 2) <= bits :=
  two_mul_sub_log_slack_le_bits_of_exactRMQShapeEncoding_of_quadratic_bound
    encoding
    (shapeCount_quadratic_lower n)

/--
Squared-count Catalan slack bridge for lossless Cartesian-shape encodings.

The theorem consumes an external cubic-square count theorem and the ordinary
capacity bound for the fixed-length shape encoding.  The conclusion is stated
in doubled bits, avoiding rational arithmetic while exposing the coefficient
`3` on the logarithmic slack.
-/
theorem four_mul_sub_three_log_slack_le_two_mul_bits_of_losslessShapeEncoding_of_cubic_square_bound
    {n bits : Nat} (encoding : LosslessShapeEncoding n bits)
    (hcubic :
      2 ^ (4 * n) <=
        ((2 * n + 1) * (2 * n + 1) * (2 * n + 1)) *
          (Cartesian.shapeCount n * Cartesian.shapeCount n)) :
    4 * n - (3 * Nat.log2 (2 * n + 1) + 3) <= 2 * bits :=
  LowerBound.two_mul_bits_lower_of_cubic_square_bound
    (shapeCount_le_two_pow_of_lossless_shape_encoding encoding)
    hcubic

/--
No-premise doubled-bit Catalan slack lower bound for lossless Cartesian-shape
encodings.  This instantiates the squared-count bridge with
`shapeCount_cubic_square_lower`.
-/
theorem four_mul_sub_three_log_slack_le_two_mul_bits_of_losslessShapeEncoding
    {n bits : Nat} (encoding : LosslessShapeEncoding n bits) :
    4 * n - (3 * Nat.log2 (2 * n + 1) + 3) <= 2 * bits :=
  four_mul_sub_three_log_slack_le_two_mul_bits_of_losslessShapeEncoding_of_cubic_square_bound
    encoding
    (shapeCount_cubic_square_lower n)

/--
Squared-count Catalan slack bridge specialized to exact fixed-length RMQ shape
encodings.
-/
theorem four_mul_sub_three_log_slack_le_two_mul_bits_of_exactRMQShapeEncoding_of_cubic_square_bound
    {n bits : Nat} (encoding : ExactRMQShapeEncoding n bits)
    (hcubic :
      2 ^ (4 * n) <=
        ((2 * n + 1) * (2 * n + 1) * (2 * n + 1)) *
          (Cartesian.shapeCount n * Cartesian.shapeCount n)) :
    4 * n - (3 * Nat.log2 (2 * n + 1) + 3) <= 2 * bits :=
  four_mul_sub_three_log_slack_le_two_mul_bits_of_losslessShapeEncoding_of_cubic_square_bound
    (losslessShapeEncoding_of_exactRMQShapeEncoding encoding)
    hcubic

/--
Coefficient-correct Catalan information-theoretic lower bound for exact
fixed-length RMQ shape encodings, stated without rational arithmetic:
`4*n - (3*log2(2*n+1)+3) <= 2*bits`.
-/
theorem four_mul_sub_three_log_slack_le_two_mul_bits_of_exactRMQShapeEncoding
    {n bits : Nat} (encoding : ExactRMQShapeEncoding n bits) :
    4 * n - (3 * Nat.log2 (2 * n + 1) + 3) <= 2 * bits :=
  four_mul_sub_three_log_slack_le_two_mul_bits_of_exactRMQShapeEncoding_of_cubic_square_bound
    encoding
    (shapeCount_cubic_square_lower n)

theorem shapeCount_le_two_pow_of_exactRMQStateEncoding
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits) :
    Cartesian.shapeCount n <= 2 ^ bits :=
  shapeCount_le_two_pow_of_exactRMQShapeEncoding
    (exactRMQShapeEncoding_of_stateEncoding encoding)

/--
The same capacity bound routed through the generic payload-accounted lower-bound
adapter.  This is the hub-facing form used when the counted state payload, not a
bare shape encoder, is the object being analyzed.
-/
theorem shapeCount_le_two_pow_of_exactRMQStateEncoding_payloadView
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits) :
    Cartesian.shapeCount n <= 2 ^ bits := by
  have hcapacity :=
    LowerBound.domain_length_le_two_pow_of_payload_lossless_encoding
      encoding.payloadLosslessEncoding (Cartesian.shapesOfSize_nodup n)
  simpa [Cartesian.shapeCount] using hcapacity

theorem two_mul_sub_log_slack_le_bits_of_exactRMQStateEncoding
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits) :
    2 * n - (2 * Nat.log2 (2 * n + 1) + 2) <= bits :=
  two_mul_sub_log_slack_le_bits_of_exactRMQShapeEncoding
    (exactRMQShapeEncoding_of_stateEncoding encoding)

/--
Payload-view route for the state-encoding lower bound.  Unlike the direct
shape-encoding route, this theorem explicitly passes through the generic
`PayloadLosslessEncoding` adapter from `Core.PayloadLowerBound`.
-/
theorem two_mul_sub_log_slack_le_bits_of_exactRMQStateEncoding_payloadView
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits) :
    2 * n - (2 * Nat.log2 (2 * n + 1) + 2) <= bits :=
  LowerBound.lower_le_bits_of_count_lower_bound
    (shapeCount_le_two_pow_of_exactRMQStateEncoding_payloadView encoding)
    (shapeCount_log_lower_of_quadratic_bound
      (shapeCount_quadratic_lower n))

/--
Payload-bit spelling of the state-encoding lower bound. This is definitionally
the same theorem as `two_mul_sub_log_slack_le_bits_of_exactRMQStateEncoding`,
but the name makes the counted quantity explicit for paper-facing statements.
-/
theorem two_mul_sub_log_slack_le_payloadBits_of_exactRMQStateEncoding
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits) :
    2 * n - (2 * Nat.log2 (2 * n + 1) + 2) <= bits :=
  two_mul_sub_log_slack_le_bits_of_exactRMQStateEncoding encoding

theorem four_mul_sub_three_log_slack_le_two_mul_bits_of_exactRMQStateEncoding
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits) :
    4 * n - (3 * Nat.log2 (2 * n + 1) + 3) <= 2 * bits :=
  four_mul_sub_three_log_slack_le_two_mul_bits_of_exactRMQShapeEncoding
    (exactRMQShapeEncoding_of_stateEncoding encoding)

/--
Payload-view route for the doubled-bit Catalan slack lower bound.  This keeps
the RMQ statement connected to the generic payload-accounted finite-domain API.
-/
theorem four_mul_sub_three_log_slack_le_two_mul_bits_of_exactRMQStateEncoding_payloadView
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits) :
    4 * n - (3 * Nat.log2 (2 * n + 1) + 3) <= 2 * bits :=
  LowerBound.two_mul_bits_lower_of_cubic_square_bound
    (shapeCount_le_two_pow_of_exactRMQStateEncoding_payloadView encoding)
    (shapeCount_cubic_square_lower n)

/--
Payload-bit spelling of the doubled-bit Catalan slack lower bound for paper-facing
fixed-length state-encoding statements.
-/
theorem four_mul_sub_three_log_slack_le_two_mul_payloadBits_of_exactRMQStateEncoding
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits) :
    4 * n - (3 * Nat.log2 (2 * n + 1) + 3) <= 2 * bits :=
  four_mul_sub_three_log_slack_le_two_mul_bits_of_exactRMQStateEncoding
    encoding

theorem two_mul_sub_log_slack_le_bits_of_canonicalRepresentativeStateEncoding
    (n : Nat) :
    2 * n - (2 * Nat.log2 (2 * n + 1) + 2) <= 2 * n :=
  two_mul_sub_log_slack_le_bits_of_exactRMQStateEncoding
    (canonicalRepresentativeStateEncoding n)

theorem four_mul_sub_three_log_slack_le_two_mul_bits_of_canonicalRepresentativeStateEncoding
    (n : Nat) :
    4 * n - (3 * Nat.log2 (2 * n + 1) + 3) <= 2 * (2 * n) :=
  four_mul_sub_three_log_slack_le_two_mul_bits_of_exactRMQStateEncoding
    (canonicalRepresentativeStateEncoding n)

/--
Two-sided fixed-length RMQ space bounds for a concrete exact payload model.

`lower_le_any` is the universal lower bound: every exact state encoding over
representative arrays needs at least `lower` bits. `upperEncoding` is a
concrete payload-only decoder at `upper` bits, so the upper side is not a bare
existential.
-/
structure ExactRMQSpaceBounds (n lower upper : Nat) where
  lower_le_any :
    forall {bits : Nat}, ExactRMQStateEncoding n bits -> lower <= bits
  upperEncoding : ExactRMQStateEncoding n upper

/-- The logarithmic-slack lower expression from the Catalan/RMQ lower bound. -/
def logSlackLower (n : Nat) : Nat :=
  2 * n - (2 * Nat.log2 (2 * n + 1) + 2)

/-- The doubled-bit Catalan slack lower expression from the cubic-square count. -/
def doubledLogSlackLower (n : Nat) : Nat :=
  4 * n - (3 * Nat.log2 (2 * n + 1) + 3)

/--
Charged-payload form of the exact RMQ lower bound.

For any exact fixed-length state encoding, every on-domain built state charges
at least the logarithmic-slack lower bound in its `PayloadView`.  This is the
bridge from the abstract `bits` parameter to the model-level payload budget.
-/
theorem logSlackLower_le_payloadBitCount_of_exactRMQStateEncoding
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    logSlackLower n <=
      (encoding.payloadView).payloadBitCount
        (encoding.buildState shape) := by
  have hlower :
      logSlackLower n <= bits := by
    simpa [logSlackLower] using
      two_mul_sub_log_slack_le_bits_of_exactRMQStateEncoding_payloadView
        encoding
  have hbits :
      bits <=
        (encoding.payloadView).payloadBitCount
          (encoding.buildState shape) :=
    encoding.payloadBitCount_ge_bits_of_mem hshape
  exact Nat.le_trans hlower hbits

theorem logSlackLower_le_budget_of_exactRMQStateEncoding
    {n bits budget : Nat} (encoding : ExactRMQStateEncoding n bits)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (hbudget :
      forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          (encoding.payloadView).payloadBitCount
            (encoding.buildState shape) <= budget) :
    logSlackLower n <= budget := by
  exact Nat.le_trans
    (logSlackLower_le_payloadBitCount_of_exactRMQStateEncoding
      encoding hshape)
    (hbudget hshape)

/--
Charged-payload form of the coefficient-correct Catalan slack lower bound.
The conclusion is doubled to avoid rational arithmetic:
`doubledLogSlackLower n <= 2 * payloadBitCount`.
-/
theorem doubledLogSlackLower_le_two_mul_payloadBitCount_of_exactRMQStateEncoding
    {n bits : Nat} (encoding : ExactRMQStateEncoding n bits)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    doubledLogSlackLower n <=
      2 *
        (encoding.payloadView).payloadBitCount
          (encoding.buildState shape) := by
  have hlower :
      doubledLogSlackLower n <= 2 * bits := by
    simpa [doubledLogSlackLower] using
      four_mul_sub_three_log_slack_le_two_mul_bits_of_exactRMQStateEncoding_payloadView
        encoding
  have hbits :
      bits <=
        (encoding.payloadView).payloadBitCount
          (encoding.buildState shape) :=
    encoding.payloadBitCount_ge_bits_of_mem hshape
  exact Nat.le_trans hlower (Nat.mul_le_mul_left 2 hbits)

theorem doubledLogSlackLower_le_two_mul_budget_of_exactRMQStateEncoding
    {n bits budget : Nat} (encoding : ExactRMQStateEncoding n bits)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (hbudget :
      forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          (encoding.payloadView).payloadBitCount
            (encoding.buildState shape) <= budget) :
    doubledLogSlackLower n <= 2 * budget := by
  have hlower :
      doubledLogSlackLower n <=
        2 *
          (encoding.payloadView).payloadBitCount
            (encoding.buildState shape) :=
    doubledLogSlackLower_le_two_mul_payloadBitCount_of_exactRMQStateEncoding
      encoding hshape
  exact Nat.le_trans hlower (Nat.mul_le_mul_left 2 (hbudget hshape))

theorem canonicalRepresentative_payloadBitCount_eq_two_mul
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    ((canonicalRepresentativeStateEncoding n).payloadView).payloadBitCount
        ((canonicalRepresentativeStateEncoding n).buildState shape) =
      2 * n := by
  exact
    ExactRMQStateEncoding.payloadBitCount_eq_bits_of_mem
      (canonicalRepresentativeStateEncoding n) hshape

/--
Generic hub-level payload-space bounds for the RMQ representative-shape domain.

The lower side is the Catalan/RMQ logarithmic-slack count bound, and the upper
side is the canonical explicit `2*n` shape payload viewed through
`PayloadLosslessEncoding`.
-/
def canonicalRepresentativePayloadSpaceBounds (n : Nat) :
    LowerBound.PayloadSpaceBounds
      (Cartesian.shapesOfSize n) (logSlackLower n) (2 * n) where
  nodup := Cartesian.shapesOfSize_nodup n
  count_lower := by
    simpa [logSlackLower, Cartesian.shapeCount] using
      shapeCount_log_lower_of_quadratic_bound
        (shapeCount_quadratic_lower n)
  upperEncoding :=
    (canonicalRepresentativeStateEncoding n).payloadLosslessEncoding

theorem canonicalRepresentativePayloadSpaceBounds_lower_le_bits
    (n : Nat) {bits : Nat}
    (encoding :
      LowerBound.PayloadLosslessEncoding (Cartesian.shapesOfSize n) bits) :
    logSlackLower n <= bits :=
  (canonicalRepresentativePayloadSpaceBounds n).lower_le_bits encoding

theorem canonicalRepresentativePayloadSpaceBounds_lower_le_budget
    (n : Nat) {bits budget : Nat}
    (encoding :
      LowerBound.PayloadLosslessEncoding (Cartesian.shapesOfSize n) bits)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (hbudget :
      forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          encoding.payloadView.payloadBitCount
            (encoding.buildState shape) <= budget) :
    logSlackLower n <= budget :=
  (canonicalRepresentativePayloadSpaceBounds n).lower_le_budget
    encoding hshape hbudget

theorem canonicalRepresentativePayloadSpaceBounds_lower_le_upper
    (n : Nat) :
    logSlackLower n <= 2 * n :=
  (canonicalRepresentativePayloadSpaceBounds n).lower_le_upper

/--
Concrete two-sided RMQ space bound.

The lower side is the no-premise `2n - O(log n)` exact-RMQ lower bound.  The
upper side is the explicit canonical Cartesian-shape payload of length `2*n`,
whose decoder answers every representative RMQ query from the payload alone.
This is the tight fixed-length `2n` plus/minus logarithmic-slack sandwich; packed
`2n + o(n)` query structures remain a stronger future refinement.
-/
def canonicalRepresentativeSpaceBounds (n : Nat) :
    ExactRMQSpaceBounds n (logSlackLower n) (2 * n) where
  lower_le_any := by
    intro bits encoding
    exact two_mul_sub_log_slack_le_bits_of_exactRMQStateEncoding encoding
  upperEncoding := canonicalRepresentativeStateEncoding n

theorem canonicalRepresentativeSpaceBounds_lower_le_any
    (n : Nat) {bits : Nat} (encoding : ExactRMQStateEncoding n bits) :
    logSlackLower n <= bits :=
  (canonicalRepresentativeSpaceBounds n).lower_le_any encoding

theorem canonicalRepresentativeSpaceBounds_upper_bits
    (n : Nat) :
    (canonicalRepresentativeSpaceBounds n).upperEncoding =
      canonicalRepresentativeStateEncoding n := by
  rfl

theorem exactRMQ_two_sided_log_slack_space_bound
    (n : Nat) :
    (forall {bits : Nat}, ExactRMQStateEncoding n bits ->
        logSlackLower n <= bits) ∧
      (exists _encoding : ExactRMQStateEncoding n (2 * n), True) := by
  exact ⟨canonicalRepresentativeSpaceBounds_lower_le_any n,
    ⟨(canonicalRepresentativeSpaceBounds n).upperEncoding, True.intro⟩⟩

/--
Tight fixed-length payload-space sandwich for exact RMQ state encodings.

Every exact state encoding over representative arrays needs at least
`2*n - (2*log2 (2*n+1)+2)` payload bits, the same lower bound applies to any
uniform charged payload budget, and the canonical representative decoder gives
a concrete exact upper witness charging exactly `2*n` bits on every shape.
-/
theorem exactRMQ_tight_fixed_length_payload_space_bound
    (n : Nat) :
    (forall {bits : Nat}, ExactRMQStateEncoding n bits ->
        logSlackLower n <= bits) /\
      (forall {bits budget : Nat}
          (encoding : ExactRMQStateEncoding n bits)
          {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          (forall {shape : Cartesian.CartesianShape},
            List.Mem shape (Cartesian.shapesOfSize n) ->
              (encoding.payloadView).payloadBitCount
                (encoding.buildState shape) <= budget) ->
          logSlackLower n <= budget) /\
      (exists encoding : ExactRMQStateEncoding n (2 * n),
        forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (encoding.payloadView).payloadBitCount
              (encoding.buildState shape) = 2 * n) := by
  constructor
  · intro bits encoding
    exact canonicalRepresentativeSpaceBounds_lower_le_any n encoding
  · constructor
    · intro bits budget encoding shape hshape hbudget
      exact logSlackLower_le_budget_of_exactRMQStateEncoding
        encoding hshape hbudget
    · exact ⟨canonicalRepresentativeStateEncoding n, by
        intro shape hshape
        exact canonicalRepresentative_payloadBitCount_eq_two_mul hshape⟩

/--
Coefficient-correct doubled Catalan-slack payload-space package.

The lower side is stated without rational arithmetic:
`doubledLogSlackLower n <= 2 * bits`, and the same doubled lower bound applies
to any uniform charged payload budget. The upper side is the concrete canonical
representative decoder: it stores exactly `2*n` payload bits for every shape, so
the doubled counted payload is exactly `2 * (2*n)`.
-/
theorem exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack
    (n : Nat) :
    (forall {bits : Nat}, ExactRMQStateEncoding n bits ->
        doubledLogSlackLower n <= 2 * bits) /\
      (forall {bits budget : Nat}
          (encoding : ExactRMQStateEncoding n bits)
          {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          (forall {shape : Cartesian.CartesianShape},
            List.Mem shape (Cartesian.shapesOfSize n) ->
              (encoding.payloadView).payloadBitCount
                (encoding.buildState shape) <= budget) ->
          doubledLogSlackLower n <= 2 * budget) /\
      (exists encoding : ExactRMQStateEncoding n (2 * n),
        forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (encoding.payloadView).payloadBitCount
                (encoding.buildState shape) = 2 * n /\
              2 *
                (encoding.payloadView).payloadBitCount
                  (encoding.buildState shape) = 2 * (2 * n)) := by
  constructor
  · intro bits encoding
    simpa [doubledLogSlackLower] using
      four_mul_sub_three_log_slack_le_two_mul_bits_of_exactRMQStateEncoding_payloadView
        encoding
  · constructor
    · intro bits budget encoding shape hshape hbudget
      exact doubledLogSlackLower_le_two_mul_budget_of_exactRMQStateEncoding
        encoding hshape hbudget
    · exact ⟨canonicalRepresentativeStateEncoding n, by
        intro shape hshape
        have hpayload :=
          canonicalRepresentative_payloadBitCount_eq_two_mul hshape
        exact ⟨hpayload, by rw [hpayload]⟩⟩

end EncodingLowerBound

end RMQ
