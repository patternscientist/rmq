import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.SourceFactorization

/-!
# The `K = 1` packed header

This module works towards `EG-CP` falsification row `FG-04-WIDTH-AND-HEADER`.

It fixes the input-size-only canonical payload length `P n`, the cell width
`w n = machineWordBits (P n + 2)`, and the one-cell header carrying `longCount`.

## What this module does not establish

* No memory exists yet, so "the header occupies cell zero" is not stated here; it
  is length arithmetic about an object with no cells until `FG-05` defines one.
* Nothing here shows a controller can obtain `longCount`. The header is defined
  and decodable; that it is ever read is a separate obligation.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-! ### Every shape has its own size -/

/--
A shape is a shape of its own size.

Needed because the canonical payload-length theorem is keyed on membership in
`shapesOfSize n` rather than on `shape.size`.
-/
theorem shapeOfSize_self (shape : CartesianShape) :
    Cartesian.ShapeOfSize shape.size shape := by
  induction shape with
  | empty => simpa [CartesianShape.size] using Cartesian.ShapeOfSize.empty
  | node left right ihleft ihright =>
      simpa [CartesianShape.size] using Cartesian.ShapeOfSize.node ihleft ihright

theorem mem_shapesOfSize_size (shape : CartesianShape) :
    shape ∈ Cartesian.shapesOfSize shape.size :=
  Cartesian.shapeOfSize_mem_shapesOfSize (shapeOfSize_self shape)

/-! ### `P n`: the input-size-only canonical payload length -/

/--
The exact length of the canonical flat payload at input size `n`.

Input-size-only by construction: `concreteBPNativeSuccinctRMQOverhead` and both of
its summands have type `Nat -> Nat`.
-/
def packedPayloadLength (n : Nat) : Nat :=
  2 * n +
    concreteBPNativeSuccinctRMQOverhead
      genericSparseExceptionBPCloseAccessOverhead n

theorem packedPayloadLength_eq (shape : CartesianShape) :
    (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload.length =
      packedPayloadLength shape.size :=
  concreteBPNativeSuccinctRMQFlatPayloadLayout_payload_length
    (mem_shapesOfSize_size shape)

/-! ### `w n`: the packed cell width -/

/--
The packed cell width.

`P n + 2` rather than `P n` so that both the largest payload bit index and the
one-past-the-end address are representable at this width.
-/
def packedCellWidth (n : Nat) : Nat :=
  SuccinctRank.machineWordBits (packedPayloadLength n + 2)

theorem packedCellWidth_pos (n : Nat) : 0 < packedCellWidth n :=
  SuccinctRank.machineWordBits_pos _

/-- The payload length and its one-past-the-end address both fit one cell. -/
theorem packedPayloadLength_lt_two_pow_width (n : Nat) :
    packedPayloadLength n + 2 < 2 ^ packedCellWidth n :=
  SuccinctRank.self_lt_two_pow_machineWordBits _

/-! ### The long count fits one cell at every size -/

/-- The long count never exceeds the number of super slots. -/
theorem longCount_le_superSlots (shape : CartesianShape) :
    longCount shape <= packedSuperSlots shape.size := by
  have h :=
    RMQ.Succinct.rankPrefix_le_length true
      (GenericSelect.longSuperFlagBits shape.bpCode false)
      (GenericSelect.superSlotCount shape.bpCode false)
  rw [GenericSelect.longSuperFlagBits_length] at h
  rw [← superSlotCount_eq_packed]
  exact h

/-- The number of super slots never exceeds the input size. -/
theorem packedSuperSlots_le (n : Nat) : packedSuperSlots n <= n := by
  have hstride : 0 < GenericSelect.superStride (2 * n) := by
    unfold GenericSelect.superStride
    simp only [GenericSelect.wordBits]
    exact Nat.mul_pos (SuccinctRank.machineWordBits_pos _)
      (SuccinctRank.machineWordBits_pos _)
  by_cases hn : 0 < n
  · exact GenericSelect.selectCeilDiv_le_self_of_pos hn hstride
  · have hz : n = 0 := by omega
    subst hz
    have h0 : 0 < GenericSelect.superStride 0 := by simpa using hstride
    unfold packedSuperSlots GenericSelect.selectCeilDiv
    simp
    omega

/--
**All-size count fit.** The long count is representable in one `w n`-bit cell for
every shape, with no size side condition.
-/
theorem longCount_lt_two_pow_width (shape : CartesianShape) :
    longCount shape < 2 ^ packedCellWidth shape.size := by
  have h1 := longCount_le_superSlots shape
  have h2 := packedSuperSlots_le shape.size
  have h3 := packedPayloadLength_lt_two_pow_width shape.size
  have h4 : shape.size <= packedPayloadLength shape.size := by
    unfold packedPayloadLength
    omega
  omega

/-! ### The header cell -/

/-- The header: `longCount` encoded little-endian in exactly `w n` bits. -/
def packedHeaderBits (shape : CartesianShape) : List Bool :=
  SuccinctSpace.natToBitsLE (packedCellWidth shape.size) (longCount shape)

/-- **Exact arity.** The header is exactly one cell wide at every size. -/
theorem packedHeaderBits_length (shape : CartesianShape) :
    (packedHeaderBits shape).length = packedCellWidth shape.size :=
  SuccinctSpace.natToBitsLE_length _ _

/--
**Decoding.** Reading the header back recovers the long count exactly, at every
size and for every shape.

The `_of_lt` side condition is discharged by `longCount_lt_two_pow_width`, which is
itself unconditional, so this theorem carries no size hypothesis either.
-/
theorem packedHeaderBits_decode (shape : CartesianShape) :
    SuccinctSpace.bitsToNatLE (packedHeaderBits shape) = longCount shape :=
  SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt (longCount_lt_two_pow_width shape)

/-! ### Small cases

The empty and singleton shapes are instantiated explicitly. At `n = 0` the cell is
still `machineWordBits (P 0 + 2)` bits rather than a byte or a word, so a chunker
that assumes any minimum cell size is wrong at the bottom of the range.
-/

example : packedHeaderBits CartesianShape.empty =
    SuccinctSpace.natToBitsLE (packedCellWidth 0) (longCount CartesianShape.empty) := rfl

example :
    (packedHeaderBits CartesianShape.empty).length = packedCellWidth 0 :=
  packedHeaderBits_length CartesianShape.empty

example :
    SuccinctSpace.bitsToNatLE (packedHeaderBits CartesianShape.empty) =
      longCount CartesianShape.empty :=
  packedHeaderBits_decode CartesianShape.empty

example :
    SuccinctSpace.bitsToNatLE
        (packedHeaderBits (CartesianShape.node CartesianShape.empty
          CartesianShape.empty)) =
      longCount (CartesianShape.node CartesianShape.empty CartesianShape.empty) :=
  packedHeaderBits_decode _

end PackedCellProbe
end SuccinctFinal
end RMQ
