import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Space

/-!
# Packed probe addresses

This module works towards `EG-CP` rows `FG-07-CLOSED-CONTROLLER` and
`FG-08-PHYSICAL-LOWERING`. It supplies the address arithmetic a probe-only
controller needs, and nothing else.

Every function here has a `Nat`-only signature. Composed with
`packedSourceFlatOffset_eq` and `packedSpan_from_two_cells`, this is the step that
turns "which source and index do I want" into "which two cells do I probe".

## What this module does not establish

* There is no controller. These are the addresses a controller would compute, not
  a definition that computes them during an execution.
* Nothing here shows the addresses are in range, or that the words read decode to
  the logical words. Those are the totality and lowering obligations.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-! ### Bit addresses -/

/--
The bit position, inside the packed memory, of entry `index` of a fixed-width
source.

The header occupies cell zero in full, so the canonical payload begins at bit
`packedCellWidth n` and every payload offset is shifted by exactly one cell.
-/
def packedBitAddress (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index width : Nat) : Nat :=
  packedCellWidth n + packedSourceFlatOffset n longCount source + index * width

/-- The two cells a fixed-width read touches. -/
def packedProbeCells (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index width : Nat) : Nat × Nat :=
  let bit := packedBitAddress n longCount source index width
  (bit / packedCellWidth n, bit / packedCellWidth n + 1)

/-- The bit offset within the first of those two cells. -/
def packedProbeOffset (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index width : Nat) : Nat :=
  packedBitAddress n longCount source index width % packedCellWidth n

/-! ### The payload sits one cell in -/

/--
A slice of the canonical payload is the corresponding slice of the packed memory,
shifted by the one header cell.

This is what makes the shift in `packedBitAddress` correct rather than assumed.
-/
theorem packedPayloadSlice
    (shape : CartesianShape) (j width : Nat)
    (hfit : j + width <= packedPayloadLength shape.size) :
    ((packedPaddedBits shape).drop (packedCellWidth shape.size + j)).take width =
      (((concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload).drop
        j).take width := by
  have hhdr := packedHeaderBits_length shape
  have hpay := packedPayloadLength_eq shape
  have hjle :
      j <= ((concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload).length := by
    omega
  have hwle :
      width <=
        (((concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload).drop
          j).length := by
    rw [List.length_drop]
    omega
  unfold packedPaddedBits packedSerializedBits
  rw [List.append_assoc, ← List.drop_drop]
  rw [← hhdr]
  rw [List.drop_left]
  rw [List.drop_append_of_le_length hjle, List.take_append_of_le_length hwle]

/-! ### The two-probe recovery -/

/--
**Two probes suffice.** Any fixed-width slice of the canonical payload, of width at
most one cell, is recoverable from two consecutive packed cells.

The addresses are computed by `packedProbeCells` and `packedProbeOffset`, both of
which take only the input size, the decoded long count, the typed source, the
index and the width.
-/
theorem packedRead_from_two_cells
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index width : Nat)
    (hwidth : width <= packedCellWidth shape.size)
    (hfit :
      concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source +
          index * width + width <=
        packedPayloadLength shape.size) :
    (((concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload).drop
          (concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source +
            index * width)).take width =
      ((packedCellAt shape
            (packedProbeCells shape.size (longCount shape) source index width).1 ++
          packedCellAt shape
            (packedProbeCells shape.size (longCount shape) source index width).2).drop
        (packedProbeOffset shape.size (longCount shape) source index width)).take
        width := by
  have hoff := packedSourceFlatOffset_eq shape source
  have hslice :=
    packedPayloadSlice shape
      (concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source +
        index * width)
      width hfit
  have hspan :=
    packedSpan_from_two_cells shape
      (packedBitAddress shape.size (longCount shape) source index width)
      width hwidth
  unfold packedProbeCells packedProbeOffset packedBitAddress
  rw [← hslice, hoff]
  unfold packedBitAddress at hspan
  simpa [Nat.add_assoc] using hspan

end PackedCellProbe
end SuccinctFinal
end RMQ
