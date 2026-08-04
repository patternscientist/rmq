import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Space

/-!
# Packed bit addresses

This module works towards `EG-CP` rows `FG-07-CLOSED-CONTROLLER` and
`FG-08-PHYSICAL-LOWERING`. It supplies the bit arithmetic a probe-only
controller needs, and nothing else; the physical probe plan built on top of it
lives in `Probe.lean`.

Every function here has a `Nat`-only signature. Composed with
`packedSourceFlatOffset_eq`, this is the step that turns "which source and index
do I want" into "which bit does that start at".

## What this module does not establish

* There is no controller. These are the addresses a controller would compute,
  not a definition that computes them during an execution.
* Nothing here issues a probe or shows an address is allocated. That is the
  obligation of `Probe.lean`.
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

/-- The bit address is the header cell plus the flat payload address. -/
theorem packedBitAddress_eq (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index width : Nat) :
    packedBitAddress n longCount source index width =
      packedCellWidth n +
        (packedSourceFlatOffset n longCount source + index * width) := by
  unfold packedBitAddress
  omega

/-! ### The payload sits one cell in -/

/--
A slice of the canonical payload is the corresponding slice of the packed
memory, shifted by the one header cell.

This is what makes the shift in `packedBitAddress` correct rather than assumed.
-/
theorem packedPayloadSlice
    (shape : CartesianShape) (j width : Nat)
    (hfit : j + width <= packedPayloadLength shape.size) :
    ((packedPaddedBits shape).drop (packedCellWidth shape.size + j)).take width =
      ((packedPayloadBits shape).drop j).take width := by
  have hhdr := packedHeaderBits_length shape
  have hpay := packedPayloadBits_length shape
  have hjle : j <= (packedPayloadBits shape).length := by omega
  have hwle : width <= ((packedPayloadBits shape).drop j).length := by
    rw [List.length_drop]
    omega
  unfold packedPaddedBits packedSerializedBits
  rw [List.append_assoc, ← List.drop_drop]
  rw [← hhdr]
  rw [List.drop_left]
  rw [List.drop_append_of_le_length hjle, List.take_append_of_le_length hwle]

/--
The whole canonical payload is the packed memory's bit string with the header
cell removed and the counted final padding dropped.
-/
theorem packedPaddedBits_payload_window (shape : CartesianShape) :
    ((packedPaddedBits shape).drop (packedCellWidth shape.size)).take
        (packedPayloadLength shape.size) =
      packedPayloadBits shape := by
  have hpay := packedPayloadBits_length shape
  have h :=
    packedPayloadSlice shape 0 (packedPayloadLength shape.size) (by omega)
  have htake :
      (packedPayloadBits shape).take (packedPayloadLength shape.size) =
        packedPayloadBits shape := by
    rw [← hpay, List.take_length]
  simpa [htake] using h

end PackedCellProbe
end SuccinctFinal
end RMQ
