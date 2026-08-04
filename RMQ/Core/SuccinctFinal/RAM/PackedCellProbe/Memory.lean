import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Header

/-!
# The packed memory

This module works towards `EG-CP` falsification row `FG-05-PACKED-MEMORY`.

`packedMemory` is the one object the packed controller is allowed to probe:
consecutive `w n`-bit cells of `headerBits ++ payloadBits`, with zero padding in
the final cell only.

The chunker here is a `List.range` map rather than the repository's fuel-based
`chunkPayloadWords`, because that chunker leaves a short final word and this
representation must allocate whole cells. The difference is exactly the padding
the space row has to charge for, so it is made explicit rather than hidden.

## What this module does not establish

* No controller exists, so nothing here shows that these cells are the cells a
  query probes.
* Slices of a source's bits across a cell boundary are not yet related to the
  source's logical word; that is the `FG-08` lowering obligation.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-! ### Serialized bits -/

/-- The header cell followed by the canonical payload. -/
def packedSerializedBits (shape : CartesianShape) : List Bool :=
  packedHeaderBits shape ++
    (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload

theorem packedSerializedBits_length (shape : CartesianShape) :
    (packedSerializedBits shape).length =
      packedCellWidth shape.size + packedPayloadLength shape.size := by
  unfold packedSerializedBits
  rw [List.length_append, packedHeaderBits_length, packedPayloadLength_eq]

/-! ### Cell count and allocation -/

/--
The number of allocated cells: one for the header, then enough to cover the
payload.
-/
def packedCellCount (n : Nat) : Nat :=
  1 + GenericSelect.selectCeilDiv (packedPayloadLength n) (packedCellWidth n)

/-- Allocated bits: every cell counted at full width, padding included. -/
def packedAllocatedBits (n : Nat) : Nat :=
  packedCellCount n * packedCellWidth n

/-- The serialized bits fit inside the allocation. -/
theorem packedSerialized_le_allocated (n : Nat) :
    packedCellWidth n + packedPayloadLength n <= packedAllocatedBits n := by
  have hcover :
      packedPayloadLength n <=
        GenericSelect.selectCeilDiv (packedPayloadLength n) (packedCellWidth n) *
          packedCellWidth n :=
    GenericSelect.selectCeilDiv_mul_ge_of_pos (packedCellWidth_pos n)
  unfold packedAllocatedBits packedCellCount
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-! ### The padded bit string -/

/-- Serialized bits extended with zeros to exactly the allocated width. -/
def packedPaddedBits (shape : CartesianShape) : List Bool :=
  packedSerializedBits shape ++
    List.replicate
      (packedAllocatedBits shape.size - (packedSerializedBits shape).length) false

theorem packedPaddedBits_length (shape : CartesianShape) :
    (packedPaddedBits shape).length = packedAllocatedBits shape.size := by
  have hle := packedSerialized_le_allocated shape.size
  have hser := packedSerializedBits_length shape
  unfold packedPaddedBits
  rw [List.length_append, List.length_replicate]
  omega

/-! ### The memory -/

/--
`packedMemory shape` is the allocated cell array: `packedCellCount` cells, each an
exactly `w`-bit slice of the padded bit string.
-/
def packedMemory (shape : CartesianShape) : List (List Bool) :=
  (List.range (packedCellCount shape.size)).map fun i =>
    ((packedPaddedBits shape).drop (i * packedCellWidth shape.size)).take
      (packedCellWidth shape.size)

theorem packedMemory_length (shape : CartesianShape) :
    (packedMemory shape).length = packedCellCount shape.size := by
  unfold packedMemory
  rw [List.length_map, List.length_range]

/-- Every allocated cell is exactly one full width; none is short. -/
theorem packedMemory_cell_length
    (shape : CartesianShape) {cell : List Bool}
    (hmem : cell ∈ packedMemory shape) :
    cell.length = packedCellWidth shape.size := by
  unfold packedMemory at hmem
  rw [List.mem_map] at hmem
  obtain ⟨i, hi, hcell⟩ := hmem
  rw [List.mem_range] at hi
  have hpad := packedPaddedBits_length shape
  have hbound :
      i * packedCellWidth shape.size + packedCellWidth shape.size <=
        packedAllocatedBits shape.size := by
    unfold packedAllocatedBits
    have : i + 1 <= packedCellCount shape.size := hi
    calc
      i * packedCellWidth shape.size + packedCellWidth shape.size
          = (i + 1) * packedCellWidth shape.size := by rw [Nat.add_mul, Nat.one_mul]
      _ <= packedCellCount shape.size * packedCellWidth shape.size :=
          Nat.mul_le_mul_right _ this
  rw [← hcell, List.length_take, List.length_drop]
  omega

/-- **The header is cell zero, in full.** -/
theorem packedMemory_cell_zero (shape : CartesianShape) :
    (packedMemory shape)[0]? = some (packedHeaderBits shape) := by
  have hcount : 0 < packedCellCount shape.size := by
    unfold packedCellCount
    omega
  have hlen := packedHeaderBits_length shape
  unfold packedMemory packedPaddedBits packedSerializedBits
  rw [List.getElem?_map]
  simp only [List.getElem?_range hcount, Option.map_some, Option.some.injEq,
    Nat.zero_mul, List.drop_zero, List.append_assoc]
  rw [← hlen]
  simp

end PackedCellProbe
end SuccinctFinal
end RMQ
