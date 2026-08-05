import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerWidth

/-!
# The packed memory over the payload the accepted semantics consumes

Step three of the `DD-20260804-038` re-target: the `K1` header, the serialized bit
string, the cell count, the allocation and the cell array, all over
`packedReviewerPayloadBits`.

## Where `longCount` enters

`packedReviewerCellWidth` is a function of `n` alone, so cell zero is addressable
before anything has been decoded. `packedReviewerCellCount` is a function of
`n`, `longCount`, and the exact sparse-relative count, because the consumed
payload has no padding between those sources and the close tables.

The controller reads cell zero at the size-only width, decodes `longCount`, and
then obtains the sparse count through the charged K1 prelude. The memory builder
uses `packedReviewerSparseCount shape`, the same actual count whose recovery the
controller proves separately. No second header field is introduced.

## What this module does not establish

* The chunking round trip, the aligned/unaligned slice theorems and the
  boundary-crossing codec are not here; those are the rest of `FG-05` and are
  stated over the flat memory in `Memory.lean`.
* Nothing here shows a controller probes these cells. The memory exists and its
  header decodes; that any execution reads it is a separate obligation.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open RMQ.Cartesian

/-! ### The header at the new width -/

theorem packedSize_le_reviewerBound (n : Nat) : n <= packedReviewerCellBound n := by
  unfold packedReviewerCellBound
  omega

theorem longCount_lt_two_pow_reviewerWidth (shape : CartesianShape) :
    longCount shape < 2 ^ packedReviewerCellWidth shape.size := by
  have h1 := longCount_le_superSlots shape
  have h2 := packedSuperSlots_le shape.size
  have h3 := packedReviewerCellBound_lt_two_pow_width shape.size
  have h4 := packedSize_le_reviewerBound shape.size
  omega

/-- The header: `longCount` little-endian in exactly one reviewer-width cell. -/
def packedReviewerHeaderBits (shape : CartesianShape) : List Bool :=
  SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size) (longCount shape)

theorem packedReviewerHeaderBits_length (shape : CartesianShape) :
    (packedReviewerHeaderBits shape).length = packedReviewerCellWidth shape.size :=
  SuccinctSpace.natToBitsLE_length _ _

theorem packedReviewerHeaderBits_decode (shape : CartesianShape) :
    SuccinctSpace.bitsToNatLE (packedReviewerHeaderBits shape) = longCount shape :=
  SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt
    (longCount_lt_two_pow_reviewerWidth shape)

/-! ### Serialized bits -/

def packedReviewerSerializedBits (shape : CartesianShape) : List Bool :=
  packedReviewerHeaderBits shape ++ packedReviewerPayloadBits shape

theorem packedReviewerSerializedBits_length
    (shape : CartesianShape) :
    (packedReviewerSerializedBits shape).length =
      packedReviewerCellWidth shape.size +
        packedReviewerPayloadLength shape.size (longCount shape)
          (packedReviewerSparseCount shape) := by
  unfold packedReviewerSerializedBits
  rw [List.length_append, packedReviewerHeaderBits_length,
    packedReviewerPayloadBits_length_eq shape]

theorem packedReviewerSerializedBits_drop_header (shape : CartesianShape) :
    (packedReviewerSerializedBits shape).drop
        (packedReviewerCellWidth shape.size) =
      packedReviewerPayloadBits shape := by
  unfold packedReviewerSerializedBits
  rw [← packedReviewerHeaderBits_length shape, List.drop_left]

/-! ### Cell count and allocation -/

/--
The allocated cell count: one header cell, then enough to cover the payload.

Unlike the flat count this takes `longCount` and `sparseCount`, because the
consumed payload's exact length does. The header supplies the first; the charged
K1 sparse-rank prelude supplies the second.
-/
def packedReviewerCellCount (n longCount sparseCount : Nat) : Nat :=
  1 + GenericSelect.selectCeilDiv
    (packedReviewerPayloadLength n longCount sparseCount)
    (packedReviewerCellWidth n)

def packedReviewerAllocatedBits (n longCount sparseCount : Nat) : Nat :=
  packedReviewerCellCount n longCount sparseCount * packedReviewerCellWidth n

theorem packedReviewerSerialized_le_allocated (n longCount sparseCount : Nat) :
    packedReviewerCellWidth n +
        packedReviewerPayloadLength n longCount sparseCount <=
      packedReviewerAllocatedBits n longCount sparseCount := by
  have hcover :
      packedReviewerPayloadLength n longCount sparseCount <=
        GenericSelect.selectCeilDiv
            (packedReviewerPayloadLength n longCount sparseCount)
            (packedReviewerCellWidth n) *
          packedReviewerCellWidth n :=
    GenericSelect.selectCeilDiv_mul_ge_of_pos (packedReviewerCellWidth_pos n)
  unfold packedReviewerAllocatedBits packedReviewerCellCount
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-! ### The padded bit string -/

def packedReviewerPaddedBits (shape : CartesianShape) : List Bool :=
  packedReviewerSerializedBits shape ++
    List.replicate
      (packedReviewerAllocatedBits shape.size (longCount shape)
          (packedReviewerSparseCount shape) -
        (packedReviewerSerializedBits shape).length) false

theorem packedReviewerPaddedBits_length
    (shape : CartesianShape) :
    (packedReviewerPaddedBits shape).length =
      packedReviewerAllocatedBits shape.size (longCount shape)
        (packedReviewerSparseCount shape) := by
  have hle :=
    packedReviewerSerialized_le_allocated shape.size (longCount shape)
      (packedReviewerSparseCount shape)
  have hser := packedReviewerSerializedBits_length shape
  unfold packedReviewerPaddedBits
  rw [List.length_append, List.length_replicate]
  omega

/-! ### The memory -/

def packedReviewerMemory (shape : CartesianShape) : List (List Bool) :=
  (List.range (packedReviewerCellCount shape.size (longCount shape)
      (packedReviewerSparseCount shape))).map fun i =>
    ((packedReviewerPaddedBits shape).drop
      (i * packedReviewerCellWidth shape.size)).take
      (packedReviewerCellWidth shape.size)

theorem packedReviewerMemory_length (shape : CartesianShape) :
    (packedReviewerMemory shape).length =
      packedReviewerCellCount shape.size (longCount shape)
        (packedReviewerSparseCount shape) := by
  unfold packedReviewerMemory
  rw [List.length_map, List.length_range]

theorem packedReviewerMemory_cell_length
    (shape : CartesianShape)
    {cell : List Bool}
    (hmem : cell ∈ packedReviewerMemory shape) :
    cell.length = packedReviewerCellWidth shape.size := by
  unfold packedReviewerMemory at hmem
  rw [List.mem_map] at hmem
  obtain ⟨i, hi, hcell⟩ := hmem
  rw [List.mem_range] at hi
  have hpad := packedReviewerPaddedBits_length shape
  have hsucc : i + 1 <=
      packedReviewerCellCount shape.size (longCount shape)
        (packedReviewerSparseCount shape) := hi
  have hmul :=
    Nat.mul_le_mul_right (packedReviewerCellWidth shape.size) hsucc
  have hexp :
      (i + 1) * packedReviewerCellWidth shape.size =
        i * packedReviewerCellWidth shape.size +
          packedReviewerCellWidth shape.size := by
    rw [Nat.add_mul, Nat.one_mul]
  have halloc :
      packedReviewerCellCount shape.size (longCount shape)
          (packedReviewerSparseCount shape) *
          packedReviewerCellWidth shape.size =
        packedReviewerAllocatedBits shape.size (longCount shape)
          (packedReviewerSparseCount shape) := rfl
  rw [← hcell, List.length_take, List.length_drop, hpad]
  omega

/-- The header occupies cell zero exactly. -/
theorem packedReviewerMemory_header_cell (shape : CartesianShape) :
    (packedReviewerMemory shape)[0]? = some (packedReviewerHeaderBits shape) := by
  have hcount :
      0 < packedReviewerCellCount shape.size (longCount shape)
        (packedReviewerSparseCount shape) := by
    unfold packedReviewerCellCount
    omega
  unfold packedReviewerMemory
  rw [List.getElem?_map, List.getElem?_range hcount]
  simp only [Option.map_some, Nat.zero_mul, List.drop_zero]
  congr 1
  unfold packedReviewerPaddedBits packedReviewerSerializedBits
  rw [List.append_assoc, ← packedReviewerHeaderBits_length shape,
    List.take_left]

end PackedCellProbe
end SuccinctFinal
end RMQ
