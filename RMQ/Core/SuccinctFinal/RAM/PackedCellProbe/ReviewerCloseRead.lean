import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerCloseWidth

/-!
# Reading the close half's chunk tables by probing

Segments `21` (fringe chunk table) and `22` (select chunk table) are the two close
segments that *are* uniform word grids, by `packedReviewerFringeChunkWords` and
`packedReviewerSelectChunkWords`. This module gives them shape-free offsets into the
consumed payload and lowers their reads to the conditional probe plan.

## Why these two are simpler than the live access sources

Both are `FixedWidthNatTable`s whose payload length is exactly
`entries.length * width`. So an in-range read is a **full**-width window: there is no
partial final word, and no counterpart of the sparse relative table's capacity gap.
The read width is therefore the entry width itself rather than a `min`, and the
lowering is an equation on successful reads rather than needing the width to be
recomputed from the actual payload.

## Offsets

The consumed payload is `bpCode ++ access ++ interior ++ fringe ++ selectChunk`, so
the two offsets are the summed lengths of everything earlier. Each of those lengths
is a size-only function -- `canonicalRelativeRmmInteriorRawPayloadOverhead` and
`bpFringeTableOverhead` -- except the access half, which additionally takes the
header's `longCount`. That is the same dependency the access half's own offsets
have, and the same one the cell count has.

## What this module does not establish

Segment `20`. The interior component store is not a uniform grid
(`ReviewerCloseGeometry`), so it has neither a single entry width nor a single word
count, and its read is a separate obligation.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open RMQ.Cartesian

/-! ### The offsets -/

/-- The bit offset of the close half inside the consumed payload. -/
def packedReviewerCloseOffset (n longCount : Nat) : Nat :=
  2 * n + packedReviewerAccessLength n longCount

/-- The bit offset of the fringe chunk table. -/
def packedReviewerFringeOffset (n longCount : Nat) : Nat :=
  packedReviewerCloseOffset n longCount +
    SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n

/-- The bit offset of the select chunk table. -/
def packedReviewerSelectChunkOffset (n longCount : Nat) : Nat :=
  packedReviewerFringeOffset n longCount + SuccinctClose.bpFringeTableOverhead n

/-- The shape-facing close offset is the shape-free one. -/
theorem packedReviewerCloseBitOffset_eq
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1) :
    concreteBPNativeSuccinctRMQCanonicalReviewerCloseBitOffset shape =
      packedReviewerCloseOffset shape.size (longCount shape) := by
  have hbp : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have haccess := packedReviewerAccessLength_eq shape hstride
  show
    shape.bpCode.length +
        (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload
          shape).length =
      packedReviewerCloseOffset shape.size (longCount shape)
  unfold packedReviewerCloseOffset
  omega

/-! ### What each offset drops to -/

/-- Past the fringe offset, the payload is the fringe table then the select table. -/
theorem packedReviewerPayload_drop_fringeOffset
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1) :
    (packedReviewerPayloadBits shape).drop
        (packedReviewerFringeOffset shape.size (longCount shape)) =
      (SuccinctClose.bpFringeChunkTable
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload ++
        (SuccinctClose.bpChunkSelectTable
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).payload := by
  have hinterior :=
    SuccinctClose.canonicalRelativeRmmInteriorDirectory_payload_length_eq_raw shape
  have hclose := packedReviewerCloseBitOffset_eq shape hstride
  have hsplit :
      packedReviewerFringeOffset shape.size (longCount shape) =
        packedReviewerCloseOffset shape.size (longCount shape) +
          (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload.length := by
    unfold packedReviewerFringeOffset
    omega
  rw [hsplit, ← hclose, ← List.drop_drop,
    packedReviewerPayload_drop_closeOffset shape,
    show
        (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload ++
            (SuccinctClose.bpFringeChunkTable
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload ++
              (SuccinctClose.bpChunkSelectTable
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
                false).payload =
          (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload ++
            ((SuccinctClose.bpFringeChunkTable
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload ++
              (SuccinctClose.bpChunkSelectTable
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
                false).payload) by
      simp [List.append_assoc]]
  exact List.drop_left

/-- Past the select chunk offset, the payload is exactly the select chunk table. -/
theorem packedReviewerPayload_drop_selectChunkOffset
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1) :
    (packedReviewerPayloadBits shape).drop
        (packedReviewerSelectChunkOffset shape.size (longCount shape)) =
      (SuccinctClose.bpChunkSelectTable
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).payload := by
  have hbp : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have hfringe :
      (SuccinctClose.bpFringeChunkTable
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload.length =
        SuccinctClose.bpFringeTableOverhead shape.size := by
    rw [hbp]
    exact SuccinctClose.bpFringeChunkTable_payload_length _
  have hsplit :
      packedReviewerSelectChunkOffset shape.size (longCount shape) =
        packedReviewerFringeOffset shape.size (longCount shape) +
          (SuccinctClose.bpFringeChunkTable
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload.length := by
    unfold packedReviewerSelectChunkOffset
    omega
  rw [hsplit, ← List.drop_drop,
    packedReviewerPayload_drop_fringeOffset shape hstride]
  exact List.drop_left

/-! ### Slices -/

theorem packedReviewerPayload_fringeSlice
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1)
    {off len : Nat}
    (h :
      off + len <=
        (SuccinctClose.bpFringeChunkTable
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload.length) :
    ((packedReviewerPayloadBits shape).drop
        (packedReviewerFringeOffset shape.size (longCount shape) + off)).take len =
      (((SuccinctClose.bpFringeChunkTable
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload).drop
        off).take len := by
  rw [← List.drop_drop, packedReviewerPayload_drop_fringeOffset shape hstride]
  exact packedPrefixSlice _ _ h

theorem packedReviewerPayload_selectChunkSlice
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1)
    (off len : Nat) :
    ((packedReviewerPayloadBits shape).drop
        (packedReviewerSelectChunkOffset shape.size (longCount shape) +
          off)).take len =
      (((SuccinctClose.bpChunkSelectTable
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).payload).drop
        off).take len := by
  rw [← List.drop_drop,
    packedReviewerPayload_drop_selectChunkOffset shape hstride]

/-! ### The tables end inside the payload -/

theorem packedReviewerFringeOffset_fits (n longCount : Nat) :
    packedReviewerFringeOffset n longCount +
        SuccinctClose.bpFringeTableOverhead n <=
      packedReviewerPayloadLength n longCount := by
  unfold packedReviewerFringeOffset packedReviewerCloseOffset
    packedReviewerPayloadLength
  omega

theorem packedReviewerSelectChunkOffset_fits (n longCount : Nat) :
    packedReviewerSelectChunkOffset n longCount +
        SuccinctClose.bpChunkSelectTableOverhead n <=
      packedReviewerPayloadLength n longCount := by
  unfold packedReviewerSelectChunkOffset packedReviewerFringeOffset
    packedReviewerCloseOffset packedReviewerPayloadLength
  omega

/-! ### The reads -/

/-- The fringe chunk table's entry width, as a function of the input size. -/
def packedReviewerFringeWidth (n : Nat) : Nat :=
  SuccinctClose.bpFringeChunkEntryWidth (SuccinctClose.bpFringeChunkBits (2 * n))

/-- The fringe chunk table's row count, as a function of the input size. -/
def packedReviewerFringeCount (n : Nat) : Nat :=
  SuccinctClose.bpFringeChunkRowCount (SuccinctClose.bpFringeChunkBits (2 * n))

/-- The select chunk table's entry width, as a function of the input size. -/
def packedReviewerSelectChunkWidth (n : Nat) : Nat :=
  SuccinctClose.bpChunkSelectEntryWidth (SuccinctClose.bpFringeChunkBits (2 * n))

/-- The select chunk table's row count, as a function of the input size. -/
def packedReviewerSelectChunkCount (n : Nat) : Nat :=
  SuccinctClose.bpChunkSelectRowCount (SuccinctClose.bpFringeChunkBits (2 * n))

def packedReviewerFringeAddress (n longCount index : Nat) : Nat :=
  packedReviewerCellWidth n + packedReviewerFringeOffset n longCount +
    index * packedReviewerFringeWidth n

def packedReviewerSelectChunkAddress (n longCount index : Nat) : Nat :=
  packedReviewerCellWidth n + packedReviewerSelectChunkOffset n longCount +
    index * packedReviewerSelectChunkWidth n

/-- One fringe chunk word, answered by probing the reviewer memory. -/
def packedReviewerFringeRead (n longCount : Nat) (memory : List (List Bool))
    (index : Nat) : Option (List Bool) :=
  if index < packedReviewerFringeCount n then
    (packedFetch memory
        (packedReviewerProbePlan n (packedReviewerFringeAddress n longCount index)
          (packedReviewerFringeWidth n))).map
      (packedReviewerDecodeSpan n (packedReviewerFringeAddress n longCount index)
        (packedReviewerFringeWidth n))
  else
    none

/-- One select chunk word, answered by probing the reviewer memory. -/
def packedReviewerSelectChunkRead (n longCount : Nat) (memory : List (List Bool))
    (index : Nat) : Option (List Bool) :=
  if index < packedReviewerSelectChunkCount n then
    (packedFetch memory
        (packedReviewerProbePlan n
          (packedReviewerSelectChunkAddress n longCount index)
          (packedReviewerSelectChunkWidth n))).map
      (packedReviewerDecodeSpan n
        (packedReviewerSelectChunkAddress n longCount index)
        (packedReviewerSelectChunkWidth n))
  else
    none

theorem packedReviewerFringeReadPlan_length_le_two (n longCount index : Nat) :
    (packedReviewerProbePlan n (packedReviewerFringeAddress n longCount index)
        (packedReviewerFringeWidth n)).length <= 2 :=
  packedReviewerProbeCount_le_two _ _ _

theorem packedReviewerSelectChunkReadPlan_length_le_two (n longCount index : Nat) :
    (packedReviewerProbePlan n
        (packedReviewerSelectChunkAddress n longCount index)
        (packedReviewerSelectChunkWidth n)).length <= 2 :=
  packedReviewerProbeCount_le_two _ _ _

/-! ### The lowering

Neither proof rewrites the entry width anywhere near its table. `FixedWidthNatTable`
takes the width as a **type index**, so `bpFringeChunkTable c` has a type mentioning
`bpFringeChunkEntryWidth c`; rewriting that width inside any term containing the
table makes the rewrite motive ill-typed. The size-only width therefore appears only
in the goal -- where no table occurs -- and the word equation is obtained by
transitivity rather than by rewriting a hypothesis.
-/

set_option maxHeartbeats 800000 in
/--
**Segment 21 lowers.** Every successful fringe chunk word read of the executed store
is answered identically by probing the reviewer memory.
-/
theorem packedReviewerFringeRead_of_some
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1)
    {index : Nat} {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21 index =
        some word) :
    packedReviewerFringeRead shape.size (longCount shape)
        (packedReviewerMemory shape) index =
      some word := by
  have hbp : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have hwidth :
      packedReviewerFringeWidth shape.size =
        SuccinctClose.bpFringeChunkEntryWidth
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) := by
    unfold packedReviewerFringeWidth
    rw [hbp]
  have hcount :
      packedReviewerFringeCount shape.size =
        (SuccinctClose.bpFringeChunkEntries
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).length := by
    unfold packedReviewerFringeCount
    rw [hbp, SuccinctClose.bpFringeChunkEntries_length]
  have hwords := packedReviewerFringeChunkWords shape index
  rw [hread] at hwords
  have hlt : index < packedReviewerFringeCount shape.size := by
    by_cases h : index < packedReviewerFringeCount shape.size
    · exact h
    · rw [packedWordSlice_of_le (by omega)] at hwords
      exact absurd hwords.symm (by simp)
  have hlt' :
      index <
        (SuccinctClose.bpFringeChunkEntries
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).length := by
    omega
  have hword := Option.some.inj (hwords.trans (packedWordSlice_of_lt hlt'))
  -- the read window ends inside the table
  have hplen :=
    (SuccinctClose.bpFringeChunkTable
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload_length_eq
  have hmul :
      (index + 1) *
          SuccinctClose.bpFringeChunkEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) <=
        (SuccinctClose.bpFringeChunkEntries
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).length *
          SuccinctClose.bpFringeChunkEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) :=
    Nat.mul_le_mul_right _ hlt'
  have hexp :
      (index + 1) *
          SuccinctClose.bpFringeChunkEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) =
        index *
            SuccinctClose.bpFringeChunkEntryWidth
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length) +
          SuccinctClose.bpFringeChunkEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) := by
    rw [Nat.add_mul, Nat.one_mul]
  have hinside :
      index *
            SuccinctClose.bpFringeChunkEntryWidth
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length) +
          SuccinctClose.bpFringeChunkEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) <=
        (SuccinctClose.bpFringeChunkTable
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload.length := by
    omega
  have hoverhead :
      (SuccinctClose.bpFringeChunkTable
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload.length =
        SuccinctClose.bpFringeTableOverhead shape.size := by
    rw [hbp]
    exact SuccinctClose.bpFringeChunkTable_payload_length _
  have hfitpay := packedReviewerFringeOffset_fits shape.size (longCount shape)
  have hfit2 :
      packedReviewerFringeOffset shape.size (longCount shape) +
            index *
              SuccinctClose.bpFringeChunkEntryWidth
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length) +
          SuccinctClose.bpFringeChunkEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) <=
        packedReviewerPayloadLength shape.size (longCount shape) := by
    omega
  have hserial :=
    packedReviewerSerialized_le_allocated shape.size (longCount shape)
  have hfitalloc :
      packedReviewerCellWidth shape.size +
              packedReviewerFringeOffset shape.size (longCount shape) +
            index *
              SuccinctClose.bpFringeChunkEntryWidth
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length) +
          SuccinctClose.bpFringeChunkEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) <=
        packedReviewerAllocatedBits shape.size (longCount shape) := by
    omega
  have hwle :
      SuccinctClose.bpFringeChunkEntryWidth
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) <=
        packedReviewerCellWidth shape.size := by
    rw [← hwidth]
    exact packedFringeEntryWidth_le_reviewerCellWidth shape.size
  have hdecode := packedReviewerProbePlan_decode shape hwle hfitalloc
  have haddr :
      packedReviewerCellWidth shape.size +
            packedReviewerFringeOffset shape.size (longCount shape) +
          index *
            SuccinctClose.bpFringeChunkEntryWidth
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length) =
        packedReviewerCellWidth shape.size +
          (packedReviewerFringeOffset shape.size (longCount shape) +
            index *
              SuccinctClose.bpFringeChunkEntryWidth
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length)) := by
    omega
  have hpadslice :=
    packedReviewerPayloadSlice shape hstride
      (packedReviewerFringeOffset shape.size (longCount shape) +
        index *
          SuccinctClose.bpFringeChunkEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length))
      (SuccinctClose.bpFringeChunkEntryWidth
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)) hfit2
  have hfringeslice :=
    packedReviewerPayload_fringeSlice shape hstride
      (off :=
        index *
          SuccinctClose.bpFringeChunkEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length))
      (len :=
        SuccinctClose.bpFringeChunkEntryWidth
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)) hinside
  unfold packedReviewerFringeRead packedReviewerFringeAddress
  rw [hwidth, if_pos hlt, hdecode, haddr, hpadslice, hfringeslice, ← hword]

set_option maxHeartbeats 800000 in
/--
**Segment 22 lowers.** Every successful select chunk word read of the executed store
is answered identically by probing the reviewer memory.
-/
theorem packedReviewerSelectChunkRead_of_some
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1)
    {index : Nat} {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 22 index =
        some word) :
    packedReviewerSelectChunkRead shape.size (longCount shape)
        (packedReviewerMemory shape) index =
      some word := by
  have hbp : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have hwidth :
      packedReviewerSelectChunkWidth shape.size =
        SuccinctClose.bpChunkSelectEntryWidth
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) := by
    unfold packedReviewerSelectChunkWidth
    rw [hbp]
  have hcount :
      packedReviewerSelectChunkCount shape.size =
        (SuccinctClose.bpChunkSelectEntries
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).length := by
    unfold packedReviewerSelectChunkCount
    rw [hbp, SuccinctClose.bpChunkSelectEntries_length]
  have hwords := packedReviewerSelectChunkWords shape index
  rw [hread] at hwords
  have hlt : index < packedReviewerSelectChunkCount shape.size := by
    by_cases h : index < packedReviewerSelectChunkCount shape.size
    · exact h
    · rw [packedWordSlice_of_le (by omega)] at hwords
      exact absurd hwords.symm (by simp)
  have hlt' :
      index <
        (SuccinctClose.bpChunkSelectEntries
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).length := by
    omega
  have hword := Option.some.inj (hwords.trans (packedWordSlice_of_lt hlt'))
  have hplen :=
    (SuccinctClose.bpChunkSelectTable
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).payload_length_eq
  have hmul :
      (index + 1) *
          SuccinctClose.bpChunkSelectEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) <=
        (SuccinctClose.bpChunkSelectEntries
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).length *
          SuccinctClose.bpChunkSelectEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) :=
    Nat.mul_le_mul_right _ hlt'
  have hexp :
      (index + 1) *
          SuccinctClose.bpChunkSelectEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) =
        index *
            SuccinctClose.bpChunkSelectEntryWidth
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length) +
          SuccinctClose.bpChunkSelectEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) := by
    rw [Nat.add_mul, Nat.one_mul]
  have hoverhead :
      (SuccinctClose.bpChunkSelectTable
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        false).payload.length =
        SuccinctClose.bpChunkSelectTableOverhead shape.size := by
    rw [hbp]
    exact SuccinctClose.bpChunkSelectTable_payload_length _ false
  have hfitpay :=
    packedReviewerSelectChunkOffset_fits shape.size (longCount shape)
  have hfit2 :
      packedReviewerSelectChunkOffset shape.size (longCount shape) +
            index *
              SuccinctClose.bpChunkSelectEntryWidth
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length) +
          SuccinctClose.bpChunkSelectEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) <=
        packedReviewerPayloadLength shape.size (longCount shape) := by
    omega
  have hserial :=
    packedReviewerSerialized_le_allocated shape.size (longCount shape)
  have hfitalloc :
      packedReviewerCellWidth shape.size +
              packedReviewerSelectChunkOffset shape.size (longCount shape) +
            index *
              SuccinctClose.bpChunkSelectEntryWidth
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length) +
          SuccinctClose.bpChunkSelectEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) <=
        packedReviewerAllocatedBits shape.size (longCount shape) := by
    omega
  have hwle :
      SuccinctClose.bpChunkSelectEntryWidth
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) <=
        packedReviewerCellWidth shape.size := by
    rw [← hwidth]
    exact packedSelectChunkEntryWidth_le_reviewerCellWidth shape.size
  have hdecode := packedReviewerProbePlan_decode shape hwle hfitalloc
  have haddr :
      packedReviewerCellWidth shape.size +
            packedReviewerSelectChunkOffset shape.size (longCount shape) +
          index *
            SuccinctClose.bpChunkSelectEntryWidth
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length) =
        packedReviewerCellWidth shape.size +
          (packedReviewerSelectChunkOffset shape.size (longCount shape) +
            index *
              SuccinctClose.bpChunkSelectEntryWidth
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length)) := by
    omega
  have hpadslice :=
    packedReviewerPayloadSlice shape hstride
      (packedReviewerSelectChunkOffset shape.size (longCount shape) +
        index *
          SuccinctClose.bpChunkSelectEntryWidth
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length))
      (SuccinctClose.bpChunkSelectEntryWidth
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)) hfit2
  have hselectslice :=
    packedReviewerPayload_selectChunkSlice shape hstride
      (index *
        SuccinctClose.bpChunkSelectEntryWidth
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length))
      (SuccinctClose.bpChunkSelectEntryWidth
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length))
  unfold packedReviewerSelectChunkRead packedReviewerSelectChunkAddress
  rw [hwidth, if_pos hlt, hdecode, haddr, hpadslice, hselectslice, ← hword]

end PackedCellProbe

end SuccinctFinal

end RMQ
