import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.PhysicalRead

/-!
# The executed store is a different segment universe from segment 20 up

`PhysicalRead` lowers every logical read of
`concreteBPNativeSuccinctRMQFlatPayloadReadStore` to a probe of `packedMemory`.
That is the store the **flat payload** describes. It is not the store the
whole-query evaluator runs against.

This module records the difference as checked theorems rather than as a note,
because the matrix's `FG-08` clause (c) previously described it as a *numbering*
difference at segments 21 and 22, and it is not: from segment 20 up the two
stores read different objects, and the objects the executed store reads at 20, 21
and 22 are not sources of the flat payload at all.

Every theorem below is `rfl` against the two store definitions, composed with the
pre-existing `concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global`.

The consequence for the campaign is stated exactly in `DD-20260804-027`: the
per-read lowering covers global segments `0` through `19` and no more, so
`packedMemory` as built over the `FG-01` payload object cannot answer the
executed close route. This is not a `K1` question -- the header cell is not
involved -- and it is therefore recorded as a gap rather than reported as an
obstruction.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open Cartesian

/-! ## Where the two universes agree

Segments `0` .. `19` are the BP code, the select tables and the final rank
samples, and the executed store reads them from the flat payload's own sources.
One representative and the two ends are enough to fix the convention.
-/

theorem packedExecutedStore_bpCodeSegment
    (shape : CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 index =
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? 0
        index := by
  rw [← concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global]
  rfl

theorem packedExecutedStore_sparseRelativeSegment
    (shape : CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 16 index =
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? 16
        index := by
  rw [← concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global]
  rfl

theorem packedExecutedStore_finalRankAliasSegment
    (shape : CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 19 index =
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? 19
        index := by
  rw [← concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global]
  rfl

/-! ## Where they diverge

Segment `20` is the whole canonical interior component in the executed store and
the close summary's baseline column in the flat store. Segments `21` and `22` are
the two charged chunk tables in the executed store and two more summary columns in
the flat store. From segment `23` on the executed store is silent while the flat
store still answers.
-/

theorem packedExecutedStore_interiorComponentSegment
    (shape : CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20 index =
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words[index]? := by
  rw [← concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global]
  rfl

theorem packedFlatStore_interiorComponentSegment
    (shape : CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? 20 index =
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .closeSummaryBaseline)[index]? :=
  rfl

theorem packedExecutedStore_fringeChunkSegment
    (shape : CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21 index =
      (SuccinctClose.bpFringeChunkTable
        (SuccinctClose.bpFringeChunkBits
          shape.bpCode.length)).store.words[index]? := by
  rw [← concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global]
  rfl

theorem packedFlatStore_fringeChunkSegment
    (shape : CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? 21 index =
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .closeSummaryMinRel)[index]? :=
  rfl

theorem packedExecutedStore_selectChunkSegment
    (shape : CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 22 index =
      (SuccinctClose.bpChunkSelectTable
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        false).store.words[index]? := by
  rw [← concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global]
  rfl

theorem packedFlatStore_selectChunkSegment
    (shape : CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? 22 index =
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .closeSummaryMaxRel)[index]? :=
  rfl

/-- From segment `23` on the executed store answers nothing. -/
theorem packedExecutedStore_silent_from_twentyThree
    (shape : CartesianShape) (index offset : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? (23 + offset)
        index = none := by
  rw [← concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global]
  have hlt : ¬ (23 + offset < 20) := by omega
  have h20 : 23 + offset ≠ 20 := by omega
  have h21 : 23 + offset ≠ 21 := by omega
  have h22 : 23 + offset ≠ 22 := by omega
  simp [concreteBPNativeSuccinctRMQCanonicalReviewerReadStore,
    concreteBPNativeInteriorTraceSegments,
    concreteBPNativeFringeChunkTraceSegment,
    concreteBPNativeSelectChunkTraceSegment, hlt, h20, h21, h22]

/-- The flat store, by contrast, still answers there. -/
theorem packedFlatStore_answers_at_twentyThree
    (shape : CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? 23 index =
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .closeSummaryArgOffset)[index]? :=
  rfl

/-! ## The two universes give different *answers*, not just different definitions

Everything above is `rfl`: it shows the two stores are defined by different
expressions from segment 20 up. That alone would leave room for a bridge -- two
definitions can agree pointwise.

This section closes that room. Whenever the close summary is active with at least
one block, the flat payload store **answers** at segment 23 and the executed store
**does not**. So no bridge exists, and the per-read lowering of `PhysicalRead.lean`
cannot be extended past executed segment 19 by finding one.

The hypothesis is the ordinary case rather than a contrivance: it is exactly the
condition under which the close summary carries any data at all.
-/

theorem packedStoresDisagree_atSegmentTwentyThree
    (shape : CartesianShape)
    (hpos : 0 < packedSummaryBlockCount shape.size) :
    (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? 23 0 ≠
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 23 0 := by
  have hglobal :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 23 0 = none := by
    have h := packedExecutedStore_silent_from_twentyThree shape 0 0
    simpa using h
  have hflat :
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? 23 0 =
        packedWordSlice
          (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
            .closeSummaryArgOffset)
          (packedSummaryBlockCount shape.size)
          (packedSummaryRelativeWidth shape.size) 0 := by
    rw [packedFlatStore_answers_at_twentyThree shape 0]
    exact packedCloseSummaryArgOffsetWords shape 0
  rw [hglobal, hflat, packedWordSlice_of_lt hpos]
  exact fun h => Option.noConfusion h

/--
**The stores are not equal.** Stated on the stores themselves rather than at one
address, so it cannot be read as an artefact of the chosen index.
-/
theorem packedStoresNotEqual
    (shape : CartesianShape)
    (hpos : 0 < packedSummaryBlockCount shape.size) :
    concreteBPNativeSuccinctRMQFlatPayloadReadStore shape ≠
      concreteBPNativeSuccinctRMQGlobalReadStore shape := by
  intro heq
  exact packedStoresDisagree_atSegmentTwentyThree shape hpos (by rw [heq])

end PackedCellProbe

end SuccinctFinal

end RMQ
