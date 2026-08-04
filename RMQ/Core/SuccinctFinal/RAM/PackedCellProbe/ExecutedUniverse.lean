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

end PackedCellProbe

end SuccinctFinal

end RMQ
