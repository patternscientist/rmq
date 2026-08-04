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

/-! ## The header value is load-bearing for addresses

`FG-11` asks for an inequality whose two sides are a probe **address** or the
returned value, explicitly not the enclosing trace record -- an aggregate trace
inequality can be satisfied by its log alone.

The address side is checkable without an execution, because
`packedSourceFlatOffset` takes the decoded long count as an argument and every
source placed after the long relative table is displaced by
`longCount * packedLongBlockBits n`. That block is never empty, so the map from
long count to address is injective.

This is a genuine value-dependency witness for the address projection. It is *not*
the whole of `FG-11`, and the gap is named precisely below.
-/

theorem packedLongBlockBits_pos (n : Nat) : 0 < packedLongBlockBits n := by
  unfold packedLongBlockBits
  exact Nat.mul_pos (GenericSelect.superStride_pos (2 * n))
    (GenericSelect.wordBits_pos (2 * n))

/--
**Changing only the header count moves the address.** For a source placed after
the long relative table, the flat offset is injective in the decoded long count.
-/
theorem packedSourceFlatOffset_injective_longCount
    (n : Nat) {lc1 lc2 : Nat} (hne : lc1 ≠ lc2) :
    packedSourceFlatOffset n lc1
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence ≠
      packedSourceFlatOffset n lc2
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence := by
  intro heq
  simp only [packedSourceFlatOffset, packedSourceComponentOffset] at heq
  have hpos := packedLongBlockBits_pos n
  have hmul : lc1 * packedLongBlockBits n = lc2 * packedLongBlockBits n := by
    omega
  exact hne (Nat.eq_of_mul_eq_mul_right hpos hmul)

/-- The same, at the bit address the probe plan is computed from. -/
theorem packedStridedBitAddress_injective_longCount
    (n : Nat) {lc1 lc2 : Nat} (index stride : Nat) (hne : lc1 ≠ lc2) :
    packedStridedBitAddress n lc1
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence
        index stride ≠
      packedStridedBitAddress n lc2
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence
        index stride := by
  intro heq
  unfold packedStridedBitAddress at heq
  exact packedSourceFlatOffset_injective_longCount n hne (by omega)

/-! ### Lifting the witness from the bit address to the issued cell

The obvious lift needs `packedCellWidth n <= packedLongBlockBits n`, so that a
one-unit change in the count cannot leave the probe inside the same cell. That
bound is **false**: at `n = 0` it is `10 <= 1` and at `n = 1` it is `14 <= 8`. It
holds from `n = 2` on, but only by evaluation, and a general proof would need an
explicit upper bound on `packedPayloadLength`, which the development supplies only
asymptotically.

The bound is also unnecessary. `FG-11` asks for *a* pinned pair of counts whose
probe address differs, not for every pair, so the difference can be chosen instead
of estimated: separating the two counts by one cell width moves the address by
`packedCellWidth n * packedLongBlockBits n`, which is a whole number of cells by
construction. No inequality between the two quantities is required.
-/

theorem packedStridedBitAddress_step_longCount
    (n lc index stride : Nat) :
    packedStridedBitAddress n (lc + packedCellWidth n)
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence
        index stride =
      packedStridedBitAddress n lc
          ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence
          index stride +
        packedCellWidth n * packedLongBlockBits n := by
  simp only [packedStridedBitAddress, packedSourceFlatOffset,
    packedSourceComponentOffset, Nat.add_mul]
  omega

/--
**Changing only the header count changes the issued probe cell.** Not the bit
address, and not the enclosing trace record: the cell index the plan issues.
-/
theorem packedProbeCell_moves_with_longCount
    (n lc index stride : Nat) :
    packedStridedBitAddress n (lc + packedCellWidth n)
          ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence
          index stride / packedCellWidth n ≠
      packedStridedBitAddress n lc
          ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence
          index stride / packedCellWidth n := by
  have hcw : 0 < packedCellWidth n := packedCellWidth_pos n
  have hblock : 0 < packedLongBlockBits n := packedLongBlockBits_pos n
  have hstep := packedStridedBitAddress_step_longCount n lc index stride
  rw [hstep, Nat.add_mul_div_left _ _ hcw]
  omega

end PackedCellProbe

end SuccinctFinal

end RMQ
