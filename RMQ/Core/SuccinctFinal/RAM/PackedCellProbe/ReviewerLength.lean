import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerPayload

/-!
# The all-size length of the payload the accepted semantics consumes

This module is step one of the `DD-20260804-038` re-target. It gives the exact
bit length of `packedReviewerPayloadBits` as a function of the input size `n`,
the header's `longCount`, and the sparse-relative entry count recovered by the
reviewer controller.

## Why the length needs two decoded counts

The flat payload of `Header.lean` is input-size-only because its layout carries
explicit padding fields that absorb every input-dependent variation. The payload
the accepted semantics consumes has no padding: it is

```
bpCode ++ liveAccessPayload ++ interiorDirectory ++ fringeChunkTable ++ selectChunkTable
```

and of its eighteen live access sources, `selectLongRelative` has
`longCount`-many rows while `selectSparseRelative` has
`packedReviewerSparseCount shape` rows. The first count is carried by the one-cell
header. The second is the exact length of the sparse-relative entry list and is
recoverable by the charged K1 rank-at-end prelude; it is deliberately not added
to the header.

The cell *width* stays input-size-only -- it is derived from the advertised space
bound, not from either exact count -- so cell zero remains readable before any
decoded count is known.

## What this module does not establish

* No cell, width, address or memory is defined here. This is a bit-length
  equation about a bit string.
* The equation is stated at `packedReviewerPayloadBits`, so it says nothing about
  the flat payload of `Payload.lean`, whose length is unchanged.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open RMQ.Cartesian

/-! ### The access sources and the sparse count -/

/--
The live access sources whose bit length the packed geometry pins exactly: the
canonical reviewer list minus the sparse relative table.
-/
def packedReviewerCountedAccessSources :
    List ConcreteBPNativeSuccinctRMQFlatPayloadSource :=
  [ .finalRankSuperFalse, .finalRankBlockFalse,
    .selectSuperBaseOccurrence, .selectSuperBaseWordIndex,
    .selectSuperRankBefore, .selectSuperFirstOffset,
    .selectLocalBaseOccurrence, .selectLocalBaseWordIndex,
    .selectLocalRankBefore, .selectLocalFirstOffset,
    .selectLongFlagRankSuperTrue, .selectLongFlagRankBlockTrue,
    .selectLongFlagBits, .selectLongRelative,
    .selectSparseRankSuperTrue, .selectSparseRankBlockTrue,
    .selectSparseFlagBits ]

/--
**Drift guard.** This list is exactly the canonical live access list with the
sparse relative table removed, so it cannot silently fall out of step with the
payload it is meant to measure. Editing either list breaks this `rfl`.
-/
theorem packedReviewerCountedAccessSources_eq :
    packedReviewerCountedAccessSources =
      concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources.filter
        (fun source =>
          source !=
            ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative) :=
  rfl

/-- The actual number of fixed-width words in the sparse-relative table. -/
def packedReviewerSparseCount (shape : CartesianShape) : Nat :=
  (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false).length

/--
The exact reviewer-layout bit length of one source.  All source geometries reuse
the existing size/long-count formula except the sparse-relative table, whose
actual word count is supplied explicitly.
-/
def packedReviewerSourceBitLength (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) : Nat :=
  if source =
      ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative then
    sparseCount * packedLocalWidth n
  else
    packedSourceBitLength n longCount source

/-- Every source's actual payload has the reviewer-only exact bit length. -/
theorem packedReviewerSourceBitLength_eq
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length =
      packedReviewerSourceBitLength shape.size (longCount shape)
        (packedReviewerSparseCount shape) source := by
  by_cases hsparse :
      source =
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative
  · subst source
    have hbp : shape.bpCode.length = 2 * shape.size :=
      CartesianShape.bpCode_length shape
    have hwidth :
        GenericSelect.sparseExceptionRelativeWidth shape.bpCode =
          packedLocalWidth shape.size := by
      unfold GenericSelect.sparseExceptionRelativeWidth packedLocalWidth
      rw [hbp]
    change
      (GenericSelect.sparseExceptionRelativeTable shape.bpCode false).payload.length =
        packedReviewerSourceBitLength shape.size (longCount shape)
          (packedReviewerSparseCount shape) .selectSparseRelative
    rw [GenericSelect.sparseExceptionRelativeTable_payload_length]
    simp [packedReviewerSourceBitLength, packedReviewerSparseCount, hwidth]
  · rw [packedSourceBitLength_eq shape source (by simp [hsparse])]
    simp [packedReviewerSourceBitLength, hsparse]

/-! ### The length functions -/

/-- Total bits of all live access sources at the three all-size geometry inputs. -/
def packedReviewerAccessLength (n longCount sparseCount : Nat) : Nat :=
  (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources.map
    (packedReviewerSourceBitLength n longCount sparseCount)).sum

/--
The exact bit length of the consumed payload, as a function of the input size,
the `longCount` carried by the `K1` header, and the `sparseCount` recovered by
the fixed charged prelude.
-/
def packedReviewerPayloadLength (n longCount sparseCount : Nat) : Nat :=
  2 * n + packedReviewerAccessLength n longCount sparseCount +
    SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n +
    SuccinctClose.bpFringeTableOverhead n +
    SuccinctClose.bpChunkSelectTableOverhead n

/-! ### The equations -/

/-- The live access half, summed source by source. -/
theorem packedReviewerAccessLength_eq
    (shape : CartesianShape) :
    (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape).length =
      packedReviewerAccessLength shape.size (longCount shape)
        (packedReviewerSparseCount shape) := by
  unfold concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload
    packedReviewerAccessLength
  rw [List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro source _hmem
  exact packedReviewerSourceBitLength_eq shape source

/--
**The exact length of the consumed payload.** Once the header and fixed prelude
have decoded the two counts, no further information about the shape is needed.
-/
theorem packedReviewerPayloadBits_length_eq
    (shape : CartesianShape) :
    (packedReviewerPayloadBits shape).length =
      packedReviewerPayloadLength shape.size (longCount shape)
        (packedReviewerSparseCount shape) := by
  have hbp : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have haccess := packedReviewerAccessLength_eq shape
  have hclose :=
    SuccinctClose.canonicalRelativeRmmInteriorDirectory_payload_length_eq_raw shape
  have hfringe :
      (SuccinctClose.bpFringeChunkTable
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload.length =
        SuccinctClose.bpFringeTableOverhead shape.size := by
    rw [hbp]
    exact SuccinctClose.bpFringeChunkTable_payload_length _
  have hselect :
      (SuccinctClose.bpChunkSelectTable
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        false).payload.length =
        SuccinctClose.bpChunkSelectTableOverhead shape.size := by
    rw [hbp]
    exact SuccinctClose.bpChunkSelectTable_payload_length _ false
  unfold packedReviewerPayloadBits packedReviewerPayloadLength
  simp only [concreteBPNativeSuccinctRMQCanonicalReviewerPayload,
    concreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout,
    List.length_append]
  omega

/--
**The exact length never exceeds the advertised size-only bound.** This is the
clause the packed cell width will be derived from: the width may not depend on
`longCount`, because cell zero must be readable before the header is decoded.
-/
theorem packedReviewerPayloadLength_le_bound
    (shape : CartesianShape) :
    packedReviewerPayloadLength shape.size (longCount shape)
        (packedReviewerSparseCount shape) <=
      2 * shape.size +
        concreteBPNativeSuccinctRMQCanonicalReviewerOverhead shape.size := by
  have heq := packedReviewerPayloadBits_length_eq shape
  have hle :=
    packedReviewerPayloadBits_length_le (mem_shapesOfSize_size shape)
  omega

/-! ### The consumed object is the executed one

Recorded here so the re-target's premise is checkable in the same module as the
length it justifies, rather than resting on a reading of the row text.
-/

/--
**The store the accepted semantics executes against is the reviewer store.** The
repository proves the two are the same object; combined with
`packedReviewerPayloadBits_eq_buildPayload` this is what identifies the payload
measured above as the consumed one.
-/
theorem packedExecutedStore_is_reviewerStore
    (shape : CartesianShape) (segment index : Nat) :
    (concreteBPNativeSuccinctRMQCanonicalReviewerReadStore shape).readWord?
        segment index =
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index :=
  concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global shape
    segment index

end PackedCellProbe

end SuccinctFinal

end RMQ
