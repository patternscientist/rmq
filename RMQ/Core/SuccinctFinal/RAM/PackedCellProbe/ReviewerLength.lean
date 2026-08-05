import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerPayload

/-!
# The length of the payload the accepted semantics consumes

This module is step one of the `DD-20260804-038` re-target. It gives the exact
bit length of `packedReviewerPayloadBits` as a function of the input size `n` and
the header's `longCount`, and nothing else.

## Why the length needs `longCount`

The flat payload of `Header.lean` is input-size-only because its layout carries
explicit padding fields that absorb every input-dependent variation. The payload
the accepted semantics consumes has no padding: it is

```
bpCode ++ liveAccessPayload ++ interiorDirectory ++ fringeChunkTable ++ selectChunkTable
```

and of its eighteen live access sources, `selectLongRelative` has
`longCount`-many rows. So the exact length is a function of `(n, longCount)`, not
of `n` alone.

That is the `K1` header's purpose rather than a defect. `longCount` is exactly the
one number a controller cannot recompute from `n`, and it is exactly the one
number the header carries. The cell *width* stays input-size-only -- it is derived
from the advertised space bound, not from this exact length -- so cell zero is
readable before `longCount` is known, and everything after it is computable once
the header is decoded.

## The unit-stride hypothesis

The nineteenth source, `selectSparseRelative`, has no size-only row count. Under
`GenericSelect.localStride (2 * n) = 1` it has no rows at all
(`packedSparseExceptionEntries_nil_of_unit_stride`), which is what makes the
length equation exact rather than an inequality.

That hypothesis is not a small-input restriction. `localStride n` is
`max 1 (wordBits n / (ell n * ell n))`, which first exceeds `1` when
`wordBits n >= 98`, i.e. when `n >= 2 ^ 97`. It holds at every size this
development, or any machine, can represent.

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

/-! ### The counted access sources -/

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

/-! ### The length functions -/

/-- Total bits of the counted live access sources at size `n` and header count. -/
def packedReviewerAccessLength (n longCount : Nat) : Nat :=
  (packedReviewerCountedAccessSources.map (packedSourceBitLength n longCount)).sum

/--
The exact bit length of the consumed payload, as a function of the input size and
the one number the `K1` header carries.
-/
def packedReviewerPayloadLength (n longCount : Nat) : Nat :=
  2 * n + packedReviewerAccessLength n longCount +
    SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n +
    SuccinctClose.bpFringeTableOverhead n +
    SuccinctClose.bpChunkSelectTableOverhead n

/-! ### The sparse relative table contributes nothing -/

/--
**The one source without a size-only row count carries no bits at unit stride.**
This is what turns the space *bound* into a length *equation*.
-/
theorem packedSparseRelativePayload_length_of_unit_stride
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
      .selectSparseRelative).length = 0 := by
  have hnil :=
    packedSparseExceptionEntries_nil_of_unit_stride shape.bpCode false hstride
  show
    (GenericSelect.sparseExceptionRelativeTable shape.bpCode
      false).payload.length = 0
  rw [(GenericSelect.sparseExceptionRelativeTable shape.bpCode
    false).payload_length_eq, hnil]
  simp

/-! ### The equations -/

/-- The live access half, summed source by source. -/
theorem packedReviewerAccessLength_eq
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1) :
    (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape).length =
      packedReviewerAccessLength shape.size (longCount shape) := by
  have hsparse := packedSparseRelativePayload_length_of_unit_stride shape hstride
  have e01 := packedSourceBitLength_eq shape .finalRankSuperFalse (by decide)
  have e02 := packedSourceBitLength_eq shape .finalRankBlockFalse (by decide)
  have e03 := packedSourceBitLength_eq shape .selectSuperBaseOccurrence (by decide)
  have e04 := packedSourceBitLength_eq shape .selectSuperBaseWordIndex (by decide)
  have e05 := packedSourceBitLength_eq shape .selectSuperRankBefore (by decide)
  have e06 := packedSourceBitLength_eq shape .selectSuperFirstOffset (by decide)
  have e07 := packedSourceBitLength_eq shape .selectLocalBaseOccurrence (by decide)
  have e08 := packedSourceBitLength_eq shape .selectLocalBaseWordIndex (by decide)
  have e09 := packedSourceBitLength_eq shape .selectLocalRankBefore (by decide)
  have e10 := packedSourceBitLength_eq shape .selectLocalFirstOffset (by decide)
  have e11 := packedSourceBitLength_eq shape .selectLongFlagRankSuperTrue (by decide)
  have e12 := packedSourceBitLength_eq shape .selectLongFlagRankBlockTrue (by decide)
  have e13 := packedSourceBitLength_eq shape .selectLongFlagBits (by decide)
  have e14 := packedSourceBitLength_eq shape .selectLongRelative (by decide)
  have e15 := packedSourceBitLength_eq shape .selectSparseRankSuperTrue (by decide)
  have e16 := packedSourceBitLength_eq shape .selectSparseRankBlockTrue (by decide)
  have e17 := packedSourceBitLength_eq shape .selectSparseFlagBits (by decide)
  unfold concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload
    concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources
    packedReviewerAccessLength packedReviewerCountedAccessSources
  rw [List.length_flatMap]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/--
**The exact length of the consumed payload.** Input size and header count
determine it; nothing else about the shape does.
-/
theorem packedReviewerPayloadBits_length_eq
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1) :
    (packedReviewerPayloadBits shape).length =
      packedReviewerPayloadLength shape.size (longCount shape) := by
  have hbp : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have haccess := packedReviewerAccessLength_eq shape hstride
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
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1) :
    packedReviewerPayloadLength shape.size (longCount shape) <=
      2 * shape.size +
        concreteBPNativeSuccinctRMQCanonicalReviewerOverhead shape.size := by
  have heq := packedReviewerPayloadBits_length_eq shape hstride
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
