import RMQ.Core.SuccinctFinal.RAM.FlatPayload

/-!
# K1 source factorization for the packed cell-probe representation

This module works towards `EG-CP` falsification rows `FG-02-K1-SOURCE-FACTORIZATION`
and `FG-03-SPARSE-COUNT-ELIMINATION`.

The question both rows ask is whether the flat-payload addressing of
`RMQ/Core/SuccinctFinal/RAM/FlatPayload.lean` can be recomputed by a controller
that never sees a `CartesianShape`. Concretely: is

```text
concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source
```

equal to `f shape.size (longCount shape) source` for one fixed `f` whose
signature mentions no shape?

The technique here is the mirror discipline: for each shape-indexed quantity that
enters an offset, define a `Nat`-only mirror and prove the two agree. The mirror's
*signature* is the evidence. A definition of type `Nat -> Nat -> Source -> Nat`
cannot consult shape content, so once the equality is proved the factorization is
enforced by the elaborator rather than argued in prose.

Coverage is enforced the same way. `ConcreteBPNativeSuccinctRMQFlatPayloadSource`
and `ConcreteBPNativeSuccinctRMQFlatPayloadComponent` are closed inductives, so the
theorems below are proved by `cases` and adding a constructor breaks elaboration.
This is deliberately the `SourceInventory.lean` pattern; per `WDD-20260726-010` a
curated census over an open universe is not usable here.

## What this module does not establish

* It does not build a controller, a packed memory, or any probe. Offsets are bit
  positions inside the existing flat payload; nothing here chunks them into cells.
* It does not claim the offsets are *reachable*. `concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat`
  gates which sources are counted, and two close sources are counted only in the
  interior-ready regime; see `packedCloseInteriorNeedsReadyGuard` below.
* `longCount` is defined here but no header cell exists yet, so nothing here shows
  a controller could obtain it.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-! ### The single header descriptor -/

/--
The number of long super slots in the canonical select source over a shape's BP
code.

This is the one content-dependent quantity the `K = 1` packed header is proposed to
carry. `GenericSelect.longSuperRelativeTable_payload_length` states that the long
relative table's payload length is exactly this count times two size-only factors,
which is why one number suffices.
-/
def longCount (shape : CartesianShape) : Nat :=
  RMQ.Succinct.rankPrefix true
    (GenericSelect.longSuperFlagBits shape.bpCode false)
    (GenericSelect.superSlotCount shape.bpCode false)

/-! ### Size-only mirrors of the flat-payload component budgets -/

/--
Size-only mirror of the access-directory budget.

`genericSparseExceptionBPCloseAccessOverhead` already has type `Nat -> Nat`; this
abbreviation records that the packed layout consumes it at the input size and
nowhere consults the shape.
-/
def packedAccessOverhead (n : Nat) : Nat :=
  genericSparseExceptionBPCloseAccessOverhead n

/-- Size-only mirror of the close-component budget. -/
def packedCloseOverhead (n : Nat) : Nat :=
  SuccinctClose.compactBPCloseOverhead n

/-! ### The access-padding cancellation (`FG-03`) -/

/--
The access directory's payload is exactly the flat layout's access-rank component
followed by its select component.

This is the identity that makes the padding cancel: the quantity subtracted to form
`accessPadding` is the same quantity that precedes it.
-/
theorem accessDirectory_payload_length
    (shape : CartesianShape) :
    (builtGenericSparseExceptionSelectBPCloseAccessDirectory shape).payload.length =
      (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).accessRankPayload.length +
        (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).selectPayload.length := by
  simp [builtGenericSparseExceptionSelectBPCloseAccessDirectory,
    concreteBPNativeSuccinctRMQFlatPayloadLayout, List.length_append]

/--
The access padding has exactly the length that completes the access components to
the size-only budget.

Truncated `Nat` subtraction makes this a real obligation rather than bookkeeping:
without `payload_length_le_overhead` the sum below collapses to a content-dependent
value instead of `packedAccessOverhead`.
-/
theorem accessComponents_add_padding
    (shape : CartesianShape) :
    (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).accessRankPayload.length +
        (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).selectPayload.length +
        (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).accessPadding.length =
      packedAccessOverhead shape.size := by
  have hle :
      (builtGenericSparseExceptionSelectBPCloseAccessDirectory shape).payload.length <=
        genericSparseExceptionBPCloseAccessOverhead shape.size :=
    (builtGenericSparseExceptionSelectBPCloseAccessDirectory
      shape).payload_length_le_overhead
  have hsplit := accessDirectory_payload_length shape
  have hpad :
      (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).accessPadding.length =
        genericSparseExceptionBPCloseAccessOverhead shape.size -
          (builtGenericSparseExceptionSelectBPCloseAccessDirectory shape).payload.length := by
    simp [concreteBPNativeSuccinctRMQFlatPayloadLayout,
      builtGenericSparseExceptionSelectBPCloseAccessDirectory, List.length_append]
  rw [hpad, packedAccessOverhead]
  omega

/-! ### Size-only component base offsets -/

/--
Size-only mirror of the final rank word size.

`builtRelativeSplitBPCloseRankWordSize` is `machineWordBits` of the BP code length,
and the BP code of a shape of size `n` has length `2 * n`.
-/
def packedRankWordSize (n : Nat) : Nat :=
  SuccinctRank.machineWordBits (2 * n)

theorem rankWordSize_eq_packed (shape : CartesianShape) :
    builtRelativeSplitBPCloseRankWordSize shape = packedRankWordSize shape.size := by
  unfold builtRelativeSplitBPCloseRankWordSize packedRankWordSize
  rw [CartesianShape.bpCode_length]

/-- Size-only mirror of the final rank block width. -/
def packedRankBlockWidth (n : Nat) : Nat :=
  SuccinctRank.machineWordBits (packedRankWordSize n * packedRankWordSize n)

theorem rankBlockWidth_eq_packed (shape : CartesianShape) :
    builtRelativeSplitBPCloseRankBlockWidth shape = packedRankBlockWidth shape.size := by
  unfold builtRelativeSplitBPCloseRankBlockWidth packedRankBlockWidth
  rw [rankWordSize_eq_packed]

/--
Size-only mirror of the final rank superblock-sample overhead.

Written in the exact shape produced by `canonicalSuperRankSampleTables_payload_length`
followed by `canonicalSuperRankEntries_length`: one summand per sample polarity,
each an entry count times the sample width.
-/
def packedRankSuperOverhead (n : Nat) : Nat :=
  (2 * n / packedRankWordSize n / packedRankWordSize n + 1) * packedRankWordSize n +
    (2 * n / packedRankWordSize n / packedRankWordSize n + 1) * packedRankWordSize n

theorem rankSuperOverhead_eq_packed (shape : CartesianShape) :
    builtRelativeSplitBPCloseRankSuperOverhead shape =
      packedRankSuperOverhead shape.size := by
  unfold builtRelativeSplitBPCloseRankSuperOverhead packedRankSuperOverhead
  rw [SuccinctRank.canonicalSuperRankSampleTables_payload_length,
    SuccinctRank.canonicalSuperRankEntries_length,
    SuccinctRank.canonicalSuperRankEntries_length,
    CartesianShape.bpCode_length, rankWordSize_eq_packed,
    builtRelativeSplitBPCloseRankBlocksPerSuper, rankWordSize_eq_packed]

/-- Size-only mirror of the final rank block-sample overhead. -/
def packedRankBlockOverhead (n : Nat) : Nat :=
  (2 * n / packedRankWordSize n + 1) * packedRankBlockWidth n +
    (2 * n / packedRankWordSize n + 1) * packedRankBlockWidth n

theorem rankBlockOverhead_eq_packed (shape : CartesianShape) :
    builtRelativeSplitBPCloseRankBlockOverhead shape =
      packedRankBlockOverhead shape.size := by
  unfold builtRelativeSplitBPCloseRankBlockOverhead packedRankBlockOverhead
  rw [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length,
    SuccinctRank.canonicalBlockRankEntries_length,
    SuccinctRank.canonicalBlockRankEntries_length,
    CartesianShape.bpCode_length, rankWordSize_eq_packed,
    rankBlockWidth_eq_packed]

/--
Size-only mirror of the rank component's length.

The rank data's type is indexed by its two overheads and carries
`superPayload_length` / `blockPayload_length` as fields, so the length is fixed by
the index rather than by the stored bits. Both indices are themselves size-only by
the two theorems above, which is what makes this a mirror the controller can
evaluate rather than a congruence it cannot.
-/
def packedRankAuxLength (n : Nat) : Nat :=
  packedRankSuperOverhead n + packedRankBlockOverhead n

theorem rankAuxPayload_length
    (shape : CartesianShape) :
    (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).accessRankPayload.length =
      packedRankAuxLength shape.size := by
  have hsuper :=
    (builtRelativeSplitBPCloseRankData shape).superPayload_length
  have hblock :=
    (builtRelativeSplitBPCloseRankData shape).blockPayload_length
  simp only [concreteBPNativeSuccinctRMQFlatPayloadLayout, packedRankAuxLength,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.auxPayload,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superPayload,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockPayload,
    List.length_append, hsuper, hblock]
  rw [rankSuperOverhead_eq_packed, rankBlockOverhead_eq_packed]

/--
The close component begins at a position determined by the input size alone.

This is `FG-03`'s second clause. Every content-dependent length between the BP code
and the close component -- the whole select payload, including the long and sparse
relative tables -- is absorbed by the access padding.
-/
theorem closeComponent_flatOffset
    (shape : CartesianShape) :
    (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).componentFlatOffset
        .closePayload =
      2 * shape.size + packedAccessOverhead shape.size := by
  have hbp : (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).bpCodePayload.length =
      2 * shape.size := by
    simpa [concreteBPNativeSuccinctRMQFlatPayloadLayout] using
      CartesianShape.bpCode_length shape
  have haccess := accessComponents_add_padding shape
  simp only [ConcreteBPNativeSuccinctRMQFlatPayloadLayout.componentFlatOffset]
  omega

/-! ### Size-only mirrors of the select slot geometry -/

/--
Size-only mirror of the select super-slot count.

`GenericSelect.superSlotCount` divides the occurrence count by a stride computed
from the bit length. Over a shape's BP code with target `false` both inputs are
fixed by the size: the occurrence count is the number of closing parentheses,
which is the shape's size, and the bit length is twice the size.
-/
def packedSuperSlots (n : Nat) : Nat :=
  GenericSelect.selectCeilDiv n (GenericSelect.superStride (2 * n))

theorem superSlotCount_eq_packed (shape : CartesianShape) :
    GenericSelect.superSlotCount shape.bpCode false = packedSuperSlots shape.size := by
  have hcount : GenericSelect.occurrenceCount shape.bpCode false = shape.size := by
    unfold GenericSelect.occurrenceCount
    exact SuccinctSpace.bpCode_rankFalse_full shape
  have hlen : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  unfold GenericSelect.superSlotCount packedSuperSlots
  rw [hcount, hlen]

/-- Size-only mirror of the select super field width. -/
def packedSuperWidth (n : Nat) : Nat :=
  GenericSelect.wordBits (2 * n)

theorem superFieldWidth_eq_packed (shape : CartesianShape) :
    GenericSelect.superFieldWidth shape.bpCode = packedSuperWidth shape.size := by
  have hlen : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  unfold GenericSelect.superFieldWidth packedSuperWidth
  rw [hlen]

/-- Size-only mirror of the long-super flag list's length. -/
theorem longFlagBits_length_eq_packed (shape : CartesianShape) :
    (GenericSelect.longSuperFlagBits shape.bpCode false).length =
      packedSuperSlots shape.size := by
  rw [GenericSelect.longSuperFlagBits_length, superSlotCount_eq_packed]

/-! ### The long relative table is the only long-count-dependent length -/

/--
The long relative table's payload length is exactly the long count times two
size-only factors.

This is the whole justification for `K = 1`. Every other length reachable from a
select offset is fixed by the input size; this one is not, and one number
recovers it.
-/
theorem longSuperRelativeTable_length_eq (shape : CartesianShape) :
    (GenericSelect.longSuperRelativeTable shape.bpCode false).payload.length =
      longCount shape *
        (GenericSelect.superStride (2 * shape.size) *
          GenericSelect.wordBits (2 * shape.size)) := by
  have hlen : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  rw [GenericSelect.longSuperRelativeTable_payload_length]
  unfold longCount GenericSelect.longSuperRelativeWidth GenericSelect.wordBits
  rw [hlen, Nat.mul_assoc]

/-! ### Super-table component offsets -/

/--
Each of the four super sub-tables occupies `packedSuperSlots * packedSuperWidth`
bits.

The dense entry table stores one field per entry per column, and every column has
the same entry list, so all four sub-payloads share one length.
-/
theorem superTable_column_length (shape : CartesianShape) :
    (GenericSelect.superTable shape.bpCode false).baseOccurrenceTable.payload.length =
      packedSuperSlots shape.size * packedSuperWidth shape.size := by
  rw [SuccinctSpace.FixedWidthNatTable.payload_length]
  simp only [GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences,
    List.length_map]
  rw [GenericSelect.superEntries_length, superSlotCount_eq_packed,
    superFieldWidth_eq_packed]

/-! ### Sparse terminality -/

/--
Everything the select payload places before the sparse relative table.

Naming this explicitly is the point: the definition mentions the super table, the
long flag bits and their rank, the long relative table, the local table, and the
sparse directory's flag bits and rank, and it does not mention the sparse relative
table at all.
-/
def packedSelectPrefixBits (shape : CartesianShape) : List Bool :=
  (GenericSelect.superTable shape.bpCode false).payload ++
    GenericSelect.longSuperFlagBits shape.bpCode false ++
      (GenericSelect.longFlagRankData shape.bpCode false).auxPayload ++
        (GenericSelect.longSuperRelativeTable shape.bpCode false).payload ++
          (GenericSelect.localTable shape.bpCode false).payload ++
            GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false ++
              (GenericSelect.sparseExceptionEffectiveFlagRankData
                shape.bpCode false).auxPayload

/--
**Sparse terminality.** The canonical select payload is that prefix followed by the
sparse relative table, with nothing after it.

This is the first clause of `FG-03`. Because the sparse relative table is a proper
suffix of the select payload, and the close component's base is fixed by the input
size (`closeComponent_flatOffset`), the number of sparse exceptions cannot move any
address in the layout.
-/
theorem selectPayload_eq_prefix_append_sparseRelative (shape : CartesianShape) :
    (GenericSelect.sparseExceptionSelectSource shape.bpCode false).payload =
      packedSelectPrefixBits shape ++
        (GenericSelect.sparseExceptionRelativeTable shape.bpCode false).payload := by
  simp [GenericSelect.sparseExceptionSelectSource,
    GenericSelect.SparseExceptionSelectData.toChargedSelectPositionSource,
    GenericSelect.SparseExceptionSelectData.payload,
    GenericSelect.SparseExceptionDirectory.payload,
    GenericSelect.sparseExceptionSelectData,
    GenericSelect.sparseExceptionDirectory,
    packedSelectPrefixBits, List.append_assoc]

/--
Every source that lives in the select component is addressed at or before the start
of the sparse relative table.

Stated as the bound rather than as an equality because `.selectSparseRelative`
itself is addressed exactly at the prefix length, and every earlier source strictly
inside it. Either way no base is a function of the sparse relative table's length.
-/
theorem selectSourceComponentOffset_le_prefix
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hcomponent :
      concreteBPNativeSuccinctRMQFlatPayloadSourceComponent source =
        .selectPayload) :
    concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset shape source <=
      (packedSelectPrefixBits shape).length := by
  cases source <;>
    simp_all [concreteBPNativeSuccinctRMQFlatPayloadSourceComponent,
      concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset,
      packedSelectPrefixBits,
      GenericSelect.sparseExceptionSelectData,
      GenericSelect.sparseExceptionDirectory,
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.payload,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.auxPayload,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superPayload,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockPayload,
      List.length_append, Nat.add_assoc]

end PackedCellProbe
end SuccinctFinal
end RMQ
