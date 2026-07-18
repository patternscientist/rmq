import RMQ.Core.WordRAM.E1SelectDispatch
import RMQ.Core.WordRAM.E1RankCanonical
import RMQ.Core.SuccinctFinal.RAM.RankSamplePresence

/-!
# E1 amended machine: select-close dispatch at the accepted component (M3c-6g)

Canonical instantiation of `selectCloseBlock_runsTo` at the accepted
select-close component
`concreteBPNativeChunkedSelectCloseGlobalWordTraceResult shape idx`
(frozen matrix REQ-E1-03/04): the three route-side hypotheses of the
dispatch — the long-leg seed reads, the sparse-leg seed reads, and the
dense-leg word lengths — are discharged from the route's own data, so the
405-instruction dispatch block simulates the component for EVERY shape and
EVERY occurrence index, with no sampling and no readiness guards.

The segment instantiation is the canonical one: `G := 17`
(`concreteBPNativeRankCloseTraceSegmentBase`), so `G + 4 = 21 =
concreteBPNativeFringeChunkTraceSegment` definitionally, and `ST := 22`
(`concreteBPNativeSelectChunkTraceSegment`).
-/

namespace RMQ
namespace WordRAM
namespace E1SelectCanonical

open E1Machine
open E1RankBlock
open E1SelectDispatch
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.GenericSelect

/-- Abbreviation for the accepted select-close data at a shape. -/
private abbrev selData (shape : Cartesian.CartesianShape) :
    SparseExceptionSelectData shape.bpCode false
      (GenericSelect.sparseExceptionEffectiveFlagRankSuperOverhead
        shape.bpCode false)
      (GenericSelect.sparseExceptionEffectiveFlagRankBlockOverhead
        shape.bpCode false) :=
  GenericSelect.sparseExceptionSelectData shape.bpCode false

/-! ## Sentinel-chunked payload identifications for the two select rank objects -/

/-- The long-flag rank object's payload store is the sentinel-padded
chunking of its own flag bits (definitional: it is built by
`canonicalTwoLevelRankDataOfChunksExactLocalBlock`). -/
private theorem longFlagRankData_bitWords_words
    (shape : Cartesian.CartesianShape) :
    (selData shape).longFlagRankData.bitWords.store.words =
      (SuccinctSpace.chunkPayloadWords
          (selData shape).longFlagRankData.wordSize
          (GenericSelect.longSuperFlagBits shape.bpCode false) ++
        List.replicate
          ((GenericSelect.longSuperFlagBits shape.bpCode false).length + 1)
          []).toArray := rfl

/-- The sparse-directory rank object's payload store is the sentinel-padded
chunking of its own effective-flag bits (definitional, same constructor). -/
private theorem sparseRankData_bitWords_words
    (shape : Cartesian.CartesianShape) :
    (selData shape).sparseDirectory.rankData.bitWords.store.words =
      (SuccinctSpace.chunkPayloadWords
          (selData shape).sparseDirectory.rankData.wordSize
          (selData shape).sparseDirectory.flagBits ++
        List.replicate
          ((selData shape).sparseDirectory.flagBits.length + 1)
          []).toArray := rfl

/-! ## The three route-side hypotheses at the canonical store -/

/--
Long-leg seed presence and offset bound at the canonical global store: the
three seed reads of the long-flag rank object (super sample, block sample,
packed payload word) all succeed at the addresses the dispatch reads, and
the in-word offset lies inside the word it reads.  Unconditional in the
super entry — presence does not depend on the entry's contents.
-/
theorem canonical_longSeed (shape : Cartesian.CartesianShape) (idx : Nat) :
    ∃ sw dw w,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          ((selData shape).longFlagRankData.superIndex
            (selectSuperSlot idx (selData shape).superStride)) = some sw ∧
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase + 1)
          ((selData shape).longFlagRankData.wordIndex
            (selectSuperSlot idx (selData shape).superStride)) = some dw ∧
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase + 2)
          ((selData shape).longFlagRankData.wordIndex
            (selectSuperSlot idx (selData shape).superStride)) = some w ∧
      (selData shape).longFlagRankData.wordOffset
        (selectSuperSlot idx (selData shape).superStride) ≤ w.length := by
  have hp : (selData shape).longFlagRankData.queryPos
      (selectSuperSlot idx (selData shape).superStride) ≤
        (GenericSelect.longSuperFlagBits shape.bpCode false).length :=
    Nat.min_le_right _ _
  obtain ⟨⟨sw, hsw⟩, ⟨dw, hdw⟩, ⟨w, hw⟩⟩ :=
    twoLevelRankData_sample_words_present (selData shape).longFlagRankData
      true
      ((selData shape).longFlagRankData.queryPos
        (selectSuperSlot idx (selData shape).superStride)) hp
  refine ⟨sw, dw, w, ?_, ?_, ?_, ?_⟩
  · rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagSuper]
    exact hsw
  · rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagBlock]
    exact hdw
  · rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagWord]
    exact hw
  · exact twoLevelRankData_wordOffset_le (selData shape).longFlagRankData
      (longFlagRankData_bitWords_words shape)
      (selectSuperSlot idx (selData shape).superStride) hw

/--
Sparse-leg seed presence and offset bound at the canonical global store,
for the sparse-directory rank object at the local compact slot.  Note the
slot uses `data.sparseDirectory.localStride`, not `data.localStride`.
-/
theorem canonical_sparseSeed (shape : Cartesian.CartesianShape) (idx : Nat)
    (super : SparseDenseSelectDenseLocalEntry) :
    ∃ sw dw w,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
          ((selData shape).sparseDirectory.rankData.superIndex
            (relativeSplitSelectLocalSlot idx (selData shape).superStride
              (selData shape).localSlotsPerSuper (selData shape).localStride
              super)) = some sw ∧
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
            + 1)
          ((selData shape).sparseDirectory.rankData.wordIndex
            (relativeSplitSelectLocalSlot idx (selData shape).superStride
              (selData shape).localSlotsPerSuper (selData shape).localStride
              super)) = some dw ∧
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
            + 2)
          ((selData shape).sparseDirectory.rankData.wordIndex
            (relativeSplitSelectLocalSlot idx (selData shape).superStride
              (selData shape).localSlotsPerSuper (selData shape).localStride
              super)) = some w ∧
      (selData shape).sparseDirectory.rankData.wordOffset
        (relativeSplitSelectLocalSlot idx (selData shape).superStride
          (selData shape).localSlotsPerSuper (selData shape).localStride
          super) ≤ w.length := by
  have hp : (selData shape).sparseDirectory.rankData.queryPos
      (relativeSplitSelectLocalSlot idx (selData shape).superStride
        (selData shape).localSlotsPerSuper (selData shape).localStride
        super) ≤ (selData shape).sparseDirectory.flagBits.length :=
    Nat.min_le_right _ _
  obtain ⟨⟨sw, hsw⟩, ⟨dw, hdw⟩, ⟨w, hw⟩⟩ :=
    twoLevelRankData_sample_words_present
      (selData shape).sparseDirectory.rankData true
      ((selData shape).sparseDirectory.rankData.queryPos
        (relativeSplitSelectLocalSlot idx (selData shape).superStride
          (selData shape).localSlotsPerSuper (selData shape).localStride
          super)) hp
  refine ⟨sw, dw, w, ?_, ?_, ?_, ?_⟩
  · rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankSuper]
    exact hsw
  · rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankBlock]
    exact hdw
  · rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankWord]
    exact hw
  · exact twoLevelRankData_wordOffset_le
      (selData shape).sparseDirectory.rankData
      (sparseRankData_bitWords_words shape)
      (relativeSplitSelectLocalSlot idx (selData shape).superStride
        (selData shape).localSlotsPerSuper (selData shape).localStride
        super) hw

/--
Dense-leg word lengths at the canonical global store.  The select payload
store is SENTINEL-FREE (`BoundedPayloadWordStore.ofChunks`, not
`ofChunksWithSentinel`), so every present word is a genuine chunk and its
length is the exact `Nat.min` — unconditionally, with no case split on
whether the index is a full or partial chunk.
-/
theorem canonical_denseLen (shape : Cartesian.CartesianShape) (i : Nat)
    {w : List Bool}
    (hw : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase i =
      some w) :
    w.length = Nat.min (selData shape).wordSize
      (shape.bpCode.length - i * (selData shape).wordSize) := by
  rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectBitWords] at hw
  have haligned :
      SelectAlignedBitWords shape.bpCode (selData shape).wordSize
        (selData shape).bitWords :=
    selectAlignedBitWords_ofChunks shape.bpCode
      (GenericSelect.wordBits_pos shape.bpCode.length)
  rw [haligned.get_eq_take_drop hw]
  simp [List.length_take, List.length_drop]

/-! ## The canonical-store select-close dispatch -/

/--
Select-close component simulation at the CANONICAL global store: for every
shape, every hosting base, and every occurrence index, the hosted
405-instruction dispatch block runs against
`concreteBPNativeSuccinctRMQGlobalReadStore shape` — the single store the
whole accepted query reads — from block entry to `A + 405` with receipts
POSITIONALLY EQUAL to
`(concreteBPNativeChunkedSelectCloseGlobalWordTraceResult shape idx).trace`,
the component's `.value` recovered from `rVal` under `decodePacket`, the
frozen `selectCloseCats` category log, and the query registers preserved.
The machine store and the component store are the SAME argument, so this is
the store-swap glue form consumed by the whole-query composition
(REQ-E1-03/04 select-close leg at the canonical store).
-/
theorem selectCloseBlock_runsTo_canonical
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {A : Nat}
    (hhost : HostedAt program A
      (selectCloseBlockAt (selData shape)
        concreteBPNativeSelectCloseTraceSegmentLayout A
        concreteBPNativeRankCloseTraceSegmentBase
        concreteBPNativeSelectChunkTraceSegment
        (bpFringeChunkBits shape.bpCode.length)))
    (regs0 : RegFile) (idx : Nat) (hIdx : regs0 E1SelectBridge.xIdx = idx) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs0, A, false⟩ ⟨regsF, A + 405, false⟩
        (concreteBPNativeChunkedSelectCloseGlobalWordTraceResult
          shape idx).trace
        (selectCloseCats (selData shape)
          concreteBPNativeSelectCloseTraceSegmentLayout
          concreteBPNativeRankCloseTraceSegmentBase
          concreteBPNativeSelectChunkTraceSegment
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (bpFringeChunkBits shape.bpCode.length) idx) ∧
      E1Query.decodePacket (regsF rVal) =
        (concreteBPNativeChunkedSelectCloseGlobalWordTraceResult
          shape idx).value ∧
      (∀ r, r ≤ 7 ∨ r = 28 → regsF r = regs0 r) := by
  -- the accepted canonical component IS the dispatch's component at the
  -- canonical segment instantiation (`17 + 4 = 21` by `rfl`, `ST = 22`)
  have htr : concreteBPNativeChunkedSelectCloseGlobalWordTraceResult
      shape idx =
    (selData shape).bpChunkedSelectTraceResultWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout
      (concreteBPNativeRankCloseTraceSegmentBase + 4)
      concreteBPNativeSelectChunkTraceSegment
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (bpFringeChunkBits shape.bpCode.length) idx := by
    rw [show concreteBPNativeRankCloseTraceSegmentBase + 4 =
      concreteBPNativeFringeChunkTraceSegment from rfl]
    rfl
  rw [htr]
  exact selectCloseBlock_runsTo
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) (selData shape)
    concreteBPNativeSelectCloseTraceSegmentLayout hhost regs0 idx hIdx
    (fun _super _hsuper _hmk => canonical_longSeed shape idx)
    (fun super _loc _hsuper _hunm _hloc _hlmk =>
      canonical_sparseSeed shape idx super)
    (fun _super _loc _hsuper _hunm _hloc _hlunm =>
      ⟨fun _w1 h1 => canonical_denseLen shape _ h1,
        fun _w2 h2 => canonical_denseLen shape _ h2⟩)

end E1SelectCanonical
end WordRAM
end RMQ
