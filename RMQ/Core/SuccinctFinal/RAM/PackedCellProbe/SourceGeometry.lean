import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.SourceWords

/-!
# The size-only word geometry, as one function per quantity

`SourceWords` proves one theorem per source. This module collects the counts, the
strides and the payload bit lengths into three total functions of the input size,
the decoded long count and the typed source, and then states the twenty-nine
theorems as a single implication over the closed source inductive.

The implication direction is forced by `DD-20260804-022`: the sparse relative
table's word count is not size-only, so the geometry below uses its size-only
capacity and the aggregate theorem lowers **successful** logical reads only.
Twenty-eight of the arms are equations underneath; only that one is not.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open Cartesian
open SuccinctSpace

/-! ## The three geometry functions -/

/-- The stride of one typed source, from the input size alone. -/
def packedSourceStride (n : Nat) :
    ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat
  | .bpCode => packedBpCodeWordWidth n
  | .selectSuperBaseOccurrence => packedSuperWidth n
  | .selectSuperBaseWordIndex => packedSuperWidth n
  | .selectSuperRankBefore => packedSuperWidth n
  | .selectSuperFirstOffset => packedSuperWidth n
  | .selectLocalBaseOccurrence => packedLocalWidth n
  | .selectLocalBaseWordIndex => packedLocalWidth n
  | .selectLocalRankBefore => packedLocalWidth n
  | .selectLocalFirstOffset => packedLocalWidth n
  | .selectLongFlagBits => packedLongFlagWordSize n
  | .selectLongFlagRankSuperTrue => packedLongFlagWordSize n
  | .selectLongFlagRankBlockTrue => packedLongFlagWordSize n
  | .selectLongRelative => packedSuperWidth n
  | .selectSparseFlagBits => packedSparseWordSize n
  | .selectSparseRankSuperTrue => packedSparseWordSize n
  | .selectSparseRankBlockTrue => packedSparseWordSize n
  | .selectSparseRelative => packedLocalWidth n
  | .finalRankSuperFalse => packedRankWordSize n
  | .finalRankBlockFalse => packedRankBlockWidth n
  | .finalRankBPCodeAlias => packedRankWordSize n
  | .closeSummaryBaseline => packedSummarySuperWidth n
  | .closeSummaryMinRel => packedSummaryRelativeWidth n
  | .closeSummaryMaxRel => packedSummaryRelativeWidth n
  | .closeSummaryArgOffset => packedSummaryRelativeWidth n
  | .closeInteriorLocal => packedInteriorOffsetWidth n
  | .closeInteriorGlobal => packedInteriorBlockWidth n
  | .closeFiniteSmallInteriorMin => 0
  | .closeFiniteSmallInteriorArg => 0
  | .closeFiniteSmallSameBlock => 0

/--
The word count of one typed source, from the input size and the decoded long
count.

Two arms are not the number of payload-carrying words. The three chunked rank
directories append `payload.length + 1` empty sentinel words, which are counted
here because the store returns them; and `.selectSparseRelative` carries its
size-only capacity rather than its actual entry count, which is the one quantity
`K1` does not record.
-/
def packedSourceWordCount (n longCount : Nat) :
    ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat
  | .bpCode => packedChunkCount (2 * n) (packedBpCodeWordWidth n)
  | .selectSuperBaseOccurrence => packedSuperSlots n
  | .selectSuperBaseWordIndex => packedSuperSlots n
  | .selectSuperRankBefore => packedSuperSlots n
  | .selectSuperFirstOffset => packedSuperSlots n
  | .selectLocalBaseOccurrence => packedLocalSlots n
  | .selectLocalBaseWordIndex => packedLocalSlots n
  | .selectLocalRankBefore => packedLocalSlots n
  | .selectLocalFirstOffset => packedLocalSlots n
  | .selectLongFlagBits =>
      packedChunkCount (packedSuperSlots n) (packedLongFlagWordSize n) +
        (packedSuperSlots n + 1)
  | .selectLongFlagRankSuperTrue => packedLongFlagRankSlots n
  | .selectLongFlagRankBlockTrue => packedLongFlagRankSlots n
  | .selectLongRelative => packedLongRelativeSlots n longCount
  | .selectSparseFlagBits =>
      packedChunkCount (packedSparseSlots n) (packedSparseWordSize n) +
        (packedSparseSlots n + 1)
  | .selectSparseRankSuperTrue => packedSparseRankSlots n
  | .selectSparseRankBlockTrue => packedSparseRankSlots n
  | .selectSparseRelative => packedSparseRelativeCapacity n
  | .finalRankSuperFalse => packedRankSuperSlots n
  | .finalRankBlockFalse => packedRankBlockSlots n
  | .finalRankBPCodeAlias =>
      packedChunkCount (2 * n) (packedRankWordSize n) + (2 * n + 1)
  | .closeSummaryBaseline => packedSummarySuperCount n
  | .closeSummaryMinRel => packedSummaryBlockCount n
  | .closeSummaryMaxRel => packedSummaryBlockCount n
  | .closeSummaryArgOffset => packedSummaryBlockCount n
  | .closeInteriorLocal => packedInteriorLocalSlots n
  | .closeInteriorGlobal => packedInteriorGlobalSlots n
  | .closeFiniteSmallInteriorMin => 0
  | .closeFiniteSmallInteriorArg => 0
  | .closeFiniteSmallSameBlock => 0

/--
The payload bit length of one typed source.

For the four chunked bit sources this is the bit list's own length, which is why
their final word is short. For every other source it is the count times the
stride, and no word truncates.
-/
def packedSourceBitLength (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) : Nat :=
  match source with
  | .bpCode => 2 * n
  | .selectLongFlagBits => packedSuperSlots n
  | .selectSparseFlagBits => packedSparseSlots n
  | .finalRankBPCodeAlias => 2 * n
  | _ => packedSourceWordCount n longCount source * packedSourceStride n source

/-- The exact number of bits word `index` of a source carries. -/
def packedSourceReadWidth (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    Nat :=
  min (packedSourceStride n source)
    (packedSourceBitLength n longCount source -
      index * packedSourceStride n source)

theorem packedSourceReadWidth_le_stride (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    packedSourceReadWidth n longCount source index <=
      packedSourceStride n source := by
  unfold packedSourceReadWidth
  omega

/-! ## The aggregate lowering of the word arrays

One implication over the closed source inductive. Adding a constructor breaks
elaboration until its geometry is supplied on all three functions and its word
theorem exists.
-/

theorem packedSourceWords_of_some
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    {index : Nat} {word : List Bool}
    (hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? =
        some word) :
    packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source)
        (packedSourceWordCount shape.size (longCount shape) source)
        (packedSourceStride shape.size source) index =
      some word := by
  cases source with
  | bpCode =>
      rw [packedBpCodeWords shape index] at hget
      exact hget
  | selectSuperBaseOccurrence =>
      rw [packedSelectSuperBaseOccurrenceWords shape index] at hget
      exact hget
  | selectSuperBaseWordIndex =>
      rw [packedSelectSuperBaseWordIndexWords shape index] at hget
      exact hget
  | selectSuperRankBefore =>
      rw [packedSelectSuperRankBeforeWords shape index] at hget
      exact hget
  | selectSuperFirstOffset =>
      rw [packedSelectSuperFirstOffsetWords shape index] at hget
      exact hget
  | selectLocalBaseOccurrence =>
      rw [packedSelectLocalBaseOccurrenceWords shape index] at hget
      exact hget
  | selectLocalBaseWordIndex =>
      rw [packedSelectLocalBaseWordIndexWords shape index] at hget
      exact hget
  | selectLocalRankBefore =>
      rw [packedSelectLocalRankBeforeWords shape index] at hget
      exact hget
  | selectLocalFirstOffset =>
      rw [packedSelectLocalFirstOffsetWords shape index] at hget
      exact hget
  | selectLongFlagBits =>
      rw [packedSelectLongFlagBitsWords shape index] at hget
      exact hget
  | selectLongFlagRankSuperTrue =>
      rw [packedSelectLongFlagRankSuperTrueWords shape index] at hget
      exact hget
  | selectLongFlagRankBlockTrue =>
      rw [packedSelectLongFlagRankBlockTrueWords shape index] at hget
      exact hget
  | selectLongRelative =>
      rw [packedSelectLongRelativeWords shape index] at hget
      exact hget
  | selectSparseFlagBits =>
      rw [packedSelectSparseFlagBitsWords shape index] at hget
      exact hget
  | selectSparseRankSuperTrue =>
      rw [packedSelectSparseRankSuperTrueWords shape index] at hget
      exact hget
  | selectSparseRankBlockTrue =>
      rw [packedSelectSparseRankBlockTrueWords shape index] at hget
      exact hget
  | selectSparseRelative =>
      exact packedSelectSparseRelativeWords_of_some shape hget
  | finalRankSuperFalse =>
      rw [packedFinalRankSuperFalseWords shape index] at hget
      exact hget
  | finalRankBlockFalse =>
      rw [packedFinalRankBlockFalseWords shape index] at hget
      exact hget
  | finalRankBPCodeAlias =>
      rw [packedFinalRankBPCodeAliasWords shape index] at hget
      exact hget
  | closeSummaryBaseline =>
      rw [packedCloseSummaryBaselineWords shape index] at hget
      exact hget
  | closeSummaryMinRel =>
      rw [packedCloseSummaryMinRelWords shape index] at hget
      exact hget
  | closeSummaryMaxRel =>
      rw [packedCloseSummaryMaxRelWords shape index] at hget
      exact hget
  | closeSummaryArgOffset =>
      rw [packedCloseSummaryArgOffsetWords shape index] at hget
      exact hget
  | closeInteriorLocal =>
      rw [packedCloseInteriorLocalWords shape index] at hget
      exact hget
  | closeInteriorGlobal =>
      rw [packedCloseInteriorGlobalWords shape index] at hget
      exact hget
  | closeFiniteSmallInteriorMin =>
      rw [packedCloseFiniteSmallInteriorMinWords shape index] at hget
      exact hget
  | closeFiniteSmallInteriorArg =>
      rw [packedCloseFiniteSmallInteriorArgWords shape index] at hget
      exact hget
  | closeFiniteSmallSameBlock =>
      rw [packedCloseFiniteSmallSameBlockWords shape index] at hget
      exact hget

/-! ## The length mirrors the offset factorization did not need

`SourceFactorization` proves a length for every column an *offset* depends on. A
column that nothing is addressed after -- the fourth column of each dense entry
table, the second polarity of each rank sample table, the interior global table --
never needed one. Sizing every source needs them all.
-/

theorem packedSuperTable_firstOffset_length (shape : CartesianShape) :
    (GenericSelect.superTable shape.bpCode false).firstOffsetTable.payload.length =
      packedSuperColumn shape.size := by
  rw [SuccinctSpace.FixedWidthNatTable.payload_length]
  simp only [GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffsets,
    List.length_map]
  rw [GenericSelect.superEntries_length, superSlotCount_eq_packed,
    superFieldWidth_eq_packed]
  rfl

theorem packedLocalTable_firstOffset_length (shape : CartesianShape) :
    (GenericSelect.localTable shape.bpCode false).firstOffsetTable.payload.length =
      packedLocalColumn shape.size := by
  rw [SuccinctSpace.FixedWidthNatTable.payload_length]
  simp only [GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffsets,
    List.length_map]
  rw [GenericSelect.localEntries_length, localSlotCount_eq_packed,
    localFieldWidth_eq_packed]
  rfl

theorem packedRankSuperFalse_length (shape : CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).superTables.falseTable.payload.length =
      packedRankSuperColumn shape.size := by
  rw [SuccinctSpace.FixedWidthNatTable.payload_length]
  simp only [builtRelativeSplitBPCloseRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalSuperRankSampleTables,
    SuccinctRank.canonicalSuperRankEntries_length,
    packedRankSuperColumn]
  rw [CartesianShape.bpCode_length, rankWordSize_eq_packed,
    builtRelativeSplitBPCloseRankBlocksPerSuper, rankWordSize_eq_packed]

theorem packedRankBlockFalse_length (shape : CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).blockTables.falseTable.payload.length =
      packedRankBlockColumn shape.size := by
  rw [SuccinctSpace.FixedWidthNatTable.payload_length]
  simp only [builtRelativeSplitBPCloseRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan,
    SuccinctRank.canonicalBlockRankEntries_length,
    packedRankBlockColumn]
  rw [CartesianShape.bpCode_length, rankWordSize_eq_packed,
    rankBlockWidth_eq_packed]

theorem packedLongFlagRankSuperTrue_length (shape : CartesianShape) :
    (GenericSelect.longFlagRankData shape.bpCode
      false).superTables.trueTable.payload.length =
      packedLongFlagRankSlots shape.size * packedLongFlagWordSize shape.size := by
  rw [SuccinctSpace.FixedWidthNatTable.payload_length]
  simp only [GenericSelect.longFlagRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalSuperRankSampleTables,
    SuccinctRank.canonicalSuperRankEntries_length,
    GenericSelect.longFlagRankBlocksPerSuper, Nat.div_one,
    packedLongFlagRankSlots, longFlagBits_length_eq_packed,
    longFlagRankWordSize_eq_packed]

theorem packedLongFlagRankBlockTrue_length (shape : CartesianShape) :
    (GenericSelect.longFlagRankData shape.bpCode
      false).blockTables.trueTable.payload.length =
      packedLongFlagRankSlots shape.size * packedLongFlagWordSize shape.size := by
  rw [SuccinctSpace.FixedWidthNatTable.payload_length]
  simp only [GenericSelect.longFlagRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan,
    SuccinctRank.canonicalBlockRankEntries_length,
    GenericSelect.longFlagRankBlockWidth, packedLongFlagRankSlots,
    longFlagBits_length_eq_packed, longFlagRankWordSize_eq_packed]

theorem packedSparseRankSuperTrue_length (shape : CartesianShape) :
    (GenericSelect.sparseExceptionEffectiveFlagRankData shape.bpCode
      false).superTables.trueTable.payload.length =
      packedSparseRankSlots shape.size * packedSparseWordSize shape.size := by
  rw [SuccinctSpace.FixedWidthNatTable.payload_length]
  simp only [GenericSelect.sparseExceptionEffectiveFlagRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalSuperRankSampleTables,
    SuccinctRank.canonicalSuperRankEntries_length,
    GenericSelect.sparseExceptionEffectiveFlagRankBlocksPerSuper, Nat.div_one,
    packedSparseRankSlots, sparseFlagBits_length_eq_packed,
    sparseFlagRankWordSize_eq_packed]

theorem packedSparseRankBlockTrue_length (shape : CartesianShape) :
    (GenericSelect.sparseExceptionEffectiveFlagRankData shape.bpCode
      false).blockTables.trueTable.payload.length =
      packedSparseRankSlots shape.size * packedSparseWordSize shape.size := by
  rw [SuccinctSpace.FixedWidthNatTable.payload_length]
  simp only [GenericSelect.sparseExceptionEffectiveFlagRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan,
    SuccinctRank.canonicalBlockRankEntries_length,
    GenericSelect.sparseExceptionEffectiveFlagRankBlockWidth,
    packedSparseRankSlots, sparseFlagBits_length_eq_packed,
    sparseFlagRankWordSize_eq_packed]

theorem packedInteriorGlobal_length (shape : CartesianShape) :
    (SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable shape).payload.length =
      packedInteriorGlobalSlots shape.size *
        packedInteriorBlockWidth shape.size := by
  rw [SuccinctClose.PayloadLiveBPGlobalSparseBlockTable.payload_length]
  unfold packedInteriorGlobalSlots packedInteriorGlobalLevelCount
    packedInteriorBlockWidth
  simp only [SuccinctClose.concreteBPRelativeRmmInteriorGlobalLevelCount,
    SuccinctClose.concreteBPRelativeRmmInteriorBlockWidth,
    interiorMacroCount_eq_packed, summaryBlockCount_eq_packed]

/-! ## The bit lengths agree with the shape-indexed payloads

The same closed case analysis as `packedSourceComponentOffset_eq`, over the same
length mirrors: what that theorem uses to place a source, this one uses to size
it.
-/

set_option maxHeartbeats 1000000 in
theorem packedSourceBitLength_eq
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hne :
      source !=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length =
      packedSourceBitLength shape.size (longCount shape) source := by
  have hbp := CartesianShape.bpCode_length shape
  have hsuperBase := superTable_column_length shape
  have hsuperWord := superTable_baseWordIndex_length shape
  have hsuperRank := superTable_rankBefore_length shape
  have hsuperAll := superTable_length shape
  have hflag := longFlagBits_length_eq_packed shape
  have hlongRel := longSuperRelativeTable_length_eq shape
  have hlocalBase := localTable_baseOccurrence_length shape
  have hlocalWord := localTable_baseWordIndex_length shape
  have hlocalRank := localTable_rankBefore_length shape
  have hlocalAll := localTable_length shape
  have hsparseFlag := sparseFlagBits_length_eq_packed shape
  have hrankSuperTrue := rankSuperTrue_length_eq_packed shape
  have hrankBlockTrue := rankBlockTrue_length_eq_packed shape
  have hsumBaseline := summaryBaseline_length_eq_packed shape
  have hsumMin := summaryMinRel_length_eq_packed shape
  have hsumMax := summaryMaxRel_length_eq_packed shape
  have hsumArg := summaryArgOffset_length_eq_packed shape
  have hinteriorLocal := interiorLocal_length_eq_packed shape
  have hsuperFirst := packedSuperTable_firstOffset_length shape
  have hlocalFirst := packedLocalTable_firstOffset_length shape
  have hrankSuperFalse := packedRankSuperFalse_length shape
  have hrankBlockFalse := packedRankBlockFalse_length shape
  have hlongFlagSuper := packedLongFlagRankSuperTrue_length shape
  have hlongFlagBlock := packedLongFlagRankBlockTrue_length shape
  have hsparseRankSuper := packedSparseRankSuperTrue_length shape
  have hsparseRankBlock := packedSparseRankBlockTrue_length shape
  have hinteriorGlobal := packedInteriorGlobal_length shape
  cases source <;>
    simp only [concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
      packedSourceBitLength, packedSourceWordCount, packedSourceStride,
      GenericSelect.sparseExceptionSelectData,
      GenericSelect.sparseExceptionDirectory,
      hbp, hsuperBase, hsuperWord, hsuperRank, hflag, hlongRel,
      hlocalBase, hlocalWord, hlocalRank, hsparseFlag,
      hrankSuperTrue, hrankBlockTrue,
      hsumBaseline, hsumMin, hsumMax, hsumArg, hinteriorLocal,
      packedSuperColumn, packedLocalColumn, packedRankSuperColumn,
      packedRankBlockColumn, packedSummaryBaselineLength,
      packedSummaryBlockColumnLength, packedInteriorLocalLength,
      packedRankSuperSlots, packedRankBlockSlots, packedLongRelativeSlots,
      packedInteriorLocalSlots, packedLongBlockBits, packedSuperWidth,
      hsuperFirst, hlocalFirst, hrankSuperFalse, hrankBlockFalse,
      hlongFlagSuper, hlongFlagBlock, hsparseRankSuper, hsparseRankBlock,
      hinteriorGlobal, Nat.mul_assoc] <;>
    first
      | rfl
      | simp at hne
      | omega


/-! ## The equation, for the twenty-eight size-only sources

`packedSourceWords_of_some` is one-directional because of `.selectSparseRelative`.
Excluding that one source recovers the equation, and with it the `none` direction
a store equality needs: past the word count the store has nothing and neither does
the packed read.
-/

theorem packedSourceWords_eq
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hsparse :
      source !=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative)
    (index : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source)
        (packedSourceWordCount shape.size (longCount shape) source)
        (packedSourceStride shape.size source) index := by
  cases source with
  | bpCode =>
      exact packedBpCodeWords shape index
  | selectSuperBaseOccurrence =>
      exact packedSelectSuperBaseOccurrenceWords shape index
  | selectSuperBaseWordIndex =>
      exact packedSelectSuperBaseWordIndexWords shape index
  | selectSuperRankBefore =>
      exact packedSelectSuperRankBeforeWords shape index
  | selectSuperFirstOffset =>
      exact packedSelectSuperFirstOffsetWords shape index
  | selectLocalBaseOccurrence =>
      exact packedSelectLocalBaseOccurrenceWords shape index
  | selectLocalBaseWordIndex =>
      exact packedSelectLocalBaseWordIndexWords shape index
  | selectLocalRankBefore =>
      exact packedSelectLocalRankBeforeWords shape index
  | selectLocalFirstOffset =>
      exact packedSelectLocalFirstOffsetWords shape index
  | selectLongFlagBits =>
      exact packedSelectLongFlagBitsWords shape index
  | selectLongFlagRankSuperTrue =>
      exact packedSelectLongFlagRankSuperTrueWords shape index
  | selectLongFlagRankBlockTrue =>
      exact packedSelectLongFlagRankBlockTrueWords shape index
  | selectLongRelative =>
      exact packedSelectLongRelativeWords shape index
  | selectSparseFlagBits =>
      exact packedSelectSparseFlagBitsWords shape index
  | selectSparseRankSuperTrue =>
      exact packedSelectSparseRankSuperTrueWords shape index
  | selectSparseRankBlockTrue =>
      exact packedSelectSparseRankBlockTrueWords shape index
  | selectSparseRelative =>
      simp at hsparse
  | finalRankSuperFalse =>
      exact packedFinalRankSuperFalseWords shape index
  | finalRankBlockFalse =>
      exact packedFinalRankBlockFalseWords shape index
  | finalRankBPCodeAlias =>
      exact packedFinalRankBPCodeAliasWords shape index
  | closeSummaryBaseline =>
      exact packedCloseSummaryBaselineWords shape index
  | closeSummaryMinRel =>
      exact packedCloseSummaryMinRelWords shape index
  | closeSummaryMaxRel =>
      exact packedCloseSummaryMaxRelWords shape index
  | closeSummaryArgOffset =>
      exact packedCloseSummaryArgOffsetWords shape index
  | closeInteriorLocal =>
      exact packedCloseInteriorLocalWords shape index
  | closeInteriorGlobal =>
      exact packedCloseInteriorGlobalWords shape index
  | closeFiniteSmallInteriorMin =>
      exact packedCloseFiniteSmallInteriorMinWords shape index
  | closeFiniteSmallInteriorArg =>
      exact packedCloseFiniteSmallInteriorArgWords shape index
  | closeFiniteSmallSameBlock =>
      exact packedCloseFiniteSmallSameBlockWords shape index

theorem packedSourceWords_of_none
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hsparse :
      source !=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative)
    {index : Nat}
    (hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? =
        none) :
    packedSourceWordCount shape.size (longCount shape) source <= index := by
  rw [packedSourceWords_eq shape source hsparse index] at hget
  by_cases hlt : index < packedSourceWordCount shape.size (longCount shape) source
  · rw [packedWordSlice_of_lt hlt] at hget
    exact absurd hget (by simp)
  · omega

end PackedCellProbe

end SuccinctFinal

end RMQ
