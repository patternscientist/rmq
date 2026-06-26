import RMQ.Core.SuccinctSelect.CloseSelect.BuiltRouting.RelativeEntries

/-!
# Sparse/dense flag-rank tables

Split implementation layer for built sparse/dense close-select routing.
Public declarations stay in the historical `RMQ.SuccinctSelectProposal`
namespace until the namespace-alignment cleanup pass.
-/

namespace RMQ
namespace SuccinctSelectProposal

def builtRelativeSplitFalseSelectSuperEntry
    (shape : Cartesian.CartesianShape) (superSlot : Nat) :
    SparseDenseFalseSelectDenseLocalEntry :=
  let baseOccurrence :=
    superSlot * sparseDenseFalseSelectSuperStride shape
  let basePosition :=
    builtRelativeSplitFalseSelectPosition shape baseOccurrence
  let wordSize := sparseDenseFalseSelectWordBits shape
  { baseOccurrence := baseOccurrence
    baseWordIndex := basePosition / wordSize
    rankBefore :=
      if builtRelativeSplitFalseSelectSuperIsLong shape superSlot then 1 else 0
    firstOffset := basePosition - (basePosition / wordSize) * wordSize }

def builtRelativeSplitFalseSelectSuperEntries
    (shape : Cartesian.CartesianShape) :
    List SparseDenseFalseSelectDenseLocalEntry :=
  (List.range (builtRectangularFalseSelectSuperSlotCount shape)).map
    (builtRelativeSplitFalseSelectSuperEntry shape)

def builtRelativeSplitFalseSelectCompactLocalEntryIsLive
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Bool :=
  (! builtRelativeSplitFalseSelectSuperIsLong shape
      (builtRelativeSplitFalseSelectLocalSuperSlot
        shape globalLocalSlot)) &&
    decide
      (builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot <
        falseSelectOccurrenceCount shape)

def builtRelativeSplitFalseSelectLocalEntry
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    SparseDenseFalseSelectDenseLocalEntry :=
  if builtRelativeSplitFalseSelectCompactLocalEntryIsLive
      shape globalLocalSlot then
    let superSlot :=
      builtRelativeSplitFalseSelectLocalSuperSlot shape globalLocalSlot
    let superBaseOccurrence :=
      superSlot * sparseDenseFalseSelectSuperStride shape
    let superBasePosition :=
      builtRelativeSplitFalseSelectPosition shape superBaseOccurrence
    let baseOccurrence :=
      builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot
    let basePosition :=
      builtRelativeSplitFalseSelectPosition shape baseOccurrence
    let wordSize := sparseDenseFalseSelectWordBits shape
    { baseOccurrence := baseOccurrence - superBaseOccurrence
      baseWordIndex := basePosition / wordSize - superBasePosition / wordSize
      rankBefore :=
        if builtRelativeSplitFalseSelectLocalIsSparseException
            shape globalLocalSlot then 1 else 0
      firstOffset := basePosition - (basePosition / wordSize) * wordSize }
  else
    { baseOccurrence := 0
      baseWordIndex := 0
      rankBefore := 0
      firstOffset := 0 }

def builtRelativeSplitFalseSelectLocalEntries
    (shape : Cartesian.CartesianShape) :
    List SparseDenseFalseSelectDenseLocalEntry :=
  (List.range (builtRectangularFalseSelectLocalSlotCount shape)).map
    (builtRelativeSplitFalseSelectLocalEntry shape)

def builtRelativeSplitFalseSelectSparseFlagBits
    (shape : Cartesian.CartesianShape) : List Bool :=
  (List.range (builtRectangularFalseSelectLocalSlotCount shape)).map
    (builtRelativeSplitFalseSelectLocalIsSparse shape)

def builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    List Nat :=
  if builtRelativeSplitFalseSelectLocalIsSparse shape globalLocalSlot then
    let baseOccurrence :=
      builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot
    let basePosition :=
      builtRelativeSplitFalseSelectPosition shape baseOccurrence
    (falseSelectPositions shape.bpCode baseOccurrence
      (sparseDenseFalseSelectLocalStride shape)).map
        (fun pos => pos - basePosition)
  else
    []

def builtRelativeSplitFalseSelectSparseRelativeEntries
    (shape : Cartesian.CartesianShape) : List Nat :=
  (List.range (builtRectangularFalseSelectLocalSlotCount shape)).flatMap
    (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape)

def builtRelativeSplitFalseSelectFlagRankWordSize
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits
    (builtRelativeSplitFalseSelectSparseFlagBits shape).length

def builtRelativeSplitFalseSelectFlagRankBlocksPerSuper
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRelativeSplitFalseSelectFlagRankWordSize shape

def builtRelativeSplitFalseSelectFlagRankBlockWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits
    (builtRelativeSplitFalseSelectFlagRankBlocksPerSuper shape *
      builtRelativeSplitFalseSelectFlagRankWordSize shape)

theorem builtRelativeSplitFalseSelectFlagRankWordSize_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtRelativeSplitFalseSelectFlagRankWordSize shape := by
  simp [builtRelativeSplitFalseSelectFlagRankWordSize,
    SuccinctRank.machineWordBits_pos]

theorem builtRelativeSplitFalseSelectFlagRankBlocksPerSuper_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtRelativeSplitFalseSelectFlagRankBlocksPerSuper shape := by
  simpa [builtRelativeSplitFalseSelectFlagRankBlocksPerSuper] using
    builtRelativeSplitFalseSelectFlagRankWordSize_pos shape

theorem builtRelativeSplitFalseSelectSparseFlagBits_length_lt_rank_word_pow
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseFlagBits shape).length <
      2 ^ builtRelativeSplitFalseSelectFlagRankWordSize shape := by
  simpa [builtRelativeSplitFalseSelectFlagRankWordSize,
    SuccinctRank.machineWordBits] using
    (Nat.lt_log2_self
      (n := (builtRelativeSplitFalseSelectSparseFlagBits shape).length))

theorem builtRelativeSplitFalseSelectFlagRankBlockSpan_lt_pow
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectFlagRankBlocksPerSuper shape *
        builtRelativeSplitFalseSelectFlagRankWordSize shape <
      2 ^ builtRelativeSplitFalseSelectFlagRankBlockWidth shape := by
  simpa [builtRelativeSplitFalseSelectFlagRankBlockWidth,
    SuccinctRank.machineWordBits] using
    (Nat.lt_log2_self
      (n :=
        builtRelativeSplitFalseSelectFlagRankBlocksPerSuper shape *
          builtRelativeSplitFalseSelectFlagRankWordSize shape))

def builtRelativeSplitFalseSelectFlagRankSuperOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRank.canonicalSuperRankSampleTables
      (builtRelativeSplitFalseSelectSparseFlagBits shape)
      (builtRelativeSplitFalseSelectFlagRankWordSize shape)
      (builtRelativeSplitFalseSelectFlagRankBlocksPerSuper shape)
      (builtRelativeSplitFalseSelectFlagRankWordSize shape)
      (builtRelativeSplitFalseSelectSparseFlagBits_length_lt_rank_word_pow
        shape)).payload.length

def builtRelativeSplitFalseSelectFlagRankBlockOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan
      (builtRelativeSplitFalseSelectSparseFlagBits shape)
      (builtRelativeSplitFalseSelectFlagRankWordSize shape)
      (builtRelativeSplitFalseSelectFlagRankBlocksPerSuper shape)
      (builtRelativeSplitFalseSelectFlagRankBlockWidth shape)
      (builtRelativeSplitFalseSelectFlagRankBlocksPerSuper_pos shape)
      (builtRelativeSplitFalseSelectFlagRankBlockSpan_lt_pow
        shape)).payload.length

def builtRelativeSplitFalseSelectFlagRankData
    (shape : Cartesian.CartesianShape) :
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      (builtRelativeSplitFalseSelectSparseFlagBits shape)
      (builtRelativeSplitFalseSelectFlagRankSuperOverhead shape)
      (builtRelativeSplitFalseSelectFlagRankBlockOverhead shape)
      4 :=
  SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock
    (builtRelativeSplitFalseSelectSparseFlagBits shape)
    (builtRelativeSplitFalseSelectFlagRankWordSize_pos shape)
    (by simp [builtRelativeSplitFalseSelectFlagRankWordSize])
    (builtRelativeSplitFalseSelectFlagRankBlocksPerSuper_pos shape)
    (builtRelativeSplitFalseSelectSparseFlagBits_length_lt_rank_word_pow
      shape)
    (builtRelativeSplitFalseSelectFlagRankBlockSpan_lt_pow shape)
    (by omega)

theorem builtRelativeSplitFalseSelectFlagRankData_profile
    (shape : Cartesian.CartesianShape) :
    let data := builtRelativeSplitFalseSelectFlagRankData shape
    data.auxPayload.length =
        builtRelativeSplitFalseSelectFlagRankSuperOverhead shape +
          builtRelativeSplitFalseSelectFlagRankBlockOverhead shape /\
      data.wordSize <=
        SuccinctRank.machineWordBits
          (builtRelativeSplitFalseSelectSparseFlagBits shape).length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        builtRelativeSplitFalseSelectSparseFlagBits shape /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <=
            SuccinctRank.machineWordBits
              (builtRelativeSplitFalseSelectSparseFlagBits shape).length) /\
      forall target pos,
        (data.rankCosted target pos).cost <= 4 /\
          (data.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target
              (builtRelativeSplitFalseSelectSparseFlagBits shape) pos := by
  exact
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
      (builtRelativeSplitFalseSelectSparseFlagBits shape)
      (builtRelativeSplitFalseSelectFlagRankWordSize_pos shape)
      (by simp [builtRelativeSplitFalseSelectFlagRankWordSize])
      (builtRelativeSplitFalseSelectFlagRankBlocksPerSuper_pos shape)
      (builtRelativeSplitFalseSelectSparseFlagBits_length_lt_rank_word_pow
        shape)
      (builtRelativeSplitFalseSelectFlagRankBlockSpan_lt_pow shape)
      (by omega)

def builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits
    (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape).length

def builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize shape

def builtRelativeSplitFalseSelectSparseExceptionFlagRankBlockWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits
    (builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper
        shape *
      builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize shape)

theorem builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize_pos
    (shape : Cartesian.CartesianShape) :
    0 <
      builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize
        shape := by
  simp [builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize,
    SuccinctRank.machineWordBits_pos]

theorem builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper_pos
    (shape : Cartesian.CartesianShape) :
    0 <
      builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper
        shape := by
  simpa [builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper]
    using
      builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize_pos
        shape

theorem builtRelativeSplitFalseSelectSparseExceptionFlagBits_length_lt_rank_word_pow
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape).length <
      2 ^
        builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize
          shape := by
  simpa [builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize,
    SuccinctRank.machineWordBits] using
    (Nat.lt_log2_self
      (n :=
        (builtRelativeSplitFalseSelectSparseExceptionFlagBits
          shape).length))

theorem builtRelativeSplitFalseSelectSparseExceptionFlagRankBlockSpan_lt_pow
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper
          shape *
        builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize
          shape <
      2 ^
        builtRelativeSplitFalseSelectSparseExceptionFlagRankBlockWidth
          shape := by
  simpa [builtRelativeSplitFalseSelectSparseExceptionFlagRankBlockWidth,
    SuccinctRank.machineWordBits] using
    (Nat.lt_log2_self
      (n :=
        builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper
            shape *
          builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize
            shape))

def builtRelativeSplitFalseSelectSparseExceptionFlagRankSuperOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRank.canonicalSuperRankSampleTables
      (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagBits_length_lt_rank_word_pow
        shape)).payload.length

def builtRelativeSplitFalseSelectSparseExceptionFlagRankBlockOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan
      (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankBlockWidth
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper_pos
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankBlockSpan_lt_pow
        shape)).payload.length

def builtRelativeSplitFalseSelectSparseExceptionFlagRankData
    (shape : Cartesian.CartesianShape) :
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankSuperOverhead
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankBlockOverhead
        shape)
      4 :=
  SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock
    (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
    (builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize_pos
      shape)
    (by
      simp [builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize])
    (builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper_pos
      shape)
    (builtRelativeSplitFalseSelectSparseExceptionFlagBits_length_lt_rank_word_pow
      shape)
    (builtRelativeSplitFalseSelectSparseExceptionFlagRankBlockSpan_lt_pow
      shape)
    (by omega)

theorem builtRelativeSplitFalseSelectSparseExceptionFlagRankData_profile
    (shape : Cartesian.CartesianShape) :
    let data :=
      builtRelativeSplitFalseSelectSparseExceptionFlagRankData shape
    data.auxPayload.length =
        builtRelativeSplitFalseSelectSparseExceptionFlagRankSuperOverhead
            shape +
          builtRelativeSplitFalseSelectSparseExceptionFlagRankBlockOverhead
            shape /\
      data.wordSize <=
        SuccinctRank.machineWordBits
          (builtRelativeSplitFalseSelectSparseExceptionFlagBits
            shape).length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        builtRelativeSplitFalseSelectSparseExceptionFlagBits shape /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <=
            SuccinctRank.machineWordBits
              (builtRelativeSplitFalseSelectSparseExceptionFlagBits
                shape).length) /\
      forall target pos,
        (data.rankCosted target pos).cost <= 4 /\
          (data.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target
              (builtRelativeSplitFalseSelectSparseExceptionFlagBits
                shape) pos := by
  exact
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
      (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize_pos
        shape)
      (by
        simp [builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize])
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper_pos
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagBits_length_lt_rank_word_pow
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankBlockSpan_lt_pow
        shape)
      (by omega)

def builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
      shape).length

def builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper
    (_shape : Cartesian.CartesianShape) : Nat := 1

def builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
    shape

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize_pos
    (shape : Cartesian.CartesianShape) :
    0 <
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
        shape := by
  simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize,
    SuccinctRank.machineWordBits_pos]

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_le_bpCode_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
        shape).length <= shape.bpCode.length := by
  have hlen :
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
          shape).length <= falseSelectOccurrenceCount shape := by
    rw [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length]
    exact
      builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_count
        shape
  have hcountSize :
      falseSelectOccurrenceCount shape = shape.size :=
    falseSelectOccurrenceCount_eq_size shape
  have hsizeLen : shape.size <= shape.bpCode.length := by
    have hbp : shape.bpCode.length = 2 * shape.size := by
      exact Cartesian.CartesianShape.bpCode_length shape
    omega
  exact Nat.le_trans hlen (by simpa [hcountSize] using hsizeLen)

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize_le_machine
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
        shape <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  unfold builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
  exact machineWordBits_mono_le
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_le_bpCode_length
      shape)

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper_pos
    (shape : Cartesian.CartesianShape) :
    0 <
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper
        shape := by
  simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper]

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_lt_rank_word_pow
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
        shape).length <
      2 ^
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
          shape := by
  simpa [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize,
    SuccinctRank.machineWordBits] using
      (Nat.lt_log2_self
        (n :=
          (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
            shape).length))

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockSpan_lt_pow
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper
          shape *
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
          shape <
      2 ^
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockWidth
          shape := by
  have hword :
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
          shape <
        2 ^
          builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
            shape := by
    have hsucc :=
      SuccinctSpace.nat_succ_le_two_pow
        (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
          shape)
    omega
  simpa [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper,
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockWidth]
    using hword

def builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRank.canonicalSuperRankSampleTables
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_lt_rank_word_pow
        shape)).payload.length

def builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockWidth
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper_pos
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockSpan_lt_pow
        shape)).payload.length

def builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData
    (shape : Cartesian.CartesianShape) :
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
        shape)
      4 :=
  SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits shape)
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize_pos
      shape)
    (by
      simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize,
        SuccinctRank.machineWordBits])
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper_pos
      shape)
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_lt_rank_word_pow
      shape)
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockSpan_lt_pow
      shape)
    (Nat.le_refl 4)

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData_profile
    (shape : Cartesian.CartesianShape) :
    let data :=
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData
        shape
    data.auxPayload.length =
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
            shape +
          builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
            shape /\
      data.wordSize <=
        SuccinctRank.machineWordBits shape.bpCode.length /\
      data.superWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length /\
      data.blockWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits shape /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      forall target pos,
        (data.rankCosted target pos).cost <= 4 /\
          (data.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target
              (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
                shape) pos := by
  have hprofile :=
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize_pos
        shape)
      (by
        simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize,
          SuccinctRank.machineWordBits])
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper_pos
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_lt_rank_word_pow
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockSpan_lt_pow
        shape)
      (Nat.le_refl 4)
  dsimp only at hprofile
  rcases hprofile with
    ⟨haux, hword, hflatten, hbitWords, hexact⟩
  have hwordBp :
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData
          shape).wordSize <=
        SuccinctRank.machineWordBits shape.bpCode.length := by
    simpa [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData]
      using
        Nat.le_trans hword
          (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize_le_machine
            shape)
  exact
    ⟨haux, hwordBp,
      hwordBp,
      by
        simpa [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockWidth]
          using
            builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize_le_machine
              shape,
      hflatten,
      (fun {word} hmem =>
        Nat.le_trans (hbitWords hmem)
          (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize_le_machine
            shape)),
      hexact⟩

theorem builtRelativeSplitFalseSelectSuperEntries_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSuperEntries shape).length =
      builtRectangularFalseSelectSuperSlotCount shape := by
  simp [builtRelativeSplitFalseSelectSuperEntries]

theorem builtRelativeSplitFalseSelectLocalEntries_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLocalEntries shape).length =
      builtRectangularFalseSelectLocalSlotCount shape := by
  simp [builtRelativeSplitFalseSelectLocalEntries]

theorem builtRelativeSplitFalseSelectSuperEntries_get?
    (shape : Cartesian.CartesianShape) {superSlot : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape) :
    (builtRelativeSplitFalseSelectSuperEntries shape)[superSlot]? =
      some (builtRelativeSplitFalseSelectSuperEntry shape superSlot) := by
  simp [builtRelativeSplitFalseSelectSuperEntries, List.getElem?_map,
    List.getElem?_range hslot]

theorem builtRelativeSplitFalseSelectLocalEntries_get?
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape) :
    (builtRelativeSplitFalseSelectLocalEntries shape)[globalLocalSlot]? =
      some
        (builtRelativeSplitFalseSelectLocalEntry shape globalLocalSlot) := by
  simp [builtRelativeSplitFalseSelectLocalEntries, List.getElem?_map,
    List.getElem?_range hslot]

theorem builtRelativeSplitFalseSelectSparseFlagBits_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseFlagBits shape).length =
      builtRectangularFalseSelectLocalSlotCount shape := by
  simp [builtRelativeSplitFalseSelectSparseFlagBits]

theorem builtRelativeSplitFalseSelectSparseFlagBits_get?
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape) :
    (builtRelativeSplitFalseSelectSparseFlagBits shape)[globalLocalSlot]? =
      some
        (builtRelativeSplitFalseSelectLocalIsSparse
          shape globalLocalSlot) := by
  simp [builtRelativeSplitFalseSelectSparseFlagBits, List.getElem?_map,
    List.getElem?_range hslot]

theorem rankPrefix_succ_eq_of_get?
    {target bit : Bool} {bits : List Bool} {n : Nat}
    (hget : bits[n]? = some bit) :
    RMQ.Succinct.rankPrefix target bits (n + 1) =
      RMQ.Succinct.rankPrefix target bits n +
        if bit = target then 1 else 0 := by
  induction bits generalizing n with
  | nil =>
      simp at hget
  | cons head tail ih =>
      cases n with
      | zero =>
          simp [RMQ.Succinct.rankPrefix] at hget ⊢
          subst bit
          omega
      | succ n =>
          simp at hget
          have htail := ih hget
          by_cases hhead : head = target
          · simp [RMQ.Succinct.rankPrefix, hhead, htail,
              Nat.add_comm, Nat.add_left_comm]
          · simp [RMQ.Succinct.rankPrefix, hhead, htail,
              Nat.add_comm]

theorem builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot_length
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
      shape globalLocalSlot).length =
      if builtRelativeSplitFalseSelectLocalIsSparse
          shape globalLocalSlot then
        sparseDenseFalseSelectLocalStride shape
      else
        0 := by
  by_cases hsparse :
      builtRelativeSplitFalseSelectLocalIsSparse shape globalLocalSlot = true
  · simp [builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot,
      hsparse, falseSelectPositions]
  · have hfalse :
      builtRelativeSplitFalseSelectLocalIsSparse shape globalLocalSlot =
        false := by
      cases h :
          builtRelativeSplitFalseSelectLocalIsSparse shape globalLocalSlot
      · rfl
      · contradiction
    simp [builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot,
      hfalse]

theorem builtRelativeSplitFalseSelectSparseRelativePrefix_length
    (shape : Cartesian.CartesianShape) {n : Nat}
    (hn :
      n <= builtRectangularFalseSelectLocalSlotCount shape) :
    ((List.range n).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
          shape)).length =
      RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseFlagBits shape) n *
          sparseDenseFalseSelectLocalStride shape := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix]
  | succ n ih =>
      have hn' :
          n <= builtRectangularFalseSelectLocalSlotCount shape := by
        omega
      have hslot :
          n < builtRectangularFalseSelectLocalSlotCount shape := by
        omega
      have hget :=
        builtRelativeSplitFalseSelectSparseFlagBits_get?
          shape (globalLocalSlot := n) hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true)
          (bits := builtRelativeSplitFalseSelectSparseFlagBits shape)
          (n := n)
          hget
      have hprefix :
          (List.map
              (List.length ∘
                builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
                  shape)
              (List.range n)).sum =
            RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectSparseFlagBits shape) n *
                sparseDenseFalseSelectLocalStride shape := by
        simpa [List.length_flatMap, Function.comp] using ih hn'
      rw [List.range_succ]
      rw [List.flatMap_append]
      simp [List.flatMap,
        builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot_length,
        hrank]
      by_cases hsparse :
          builtRelativeSplitFalseSelectLocalIsSparse shape n = true
      · rw [hprefix]
        simp [hsparse, Nat.add_mul, Nat.add_comm]
      · have hfalse :
          builtRelativeSplitFalseSelectLocalIsSparse shape n = false := by
          cases h :
              builtRelativeSplitFalseSelectLocalIsSparse shape n
          · rfl
          · contradiction
        rw [hprefix]
        simp [hfalse]

theorem builtRelativeSplitFalseSelectSparseExceptionFlagBits_get?
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape) :
    (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)[
        globalLocalSlot]? =
      some
        (builtRelativeSplitFalseSelectLocalIsSparseException
          shape globalLocalSlot) := by
  simp [builtRelativeSplitFalseSelectSparseExceptionFlagBits,
    List.getElem?_map, List.getElem?_range hslot]

theorem builtRelativeSplitFalseSelectSparseExceptionRelativePrefix_length
    (shape : Cartesian.CartesianShape) {n : Nat}
    (hn :
      n <= builtRectangularFalseSelectLocalSlotCount shape) :
    ((List.range n).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)).length =
      RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape) n *
          sparseDenseFalseSelectLocalStride shape := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix]
  | succ n ih =>
      have hn' :
          n <= builtRectangularFalseSelectLocalSlotCount shape := by
        omega
      have hslot :
          n < builtRectangularFalseSelectLocalSlotCount shape := by
        omega
      have hget :=
        builtRelativeSplitFalseSelectSparseExceptionFlagBits_get?
          shape (globalLocalSlot := n) hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true)
          (bits := builtRelativeSplitFalseSelectSparseExceptionFlagBits
            shape)
          (n := n)
          hget
      have hprefix :
          (List.map
              (List.length ∘
                builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
                  shape)
              (List.range n)).sum =
            RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectSparseExceptionFlagBits
                shape) n *
                sparseDenseFalseSelectLocalStride shape := by
        simpa [List.length_flatMap, Function.comp] using ih hn'
      rw [List.range_succ]
      rw [List.flatMap_append]
      simp [List.flatMap,
        builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot_length,
        hrank]
      by_cases hflag :
          builtRelativeSplitFalseSelectLocalIsSparseException shape n =
            true
      · rw [hprefix]
        simp [hflag, Nat.add_mul, Nat.add_comm]
      · have hfalse :
          builtRelativeSplitFalseSelectLocalIsSparseException shape n =
            false := by
          cases h :
              builtRelativeSplitFalseSelectLocalIsSparseException shape n
          · rfl
          · contradiction
        rw [hprefix]
        simp [hfalse]

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
      shape).length =
      RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
        (builtRectangularFalseSelectLocalSlotCount shape) *
          sparseDenseFalseSelectLocalStride shape := by
  simpa [builtRelativeSplitFalseSelectSparseExceptionRelativeEntries] using
    builtRelativeSplitFalseSelectSparseExceptionRelativePrefix_length
      shape (Nat.le_refl _)

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
      shape).payload.length =
      RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
        (builtRectangularFalseSelectLocalSlotCount shape) *
          sparseDenseFalseSelectLocalStride shape *
          builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape := by
  rw [(builtRelativeSplitFalseSelectSparseExceptionRelativeTable
    shape).payload_length_eq]
  rw [builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_length]

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_of_count_bound
    (shape : Cartesian.CartesianShape) {budget : Nat}
    (hcount :
      RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
          (builtRectangularFalseSelectLocalSlotCount shape) *
            sparseDenseFalseSelectLocalStride shape *
            builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape <=
        budget) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
      shape).payload.length <= budget := by
  rw [builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_length]
  exact hcount


end SuccinctSelectProposal
end RMQ
