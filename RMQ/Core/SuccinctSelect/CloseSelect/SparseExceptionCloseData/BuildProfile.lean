import RMQ.Core.SuccinctSelect.CloseSelect.SparseExceptionCloseData.BuiltExact

/-!
# Built sparse-exception profile

Split implementation layer for sparse-exception close-select data.
Public declarations stay in the historical `RMQ.SuccinctSelectProposal`
namespace until the namespace-alignment cleanup pass.
-/

namespace RMQ
namespace SuccinctSelectProposal

theorem falseSelectCeilDiv_le_self_of_pos
    {n stride : Nat} (hn : 0 < n) (hstride : 0 < stride) :
    falseSelectCeilDiv n stride <= n := by
  unfold falseSelectCeilDiv
  cases n with
  | zero =>
      omega
  | succ n =>
      apply Nat.div_le_of_le_mul
      have hnum :
          n + 1 + stride - 1 <= (n + 1) * stride :=
        nat_add_sub_one_le_mul_of_pos
          (a := n + 1) (b := stride) (by omega) hstride
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hnum

theorem builtRelativeSplitFalseSelectLongSuperFlagBits_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length =
      builtRectangularFalseSelectSuperSlotCount shape := by
  simp [builtRelativeSplitFalseSelectLongSuperFlagBits]

theorem builtRelativeSplitFalseSelectLongSuperFlagBits_length_le_bpCode_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length <=
      shape.bpCode.length := by
  by_cases hcount : falseSelectOccurrenceCount shape = 0
  · have hsuperZero :
        builtRectangularFalseSelectSuperSlotCount shape = 0 := by
      unfold builtRectangularFalseSelectSuperSlotCount falseSelectCeilDiv
      rw [hcount]
      have hstride := sparseDenseFalseSelectSuperStride_pos shape
      have hlt :
          sparseDenseFalseSelectSuperStride shape - 1 <
            sparseDenseFalseSelectSuperStride shape :=
        Nat.pred_lt (Nat.ne_of_gt hstride)
      exact Nat.div_eq_of_lt (by simpa using hlt)
    simp [builtRelativeSplitFalseSelectLongSuperFlagBits_length,
      hsuperZero]
  · have hcountPos : 0 < falseSelectOccurrenceCount shape :=
      Nat.pos_of_ne_zero hcount
    have hsuperLeCount :
        builtRectangularFalseSelectSuperSlotCount shape <=
          falseSelectOccurrenceCount shape := by
      simpa [builtRectangularFalseSelectSuperSlotCount] using
        falseSelectCeilDiv_le_self_of_pos
          (n := falseSelectOccurrenceCount shape)
          (stride := sparseDenseFalseSelectSuperStride shape)
          hcountPos (sparseDenseFalseSelectSuperStride_pos shape)
    have hcountLe := falseSelectOccurrenceCount_le_bpCode_length shape
    rw [builtRelativeSplitFalseSelectLongSuperFlagBits_length]
    exact Nat.le_trans hsuperLeCount hcountLe

theorem builtRelativeSplitFalseSelectLongSuperFlagBits_length_mul_wordBits_le
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length *
        sparseDenseFalseSelectWordBits shape <=
      5 * ((sparseDenseFalseSelectEll shape *
        (sparseDenseFalseSelectEll shape *
          sparseDenseFalseSelectEll shape)) *
        shape.bpCode.length) := by
  let flagLen := (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length
  let superCount := builtRectangularFalseSelectSuperSlotCount shape
  let wordBits := sparseDenseFalseSelectWordBits shape
  let superStride := sparseDenseFalseSelectSuperStride shape
  let ell := sparseDenseFalseSelectEll shape
  let ell3 := ell * (ell * ell)
  let n := shape.bpCode.length
  have hellOne : 1 <= ell3 := by
    have hell : 1 <= ell := by
      simp [ell, sparseDenseFalseSelectEll]
    have hmul := Nat.mul_le_mul hell (Nat.mul_le_mul hell hell)
    simpa [ell3] using hmul
  by_cases hnZero : n = 0
  · have hcountZero : falseSelectOccurrenceCount shape = 0 := by
      have hbp : shape.bpCode.length = 2 * shape.size :=
        Cartesian.CartesianShape.bpCode_length shape
      have hcount : falseSelectOccurrenceCount shape = shape.size :=
        falseSelectOccurrenceCount_eq_size shape
      omega
    have hsuperZero : superCount = 0 := by
      unfold superCount builtRectangularFalseSelectSuperSlotCount
        falseSelectCeilDiv
      rw [hcountZero]
      have hstride := sparseDenseFalseSelectSuperStride_pos shape
      have hlt :
          sparseDenseFalseSelectSuperStride shape - 1 <
            sparseDenseFalseSelectSuperStride shape :=
        Nat.pred_lt (Nat.ne_of_gt hstride)
      simpa [superStride] using Nat.div_eq_of_lt hlt
    have hsuperZeroRaw :
        builtRectangularFalseSelectSuperSlotCount shape = 0 := by
      simpa [superCount] using hsuperZero
    have hflagZero :
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length = 0 := by
      rw [builtRelativeSplitFalseSelectLongSuperFlagBits_length,
        hsuperZeroRaw]
    rw [hflagZero]
    simp [n, hnZero]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
    have hcountLe : falseSelectOccurrenceCount shape <= n := by
      simpa [n] using falseSelectOccurrenceCount_le_bpCode_length shape
    have hsuperStrideLe : superStride <= 4 * n := by
      have hsq :=
        machineWordBits_sq_le_four_mul_self_of_pos
          (n := shape.bpCode.length) hnPos
      simpa [superStride, wordBits, n,
        sparseDenseFalseSelectSuperStride,
        sparseDenseFalseSelectWordBits] using hsq
    have hsuperCountMul :
        superCount * superStride <=
          falseSelectOccurrenceCount shape + superStride := by
      simpa [superCount, superStride,
        builtRectangularFalseSelectSuperSlotCount] using
        falseSelectCeilDiv_mul_le_add
          (falseSelectOccurrenceCount shape) superStride
    have hflagMul :
        flagLen * wordBits <= 5 * n := by
      have hflagLen : flagLen = superCount := by
        simpa [flagLen] using
          builtRelativeSplitFalseSelectLongSuperFlagBits_length shape
      have hwordLeStride : wordBits <= superStride := by
        have hwordPos : 0 < wordBits := by
          simpa [wordBits] using sparseDenseFalseSelectWordBits_pos shape
        simp [superStride, wordBits, sparseDenseFalseSelectSuperStride]
        exact Nat.le_mul_of_pos_left wordBits hwordPos
      calc
        flagLen * wordBits = superCount * wordBits := by rw [hflagLen]
        _ <= superCount * superStride := by
              exact Nat.mul_le_mul_left superCount hwordLeStride
        _ <= falseSelectOccurrenceCount shape + superStride :=
              hsuperCountMul
        _ <= n + 4 * n := Nat.add_le_add hcountLe hsuperStrideLe
        _ = 5 * n := by omega
    have hscaled :
        5 * n <= 5 * (ell3 * n) := by
      have hmul := Nat.mul_le_mul_right n hellOne
      have hscaled := Nat.mul_le_mul_left 5 hmul
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled
    exact Nat.le_trans hflagMul (by
      simpa [flagLen, wordBits, ell, ell3, n, Nat.mul_assoc,
        Nat.mul_left_comm, Nat.mul_comm] using hscaled)

theorem builtRelativeSplitFalseSelectLongSuperFlagBits_length_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        40 shape.bpCode.length := by
  exact
    payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
      (shape := shape)
      (payload :=
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length)
      (scale := 20)
      (by
        have h :=
          builtRelativeSplitFalseSelectLongSuperFlagBits_length_mul_wordBits_le
            shape
        exact Nat.le_trans h (by
          simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          omega))

theorem builtRelativeSplitFalseSelectLongFlagRankWordSize_le_machine
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectLongFlagRankWordSize shape <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  unfold builtRelativeSplitFalseSelectLongFlagRankWordSize
  exact machineWordBits_mono_le
    (builtRelativeSplitFalseSelectLongSuperFlagBits_length_le_bpCode_length
      shape)

theorem builtRelativeSplitFalseSelectLongFlagRankData_auxPayload_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongFlagRankData shape).auxPayload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        192 shape.bpCode.length + 16 := by
  let flagBits := builtRelativeSplitFalseSelectLongSuperFlagBits shape
  let flagLen := flagBits.length
  let rankWord := builtRelativeSplitFalseSelectLongFlagRankWordSize shape
  let bpWord := sparseDenseFalseSelectWordBits shape
  let ell := sparseDenseFalseSelectEll shape
  let ell3 := ell * (ell * ell)
  let n := shape.bpCode.length
  let data := builtRelativeSplitFalseSelectLongFlagRankData shape
  have hrankWordLeBp : rankWord <= bpWord := by
    simpa [rankWord, bpWord, sparseDenseFalseSelectWordBits] using
      builtRelativeSplitFalseSelectLongFlagRankWordSize_le_machine shape
  have hauxEq :
      data.auxPayload.length =
        builtRelativeSplitFalseSelectLongFlagRankSuperOverhead shape +
          builtRelativeSplitFalseSelectLongFlagRankBlockOverhead shape := by
    have hprofile :=
      builtRelativeSplitFalseSelectLongFlagRankData_profile shape
    simpa [data] using hprofile.1
  have hsuperLe :
      builtRelativeSplitFalseSelectLongFlagRankSuperOverhead shape <=
        2 * (flagLen + rankWord) := by
    unfold builtRelativeSplitFalseSelectLongFlagRankSuperOverhead
    rw [SuccinctRank.canonicalSuperRankSampleTables_payload_length]
    have hentryLen :
        (SuccinctRank.canonicalSuperRankEntries true flagBits
            rankWord
            (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord,
        builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper]
    have hentryLenFalse :
        (SuccinctRank.canonicalSuperRankEntries false flagBits
            rankWord
            (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord,
        builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper]
    rw [hentryLen, hentryLenFalse]
    have hdiv : flagLen / rankWord * rankWord <= flagLen :=
      Nat.div_mul_le_self flagLen rankWord
    calc
      (flagLen / rankWord + 1) * rankWord +
          (flagLen / rankWord + 1) * rankWord <=
        (flagLen + rankWord) + (flagLen + rankWord) := by
          have hone :
              (flagLen / rankWord + 1) * rankWord <=
                flagLen + rankWord := by
            rw [Nat.add_mul, Nat.one_mul]
            exact Nat.add_le_add_right hdiv rankWord
          exact Nat.add_le_add hone hone
      _ = 2 * (flagLen + rankWord) := by omega
  have hblockLe :
      builtRelativeSplitFalseSelectLongFlagRankBlockOverhead shape <=
        2 * (flagLen + rankWord) := by
    unfold builtRelativeSplitFalseSelectLongFlagRankBlockOverhead
    rw [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length]
    have hentryLen :
        (SuccinctRank.canonicalBlockRankEntries true flagBits
            rankWord
            (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalBlockRankEntries, flagBits,
        flagLen, rankWord]
    have hentryLenFalse :
        (SuccinctRank.canonicalBlockRankEntries false flagBits
            rankWord
            (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalBlockRankEntries, flagBits,
        flagLen, rankWord]
    rw [hentryLen, hentryLenFalse]
    have hdiv : flagLen / rankWord * rankWord <= flagLen :=
      Nat.div_mul_le_self flagLen rankWord
    calc
      (flagLen / rankWord + 1) * rankWord +
          (flagLen / rankWord + 1) * rankWord <=
        (flagLen + rankWord) + (flagLen + rankWord) := by
          have hone :
              (flagLen / rankWord + 1) * rankWord <=
                flagLen + rankWord := by
            rw [Nat.add_mul, Nat.one_mul]
            exact Nat.add_le_add_right hdiv rankWord
          exact Nat.add_le_add hone hone
      _ = 2 * (flagLen + rankWord) := by omega
  have hauxLe : data.auxPayload.length <= 4 * (flagLen + rankWord) := by
    rw [hauxEq]
    calc
      builtRelativeSplitFalseSelectLongFlagRankSuperOverhead shape +
          builtRelativeSplitFalseSelectLongFlagRankBlockOverhead shape <=
        2 * (flagLen + rankWord) + 2 * (flagLen + rankWord) :=
          Nat.add_le_add hsuperLe hblockLe
      _ = 4 * (flagLen + rankWord) := by omega
  by_cases hnZero : n = 0
  · have hflagZero : flagLen = 0 := by
      have hlen :=
        builtRelativeSplitFalseSelectLongSuperFlagBits_length_le_bpCode_length
          shape
      simpa [flagBits, flagLen, n, hnZero] using hlen
    have hbpWord : bpWord = 1 := by
      simp [bpWord, sparseDenseFalseSelectWordBits,
        SuccinctRank.machineWordBits, n, hnZero]
    have hrankSmall : rankWord <= 1 := by
      simpa [hbpWord] using hrankWordLeBp
    have hauxSmall : data.auxPayload.length <= 4 := by
      have h := hauxLe
      rw [hflagZero] at h
      omega
    exact Nat.le_trans hauxSmall (by omega)
  have hflagMul :
      flagLen * bpWord <= 5 * (ell3 * n) := by
    simpa [flagBits, flagLen, bpWord, ell, ell3, n,
      sparseDenseFalseSelectWordBits, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using
      builtRelativeSplitFalseSelectLongSuperFlagBits_length_mul_wordBits_le
        shape
  have hrankMul :
      rankWord * bpWord <= 4 * (ell3 * n) := by
    have hbpSq : bpWord * bpWord <= 4 * n := by
      have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
      simpa [bpWord, sparseDenseFalseSelectWordBits, n] using
        machineWordBits_sq_le_four_mul_self_of_pos hnPos
    have hrankBp : rankWord * bpWord <= bpWord * bpWord :=
      Nat.mul_le_mul_right bpWord hrankWordLeBp
    have hellOne : 1 <= ell3 := by
      have hell : 1 <= ell := by simp [ell, sparseDenseFalseSelectEll]
      have h1 := Nat.mul_le_mul hell (Nat.mul_le_mul hell hell)
      simpa [ell3] using h1
    calc
      rankWord * bpWord <= bpWord * bpWord := hrankBp
      _ <= 4 * n := hbpSq
      _ <= 4 * (ell3 * n) := by
        have hmul := Nat.mul_le_mul_right n hellOne
        have hscaled := Nat.mul_le_mul_left 4 hmul
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled
  have hauxMul :
      data.auxPayload.length * bpWord <= 36 * (ell3 * n) := by
    calc
      data.auxPayload.length * bpWord <=
          4 * (flagLen + rankWord) * bpWord := by
            exact Nat.mul_le_mul_right bpWord hauxLe
      _ = 4 * (flagLen * bpWord + rankWord * bpWord) := by
            simp [Nat.add_mul, Nat.mul_assoc]
      _ <= 4 * (5 * (ell3 * n) + 4 * (ell3 * n)) := by
            exact Nat.mul_le_mul_left 4
              (Nat.add_le_add hflagMul hrankMul)
      _ = 36 * (ell3 * n) := by
            let t := ell3 * n
            change 4 * (5 * t + 4 * t) = 36 * t
            omega
  exact
    Nat.le_trans
      (payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
        (shape := shape) (payload := data.auxPayload.length) (scale := 96)
        (by
          have hle : 36 * (ell3 * n) <= 96 * n * ell3 := by
            simp [Nat.mul_left_comm, Nat.mul_comm]
            omega
          exact Nat.le_trans hauxMul (by
            simpa [bpWord, ell, ell3, n, sparseDenseFalseSelectWordBits,
              Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hle)))
      (Nat.le_add_right _ _)

def builtRelativeSplitSparseExceptionFalseSelectCloseData
    (shape : Cartesian.CartesianShape) :
    RelativeSplitSparseExceptionFalseSelectCloseData
      shape
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
        shape) where
  wordSize := sparseDenseFalseSelectWordBits shape
  wordSize_pos := sparseDenseFalseSelectWordBits_pos shape
  wordSize_le_machine := by
    simp [sparseDenseFalseSelectWordBits]
  superStride := sparseDenseFalseSelectSuperStride shape
  superStride_pos := sparseDenseFalseSelectSuperStride_pos shape
  localStride := sparseDenseFalseSelectLocalStride shape
  localStride_pos := sparseDenseFalseSelectLocalStride_pos shape
  localSlotsPerSuper := builtRectangularFalseSelectLocalSlotsPerSuper shape
  superEntries := builtRelativeSplitFalseSelectSuperEntries shape
  longFlagBits := builtRelativeSplitFalseSelectLongSuperFlagBits shape
  longFlagBits_eq :=
    builtRelativeSplitFalseSelectLongSuperFlagBits_eq_relativeSplitLongFlagBits
      shape
  longFlagRankSuperOverhead :=
    builtRelativeSplitFalseSelectLongFlagRankSuperOverhead shape
  longFlagRankBlockOverhead :=
    builtRelativeSplitFalseSelectLongFlagRankBlockOverhead shape
  longFlagRankData := builtRelativeSplitFalseSelectLongFlagRankData shape
  longFlagRank_wordSize_le_machine := by
    have hprofile :=
      builtRelativeSplitFalseSelectLongFlagRankData_profile shape
    exact Nat.le_trans hprofile.2.1
      (builtRelativeSplitFalseSelectLongFlagRankWordSize_le_machine shape)
  longFlagRank_superWidth_le_machine := by
    simpa [builtRelativeSplitFalseSelectLongFlagRankData] using
      builtRelativeSplitFalseSelectLongFlagRankWordSize_le_machine shape
  longFlagRank_blockWidth_le_machine := by
    simpa [builtRelativeSplitFalseSelectLongFlagRankData,
      builtRelativeSplitFalseSelectLongFlagRankBlockWidth] using
      builtRelativeSplitFalseSelectLongFlagRankWordSize_le_machine shape
  longSuperRelativeEntries :=
    builtRelativeSplitFalseSelectLongSuperRelativeEntries shape
  localEntries := builtRelativeSplitFalseSelectLocalEntries shape
  superFieldWidth := builtRelativeSplitFalseSelectSuperFieldWidth shape
  longSuperRelativeWidth :=
    builtRelativeSplitFalseSelectLongSuperRelativeWidth shape
  localFieldWidth := builtRelativeSplitFalseSelectLocalFieldWidth shape
  superTable := builtRelativeSplitFalseSelectSuperTable shape
  longSuperRelativeTable :=
    builtRelativeSplitFalseSelectLongSuperRelativeTable shape
  localTable := builtRelativeSplitFalseSelectLocalTable shape
  sparseDirectory := builtRelativeSplitSparseExceptionDirectory shape
  bitWords :=
    SuccinctSpace.BoundedPayloadWordStore.ofChunks
      shape.bpCode (sparseDenseFalseSelectWordBits_pos shape)
  super_read_words_length_le_machine := by
    exact
      (builtRelativeSplitFalseSelectSuperTable shape).readWordsLengthLeMachine
        (by
          simp [builtRelativeSplitFalseSelectSuperFieldWidth,
            sparseDenseFalseSelectWordBits])
  long_read_words_length_le_machine := by
    intro i word hget
    rw [(builtRelativeSplitFalseSelectLongSuperRelativeTable
      shape).read_word_length_of_some hget]
    simp [builtRelativeSplitFalseSelectLongSuperRelativeWidth]
  local_read_words_length_le_machine := by
    exact
      (builtRelativeSplitFalseSelectLocalTable shape).readWordsLengthLeMachine
        (by
          simpa [builtRelativeSplitFalseSelectLocalFieldWidth] using
            builtRelativeSplitFalseSelectSparseExceptionRelativeWidth_le_machine
              shape)
  payload_length_le_overhead := by
    have hsuper :=
      builtRelativeSplitFalseSelectSuperTable_payload_le_overhead shape
    have hflags :=
      builtRelativeSplitFalseSelectLongSuperFlagBits_length_le_overhead
        shape
    have hrank :=
      builtRelativeSplitFalseSelectLongFlagRankData_auxPayload_le_overhead
        shape
    have hlong := compactLongSuperRelativeTable_payload_le_overhead shape
    have hlocal := builtRelativeSplitFalseSelectLocalTable_payload_le_overhead
      shape
    have hsparse :=
      (builtRelativeSplitSparseExceptionDirectory shape).payload_length_le_canonical
    have hbp : shape.bpCode.length = 2 * shape.size :=
      Cartesian.CartesianShape.bpCode_length shape
    rw [hbp] at hsuper hflags hrank hlocal
    simp [canonicalRelativeSplitSparseExceptionFalseSelectOverhead,
      List.length_append]
    omega
  super_missing_exact :=
    builtRelativeSplitFalseSelectSuperEntries_missing_exact shape
  long_explicit_exact :=
    builtRelativeSplitFalseSelectLongExplicit_exact shape
  local_missing_exact :=
    builtRelativeSplitFalseSelectLocalEntries_missing_exact shape
  sparse_compact_exact :=
    builtRelativeSplitFalseSelectSparseCompact_exact shape
  dense_exact :=
    builtRelativeSplitFalseSelectDense_exact shape

theorem builtRelativeSplitSparseExceptionFalseSelectCloseData_profile
    (shape : Cartesian.CartesianShape) :
    let data := builtRelativeSplitSparseExceptionFalseSelectCloseData shape
    data.payload.length <=
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead shape.size /\
      SuccinctSpace.LittleOLinear
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead /\
      (forall idx,
        (data.selectCloseCosted idx).cost <=
          sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (data.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      forall {word : List Bool},
        List.Mem word data.readWords ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length := by
  intro data
  exact data.profile

end SuccinctSelectProposal
end RMQ
