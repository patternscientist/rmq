import RMQ.Core.GenericSelect.Directory
import RMQ.Core.GenericSelect.SelectSource

/-!
# Generic select sparse-exception source layer

This module contains the payload bounds, branch exactness lemmas,
`SparseExceptionSelectData`, its charged query, and the
`ChargedSelectPositionSource` adapter.
-/

namespace RMQ.GenericSelect

open SuccinctSpace SuccinctRank
/-! ### Long-super relative table is `o(n)` -/

/-- `o(n)` budget for the long-super relative table: `n / loglog n + 1`. Fed the
bit length `n` directly (the BP original fed `2 * size` only because its argument
was `shape.size`). -/
def longSuperRelativeTableOverhead (n : Nat) : Nat :=
  SuccinctSpace.idDivLogLogOverhead 1 n + 1

theorem longSuperRelativeTableOverhead_littleO :
    SuccinctSpace.LittleOLinear longSuperRelativeTableOverhead := by
  unfold longSuperRelativeTableOverhead
  exact (SuccinctSpace.idDivLogLogOverhead_littleO 1).add_const 1

theorem longSuperRelativeTable_payload_le_overhead
    (bits : List Bool) (target : Bool) :
    (longSuperRelativeTable bits target).payload.length <=
      longSuperRelativeTableOverhead bits.length := by
  let payload := (longSuperRelativeTable bits target).payload.length
  let ellV := ell bits.length
  let n := bits.length
  have hell_pos : 0 < ellV := ell_pos bits.length
  have hpayloadEll : payload * ellV <= n := by
    have hscaled := longSuperRelativeTable_payload_mul_ell_le_spanSum bits target
    exact Nat.le_trans (by simpa [payload, ellV] using hscaled)
      (by simpa [n] using longSuperSpanSum_le_length bits target)
  let overheadLen := n / ellV + 1
  have hn_lt : n < n / ellV * ellV + ellV := Nat.lt_div_mul_add hell_pos (a := n)
  have hscaledStrict : n < overheadLen * ellV := by
    simpa [overheadLen, Nat.add_mul, Nat.one_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hn_lt
  have hpayloadStrict : payload * ellV < overheadLen * ellV :=
    Nat.lt_of_le_of_lt hpayloadEll hscaledStrict
  have hpayloadStrictLeft : ellV * payload < ellV * overheadLen := by
    simpa [Nat.mul_comm] using hpayloadStrict
  have hpayloadLe : payload <= overheadLen :=
    Nat.le_of_mul_le_mul_left (Nat.le_of_lt hpayloadStrictLeft) hell_pos
  simpa [payload, overheadLen, longSuperRelativeTableOverhead,
    SuccinctSpace.idDivLogLogOverhead, ellV, n, ell, wordBits,
    SuccinctRank.machineWordBits] using hpayloadLe

theorem superTable_payload_le_overhead
    (bits : List Bool) (target : Bool) :
    (superTable bits target).payload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        40 bits.length := by
  let payload := (superTable bits target).payload.length
  let superCount := superSlotCount bits target
  let w := wordBits bits.length
  let stride := superStride bits.length
  let e := ell bits.length
  let e3 := e * (e * e)
  let n := bits.length
  have he3One : 1 <= e3 := by
    have he : 1 <= e := by simpa [e] using ell_pos bits.length
    have hmul := Nat.mul_le_mul he (Nat.mul_le_mul he he)
    simpa [e3] using hmul
  have hpayload :
      payload = 4 * (superCount * w) := by
    have hlen := (superTable bits target).payload_length
    simp [payload, superCount, w, superTable, superFieldWidth,
      sparseDenseSelectDenseLocalEntryMultiwordPayloadBudget,
      superEntries_length] at hlen ⊢
    omega
  by_cases hnZero : n = 0
  · have hcountZero : occurrenceCount bits target = 0 := by
      have hcountLe : occurrenceCount bits target <= n := by
        simpa [n] using occurrenceCount_le_length bits target
      omega
    have hsuperZero : superCount = 0 := by
      unfold superCount superSlotCount selectCeilDiv
      rw [hcountZero]
      have hstride_pos : 0 < stride := by
        simpa [stride] using superStride_pos bits.length
      have hpred_lt : stride - 1 < stride :=
        Nat.pred_lt (Nat.ne_of_gt hstride_pos)
      simpa [stride] using Nat.div_eq_of_lt hpred_lt
    simp [payload, hpayload, hsuperZero,
      SuccinctSpace.logLogCubedSampledDirectoryOverhead]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
    have hcountLe : occurrenceCount bits target <= n := by
      simpa [n] using occurrenceCount_le_length bits target
    have hstrideLe : stride <= 4 * n := by
      have hsq :=
        machineWordBits_sq_le_four_mul_self_of_pos
          (n := bits.length) hnPos
      simpa [stride, w, n, superStride, wordBits] using hsq
    have hsuperCountMul :
        superCount * stride <= occurrenceCount bits target + stride := by
      simpa [superCount, stride, superSlotCount] using
        selectCeilDiv_mul_le_add
          (occurrenceCount bits target) stride
    have hpayloadMul :
        payload * w <= 20 * (e3 * n) := by
      rw [hpayload]
      calc
        4 * (superCount * w) * w =
            4 * (superCount * stride) := by
              simp [stride, w, superStride, Nat.mul_left_comm, Nat.mul_comm]
        _ <= 4 * (occurrenceCount bits target + stride) := by
              exact Nat.mul_le_mul_left 4 hsuperCountMul
        _ <= 4 * (n + 4 * n) := by
              exact Nat.mul_le_mul_left 4
                (Nat.add_le_add hcountLe hstrideLe)
        _ = 20 * n := by omega
        _ <= 20 * (e3 * n) := by
              have hmul := Nat.mul_le_mul_right n he3One
              have hscaled := Nat.mul_le_mul_left 20 hmul
              simpa [Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm] using hscaled
    exact
      payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
        (n := bits.length) (payload := payload) (scale := 20)
        (by
          simpa [w, e, e3, n, Nat.mul_assoc,
            Nat.mul_left_comm, Nat.mul_comm] using hpayloadMul)

theorem localTable_payload_le_overhead
    (bits : List Bool) (target : Bool) :
    (localTable bits target).payload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        640 bits.length := by
  let payload := (localTable bits target).payload.length
  let m := localSlotCount bits target
  let relWidth := localFieldWidth bits
  let w := wordBits bits.length
  let stride := localStride bits.length
  let e := ell bits.length
  let e2 := e * e
  let e3 := e * (e * e)
  let n := bits.length
  have hpayload :
      payload = 4 * (m * relWidth) := by
    have hlen := (localTable bits target).payload_length
    simp [payload, m, relWidth, localTable, localFieldWidth,
      sparseDenseSelectDenseLocalEntryMultiwordPayloadBudget,
      localEntries_length] at hlen ⊢
    omega
  have hslots :
      m * stride <= 10 * n := by
    simpa [m, stride, n] using
      localSlotCount_mul_localStride_le_const_length bits target
  have hwidth : relWidth <= 4 * e := by
    simpa [relWidth, e, localFieldWidth] using
      sparseExceptionRelativeWidth_le_four_ell bits
  have hwordLower :
      w <= 2 * stride * e2 := by
    simpa [w, stride, e, e2, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using
      wordBits_le_two_mul_localStride_mul_ell_sq bits.length
  have hcore :
      m * relWidth * w <= 80 * (e3 * n) := by
    calc
      m * relWidth * w <=
          m * relWidth * (2 * stride * e2) := by
            exact Nat.mul_le_mul_left (m * relWidth) hwordLower
      _ = 2 * (m * stride) * relWidth * e2 := by
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = 2 * ((m * stride) * relWidth) * e2 := by
            simp [Nat.mul_assoc]
      _ <= 2 * ((10 * n) * (4 * e)) * e2 := by
            have hmul := Nat.mul_le_mul hslots hwidth
            have hmul2 := Nat.mul_le_mul_left 2 hmul
            have hmul3 := Nat.mul_le_mul_right e2 hmul2
            exact hmul3
      _ = 2 * (10 * n) * (4 * e) * e2 := by
            simp [Nat.mul_assoc]
      _ = 80 * (e3 * n) := by
            calc
              2 * (10 * n) * (4 * e) * e2 =
                  n * (4 * (20 * (e * e2))) := by
                    simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
              _ = n * (80 * (e * e2)) := by
                    have hconst :
                        4 * (20 * (e * e2)) = 80 * (e * e2) := by
                      omega
                    rw [hconst]
              _ = 80 * (e3 * n) := by
                    simp [e2, e3, Nat.mul_left_comm, Nat.mul_comm]
  have hpayloadMul :
      payload * w <= 320 * (e3 * n) := by
    rw [hpayload]
    have hmul := Nat.mul_le_mul_left 4 hcore
    calc
      4 * (m * relWidth) * w <=
          4 * (80 * (e3 * n)) := by
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      _ = 320 * (e3 * n) := by
            let t := e3 * n
            change 4 * (80 * t) = 320 * t
            omega
  exact
    payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
      (n := bits.length) (payload := payload) (scale := 320)
      (by
        simpa [payload, w, e, e3, n, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using hpayloadMul)

theorem longSuperFlagBits_length (bits : List Bool) (target : Bool) :
    (longSuperFlagBits bits target).length =
      superSlotCount bits target := by
  simp [longSuperFlagBits]

theorem longSuperFlagBits_length_le_length
    (bits : List Bool) (target : Bool) :
    (longSuperFlagBits bits target).length <= bits.length := by
  by_cases hcount : occurrenceCount bits target = 0
  · have hsuperZero : superSlotCount bits target = 0 := by
      unfold superSlotCount selectCeilDiv
      rw [hcount]
      have hstride_pos : 0 < superStride bits.length :=
        superStride_pos bits.length
      have hpred_lt :
          superStride bits.length - 1 < superStride bits.length :=
        Nat.pred_lt (Nat.ne_of_gt hstride_pos)
      simpa using Nat.div_eq_of_lt hpred_lt
    simp [longSuperFlagBits_length, hsuperZero]
  · have hcountPos : 0 < occurrenceCount bits target := Nat.pos_of_ne_zero hcount
    have hsuperLeCount :
        superSlotCount bits target <= occurrenceCount bits target := by
      exact
        selectCeilDiv_le_self_of_pos
          (n := occurrenceCount bits target)
          (stride := superStride bits.length)
          hcountPos (superStride_pos bits.length)
    have hcountLe := occurrenceCount_le_length bits target
    rw [longSuperFlagBits_length]
    exact Nat.le_trans hsuperLeCount hcountLe

theorem longSuperFlagBits_length_mul_wordBits_le
    (bits : List Bool) (target : Bool) :
    (longSuperFlagBits bits target).length * wordBits bits.length <=
      5 * ((ell bits.length * (ell bits.length * ell bits.length)) *
        bits.length) := by
  let flagLen := (longSuperFlagBits bits target).length
  let superCount := superSlotCount bits target
  let w := wordBits bits.length
  let stride := superStride bits.length
  let e := ell bits.length
  let e3 := e * (e * e)
  let n := bits.length
  have he3One : 1 <= e3 := by
    have he : 1 <= e := by simpa [e] using ell_pos bits.length
    have hmul := Nat.mul_le_mul he (Nat.mul_le_mul he he)
    simpa [e3] using hmul
  by_cases hnZero : n = 0
  · have hcountZero : occurrenceCount bits target = 0 := by
      have hcountLe : occurrenceCount bits target <= n := by
        simpa [n] using occurrenceCount_le_length bits target
      omega
    have hsuperZero : superCount = 0 := by
      unfold superCount superSlotCount selectCeilDiv
      rw [hcountZero]
      have hstride_pos : 0 < stride := by
        simpa [stride] using superStride_pos bits.length
      have hpred_lt : stride - 1 < stride :=
        Nat.pred_lt (Nat.ne_of_gt hstride_pos)
      simpa [stride] using Nat.div_eq_of_lt hpred_lt
    have hsuperZeroRaw : superSlotCount bits target = 0 := by
      simpa [superCount] using hsuperZero
    have hflagZero : flagLen = 0 := by
      rw [show flagLen = (longSuperFlagBits bits target).length by rfl,
        longSuperFlagBits_length, hsuperZeroRaw]
    rw [show (longSuperFlagBits bits target).length = flagLen by rfl,
      hflagZero]
    simp [n, hnZero]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
    have hcountLe : occurrenceCount bits target <= n := by
      simpa [n] using occurrenceCount_le_length bits target
    have hstrideLe : stride <= 4 * n := by
      have hsq :=
        machineWordBits_sq_le_four_mul_self_of_pos
          (n := bits.length) hnPos
      simpa [stride, w, n, superStride, wordBits] using hsq
    have hsuperCountMul :
        superCount * stride <= occurrenceCount bits target + stride := by
      simpa [superCount, stride, superSlotCount] using
        selectCeilDiv_mul_le_add
          (occurrenceCount bits target) stride
    have hflagMul :
        flagLen * w <= 5 * n := by
      have hflagLen : flagLen = superCount := by
        simpa [flagLen] using
          longSuperFlagBits_length bits target
      have hwordLeStride : w <= stride := by
        have hwPos : 0 < w := by
          simpa [w] using wordBits_pos bits.length
        simp [stride, w, superStride]
        exact Nat.le_mul_of_pos_left w hwPos
      calc
        flagLen * w = superCount * w := by rw [hflagLen]
        _ <= superCount * stride := by
              exact Nat.mul_le_mul_left superCount hwordLeStride
        _ <= occurrenceCount bits target + stride :=
              hsuperCountMul
        _ <= n + 4 * n := Nat.add_le_add hcountLe hstrideLe
        _ = 5 * n := by omega
    have hscaled :
        5 * n <= 5 * (e3 * n) := by
      have hmul := Nat.mul_le_mul_right n he3One
      have hscaled := Nat.mul_le_mul_left 5 hmul
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled
    exact Nat.le_trans hflagMul (by
      simpa [flagLen, w, e, e3, n, Nat.mul_assoc,
        Nat.mul_left_comm, Nat.mul_comm] using hscaled)

theorem longSuperFlagBits_length_le_overhead
    (bits : List Bool) (target : Bool) :
    (longSuperFlagBits bits target).length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        40 bits.length := by
  exact
    payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
      (n := bits.length)
      (payload := (longSuperFlagBits bits target).length)
      (scale := 20)
      (by
        have h :=
          longSuperFlagBits_length_mul_wordBits_le bits target
        have hscale :
            5 * ((ell bits.length * (ell bits.length * ell bits.length)) *
                bits.length) <=
              20 * bits.length *
                (ell bits.length * (ell bits.length * ell bits.length)) := by
          have hraw :
              5 * ((ell bits.length * (ell bits.length * ell bits.length)) *
                  bits.length) <=
                20 * ((ell bits.length * (ell bits.length * ell bits.length)) *
                  bits.length) :=
            Nat.mul_le_mul_right _ (by omega : (5 : Nat) <= 20)
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hraw
        exact Nat.le_trans h hscale)

def longFlagRankWordSize (bits : List Bool) (target : Bool) : Nat :=
  SuccinctRank.machineWordBits
    (longSuperFlagBits bits target).length

def longFlagRankBlocksPerSuper (_bits : List Bool) (_target : Bool) : Nat := 1

def longFlagRankBlockWidth (bits : List Bool) (target : Bool) : Nat :=
  longFlagRankWordSize bits target

theorem longFlagRankWordSize_pos
    (bits : List Bool) (target : Bool) :
    0 < longFlagRankWordSize bits target := by
  simp [longFlagRankWordSize, SuccinctRank.machineWordBits_pos]

theorem longFlagRankWordSize_le_machine
    (bits : List Bool) (target : Bool) :
    longFlagRankWordSize bits target <=
      SuccinctRank.machineWordBits bits.length := by
  unfold longFlagRankWordSize
  exact SuccinctRank.machineWordBits_mono_le
    (longSuperFlagBits_length_le_length bits target)

theorem longFlagRankBlocksPerSuper_pos
    (bits : List Bool) (target : Bool) :
    0 < longFlagRankBlocksPerSuper bits target := by
  simp [longFlagRankBlocksPerSuper]

theorem longSuperFlagBits_length_lt_rank_word_pow
    (bits : List Bool) (target : Bool) :
    (longSuperFlagBits bits target).length <
      2 ^ longFlagRankWordSize bits target := by
  simpa [longFlagRankWordSize, SuccinctRank.machineWordBits] using
    (Nat.lt_log2_self (n := (longSuperFlagBits bits target).length))

theorem longFlagRankBlockSpan_lt_pow
    (bits : List Bool) (target : Bool) :
    longFlagRankBlocksPerSuper bits target *
        longFlagRankWordSize bits target <
      2 ^ longFlagRankBlockWidth bits target := by
  have hsucc :=
    SuccinctSpace.nat_succ_le_two_pow
      (longFlagRankWordSize bits target)
  simpa [longFlagRankBlocksPerSuper, longFlagRankBlockWidth] using
    (by omega :
      longFlagRankWordSize bits target <
        2 ^ longFlagRankWordSize bits target)

def longFlagRankSuperOverhead (bits : List Bool) (target : Bool) : Nat :=
  (SuccinctRank.canonicalSuperRankSampleTables
    (longSuperFlagBits bits target)
    (longFlagRankWordSize bits target)
    (longFlagRankBlocksPerSuper bits target)
    (longFlagRankWordSize bits target)
    (longSuperFlagBits_length_lt_rank_word_pow bits target)).payload.length

def longFlagRankBlockOverhead (bits : List Bool) (target : Bool) : Nat :=
  (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan
    (longSuperFlagBits bits target)
    (longFlagRankWordSize bits target)
    (longFlagRankBlocksPerSuper bits target)
    (longFlagRankBlockWidth bits target)
    (longFlagRankBlocksPerSuper_pos bits target)
    (longFlagRankBlockSpan_lt_pow bits target)).payload.length

def longFlagRankData (bits : List Bool) (target : Bool) :
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      (longSuperFlagBits bits target)
      (longFlagRankSuperOverhead bits target)
      (longFlagRankBlockOverhead bits target)
      4 :=
  SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock
    (longSuperFlagBits bits target)
    (longFlagRankWordSize_pos bits target)
    (by simp [longFlagRankWordSize])
    (longFlagRankBlocksPerSuper_pos bits target)
    (longSuperFlagBits_length_lt_rank_word_pow bits target)
    (longFlagRankBlockSpan_lt_pow bits target)
    (by omega)

theorem longFlagRankData_profile
    (bits : List Bool) (target : Bool) :
    let data := longFlagRankData bits target
    data.auxPayload.length =
        longFlagRankSuperOverhead bits target +
          longFlagRankBlockOverhead bits target /\
      data.wordSize <=
        SuccinctRank.machineWordBits
          (longSuperFlagBits bits target).length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        longSuperFlagBits bits target /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <=
            SuccinctRank.machineWordBits
              (longSuperFlagBits bits target).length) /\
      forall rankTarget pos,
        (data.rankCosted rankTarget pos).cost <= 4 /\
          (data.rankCosted rankTarget pos).erase =
            RMQ.Succinct.rankPrefix rankTarget
              (longSuperFlagBits bits target) pos := by
  exact
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
      (longSuperFlagBits bits target)
      (longFlagRankWordSize_pos bits target)
      (by simp [longFlagRankWordSize])
      (longFlagRankBlocksPerSuper_pos bits target)
      (longSuperFlagBits_length_lt_rank_word_pow bits target)
      (longFlagRankBlockSpan_lt_pow bits target)
      (by omega)

theorem longFlagRankData_auxPayload_le_overhead
    (bits : List Bool) (target : Bool) :
    (longFlagRankData bits target).auxPayload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 bits.length + 16 := by
  let flagBits := longSuperFlagBits bits target
  let flagLen := flagBits.length
  let rankWord := flagRankWordSize flagBits
  let w := wordBits bits.length
  let e := ell bits.length
  let e3 := e * (e * e)
  let n := bits.length
  let data := longFlagRankData bits target
  have hrankWordPos : 0 < rankWord := by
    simpa [rankWord, flagBits] using longFlagRankWordSize_pos bits target
  have hrankWordLeW : rankWord <= w := by
    simpa [rankWord, w, flagBits, wordBits] using
      longFlagRankWordSize_le_machine bits target
  have hauxEq :
      data.auxPayload.length =
        longFlagRankSuperOverhead bits target +
          longFlagRankBlockOverhead bits target := by
    have hprofile := longFlagRankData_profile bits target
    simpa [data] using hprofile.1
  have hsuperLe :
      longFlagRankSuperOverhead bits target <=
        2 * (flagLen + rankWord) := by
    unfold longFlagRankSuperOverhead
    rw [SuccinctRank.canonicalSuperRankSampleTables_payload_length]
    have hentryLen :
        (SuccinctRank.canonicalSuperRankEntries true flagBits
            rankWord
            (longFlagRankBlocksPerSuper bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord, longFlagRankBlocksPerSuper]
    have hentryLenFalse :
        (SuccinctRank.canonicalSuperRankEntries false flagBits
            rankWord
            (longFlagRankBlocksPerSuper bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord, longFlagRankBlocksPerSuper]
    change
      (SuccinctRank.canonicalSuperRankEntries true flagBits rankWord
            (longFlagRankBlocksPerSuper bits target)).length * rankWord +
        (SuccinctRank.canonicalSuperRankEntries false flagBits rankWord
            (longFlagRankBlocksPerSuper bits target)).length * rankWord <=
      2 * (flagLen + rankWord)
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
      longFlagRankBlockOverhead bits target <=
        2 * (flagLen + rankWord) := by
    unfold longFlagRankBlockOverhead
    rw [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length]
    have hentryLen :
        (SuccinctRank.canonicalBlockRankEntries true flagBits
            rankWord
            (longFlagRankBlocksPerSuper bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalBlockRankEntries, flagBits,
        flagLen, rankWord, longFlagRankBlocksPerSuper]
    have hentryLenFalse :
        (SuccinctRank.canonicalBlockRankEntries false flagBits
            rankWord
            (longFlagRankBlocksPerSuper bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalBlockRankEntries, flagBits,
        flagLen, rankWord, longFlagRankBlocksPerSuper]
    change
      (SuccinctRank.canonicalBlockRankEntries true flagBits rankWord
            (longFlagRankBlocksPerSuper bits target)).length * rankWord +
        (SuccinctRank.canonicalBlockRankEntries false flagBits rankWord
            (longFlagRankBlocksPerSuper bits target)).length * rankWord <=
      2 * (flagLen + rankWord)
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
      longFlagRankSuperOverhead bits target +
          longFlagRankBlockOverhead bits target <=
        2 * (flagLen + rankWord) + 2 * (flagLen + rankWord) :=
          Nat.add_le_add hsuperLe hblockLe
      _ = 4 * (flagLen + rankWord) := by omega
  by_cases hnZero : n = 0
  · have hflagZero : flagLen = 0 := by
      have hlen := longSuperFlagBits_length_le_length bits target
      simpa [flagBits, flagLen, n, hnZero] using hlen
    have hw : w = 1 := by
      simp [w, wordBits, SuccinctRank.machineWordBits, n, hnZero]
    have hrankSmall : rankWord <= 1 := by
      simpa [hw] using hrankWordLeW
    have hauxSmall : data.auxPayload.length <= 4 := by
      have h := hauxLe
      rw [hflagZero] at h
      omega
    exact Nat.le_trans hauxSmall (by omega)
  have hflagMul :
      flagLen * w <= 5 * (e3 * n) := by
    simpa [flagBits, flagLen, w, e, e3, n, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using
      longSuperFlagBits_length_mul_wordBits_le bits target
  have hrankMul :
      rankWord * w <= 4 * (e3 * n) := by
    have hwSq : w * w <= 4 * n := by
      have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
      simpa [w, wordBits, n] using
        machineWordBits_sq_le_four_mul_self_of_pos hnPos
    have hrankW : rankWord * w <= w * w :=
      Nat.mul_le_mul_right w hrankWordLeW
    have he3One : 1 <= e3 := by
      have he : 1 <= e := by simpa [e] using ell_pos bits.length
      have h1 := Nat.mul_le_mul he (Nat.mul_le_mul he he)
      simpa [e3] using h1
    calc
      rankWord * w <= w * w := hrankW
      _ <= 4 * n := hwSq
      _ <= 4 * (e3 * n) := by
        have hmul := Nat.mul_le_mul_right n he3One
        have hscaled := Nat.mul_le_mul_left 4 hmul
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled
  have hauxMul :
      data.auxPayload.length * w <= 36 * (e3 * n) := by
    calc
      data.auxPayload.length * w <=
          4 * (flagLen + rankWord) * w := by
            exact Nat.mul_le_mul_right w hauxLe
      _ = 4 * (flagLen * w + rankWord * w) := by
            simp [Nat.add_mul, Nat.mul_assoc]
      _ <= 4 * (5 * (e3 * n) + 4 * (e3 * n)) := by
            exact Nat.mul_le_mul_left 4
              (Nat.add_le_add hflagMul hrankMul)
      _ = 36 * (e3 * n) := by
            let t := e3 * n
            change 4 * (5 * t + 4 * t) = 36 * t
            omega
  have hauxMulWide :
      data.auxPayload.length * w <= 96 * (e3 * n) := by
    exact Nat.le_trans hauxMul
      (Nat.mul_le_mul_right _ (by omega : (36 : Nat) <= 96))
  exact
    Nat.le_trans
      (payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
        (n := bits.length) (payload := data.auxPayload.length) (scale := 96)
        (by
          simpa [w, e, e3, n, Nat.mul_assoc, Nat.mul_left_comm,
            Nat.mul_comm] using hauxMulWide))
      (Nat.le_add_right _ _)

def canonicalSparseExceptionSelectOverhead (n : Nat) : Nat :=
  SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 n +
    SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 n +
      (SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 n + 16) +
        longSuperRelativeTableOverhead n +
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 640 n +
            canonicalSparseExceptionDirectoryOverhead n

theorem canonicalSparseExceptionSelectOverhead_littleO :
    SuccinctSpace.LittleOLinear canonicalSparseExceptionSelectOverhead := by
  unfold canonicalSparseExceptionSelectOverhead
  have hsuper :
      SuccinctSpace.LittleOLinear
        (SuccinctSpace.logLogCubedSampledDirectoryOverhead 40) :=
    SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 40
  have hflags :
      SuccinctSpace.LittleOLinear
        (SuccinctSpace.logLogCubedSampledDirectoryOverhead 40) :=
    SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 40
  have hrank :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 n + 16) :=
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 192).add_const 16
  have hlocal :
      SuccinctSpace.LittleOLinear
        (SuccinctSpace.logLogCubedSampledDirectoryOverhead 640) :=
    SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 640
  exact
    (((((hsuper.add hflags).add hrank).add
      longSuperRelativeTableOverhead_littleO).add hlocal).add
      canonicalSparseExceptionDirectoryOverhead_littleO)

theorem superEntries_missing_exact
    (bits : List Bool) (target : Bool) (q : Nat)
    (hmissing :
      (superEntries bits target)[
          selectSuperSlot q
            (superStride bits.length)]? = none) :
    RMQ.Succinct.select target bits q = none := by
  cases hselect :
      RMQ.Succinct.select target bits q with
  | none =>
      rfl
  | some pos =>
      have hocc : q < occurrenceCount bits target :=
        occurrence_lt_count_of_select hselect
      have hslotMul :
          (q / superStride bits.length) *
              superStride bits.length <
            occurrenceCount bits target := by
        have hmul :=
          Nat.div_mul_le_self q (superStride bits.length)
        omega
      have hslot :
          selectSuperSlot q
              (superStride bits.length) <
            superSlotCount bits target := by
        unfold selectSuperSlot superSlotCount
        by_cases hlt :
            q / superStride bits.length <
              selectCeilDiv (occurrenceCount bits target)
                (superStride bits.length)
        · exact hlt
        · have hceilLe :
              selectCeilDiv (occurrenceCount bits target)
                  (superStride bits.length) <=
                q / superStride bits.length :=
            Nat.le_of_not_gt hlt
          have hmulLe :=
            Nat.mul_le_mul_right (superStride bits.length) hceilLe
          have hceilGe :=
            selectCeilDiv_mul_ge_of_pos
              (n := occurrenceCount bits target)
              (stride := superStride bits.length)
              (superStride_pos bits.length)
          exact False.elim (by omega)
      have hget :=
        superEntries_get? bits target hslot
      rw [hget] at hmissing
      simp at hmissing

theorem superEntry_marked_eq_long
    (bits : List Bool) (target : Bool) (superSlot : Nat) :
    relativeSplitSelectEntryIsMarked
      (superEntry bits target superSlot) =
        superIsLong bits target superSlot := by
  unfold superEntry
  by_cases hlong :
      superIsLong bits target superSlot = true
  · simp [relativeSplitSelectEntryIsMarked, hlong]
  · have hfalse :
        superIsLong bits target superSlot = false := by
      cases h :
          superIsLong bits target superSlot
      · rfl
      · contradiction
    simp [relativeSplitSelectEntryIsMarked, hfalse]

theorem longExplicit_exact
    (bits : List Bool) (target : Bool) (q : Nat)
    (super : SparseDenseSelectDenseLocalEntry)
    (hsuper :
      (superEntries bits target)[
          selectSuperSlot q
            (superStride bits.length)]? = some super)
    (hvalid : q < occurrenceCount bits target)
    (hlong :
      relativeSplitSelectEntryIsMarked super = true) :
    ((longSuperRelativeEntries bits target)[
        relativeSplitSelectLongCompactSlot
          (RMQ.Succinct.rankPrefix true
            (longSuperFlagBits bits target)
            (selectSuperSlot q
              (superStride bits.length)))
          (q - super.baseOccurrence)
          (superStride bits.length)]?).map
      (fun offset =>
        relativeSplitSelectEntryBasePosition
            (wordBits bits.length) super +
          offset) =
      RMQ.Succinct.select target bits q := by
  let superSlot :=
    selectSuperSlot q (superStride bits.length)
  have hslot : superSlot < superSlotCount bits target := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, superEntries_length] using hlen
  have hbuilt :=
    superEntries_get? bits target (superSlot := superSlot) hslot
  have hsuperEq :
      super = superEntry bits target superSlot := by
    rw [hbuilt] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  have hlongBuilt :
      superIsLong bits target superSlot = true := by
    have hmark :=
      superEntry_marked_eq_long bits target superSlot
    rw [hmark] at hlong
    exact hlong
  have hbaseLeQ :
      superBaseOccurrence bits.length superSlot <= q := by
    have hmul :=
      Nat.div_mul_le_self q (superStride bits.length)
    simpa [superSlot, selectSuperSlot, superBaseOccurrence]
      using hmul
  have hqLtBaseStride :
      q <
        superBaseOccurrence bits.length superSlot +
          superStride bits.length := by
    have hstride := superStride_pos bits.length
    have hlt :=
      Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, selectSuperSlot, superBaseOccurrence,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  have hlocalOcc :
      q - superBaseOccurrence bits.length superSlot <
        superStride bits.length := by
    omega
  have hend :
      superBaseOccurrence bits.length superSlot +
          (q - superBaseOccurrence bits.length superSlot) <
        superEndOccurrence bits target superSlot := by
    have hqEq :
        superBaseOccurrence bits.length superSlot +
            (q - superBaseOccurrence bits.length superSlot) = q := by
      omega
    rw [hqEq]
    unfold superEndOccurrence
    exact Nat.lt_min.mpr ⟨hqLtBaseStride, hvalid⟩
  rcases select_exists_of_lt_occurrenceCount
      bits target hvalid with ⟨pos, hselect⟩
  have hqEqLocal :
      superBaseOccurrence bits.length superSlot +
          (q - superBaseOccurrence bits.length superSlot) = q := by
    omega
  have hselectLocal :
      RMQ.Succinct.select target bits
          (superBaseOccurrence bits.length superSlot +
            (q - superBaseOccurrence bits.length superSlot)) =
        some pos := by
    simpa [hqEqLocal] using hselect
  have hlookup :=
    longSuperRelativeEntries_lookup_exact
      bits target (superSlot := superSlot)
      (localOccurrence :=
        q - superBaseOccurrence bits.length superSlot)
      (pos := pos) hslot hlongBuilt hlocalOcc hend hselectLocal
  have hbasePos :
      relativeSplitSelectEntryBasePosition
          (wordBits bits.length)
          (superEntry bits target superSlot) =
        position bits target
          (superBaseOccurrence bits.length superSlot) := by
    unfold relativeSplitSelectEntryBasePosition superEntry
    let baseOccurrence := superSlot * superStride bits.length
    let basePosition := position bits target baseOccurrence
    let wordSize := wordBits bits.length
    have hmod :
        basePosition / wordSize * wordSize +
            (basePosition - basePosition / wordSize * wordSize) =
          basePosition := by
      have hle := Nat.div_mul_le_self basePosition wordSize
      omega
    simpa [baseOccurrence, basePosition, wordSize,
      superBaseOccurrence, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hmod
  have hbaseLePos :
      position bits target
          (superBaseOccurrence bits.length superSlot) <= pos := by
    have hsuperCount :
        superBaseOccurrence bits.length superSlot <
          occurrenceCount bits target := by
      omega
    rcases select_exists_of_lt_occurrenceCount
        bits target hsuperCount with ⟨basePos, hbaseSelect⟩
    have hmono :=
      select_index_mono (target := target) (bits := bits)
        (lo := superBaseOccurrence bits.length superSlot)
        (hi := q)
        (posLo := basePos) (posHi := pos)
        hbaseLeQ hbaseSelect hselect
    have hbaseEq :
        position bits target
            (superBaseOccurrence bits.length superSlot) = basePos :=
      position_eq_of_select bits target hbaseSelect
    rwa [hbaseEq]
  have hposEq :
      position bits target
          (superBaseOccurrence bits.length superSlot) +
        (pos -
          position bits target
            (superBaseOccurrence bits.length superSlot)) = pos := by
    omega
  have hqueryLookup :
      (longSuperRelativeEntries bits target)[
          relativeSplitSelectLongCompactSlot
            (RMQ.Succinct.rankPrefix true
              (longSuperFlagBits bits target)
              (selectSuperSlot q
                (superStride bits.length)))
            (q - (superEntry bits target superSlot).baseOccurrence)
            (superStride bits.length)]? =
        some
          (pos -
            position bits target
              (superBaseOccurrence bits.length superSlot)) := by
    simpa [relativeSplitSelectLongCompactSlot, superEntry,
      superBaseOccurrence, superSlot] using hlookup
  rw [hselect]
  rw [hqueryLookup]
  simp [hbasePos, hposEq]

theorem localSlot_facts
    (bits : List Bool) (target : Bool) (q : Nat)
    (super : SparseDenseSelectDenseLocalEntry)
    (hsuper :
      (superEntries bits target)[
          selectSuperSlot q
            (superStride bits.length)]? = some super)
    (hvalid : q < occurrenceCount bits target)
    (hshort :
      relativeSplitSelectEntryIsMarked super = false) :
    let localSlot :=
      relativeSplitSelectLocalSlot q
        (superStride bits.length)
        (localSlotsPerSuper bits.length)
        (localStride bits.length) super
    localSlot < localSlotCount bits target /\
      localSlot <
        sparseExceptionEffectiveLocalSlotCount bits target /\
      compactLocalEntryIsLive bits target localSlot = true /\
      localSuperSlot bits.length localSlot =
        selectSuperSlot q
          (superStride bits.length) /\
      localBaseOccurrence bits.length localSlot <= q /\
      q <
        localBaseOccurrence bits.length localSlot +
          localStride bits.length := by
  let superSlot :=
    selectSuperSlot q (superStride bits.length)
  let slots := localSlotsPerSuper bits.length
  let superStrideV := superStride bits.length
  let localStrideV := localStride bits.length
  have hslot : superSlot < superSlotCount bits target := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, superEntries_length] using hlen
  have hbuilt :=
    superEntries_get? bits target (superSlot := superSlot) hslot
  have hsuperEq :
      super = superEntry bits target superSlot := by
    rw [hbuilt] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  have hshortBuilt :
      superIsLong bits target superSlot = false := by
    have hmark :=
      superEntry_marked_eq_long bits target superSlot
    rw [hmark] at hshort
    exact hshort
  have hbaseLeQ :
      superSlot * superStrideV <= q := by
    have hmul := Nat.div_mul_le_self q superStrideV
    simpa [superSlot, selectSuperSlot, superStrideV] using hmul
  have hqLtBaseStride :
      q < superSlot * superStrideV + superStrideV := by
    have hstride := superStride_pos bits.length
    have hlt := Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, selectSuperSlot, superStrideV,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  let localInSuper := (q - superSlot * superStrideV) / localStrideV
  have hlocalStridePos : 0 < localStrideV := by
    simpa [localStrideV] using localStride_pos bits.length
  have hslotsPos : 0 < slots := by
    simpa [slots] using localSlotsPerSuper_pos bits.length
  have hlocalInSuperLt : localInSuper < slots := by
    by_cases hlt : localInSuper < slots
    case pos =>
      exact hlt
    case neg =>
      have hle : slots <= localInSuper := Nat.le_of_not_gt hlt
      have hslotsMul :
          slots * localStrideV <= localInSuper * localStrideV :=
        Nat.mul_le_mul_right localStrideV hle
      have hdivMul :
          localInSuper * localStrideV <=
            q - superSlot * superStrideV := by
        simpa [localInSuper] using
          Nat.div_mul_le_self
            (q - superSlot * superStrideV) localStrideV
      have hcap :
          superStrideV <= slots * localStrideV := by
        simpa [slots, superStrideV, localStrideV, localSlotsPerSuper] using
          (selectLocalSlotsPerSuper_mul_localStride_ge_superStride
            (superStride := superStride bits.length)
            (localStride := localStride bits.length)
            (localStride_pos bits.length))
      exact False.elim (by omega)
  let localSlot := superSlot * slots + localInSuper
  have hlocalSlotEq :
      relativeSplitSelectLocalSlot q
          (superStride bits.length)
          (localSlotsPerSuper bits.length)
          (localStride bits.length)
          (superEntry bits target superSlot) =
        localSlot := by
    simp [relativeSplitSelectLocalSlot,
      relativeSplitSelectLocalSlotInSuper,
      superEntry, superSlot, slots, superStrideV, localStrideV,
      localSlot, localInSuper, selectSuperSlot]
  have hlocalSlotLt :
      localSlot < localSlotCount bits target := by
    have hnext :
        superSlot * slots + localInSuper <
          (superSlot + 1) * slots := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hle :
        (superSlot + 1) * slots <=
          superSlotCount bits target * slots := by
      exact Nat.mul_le_mul_right slots (by omega)
    simpa [localSlot, localSlotCount, slots, Nat.mul_assoc] using
      Nat.lt_of_lt_of_le hnext hle
  have hsuperSlotOfLocal :
      localSuperSlot bits.length localSlot = superSlot := by
    unfold localSuperSlot
    calc
      (localSlot / localSlotsPerSuper bits.length) =
          (localInSuper + slots * superSlot) / slots := by
            simp [localSlot, slots, Nat.mul_comm, Nat.add_comm]
      _ = localInSuper / slots + superSlot := by
            exact Nat.add_mul_div_left localInSuper superSlot hslotsPos
      _ = superSlot := by
            rw [Nat.div_eq_of_lt hlocalInSuperLt]
            simp
  have hlocalRemainder :
      localSlot -
          localSuperSlot bits.length localSlot *
            localSlotsPerSuper bits.length =
        localInSuper := by
    rw [hsuperSlotOfLocal]
    simp [localSlot, slots]
  have hlocalDiv :
      localSlot / localSlotsPerSuper bits.length =
        superSlot := by
    simpa [localSuperSlot] using hsuperSlotOfLocal
  have hlocalRemainderRaw :
      localSlot - superSlot * localSlotsPerSuper bits.length =
        localInSuper := by
    simpa [hsuperSlotOfLocal] using hlocalRemainder
  have hbaseEq :
      localBaseOccurrence bits.length localSlot =
        superSlot * superStrideV + localInSuper * localStrideV := by
    unfold localBaseOccurrence localSlotInSuperOfGlobal
    rw [hlocalDiv]
    rw [hlocalRemainderRaw]
  have hdivMul :
      localInSuper * localStrideV <=
        q - superSlot * superStrideV := by
    simpa [localInSuper] using
      Nat.div_mul_le_self (q - superSlot * superStrideV) localStrideV
  have hbaseLocalLeQ :
      localBaseOccurrence bits.length localSlot <= q := by
    rw [hbaseEq]
    omega
  have hslotsLeSuperStride :
      slots <= superStrideV := by
    simpa [slots, superStrideV, localStrideV, localSlotsPerSuper] using
      (selectLocalSlotsPerSuper_le_superStride
        (hsuper := superStride_pos bits.length)
        (hlocal := localStride_pos bits.length))
  have hlocalSlotLeBase :
      localSlot <=
        localBaseOccurrence bits.length localSlot := by
    have hslotPart :
        superSlot * slots <= superSlot * superStrideV :=
      Nat.mul_le_mul_left superSlot hslotsLeSuperStride
    have hlocalStrideOne : 1 <= localStrideV := by omega
    have hlocalPart :
        localInSuper <= localInSuper * localStrideV := by
      simpa using Nat.mul_le_mul_left localInSuper hlocalStrideOne
    rw [hbaseEq]
    simp [localSlot]
    omega
  have hlocalSlotLtCount :
      localSlot < occurrenceCount bits target := by
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans hlocalSlotLeBase hbaseLocalLeQ) hvalid
  have hlocalSlotLtEffective :
      localSlot <
        sparseExceptionEffectiveLocalSlotCount bits target := by
    unfold sparseExceptionEffectiveLocalSlotCount
    exact Nat.lt_min.mpr ⟨hlocalSlotLt, hlocalSlotLtCount⟩
  have hdeltaLtNext :
      q - superSlot * superStrideV <
        localInSuper * localStrideV + localStrideV := by
    simpa [localInSuper, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using
      Nat.lt_div_mul_add hlocalStridePos
        (a := q - superSlot * superStrideV)
  have hqLtLocalEnd :
      q <
        localBaseOccurrence bits.length localSlot +
          localStride bits.length := by
    rw [hbaseEq]
    simpa [localStrideV] using (by omega :
      q < superSlot * superStrideV + localInSuper * localStrideV +
        localStrideV)
  have hbaseCount :
      localBaseOccurrence bits.length localSlot <
        occurrenceCount bits target := by
    omega
  have hlive :
      compactLocalEntryIsLive bits target localSlot = true := by
    unfold compactLocalEntryIsLive
    simp [hsuperSlotOfLocal, hshortBuilt, hbaseCount]
  rw [hlocalSlotEq]
  exact
    ⟨hlocalSlotLt, hlocalSlotLtEffective, hlive, hsuperSlotOfLocal,
      hbaseLocalLeQ, hqLtLocalEnd⟩

theorem localEntry_marked_eq_flag
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat) :
    relativeSplitSelectEntryIsMarked
      (localEntry bits target globalLocalSlot) =
        (compactLocalEntryIsLive bits target globalLocalSlot &&
          localIsSparseException bits target globalLocalSlot) := by
  unfold localEntry
  by_cases hlive :
      compactLocalEntryIsLive bits target globalLocalSlot = true
  · by_cases hflag :
        localIsSparseException bits target globalLocalSlot = true
    · simp [relativeSplitSelectEntryIsMarked, hlive, hflag]
    · have hfalse :
          localIsSparseException bits target globalLocalSlot = false := by
        cases h :
            localIsSparseException bits target globalLocalSlot
        · rfl
        · contradiction
      simp [relativeSplitSelectEntryIsMarked, hlive, hfalse]
  · have hfalse :
        compactLocalEntryIsLive bits target globalLocalSlot = false := by
      cases h :
          compactLocalEntryIsLive bits target globalLocalSlot
      · rfl
      · exact False.elim (hlive h)
    simp [relativeSplitSelectEntryIsMarked, hfalse]

theorem localBaseOccurrence_exact
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat)
    (hlive :
      compactLocalEntryIsLive bits target globalLocalSlot = true) :
    relativeSplitSelectLocalBaseOccurrence
      (superEntry bits target
        (globalLocalSlot / localSlotsPerSuper bits.length))
      (localEntry bits target globalLocalSlot) =
      localBaseOccurrence bits.length globalLocalSlot := by
  let superBase :=
    globalLocalSlot / localSlotsPerSuper bits.length *
      superStride bits.length
  let base := localBaseOccurrence bits.length globalLocalSlot
  have hbase_ge : superBase <= base := by
    simp [superBase, base, localBaseOccurrence,
      localSlotInSuperOfGlobal]
  simp [relativeSplitSelectLocalBaseOccurrence,
    superEntry, localEntry, hlive, localSuperSlot]
  omega

theorem localBasePosition_exact
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat)
    (hlive :
      compactLocalEntryIsLive bits target globalLocalSlot = true) :
    relativeSplitSelectLocalBasePosition
      (wordBits bits.length)
      (superEntry bits target
        (globalLocalSlot / localSlotsPerSuper bits.length))
      (localEntry bits target globalLocalSlot) =
      position bits target (localBaseOccurrence bits.length globalLocalSlot) := by
  let superSlot := globalLocalSlot / localSlotsPerSuper bits.length
  let superBase := superSlot * superStride bits.length
  let base := localBaseOccurrence bits.length globalLocalSlot
  let superPos := position bits target superBase
  let basePos := position bits target base
  let wordSize := wordBits bits.length
  have hbase_ge : superBase <= base := by
    simp [superBase, base, superSlot, localBaseOccurrence,
      localSlotInSuperOfGlobal]
  have hposMono : superPos <= basePos := by
    simpa [superPos, basePos] using
      position_mono bits target hbase_ge
  have hdivMono :
      superPos / wordSize <= basePos / wordSize := by
    exact Nat.div_le_div_right hposMono
  have hmod :
      basePos / wordSize * wordSize +
          (basePos - basePos / wordSize * wordSize) =
        basePos := by
    have hle := Nat.div_mul_le_self basePos wordSize
    omega
  have hwordIndexEq :
      superPos / wordSize +
          (basePos / wordSize - superPos / wordSize) =
        basePos / wordSize := by
    omega
  have hassembled :
      (superPos / wordSize +
          (basePos / wordSize - superPos / wordSize)) * wordSize +
          (basePos - basePos / wordSize * wordSize) =
        basePos := by
    rw [hwordIndexEq]
    exact hmod
  simpa [relativeSplitSelectLocalBasePosition,
    superEntry, localEntry, hlive, localSuperSlot,
    superSlot, superBase, base, superPos, basePos, wordSize]
    using hassembled

theorem localEntries_missing_exact
    (bits : List Bool) (target : Bool) (q : Nat)
    (super : SparseDenseSelectDenseLocalEntry)
    (hsuper :
      (superEntries bits target)[
          selectSuperSlot q
            (superStride bits.length)]? = some super)
    (hvalid : q < occurrenceCount bits target)
    (hshort :
      relativeSplitSelectEntryIsMarked super = false)
    (hmissing :
      (localEntries bits target)[
          relativeSplitSelectLocalSlot q
            (superStride bits.length)
            (localSlotsPerSuper bits.length)
            (localStride bits.length) super]? =
        none) :
    RMQ.Succinct.select target bits q = none := by
  let localSlot :=
    relativeSplitSelectLocalSlot q
      (superStride bits.length)
      (localSlotsPerSuper bits.length)
      (localStride bits.length) super
  have hfacts :=
    localSlot_facts bits target q super hsuper hvalid hshort
  rcases hfacts with
    ⟨hlocalSlotLt, _heff, _hlive, _hsameSuper,
      _hbaseLe, _hend⟩
  have hget :=
    localEntries_get? bits target
      (globalLocalSlot := localSlot) hlocalSlotLt
  have hmissingLocal :
      (localEntries bits target)[localSlot]? = none := by
    simpa [localSlot] using hmissing
  rw [hget] at hmissingLocal
  cases hmissingLocal

theorem sparseCompact_exact
    (bits : List Bool) (target : Bool) (q : Nat)
    (super loc : SparseDenseSelectDenseLocalEntry)
    (hsuper :
      (superEntries bits target)[
          selectSuperSlot q
            (superStride bits.length)]? = some super)
    (hvalid : q < occurrenceCount bits target)
    (hshort :
      relativeSplitSelectEntryIsMarked super = false)
    (hlocal :
      (localEntries bits target)[
          relativeSplitSelectLocalSlot q
            (superStride bits.length)
            (localSlotsPerSuper bits.length)
            (localStride bits.length) super]? =
        some loc)
    (hsparse :
      relativeSplitSelectEntryIsMarked loc = true) :
    ((sparseExceptionDirectory bits target).readCosted
      (relativeSplitSelectLocalBasePosition
        (wordBits bits.length) super loc)
      (relativeSplitSelectLocalSlot q
        (superStride bits.length)
        (localSlotsPerSuper bits.length)
        (localStride bits.length) super)
      (q - relativeSplitSelectLocalBaseOccurrence super loc)).erase =
      RMQ.Succinct.select target bits q := by
  let superSlot :=
    selectSuperSlot q (superStride bits.length)
  have hsuperSlotLt :
      superSlot < superSlotCount bits target := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, superEntries_length] using hlen
  have hbuiltSuper :=
    superEntries_get? bits target (superSlot := superSlot) hsuperSlotLt
  have hsuperEq :
      super = superEntry bits target superSlot := by
    rw [hbuiltSuper] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  let localSlot :=
    relativeSplitSelectLocalSlot q
      (superStride bits.length)
      (localSlotsPerSuper bits.length)
      (localStride bits.length)
      (superEntry bits target superSlot)
  have hfacts :=
    localSlot_facts bits target q
      (superEntry bits target superSlot)
      hsuper hvalid hshort
  rcases hfacts with
    ⟨hlocalSlotLt, heff, hlive, hsameSuper,
      hbaseLe, hqLtLocalEnd⟩
  have hlocalGet :=
    localEntries_get? bits target
      (globalLocalSlot := localSlot) hlocalSlotLt
  have hlocalAtSlot :
      (localEntries bits target)[localSlot]? = some loc := by
    simpa [localSlot] using hlocal
  rw [hlocalGet] at hlocalAtSlot
  have hlocEq :
      loc = localEntry bits target localSlot := by
    exact (Option.some.inj hlocalAtSlot).symm
  subst loc
  have hmark :=
    localEntry_marked_eq_flag bits target localSlot
  rw [hmark] at hsparse
  have hflag :
      localIsSparseException bits target localSlot = true := by
    have hpair :
        compactLocalEntryIsLive bits target localSlot = true /\
          localIsSparseException bits target localSlot = true := by
      simpa using hsparse
    exact hpair.2
  have hsameSuperSlot :
      localSuperSlot bits.length localSlot = superSlot := by
    simpa [superSlot] using hsameSuper
  have hlocalDiv :
      localSlot / localSlotsPerSuper bits.length = superSlot := by
    simpa [localSuperSlot] using hsameSuperSlot
  have hbaseOcc0 :=
    localBaseOccurrence_exact bits target localSlot hlive
  have hbaseOcc :
      relativeSplitSelectLocalBaseOccurrence
        (superEntry bits target superSlot)
        (localEntry bits target localSlot) =
        localBaseOccurrence bits.length localSlot := by
    simpa [hlocalDiv] using hbaseOcc0
  have hbasePos0 :=
    localBasePosition_exact bits target localSlot hlive
  have hbasePos :
      relativeSplitSelectLocalBasePosition
        (wordBits bits.length)
        (superEntry bits target superSlot)
        (localEntry bits target localSlot) =
        position bits target
          (localBaseOccurrence bits.length localSlot) := by
    simpa [hlocalDiv] using hbasePos0
  have hbaseLeLocal :
      localBaseOccurrence bits.length localSlot <= q := by
    simpa [localSlot] using hbaseLe
  have hqLtLocalEndLocal :
      q <
        localBaseOccurrence bits.length localSlot +
          localStride bits.length := by
    simpa [localSlot] using hqLtLocalEnd
  have hlocalOcc :
      q - localBaseOccurrence bits.length localSlot <
        localStride bits.length := by
    omega
  have hqEq :
      localBaseOccurrence bits.length localSlot +
          (q - localBaseOccurrence bits.length localSlot) =
        q := by
    omega
  have hbaseLeSuper :
      superSlot * superStride bits.length <= q := by
    have hmul :=
      Nat.div_mul_le_self q (superStride bits.length)
    simpa [superSlot, selectSuperSlot] using hmul
  have hqLtBaseStride :
      q <
        superSlot * superStride bits.length +
          superStride bits.length := by
    have hstride := superStride_pos bits.length
    have hlt := Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, selectSuperSlot,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  have hqLtSuperEnd :
      q < superEndOccurrence bits target superSlot := by
    unfold superEndOccurrence superBaseOccurrence
    exact Nat.lt_min.mpr ⟨hqLtBaseStride, hvalid⟩
  have hend :
      localBaseOccurrence bits.length localSlot +
          (q - localBaseOccurrence bits.length localSlot) <
        superEndOccurrence bits target
          (localSuperSlot bits.length localSlot) := by
    rw [hqEq, hsameSuperSlot]
    exact hqLtSuperEnd
  rcases select_exists_of_lt_occurrenceCount
      bits target hvalid with ⟨pos, hselect⟩
  have hselectLocal :
      RMQ.Succinct.select target bits
          (localBaseOccurrence bits.length localSlot +
            (q - localBaseOccurrence bits.length localSlot)) =
        some pos := by
    simpa [hqEq] using hselect
  have hread :=
    sparseExceptionDirectory_readCosted_lookup_exact
      bits target hlocalSlotLt heff hflag hlocalOcc hend hselectLocal
  have hbaseCount :
      localBaseOccurrence bits.length localSlot <
        occurrenceCount bits target := by
    omega
  rcases select_exists_of_lt_occurrenceCount
      bits target hbaseCount with ⟨basePos, hbaseSelect⟩
  have hbaseLePos :
      position bits target
          (localBaseOccurrence bits.length localSlot) <= pos := by
    have hmono :=
      select_index_mono (target := target) (bits := bits)
        (lo := localBaseOccurrence bits.length localSlot)
        (hi := q) (posLo := basePos) (posHi := pos)
        hbaseLeLocal hbaseSelect hselect
    have hbaseEqPos :
        position bits target
            (localBaseOccurrence bits.length localSlot) = basePos :=
      position_eq_of_select bits target hbaseSelect
    rwa [hbaseEqPos]
  have hposEq :
      position bits target
          (localBaseOccurrence bits.length localSlot) +
        (pos -
          position bits target
            (localBaseOccurrence bits.length localSlot)) =
        pos := by
    omega
  rw [hselect]
  simpa [localSlot, hbaseOcc, hbasePos, hposEq] using hread

theorem selected_lt_shortLocalBase_plus_span
    (bits : List Bool) (target : Bool)
    {globalLocalSlot q pos : Nat}
    (hbaseLe :
      localBaseOccurrence bits.length globalLocalSlot <= q)
    (hqEnd :
      q < shortSuperLocalEndOccurrence bits target globalLocalSlot)
    (hselect :
      RMQ.Succinct.select target bits q = some pos) :
    pos <
      position bits target
          (localBaseOccurrence bits.length globalLocalSlot) +
        shortSuperLocalSpan bits target globalLocalSlot := by
  let base := localBaseOccurrence bits.length globalLocalSlot
  let endOcc := shortSuperLocalEndOccurrence bits target globalLocalSlot
  let basePos := position bits target base
  let lastPos := position bits target (endOcc - 1)
  have hqCount : q < occurrenceCount bits target :=
    occurrence_lt_count_of_select hselect
  have hbaseCount : base < occurrenceCount bits target := by
    omega
  rcases select_exists_of_lt_occurrenceCount
      bits target hbaseCount with ⟨baseWitness, hbaseSelect⟩
  have hbaseEq :
      basePos = baseWitness := by
    simpa [basePos, base] using
      position_eq_of_select bits target hbaseSelect
  have hbaseLePos : baseWitness <= pos :=
    select_index_mono (target := target) (bits := bits)
      (lo := base) (hi := q) (posLo := baseWitness)
      (posHi := pos) hbaseLe hbaseSelect hselect
  have hendCount : endOcc <= occurrenceCount bits target := by
    simpa [endOcc] using
      shortSuperLocalEndOccurrence_le_count bits target globalLocalSlot
  have hendPos : 0 < endOcc := by
    omega
  have hlastCount : endOcc - 1 < occurrenceCount bits target := by
    omega
  rcases select_exists_of_lt_occurrenceCount
      bits target hlastCount with ⟨lastWitness, hlastSelect⟩
  have hlastEq :
      lastPos = lastWitness := by
    simpa [lastPos, endOcc] using
      position_eq_of_select bits target hlastSelect
  have hqLeLast : q <= endOcc - 1 := by
    omega
  have hposLeLast : pos <= lastWitness :=
    select_index_mono (target := target) (bits := bits)
      (lo := q) (hi := endOcc - 1) (posLo := pos)
      (posHi := lastWitness) hqLeLast hselect hlastSelect
  unfold shortSuperLocalSpan
  change pos < basePos + (lastPos + 1 - basePos)
  rw [hbaseEq, hlastEq]
  omega

theorem dense_exact
    (bits : List Bool) (target : Bool) (q : Nat)
    (super loc : SparseDenseSelectDenseLocalEntry)
    (hsuper :
      (superEntries bits target)[
          selectSuperSlot q
            (superStride bits.length)]? = some super)
    (hvalid : q < occurrenceCount bits target)
    (hshort :
      relativeSplitSelectEntryIsMarked super = false)
    (hlocal :
      (localEntries bits target)[
          relativeSplitSelectLocalSlot q
            (superStride bits.length)
            (localSlotsPerSuper bits.length)
            (localStride bits.length) super]? =
        some loc)
    (hdense :
      relativeSplitSelectEntryIsMarked loc = false) :
    (denseTwoWordSelectCosted target
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
        bits (wordBits_pos bits.length))
      (relativeSplitSelectLocalBasePosition
        (wordBits bits.length) super loc)
      (relativeSplitSelectLocalBaseOccurrence super loc) q).erase =
      RMQ.Succinct.select target bits q := by
  let superSlot :=
    selectSuperSlot q (superStride bits.length)
  have hsuperSlotLt :
      superSlot < superSlotCount bits target := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, superEntries_length] using hlen
  have hbuiltSuper :=
    superEntries_get? bits target (superSlot := superSlot) hsuperSlotLt
  have hsuperEq :
      super = superEntry bits target superSlot := by
    rw [hbuiltSuper] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  let localSlot :=
    relativeSplitSelectLocalSlot q
      (superStride bits.length)
      (localSlotsPerSuper bits.length)
      (localStride bits.length)
      (superEntry bits target superSlot)
  have hfacts :=
    localSlot_facts bits target q
      (superEntry bits target superSlot)
      hsuper hvalid hshort
  rcases hfacts with
    ⟨hlocalSlotLt, _heff, hlive, hsameSuper,
      hbaseLe, hqLtLocalEnd⟩
  have hlocalGet :=
    localEntries_get? bits target
      (globalLocalSlot := localSlot) hlocalSlotLt
  have hlocalAtSlot :
      (localEntries bits target)[localSlot]? = some loc := by
    simpa [localSlot] using hlocal
  rw [hlocalGet] at hlocalAtSlot
  have hlocEq :
      loc = localEntry bits target localSlot := by
    exact (Option.some.inj hlocalAtSlot).symm
  subst loc
  have hmark :=
    localEntry_marked_eq_flag bits target localSlot
  rw [hmark] at hdense
  have hliveLocal :
      compactLocalEntryIsLive bits target localSlot = true := by
    simpa [localSlot] using hlive
  have hflagFalse :
      localIsSparseException bits target localSlot = false := by
    cases hflag :
        localIsSparseException bits target localSlot
    · rfl
    · have hmarkedTrue :
          (compactLocalEntryIsLive bits target localSlot &&
            localIsSparseException bits target localSlot) = true := by
        simp [hliveLocal, hflag]
      rw [hmarkedTrue] at hdense
      cases hdense
  have hsameSuperSlot :
      localSuperSlot bits.length localSlot = superSlot := by
    simpa [superSlot] using hsameSuper
  have hlocalDiv :
      localSlot / localSlotsPerSuper bits.length = superSlot := by
    simpa [localSuperSlot] using hsameSuperSlot
  have hbaseOcc0 :=
    localBaseOccurrence_exact bits target localSlot hliveLocal
  have hbaseOcc :
      relativeSplitSelectLocalBaseOccurrence
        (superEntry bits target superSlot)
        (localEntry bits target localSlot) =
        localBaseOccurrence bits.length localSlot := by
    simpa [hlocalDiv] using hbaseOcc0
  have hbasePos0 :=
    localBasePosition_exact bits target localSlot hliveLocal
  have hbasePos :
      relativeSplitSelectLocalBasePosition
        (wordBits bits.length)
        (superEntry bits target superSlot)
        (localEntry bits target localSlot) =
        position bits target
          (localBaseOccurrence bits.length localSlot) := by
    simpa [hlocalDiv] using hbasePos0
  have hbaseLeLocal :
      localBaseOccurrence bits.length localSlot <= q := by
    simpa [localSlot] using hbaseLe
  have hqLtLocalEndLocal :
      q <
        localBaseOccurrence bits.length localSlot +
          localStride bits.length := by
    simpa [localSlot] using hqLtLocalEnd
  have hbaseLeSuper :
      superSlot * superStride bits.length <= q := by
    have hmul :=
      Nat.div_mul_le_self q (superStride bits.length)
    simpa [superSlot, selectSuperSlot] using hmul
  have hqLtBaseStride :
      q <
        superSlot * superStride bits.length +
          superStride bits.length := by
    have hstride := superStride_pos bits.length
    have hlt := Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, selectSuperSlot,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  have hqLtSuperEnd :
      q < superEndOccurrence bits target superSlot := by
    unfold superEndOccurrence superBaseOccurrence
    exact Nat.lt_min.mpr ⟨hqLtBaseStride, hvalid⟩
  have hqLtShortEnd :
      q <
        shortSuperLocalEndOccurrence bits target localSlot := by
    unfold shortSuperLocalEndOccurrence
    exact Nat.lt_min.mpr
      ⟨hqLtLocalEndLocal, by
        simpa [hsameSuperSlot] using hqLtSuperEnd⟩
  have hlocalSpanLeWord :
      shortSuperLocalSpan bits target localSlot <=
        wordBits bits.length := by
    unfold localIsSparseException at hflagFalse
    have hshortBuilt :
        superIsLong bits target superSlot = false := by
      have hsuperMark :=
        superEntry_marked_eq_long bits target superSlot
      rw [hsuperMark] at hshort
      exact hshort
    have hshortAtLocal :
        superIsLong bits target
            (localSuperSlot bits.length localSlot) = false := by
      rw [hsameSuperSlot]
      exact hshortBuilt
    rw [hshortAtLocal] at hflagFalse
    simp only [Bool.not_false, Bool.true_and] at hflagFalse
    by_cases hlt :
        wordBits bits.length <
          shortSuperLocalSpan bits target localSlot
    · have hdec :
          decide
              (wordBits bits.length <
                shortSuperLocalSpan bits target localSlot) = true := by
        simp [hlt]
      rw [hdec] at hflagFalse
      cases hflagFalse
    · exact Nat.le_of_not_gt hlt
  rcases select_exists_of_lt_occurrenceCount
      bits target hvalid with ⟨pos, hselect⟩
  have hposLtLocalSpan :=
    selected_lt_shortLocalBase_plus_span
      bits target hbaseLeLocal hqLtShortEnd hselect
  have hposSpanBuilt :
      pos <
        position bits target
            (localBaseOccurrence bits.length localSlot) +
          wordBits bits.length := by
    omega
  have hbaseCount :
      localBaseOccurrence bits.length localSlot <
        occurrenceCount bits target := by
    omega
  rcases select_exists_of_lt_occurrenceCount
      bits target hbaseCount with ⟨basePos, hbaseSelect⟩
  have hbaseEqPos :
      position bits target
          (localBaseOccurrence bits.length localSlot) = basePos :=
    position_eq_of_select bits target hbaseSelect
  have hbaseSelectEntry :
      RMQ.Succinct.select target bits
          (relativeSplitSelectLocalBaseOccurrence
            (superEntry bits target superSlot)
            (localEntry bits target localSlot)) =
        some
          (relativeSplitSelectLocalBasePosition
            (wordBits bits.length)
            (superEntry bits target superSlot)
            (localEntry bits target localSlot)) := by
    simpa [hbaseOcc, hbasePos, hbaseEqPos] using hbaseSelect
  have hbaseLeEntry :
      relativeSplitSelectLocalBaseOccurrence
          (superEntry bits target superSlot)
          (localEntry bits target localSlot) <= q := by
    simpa [hbaseOcc] using hbaseLeLocal
  have hposSpanEntry :
      pos <
        relativeSplitSelectLocalBasePosition
            (wordBits bits.length)
            (superEntry bits target superSlot)
            (localEntry bits target localSlot) +
          wordBits bits.length := by
    simpa [hbasePos] using hposSpanBuilt
  have hdenseFacts :
      DenseLocalPayloadRoutingFacts
        target bits (wordBits bits.length)
        (relativeSplitSelectLocalBasePosition
          (wordBits bits.length)
          (superEntry bits target superSlot)
          (localEntry bits target localSlot))
        (relativeSplitSelectLocalBaseOccurrence
          (superEntry bits target superSlot)
          (localEntry bits target localSlot)) q :=
    denseLocalPayloadRoutingFacts_of_selected_span
      (hwordSize := wordBits_pos bits.length)
      hbaseSelectEntry hselect hbaseLeEntry hposSpanEntry
  have haligned :
      SelectAlignedBitWords bits
        (wordBits bits.length)
        (SuccinctSpace.BoundedPayloadWordStore.ofChunks
          bits (wordBits_pos bits.length)) :=
    selectAlignedBitWords_ofChunks bits
      (wordBits_pos bits.length)
  simpa [localSlot] using
    denseTwoWordSelectCosted_exact_of_payload_routing_facts
      target haligned hdenseFacts

structure SparseExceptionSelectData
    (bits : List Bool) (target : Bool)
    (rankSuperOverhead rankBlockOverhead : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  wordSize_le_machine :
    wordSize <= SuccinctRank.machineWordBits bits.length
  superStride : Nat
  superStride_pos : 0 < superStride
  localStride : Nat
  localStride_pos : 0 < localStride
  localSlotsPerSuper : Nat
  superEntries : List SparseDenseSelectDenseLocalEntry
  longFlagBits : List Bool
  longFlagRankSuperOverhead : Nat
  longFlagRankBlockOverhead : Nat
  longFlagRankData :
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      longFlagBits longFlagRankSuperOverhead longFlagRankBlockOverhead 4
  longFlagRank_wordSize_le_machine :
    longFlagRankData.wordSize <=
      SuccinctRank.machineWordBits bits.length
  longFlagRank_superWidth_le_machine :
    longFlagRankData.superWidth <=
      SuccinctRank.machineWordBits bits.length
  longFlagRank_blockWidth_le_machine :
    longFlagRankData.blockWidth <=
      SuccinctRank.machineWordBits bits.length
  longSuperRelativeEntries : List Nat
  localEntries : List SparseDenseSelectDenseLocalEntry
  superFieldWidth : Nat
  longSuperRelativeWidth : Nat
  localFieldWidth : Nat
  superTable :
    FixedWidthSparseDenseSelectDenseLocalEntryTable
      superEntries superFieldWidth
  longSuperRelativeTable :
    SuccinctSpace.FixedWidthNatTable
      longSuperRelativeEntries longSuperRelativeWidth
  localTable :
    FixedWidthSparseDenseSelectDenseLocalEntryTable
      localEntries localFieldWidth
  sparseDirectory :
    SparseExceptionDirectory
      bits target rankSuperOverhead rankBlockOverhead
  bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize
  super_read_words_length_le_machine :
    FixedWidthSparseDenseSelectDenseLocalEntryTable.ReadWordsLengthLeMachine
      superTable bits.length
  long_read_words_length_le_machine :
    forall {i : Nat} {word : List Bool},
      longSuperRelativeTable.store.words[i]? = some word ->
        word.length <= SuccinctRank.machineWordBits bits.length
  local_read_words_length_le_machine :
    FixedWidthSparseDenseSelectDenseLocalEntryTable.ReadWordsLengthLeMachine
      localTable bits.length
  payload_length_le_overhead :
    (superTable.payload ++ longFlagBits ++
      longFlagRankData.auxPayload ++ longSuperRelativeTable.payload ++
        localTable.payload ++ sparseDirectory.payload).length <=
        canonicalSparseExceptionSelectOverhead bits.length
  super_missing_exact :
    forall q,
      superEntries[selectSuperSlot q superStride]? = none ->
        RMQ.Succinct.select target bits q = none
  long_explicit_exact :
    forall q super,
      superEntries[selectSuperSlot q superStride]? = some super ->
      q < occurrenceCount bits target ->
      relativeSplitSelectEntryIsMarked super = true ->
        (longSuperRelativeEntries[
            relativeSplitSelectLongCompactSlot
              (RMQ.Succinct.rankPrefix true longFlagBits
                (selectSuperSlot q superStride))
              (q - super.baseOccurrence) superStride]?).map
          (fun offset =>
            relativeSplitSelectEntryBasePosition wordSize super +
              offset) =
          RMQ.Succinct.select target bits q
  local_missing_exact :
    forall q super,
      superEntries[selectSuperSlot q superStride]? = some super ->
      q < occurrenceCount bits target ->
      relativeSplitSelectEntryIsMarked super = false ->
      localEntries[
          relativeSplitSelectLocalSlot q superStride
            localSlotsPerSuper localStride super]? = none ->
        RMQ.Succinct.select target bits q = none
  sparse_compact_exact :
    forall q super loc,
      superEntries[selectSuperSlot q superStride]? = some super ->
      q < occurrenceCount bits target ->
      relativeSplitSelectEntryIsMarked super = false ->
      localEntries[
          relativeSplitSelectLocalSlot q superStride
            localSlotsPerSuper localStride super]? = some loc ->
      relativeSplitSelectEntryIsMarked loc = true ->
        (sparseDirectory.readCosted
          (relativeSplitSelectLocalBasePosition wordSize super loc)
          (relativeSplitSelectLocalSlot q superStride
            localSlotsPerSuper localStride super)
          (q - relativeSplitSelectLocalBaseOccurrence super loc)).erase =
          RMQ.Succinct.select target bits q
  dense_exact :
    forall q super loc,
      superEntries[selectSuperSlot q superStride]? = some super ->
      q < occurrenceCount bits target ->
      relativeSplitSelectEntryIsMarked super = false ->
      localEntries[
          relativeSplitSelectLocalSlot q superStride
            localSlotsPerSuper localStride super]? = some loc ->
      relativeSplitSelectEntryIsMarked loc = false ->
        (denseTwoWordSelectCosted target bitWords
          (relativeSplitSelectLocalBasePosition wordSize super loc)
          (relativeSplitSelectLocalBaseOccurrence super loc) q).erase =
          RMQ.Succinct.select target bits q

namespace SparseExceptionSelectData

def payload
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) :
    List Bool :=
  data.superTable.payload ++ data.longFlagBits ++
    data.longFlagRankData.auxPayload ++
      data.longSuperRelativeTable.payload ++
        data.localTable.payload ++ data.sparseDirectory.payload

def longFlagRankReadWords
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) :
    List (List Bool) :=
  (((data.longFlagRankData.superTables.trueTable.store.words.toList ++
      data.longFlagRankData.superTables.falseTable.store.words.toList) ++
    data.longFlagRankData.blockTables.trueTable.store.words.toList ++
      data.longFlagRankData.blockTables.falseTable.store.words.toList) ++
        data.longFlagRankData.bitWords.store.words.toList)

def readWords
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) :
    List (List Bool) :=
  data.superTable.readWords ++
    data.longFlagRankReadWords ++
      data.longSuperRelativeTable.store.words.toList ++
        data.localTable.readWords ++
          data.sparseDirectory.readWords ++
            data.bitWords.store.words.toList

def queryOccurrence
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (_data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (idx : Nat) : Nat :=
  idx

def selectCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (idx : Nat) : Costed (Option Nat) :=
  let q := data.queryOccurrence idx
  if idx < occurrenceCount bits target then
    Costed.bind
      (data.superTable.readCosted
        (selectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => Costed.pure none
      | some super =>
          if relativeSplitSelectEntryIsMarked super then
            Costed.bind
              (data.longFlagRankData.rankCosted true
                (selectSuperSlot q data.superStride))
              fun exceptionRank =>
                relativeOffsetReadCosted data.longSuperRelativeTable
                  (relativeSplitSelectEntryBasePosition
                    data.wordSize super)
                  (relativeSplitSelectLongCompactSlot
                    exceptionRank (q - super.baseOccurrence)
                    data.superStride)
          else
            let localSlot :=
              relativeSplitSelectLocalSlot q data.superStride
                data.localSlotsPerSuper data.localStride super
            Costed.bind (data.localTable.readCosted localSlot) fun loc? =>
              match loc? with
              | none => Costed.pure none
              | some loc =>
                  if relativeSplitSelectEntryIsMarked loc then
                    data.sparseDirectory.readCosted
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        relativeSplitSelectLocalBaseOccurrence
                          super loc)
                  else
                    denseTwoWordSelectCosted target data.bitWords
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitSelectLocalBaseOccurrence
                        super loc) q
  else
    Costed.pure none

theorem payload_length_le_canonical
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) :
    data.payload.length <=
      canonicalSparseExceptionSelectOverhead bits.length := by
  simpa [payload] using data.payload_length_le_overhead

theorem selectCosted_cost_le
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) (idx : Nat) :
    (data.selectCosted idx).cost <=
      sparseDenseSelectQueryCost := by
  unfold selectCosted queryOccurrence sparseDenseSelectQueryCost
  by_cases hvalid : idx < occurrenceCount bits target
  case pos =>
    cases hsuperValue :
        (data.superTable.readCosted
          (selectSuperSlot
            idx data.superStride)).value with
    | none =>
        simp [Costed.bind, Costed.pure, hvalid, hsuperValue] <;> omega
    | some super =>
        by_cases hlong :
            relativeSplitSelectEntryIsMarked super = true
        case pos =>
          have hrankCost :=
            data.longFlagRankData.rankCosted_cost_le true
              (selectSuperSlot
                idx data.superStride)
          have hlongCost :
              (data.longSuperRelativeTable.readCosted
                (relativeSplitSelectLongCompactSlot
                  (data.longFlagRankData.rankCosted true
                    (selectSuperSlot
                      idx data.superStride)).value
                  (idx - super.baseOccurrence)
                  data.superStride)).cost <= 1 := by
            exact data.longSuperRelativeTable.readCosted_cost_le_one _
          simp [relativeOffsetReadCosted, Costed.bind, Costed.map,
            Costed.pure, hvalid, hsuperValue, hlong] <;> omega
        case neg =>
          let localSlot :=
            relativeSplitSelectLocalSlot
              idx data.superStride
              data.localSlotsPerSuper data.localStride super
          cases hlocalValue :
              (data.localTable.readCosted localSlot).value with
          | none =>
              simp [Costed.bind, Costed.pure, hvalid, hsuperValue, hlong,
                localSlot, hlocalValue] <;> omega
          | some loc =>
              by_cases hsparse :
                  relativeSplitSelectEntryIsMarked loc = true
              case pos =>
                have hsparseCost :
                  (data.sparseDirectory.readCosted
                    (relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitSelectLocalSlot
                      idx data.superStride
                      data.localSlotsPerSuper data.localStride super)
                    (idx -
                      relativeSplitSelectLocalBaseOccurrence super loc)).cost
                      <= 5 := by
                  simpa [localSlot] using
                    data.sparseDirectory.readCosted_cost_le_five
                      (relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                      localSlot
                      (idx -
                        relativeSplitSelectLocalBaseOccurrence super loc)
                simp [Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse] <;> omega
              case neg =>
                have hdenseCost :=
                  denseTwoWordSelectCosted_cost_le_five target
                    data.bitWords
                    (relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitSelectLocalBaseOccurrence
                      super loc) idx
                simp [Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse] <;> omega
  case neg =>
    simp [Costed.pure, hvalid]

theorem selectCosted_exact
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) (idx : Nat) :
    (data.selectCosted idx).erase =
      RMQ.Succinct.select target bits idx := by
  let q := idx
  unfold selectCosted queryOccurrence
  dsimp only
  by_cases hvalid : idx < occurrenceCount bits target
  case pos =>
    have hvalidQ : q < occurrenceCount bits target := by
      simpa [q] using hvalid
    cases hsuper :
        data.superEntries[
          selectSuperSlot
            idx data.superStride]? with
    | none =>
        have hsuperQ :
            data.superEntries[
                selectSuperSlot q data.superStride]? =
              none := by
          simpa [q] using hsuper
        simp [hvalid, hsuper, Costed.erase_bind,
          FixedWidthSparseDenseSelectDenseLocalEntryTable.readCosted_erase]
        exact (data.super_missing_exact q hsuperQ).symm
    | some super =>
        have hsuperQ :
            data.superEntries[
                selectSuperSlot q data.superStride]? =
              some super := by
          simpa [q] using hsuper
        by_cases hlong :
            relativeSplitSelectEntryIsMarked super = true
        case pos =>
          have hrank :=
            data.longFlagRankData.rankCosted_exact true
              (selectSuperSlot
                idx data.superStride)
          simp [hvalid, hsuper, hlong, relativeOffsetReadCosted,
            Costed.erase_bind, Costed.erase_map,
            FixedWidthSparseDenseSelectDenseLocalEntryTable.readCosted_erase,
            SuccinctSpace.FixedWidthNatTable.readCosted_erase, hrank]
          simpa [q] using
            data.long_explicit_exact q super hsuperQ hvalidQ hlong
        case neg =>
          let localSlot :=
            relativeSplitSelectLocalSlot
              idx data.superStride
              data.localSlotsPerSuper data.localStride super
          have hlongFalse :
              relativeSplitSelectEntryIsMarked super = false := by
            cases hmark : relativeSplitSelectEntryIsMarked super
            case false =>
              rfl
            case true =>
              exact False.elim (hlong hmark)
          cases hlocal :
              data.localEntries[localSlot]? with
          | none =>
              simp [hvalid, hsuper, hlong, localSlot, hlocal,
                Costed.erase_bind,
                FixedWidthSparseDenseSelectDenseLocalEntryTable.readCosted_erase]
              have hlocal' :
                data.localEntries[
                    relativeSplitSelectLocalSlot q data.superStride
                      data.localSlotsPerSuper data.localStride super]? =
                  none := by
                simpa [q, localSlot] using hlocal
              exact (data.local_missing_exact q super hsuperQ hvalidQ hlongFalse
                hlocal').symm
          | some loc =>
              by_cases hsparse :
                  relativeSplitSelectEntryIsMarked loc = true
              case pos =>
                simp [hvalid, hsuper, hlong, localSlot, hlocal,
                  Costed.erase_bind,
                  FixedWidthSparseDenseSelectDenseLocalEntryTable.readCosted_erase]
                have hlocal' :
                    data.localEntries[
                        relativeSplitSelectLocalSlot q data.superStride
                        data.localSlotsPerSuper data.localStride super]? =
                      some loc := by
                  simpa [q, localSlot] using hlocal
                simp [hsparse]
                simpa [q] using
                  data.sparse_compact_exact q super loc hsuperQ hvalidQ
                    hlongFalse hlocal' hsparse
              case neg =>
                have hsparseFalse :
                    relativeSplitSelectEntryIsMarked loc = false := by
                  cases hmark : relativeSplitSelectEntryIsMarked loc
                  case false =>
                    rfl
                  case true =>
                    exact False.elim (hsparse hmark)
                simp [hvalid, hsuper, hlong, localSlot, hlocal,
                  Costed.erase_bind,
                  FixedWidthSparseDenseSelectDenseLocalEntryTable.readCosted_erase]
                have hlocal' :
                    data.localEntries[
                        relativeSplitSelectLocalSlot q data.superStride
                        data.localSlotsPerSuper data.localStride super]? =
                      some loc := by
                  simpa [q, localSlot] using hlocal
                simp [hsparse]
                simpa [q] using
                  data.dense_exact q super loc hsuperQ hvalidQ hlongFalse
                    hlocal' hsparseFalse
  case neg =>
    simp [hvalid, Costed.pure]
    exact
      (select_none_of_rankPrefix_length_le
        (target := target) (bits := bits) (occurrence := idx)
        (by
          simpa [occurrenceCount] using Nat.le_of_not_gt hvalid)).symm

theorem longFlagRank_read_word_length_le_machine
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    (hmem : List.Mem word data.longFlagRankReadWords) :
    word.length <=
      SuccinctRank.machineWordBits bits.length := by
  rw [longFlagRankReadWords] at hmem
  cases List.mem_append.mp hmem with
  | inl hsampleMem =>
      cases List.mem_append.mp hsampleMem with
      | inl hsamplePrefix =>
          cases List.mem_append.mp hsamplePrefix with
          | inl hsuperMem =>
              cases List.mem_append.mp hsuperMem with
              | inl hsuperTrueMem =>
                  cases (List.mem_iff_getElem?.mp hsuperTrueMem) with
                  | intro i hgetList =>
                    have hget :
                        data.longFlagRankData.superTables.trueTable.store.words[i]? =
                          some word := by
                      simpa [Array.getElem?_toList] using hgetList
                    rw [data.longFlagRankData.superTables.trueTable.read_word_length_of_some
                      hget]
                    exact data.longFlagRank_superWidth_le_machine
              | inr hsuperFalseMem =>
                  cases (List.mem_iff_getElem?.mp hsuperFalseMem) with
                  | intro i hgetList =>
                    have hget :
                        data.longFlagRankData.superTables.falseTable.store.words[i]? =
                          some word := by
                      simpa [Array.getElem?_toList] using hgetList
                    rw [data.longFlagRankData.superTables.falseTable.read_word_length_of_some
                      hget]
                    exact data.longFlagRank_superWidth_le_machine
          | inr hblockTrueMem =>
              cases (List.mem_iff_getElem?.mp hblockTrueMem) with
              | intro i hgetList =>
                have hget :
                    data.longFlagRankData.blockTables.trueTable.store.words[i]? =
                      some word := by
                  simpa [Array.getElem?_toList] using hgetList
                rw [data.longFlagRankData.blockTables.trueTable.read_word_length_of_some
                  hget]
                exact data.longFlagRank_blockWidth_le_machine
      | inr hblockFalseMem =>
          cases (List.mem_iff_getElem?.mp hblockFalseMem) with
          | intro i hgetList =>
            have hget :
                data.longFlagRankData.blockTables.falseTable.store.words[i]? =
                  some word := by
              simpa [Array.getElem?_toList] using hgetList
            rw [data.longFlagRankData.blockTables.falseTable.read_word_length_of_some
              hget]
            exact data.longFlagRank_blockWidth_le_machine
  | inr hflagMem =>
      exact Nat.le_trans
        (data.longFlagRankData.bitWords.word_length_le hflagMem)
        data.longFlagRank_wordSize_le_machine

theorem read_word_length_le_machine
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    (hmem : List.Mem word data.readWords) :
    word.length <=
      SuccinctRank.machineWordBits bits.length := by
  rw [readWords] at hmem
  cases List.mem_append.mp hmem with
  | inl hprefix0 =>
      cases List.mem_append.mp hprefix0 with
      | inl hprefix1 =>
          cases List.mem_append.mp hprefix1 with
          | inl hprefix2 =>
              cases List.mem_append.mp hprefix2 with
              | inl hsuperOrRank =>
                  cases List.mem_append.mp hsuperOrRank with
                  | inl hsuperMem =>
                      exact data.superTable.read_word_length_le_machine
                        data.super_read_words_length_le_machine hsuperMem
                  | inr hrankMem =>
                      exact data.longFlagRank_read_word_length_le_machine
                        hrankMem
              | inr hlongMem =>
                  cases (List.mem_iff_getElem?.mp hlongMem) with
                  | intro i hgetList =>
                    have hget :
                        data.longSuperRelativeTable.store.words[i]? =
                          some word := by
                      simpa [Array.getElem?_toList] using hgetList
                    exact data.long_read_words_length_le_machine hget
          | inr hlocalMem =>
              exact data.localTable.read_word_length_le_machine
                data.local_read_words_length_le_machine hlocalMem
      | inr hsparseMem =>
          exact data.sparseDirectory.read_words_length_le_machine hsparseMem
  | inr hbitsMem =>
      exact Nat.le_trans (data.bitWords.word_length_le hbitsMem)
        data.wordSize_le_machine

theorem profile
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) :
    data.payload.length <=
        canonicalSparseExceptionSelectOverhead bits.length /\
      SuccinctSpace.LittleOLinear canonicalSparseExceptionSelectOverhead /\
      (forall idx,
        (data.selectCosted idx).cost <= sparseDenseSelectQueryCost) /\
      (forall idx,
        (data.selectCosted idx).erase =
          RMQ.Succinct.select target bits idx) /\
      forall {word : List Bool},
        List.Mem word data.readWords ->
          word.length <=
            SuccinctRank.machineWordBits bits.length := by
  exact
    ⟨data.payload_length_le_canonical,
      canonicalSparseExceptionSelectOverhead_littleO,
      data.selectCosted_cost_le,
      data.selectCosted_exact,
      fun {word} hmem => data.read_word_length_le_machine hmem⟩

def toChargedSelectPositionSource
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) :
    ChargedSelectPositionSource target bits
      canonicalSparseExceptionSelectOverhead
      sparseDenseSelectQueryCost :=
  let payloadBits := SparseExceptionSelectData.payload data
  let words := SparseExceptionSelectData.readWords data
  let query := SparseExceptionSelectData.selectCosted data
  let hpayload :
      payloadBits.length <=
        canonicalSparseExceptionSelectOverhead bits.length := by
    simpa [payloadBits] using payload_length_le_canonical data
  { domainSize := bits.length
    payload := payloadBits
    readWords := words
    selectPositionCosted := query
    payload_length_le := hpayload
    overhead_littleO :=
      canonicalSparseExceptionSelectOverhead_littleO
    selectPositionCosted_cost_le := by
      intro idx
      simpa [query] using selectCosted_cost_le data idx
    selectPositionCosted_exact := by
      intro idx
      simpa [query] using selectCosted_exact data idx
    read_word_length_le_machine := by
      intro word hmem
      simpa [words] using read_word_length_le_machine data hmem }

end SparseExceptionSelectData

def sparseExceptionSelectData (bits : List Bool) (target : Bool) :
    SparseExceptionSelectData bits target
      (sparseExceptionEffectiveFlagRankSuperOverhead bits target)
      (sparseExceptionEffectiveFlagRankBlockOverhead bits target) where
  wordSize := wordBits bits.length
  wordSize_pos := wordBits_pos bits.length
  wordSize_le_machine := by
    simp [wordBits]
  superStride := superStride bits.length
  superStride_pos := superStride_pos bits.length
  localStride := localStride bits.length
  localStride_pos := localStride_pos bits.length
  localSlotsPerSuper := localSlotsPerSuper bits.length
  superEntries := superEntries bits target
  longFlagBits := longSuperFlagBits bits target
  longFlagRankSuperOverhead := longFlagRankSuperOverhead bits target
  longFlagRankBlockOverhead := longFlagRankBlockOverhead bits target
  longFlagRankData := longFlagRankData bits target
  longFlagRank_wordSize_le_machine := by
    have hprofile := longFlagRankData_profile bits target
    exact Nat.le_trans hprofile.2.1
      (longFlagRankWordSize_le_machine bits target)
  longFlagRank_superWidth_le_machine := by
    simpa [longFlagRankData] using
      longFlagRankWordSize_le_machine bits target
  longFlagRank_blockWidth_le_machine := by
    simpa [longFlagRankData, longFlagRankBlockWidth] using
      longFlagRankWordSize_le_machine bits target
  longSuperRelativeEntries := longSuperRelativeEntries bits target
  localEntries := localEntries bits target
  superFieldWidth := superFieldWidth bits
  longSuperRelativeWidth := longSuperRelativeWidth bits
  localFieldWidth := localFieldWidth bits
  superTable := superTable bits target
  longSuperRelativeTable := longSuperRelativeTable bits target
  localTable := localTable bits target
  sparseDirectory := sparseExceptionDirectory bits target
  bitWords :=
    SuccinctSpace.BoundedPayloadWordStore.ofChunks
      bits (wordBits_pos bits.length)
  super_read_words_length_le_machine := by
    exact
      (superTable bits target).readWordsLengthLeMachine
        (by simp [superFieldWidth, wordBits])
  long_read_words_length_le_machine := by
    intro i word hget
    rw [(longSuperRelativeTable bits target).read_word_length_of_some hget]
    simp [longSuperRelativeWidth]
  local_read_words_length_le_machine := by
    exact
      (localTable bits target).readWordsLengthLeMachine
        (by
          simpa [localFieldWidth] using
            sparseExceptionRelativeWidth_le_machine bits)
  payload_length_le_overhead := by
    have hsuper := superTable_payload_le_overhead bits target
    have hflags := longSuperFlagBits_length_le_overhead bits target
    have hrank := longFlagRankData_auxPayload_le_overhead bits target
    have hlong := longSuperRelativeTable_payload_le_overhead bits target
    have hlocal := localTable_payload_le_overhead bits target
    have hsparse :=
      (sparseExceptionDirectory bits target).payload_length_le_canonical
    let A := (superTable bits target).payload.length
    let B := (longSuperFlagBits bits target).length
    let C := (longFlagRankData bits target).auxPayload.length
    let D := (longSuperRelativeTable bits target).payload.length
    let E := (localTable bits target).payload.length
    let F := (sparseExceptionDirectory bits target).payload.length
    let OA :=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 bits.length
    let OB :=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 bits.length
    let OC :=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 bits.length + 16
    let OD := longSuperRelativeTableOverhead bits.length
    let OE :=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 640 bits.length
    let OF := canonicalSparseExceptionDirectoryOverhead bits.length
    have hsum :
        A + B + C + D + E + F <=
          OA + OB + OC + OD + OE + OF := by
      have hA : A <= OA := by simpa [A, OA] using hsuper
      have hB : B <= OB := by simpa [B, OB] using hflags
      have hC : C <= OC := by simpa [C, OC] using hrank
      have hD : D <= OD := by simpa [D, OD] using hlong
      have hE : E <= OE := by simpa [E, OE] using hlocal
      have hF : F <= OF := by simpa [F, OF] using hsparse
      omega
    simpa [A, B, C, D, E, F, OA, OB, OC, OD, OE, OF,
      canonicalSparseExceptionSelectOverhead, List.length_append,
      Nat.add_assoc] using hsum
  super_missing_exact := superEntries_missing_exact bits target
  long_explicit_exact := longExplicit_exact bits target
  local_missing_exact := localEntries_missing_exact bits target
  sparse_compact_exact := sparseCompact_exact bits target
  dense_exact := dense_exact bits target

theorem sparseExceptionSelectData_profile
    (bits : List Bool) (target : Bool) :
    let data := sparseExceptionSelectData bits target
    data.payload.length <=
        canonicalSparseExceptionSelectOverhead bits.length /\
      SuccinctSpace.LittleOLinear canonicalSparseExceptionSelectOverhead /\
      (forall idx,
        (data.selectCosted idx).cost <= sparseDenseSelectQueryCost) /\
      (forall idx,
        (data.selectCosted idx).erase =
          RMQ.Succinct.select target bits idx) /\
      forall {word : List Bool},
        List.Mem word data.readWords ->
          word.length <=
            SuccinctRank.machineWordBits bits.length := by
  intro data
  exact data.profile

def sparseExceptionSelectSource (bits : List Bool) (target : Bool) :
    ChargedSelectPositionSource target bits
      canonicalSparseExceptionSelectOverhead
      sparseDenseSelectQueryCost :=
  (sparseExceptionSelectData bits target).toChargedSelectPositionSource

theorem sparseExceptionSelectSource_profile
    (bits : List Bool) (target : Bool) :
    let source := sparseExceptionSelectSource bits target
    source.payload.length <=
        canonicalSparseExceptionSelectOverhead source.domainSize /\
      SuccinctSpace.LittleOLinear canonicalSparseExceptionSelectOverhead /\
      (forall idx,
        (source.selectPositionCosted idx).cost <=
          sparseDenseSelectQueryCost) /\
      (forall idx,
        (source.selectPositionCosted idx).erase =
          RMQ.Succinct.select target bits idx) /\
      forall {word : List Bool},
        List.Mem word source.readWords ->
          word.length <=
            SuccinctRank.machineWordBits bits.length := by
  intro source
  exact
    ⟨source.payload_length_le, source.overhead_littleO,
      source.selectPositionCosted_cost_le,
      source.selectPositionCosted_exact,
      fun {word} hmem => source.read_word_length_le_machine hmem⟩

end RMQ.GenericSelect
