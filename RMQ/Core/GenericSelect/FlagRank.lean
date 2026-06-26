import RMQ.Core.GenericSelect.Entries

/-!
# Generic select flag-rank table layer

This module contains the generic Jacobson-style flag-rank directory used to
route sparse exception slots in the sparse-exception select directory.
-/

namespace RMQ.GenericSelect

open SuccinctSpace SuccinctRank
/-! ### Jacobson flag-rank directory (generic over the flag-bit list)

The sparse-exception construction needs the same two-level payload-live rank
directory over several classification flag vectors.  This module factors that
shared `flagRank*` family over an arbitrary flag-bit list. -/

/-- Payload-word size of a flag-rank directory: `machineWordBits` of the flag
vector's length. -/
def flagRankWordSize (flagBits : List Bool) : Nat :=
  SuccinctRank.machineWordBits flagBits.length

def flagRankBlocksPerSuper (flagBits : List Bool) : Nat :=
  flagRankWordSize flagBits

def flagRankBlockWidth (flagBits : List Bool) : Nat :=
  SuccinctRank.machineWordBits
    (flagRankBlocksPerSuper flagBits * flagRankWordSize flagBits)

theorem flagRankWordSize_pos (flagBits : List Bool) :
    0 < flagRankWordSize flagBits := by
  simp [flagRankWordSize, SuccinctRank.machineWordBits_pos]

theorem flagRankBlocksPerSuper_pos (flagBits : List Bool) :
    0 < flagRankBlocksPerSuper flagBits := by
  simpa [flagRankBlocksPerSuper] using flagRankWordSize_pos flagBits

theorem flagBits_length_lt_rank_word_pow (flagBits : List Bool) :
    flagBits.length < 2 ^ flagRankWordSize flagBits := by
  simpa [flagRankWordSize, SuccinctRank.machineWordBits] using
    (Nat.lt_log2_self (n := flagBits.length))

theorem flagRankBlockSpan_lt_pow (flagBits : List Bool) :
    flagRankBlocksPerSuper flagBits * flagRankWordSize flagBits <
      2 ^ flagRankBlockWidth flagBits := by
  simpa [flagRankBlockWidth, SuccinctRank.machineWordBits] using
    (Nat.lt_log2_self
      (n := flagRankBlocksPerSuper flagBits * flagRankWordSize flagBits))

def flagRankSuperOverhead (flagBits : List Bool) : Nat :=
  (SuccinctRank.canonicalSuperRankSampleTables
    flagBits (flagRankWordSize flagBits) (flagRankBlocksPerSuper flagBits)
    (flagRankWordSize flagBits)
    (flagBits_length_lt_rank_word_pow flagBits)).payload.length

def flagRankBlockOverhead (flagBits : List Bool) : Nat :=
  (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan
    flagBits (flagRankWordSize flagBits) (flagRankBlocksPerSuper flagBits)
    (flagRankBlockWidth flagBits)
    (flagRankBlocksPerSuper_pos flagBits)
    (flagRankBlockSpan_lt_pow flagBits)).payload.length

/-- The two-level payload-live rank directory over `flagBits`. -/
def flagRankData (flagBits : List Bool) :
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      flagBits (flagRankSuperOverhead flagBits)
      (flagRankBlockOverhead flagBits) 4 :=
  SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock
    flagBits
    (flagRankWordSize_pos flagBits)
    (by simp [flagRankWordSize])
    (flagRankBlocksPerSuper_pos flagBits)
    (flagBits_length_lt_rank_word_pow flagBits)
    (flagRankBlockSpan_lt_pow flagBits)
    (by omega)

theorem flagRankData_profile (flagBits : List Bool) :
    let data := flagRankData flagBits
    data.auxPayload.length =
        flagRankSuperOverhead flagBits + flagRankBlockOverhead flagBits /\
      data.wordSize <=
        SuccinctRank.machineWordBits flagBits.length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        flagBits /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <=
            SuccinctRank.machineWordBits flagBits.length) /\
      forall target pos,
        (data.rankCosted target pos).cost <= 4 /\
          (data.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target flagBits pos := by
  exact
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
      flagBits
      (flagRankWordSize_pos flagBits)
      (by simp [flagRankWordSize])
      (flagRankBlocksPerSuper_pos flagBits)
      (flagBits_length_lt_rank_word_pow flagBits)
      (flagRankBlockSpan_lt_pow flagBits)
      (by omega)

/-- Effective local slots are capped by the number of actual target
occurrences.  This is the generic version of the BP sparse-exception effective
flag prefix. -/
def sparseExceptionEffectiveLocalSlotCount
    (bits : List Bool) (target : Bool) : Nat :=
  Nat.min (localSlotCount bits target) (occurrenceCount bits target)

def sparseExceptionEffectiveFlagBits
    (bits : List Bool) (target : Bool) : List Bool :=
  (List.range (sparseExceptionEffectiveLocalSlotCount bits target)).map
    (localIsSparseException bits target)

theorem sparseExceptionEffectiveFlagBits_length
    (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagBits bits target).length =
      sparseExceptionEffectiveLocalSlotCount bits target := by
  simp [sparseExceptionEffectiveFlagBits]

theorem sparseExceptionEffectiveLocalSlotCount_le_full
    (bits : List Bool) (target : Bool) :
    sparseExceptionEffectiveLocalSlotCount bits target <=
      localSlotCount bits target := by
  unfold sparseExceptionEffectiveLocalSlotCount
  exact Nat.min_le_left _ _

theorem sparseExceptionEffectiveLocalSlotCount_le_count
    (bits : List Bool) (target : Bool) :
    sparseExceptionEffectiveLocalSlotCount bits target <=
      occurrenceCount bits target := by
  unfold sparseExceptionEffectiveLocalSlotCount
  exact Nat.min_le_right _ _

theorem sparseExceptionEffectiveFlagBits_length_le_length
    (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagBits bits target).length <= bits.length := by
  have hlen :
      (sparseExceptionEffectiveFlagBits bits target).length <=
        occurrenceCount bits target := by
    rw [sparseExceptionEffectiveFlagBits_length]
    exact sparseExceptionEffectiveLocalSlotCount_le_count bits target
  exact Nat.le_trans hlen
    (by
      simpa [occurrenceCount] using
        RMQ.Succinct.rankPrefix_le_length target bits bits.length)

theorem sparseExceptionEffectiveFlagBits_get?
    (bits : List Bool) (target : Bool) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot <
        sparseExceptionEffectiveLocalSlotCount bits target) :
    (sparseExceptionEffectiveFlagBits bits target)[globalLocalSlot]? =
      some (localIsSparseException bits target globalLocalSlot) := by
  simp [sparseExceptionEffectiveFlagBits, List.getElem?_map,
    List.getElem?_range hslot]

theorem sparseExceptionEffectiveFlagBits_prefix_eq
    (bits : List Bool) (target : Bool) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot <=
        sparseExceptionEffectiveLocalSlotCount bits target) :
    RMQ.Succinct.rankPrefix true
        (sparseExceptionEffectiveFlagBits bits target) globalLocalSlot =
      RMQ.Succinct.rankPrefix true
        (sparseExceptionFlagBits bits target) globalLocalSlot := by
  have htake :
      sparseExceptionEffectiveFlagBits bits target =
        (sparseExceptionFlagBits bits target).take
          (sparseExceptionEffectiveLocalSlotCount bits target) := by
    apply List.ext_getElem?
    intro i
    by_cases hi :
        i < sparseExceptionEffectiveLocalSlotCount bits target
    · have hfull : i < localSlotCount bits target := by
        exact Nat.lt_of_lt_of_le hi
          (sparseExceptionEffectiveLocalSlotCount_le_full bits target)
      simp [sparseExceptionEffectiveFlagBits, sparseExceptionFlagBits,
        List.getElem?_map, List.getElem?_range hfull, hi]
    · have heff :
          (sparseExceptionEffectiveFlagBits bits target)[i]? = none := by
        rw [List.getElem?_eq_none_iff]
        simp [sparseExceptionEffectiveFlagBits, Nat.le_of_not_gt hi]
      have htakeNone :
          ((sparseExceptionFlagBits bits target).take
            (sparseExceptionEffectiveLocalSlotCount bits target))[i]? =
            none := by
        rw [List.getElem?_eq_none_iff]
        simp [List.length_take, sparseExceptionFlagBits_length,
          sparseExceptionEffectiveLocalSlotCount_le_full bits target,
          Nat.le_of_not_gt hi]
      rw [heff, htakeNone]
  rw [htake]
  exact
    RMQ.Succinct.rankPrefix_take_eq_of_le
      true (sparseExceptionFlagBits bits target)
      (n := sparseExceptionEffectiveLocalSlotCount bits target)
      (limit := globalLocalSlot)
      (by
        rw [List.length_take]
        rw [sparseExceptionFlagBits_length]
        exact Nat.le_min.mpr
          ⟨hslot,
            Nat.le_trans hslot
              (sparseExceptionEffectiveLocalSlotCount_le_full bits target)⟩)

def sparseExceptionEffectiveFlagRankWordSize
    (bits : List Bool) (target : Bool) : Nat :=
  SuccinctRank.machineWordBits
    (sparseExceptionEffectiveFlagBits bits target).length

def sparseExceptionEffectiveFlagRankBlocksPerSuper
    (_bits : List Bool) (_target : Bool) : Nat := 1

def sparseExceptionEffectiveFlagRankBlockWidth
    (bits : List Bool) (target : Bool) : Nat :=
  sparseExceptionEffectiveFlagRankWordSize bits target

theorem sparseExceptionEffectiveFlagRankWordSize_pos
    (bits : List Bool) (target : Bool) :
    0 < sparseExceptionEffectiveFlagRankWordSize bits target := by
  simp [sparseExceptionEffectiveFlagRankWordSize,
    SuccinctRank.machineWordBits_pos]

theorem sparseExceptionEffectiveFlagRankWordSize_le_machine
    (bits : List Bool) (target : Bool) :
    sparseExceptionEffectiveFlagRankWordSize bits target <=
      SuccinctRank.machineWordBits bits.length := by
  unfold sparseExceptionEffectiveFlagRankWordSize
  exact SuccinctRank.machineWordBits_mono_le
    (sparseExceptionEffectiveFlagBits_length_le_length bits target)

theorem sparseExceptionEffectiveFlagRankBlocksPerSuper_pos
    (bits : List Bool) (target : Bool) :
    0 < sparseExceptionEffectiveFlagRankBlocksPerSuper bits target := by
  simp [sparseExceptionEffectiveFlagRankBlocksPerSuper]

theorem sparseExceptionEffectiveFlagBits_length_lt_rank_word_pow
    (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagBits bits target).length <
      2 ^ sparseExceptionEffectiveFlagRankWordSize bits target := by
  simpa [sparseExceptionEffectiveFlagRankWordSize,
    SuccinctRank.machineWordBits] using
    (Nat.lt_log2_self
      (n := (sparseExceptionEffectiveFlagBits bits target).length))

theorem sparseExceptionEffectiveFlagRankBlockSpan_lt_pow
    (bits : List Bool) (target : Bool) :
    sparseExceptionEffectiveFlagRankBlocksPerSuper bits target *
        sparseExceptionEffectiveFlagRankWordSize bits target <
      2 ^ sparseExceptionEffectiveFlagRankBlockWidth bits target := by
  have hword :
      sparseExceptionEffectiveFlagRankWordSize bits target <
        2 ^ sparseExceptionEffectiveFlagRankWordSize bits target := by
    have hsucc :=
      SuccinctSpace.nat_succ_le_two_pow
        (sparseExceptionEffectiveFlagRankWordSize bits target)
    omega
  simpa [sparseExceptionEffectiveFlagRankBlocksPerSuper,
    sparseExceptionEffectiveFlagRankBlockWidth] using hword

def sparseExceptionEffectiveFlagRankSuperOverhead
    (bits : List Bool) (target : Bool) : Nat :=
  (SuccinctRank.canonicalSuperRankSampleTables
    (sparseExceptionEffectiveFlagBits bits target)
    (sparseExceptionEffectiveFlagRankWordSize bits target)
    (sparseExceptionEffectiveFlagRankBlocksPerSuper bits target)
    (sparseExceptionEffectiveFlagRankWordSize bits target)
    (sparseExceptionEffectiveFlagBits_length_lt_rank_word_pow
      bits target)).payload.length

def sparseExceptionEffectiveFlagRankBlockOverhead
    (bits : List Bool) (target : Bool) : Nat :=
  (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan
    (sparseExceptionEffectiveFlagBits bits target)
    (sparseExceptionEffectiveFlagRankWordSize bits target)
    (sparseExceptionEffectiveFlagRankBlocksPerSuper bits target)
    (sparseExceptionEffectiveFlagRankBlockWidth bits target)
    (sparseExceptionEffectiveFlagRankBlocksPerSuper_pos bits target)
    (sparseExceptionEffectiveFlagRankBlockSpan_lt_pow bits target)).payload.length

def sparseExceptionEffectiveFlagRankData
    (bits : List Bool) (target : Bool) :
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      (sparseExceptionEffectiveFlagBits bits target)
      (sparseExceptionEffectiveFlagRankSuperOverhead bits target)
      (sparseExceptionEffectiveFlagRankBlockOverhead bits target)
      4 :=
  SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock
    (sparseExceptionEffectiveFlagBits bits target)
    (sparseExceptionEffectiveFlagRankWordSize_pos bits target)
    (by
      simp [sparseExceptionEffectiveFlagRankWordSize,
        SuccinctRank.machineWordBits])
    (sparseExceptionEffectiveFlagRankBlocksPerSuper_pos bits target)
    (sparseExceptionEffectiveFlagBits_length_lt_rank_word_pow bits target)
    (sparseExceptionEffectiveFlagRankBlockSpan_lt_pow bits target)
    (Nat.le_refl 4)

theorem sparseExceptionEffectiveFlagRankData_profile
    (bits : List Bool) (target : Bool) :
    let data := sparseExceptionEffectiveFlagRankData bits target
    data.auxPayload.length =
        sparseExceptionEffectiveFlagRankSuperOverhead bits target +
          sparseExceptionEffectiveFlagRankBlockOverhead bits target /\
      data.wordSize <= SuccinctRank.machineWordBits bits.length /\
      data.superWidth <= SuccinctRank.machineWordBits bits.length /\
      data.blockWidth <= SuccinctRank.machineWordBits bits.length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        sparseExceptionEffectiveFlagBits bits target /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <= SuccinctRank.machineWordBits bits.length) /\
      forall rankTarget pos,
        (data.rankCosted rankTarget pos).cost <= 4 /\
          (data.rankCosted rankTarget pos).erase =
            RMQ.Succinct.rankPrefix rankTarget
              (sparseExceptionEffectiveFlagBits bits target) pos := by
  have hprofile :=
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
      (sparseExceptionEffectiveFlagBits bits target)
      (sparseExceptionEffectiveFlagRankWordSize_pos bits target)
      (by
        simp [sparseExceptionEffectiveFlagRankWordSize,
          SuccinctRank.machineWordBits])
      (sparseExceptionEffectiveFlagRankBlocksPerSuper_pos bits target)
      (sparseExceptionEffectiveFlagBits_length_lt_rank_word_pow bits target)
      (sparseExceptionEffectiveFlagRankBlockSpan_lt_pow bits target)
      (Nat.le_refl 4)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hprofile.1
  · simpa [sparseExceptionEffectiveFlagRankData] using
      (sparseExceptionEffectiveFlagRankWordSize_le_machine bits target)
  · simpa [sparseExceptionEffectiveFlagRankData] using
      (sparseExceptionEffectiveFlagRankWordSize_le_machine bits target)
  · simpa [sparseExceptionEffectiveFlagRankData,
      sparseExceptionEffectiveFlagRankBlockWidth] using
      (sparseExceptionEffectiveFlagRankWordSize_le_machine bits target)
  · exact hprofile.2.2.1
  · intro word hmem
    exact Nat.le_trans (hprofile.2.2.2.1 hmem)
      (SuccinctRank.machineWordBits_mono_le
        (sparseExceptionEffectiveFlagBits_length_le_length bits target))
  · exact hprofile.2.2.2.2

theorem localStride_le_superStride (n : Nat) :
    localStride n <= superStride n := by
  let w := wordBits n
  have hw_pos : 0 < w := by
    simpa [w] using wordBits_pos n
  have hlocal_le_word : localStride n <= w := by
    unfold localStride
    exact Nat.max_le.2
      ⟨by simpa [w] using hw_pos,
        Nat.div_le_self w (ell n * ell n)⟩
  have hword_le_square : w <= w * w := by
    simpa using Nat.mul_le_mul_left w (by omega : 1 <= w)
  exact Nat.le_trans hlocal_le_word
    (by simpa [w, superStride] using hword_le_square)

theorem wordBits_le_two_mul_localStride_mul_ell_sq (n : Nat) :
    wordBits n <= 2 * localStride n * (ell n * ell n) := by
  let w := wordBits n
  let e := ell n
  let denom := e * e
  let q := w / denom
  let stride := localStride n
  have he_pos : 0 < e := by
    simpa [e] using ell_pos n
  have hdenom_pos : 0 < denom := Nat.mul_pos he_pos he_pos
  have hlt : w < q * denom + denom := by
    simpa [q, denom] using Nat.lt_div_mul_add hdenom_pos (a := w)
  have hsucc_le : q + 1 <= 2 * stride := by
    have hstride_def : stride = max 1 q := by
      simp [stride, q, denom, e, w, localStride, ell]
    by_cases hq : q = 0
    · have hstride_ge : 1 <= stride := by
        rw [hstride_def]
        exact Nat.le_max_left 1 q
      omega
    · have hq_pos : 0 < q := Nat.pos_of_ne_zero hq
      have hstride : stride = q := by
        rw [hstride_def]
        exact Nat.max_eq_right (by omega)
      rw [hstride]
      omega
  have hmul : (q + 1) * denom <= 2 * stride * denom := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_right denom hsucc_le
  have hle : w <= (q + 1) * denom := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.le_of_lt hlt
  exact Nat.le_trans hle
    (by
      simpa [w, e, denom, stride, q, Nat.mul_assoc,
        Nat.mul_left_comm, Nat.mul_comm] using hmul)

theorem localSlotCount_mul_localStride_le_const_length
    (bits : List Bool) (target : Bool) :
    localSlotCount bits target * localStride bits.length <=
      10 * bits.length := by
  let count := occurrenceCount bits target
  let superStrideV := superStride bits.length
  let localStrideV := localStride bits.length
  let superCount := superSlotCount bits target
  let slots := localSlotsPerSuper bits.length
  by_cases hcount : count = 0
  · have hsuperCount : superCount = 0 := by
      unfold superCount superSlotCount selectCeilDiv
      rw [show occurrenceCount bits target = 0 by simpa [count] using hcount]
      have hstride_pos : 0 < superStrideV := by
        simpa [superStrideV] using superStride_pos bits.length
      have hpred_lt : superStrideV - 1 < superStrideV :=
        Nat.pred_lt (Nat.ne_of_gt hstride_pos)
      simpa [superStrideV] using Nat.div_eq_of_lt hpred_lt
    simp [localSlotCount, superCount, hsuperCount]
  · have hcount_pos : 0 < count := Nat.pos_of_ne_zero hcount
    have hn_pos : 0 < bits.length := by
      have hcountLe : count <= bits.length := by
        simpa [count, occurrenceCount] using
          RMQ.Succinct.rankPrefix_le_length target bits bits.length
      omega
    have hcount_le_len : count <= bits.length := by
      simpa [count, occurrenceCount] using
        RMQ.Succinct.rankPrefix_le_length target bits bits.length
    have hsuperStride_le :
        superStrideV <= 4 * bits.length := by
      have hsq :=
        machineWordBits_sq_le_four_mul_self_of_pos
          (n := bits.length) hn_pos
      simpa [superStrideV, superStride, wordBits] using hsq
    have hsuperCountMul :
        superCount * superStrideV <= count + superStrideV := by
      simpa [superCount, count, superStrideV, superSlotCount] using
        selectCeilDiv_mul_le_add count superStrideV
    have hslotsMul :
        slots * localStrideV <= superStrideV + localStrideV := by
      simpa [slots, superStrideV, localStrideV, localSlotsPerSuper] using
        selectLocalSlotsPerSuper_mul_localStride_le_add
          superStrideV localStrideV
    have hlocal_le_super : localStrideV <= superStrideV := by
      simpa [localStrideV, superStrideV] using
        localStride_le_superStride bits.length
    have hslotsMul' : slots * localStrideV <= 2 * superStrideV := by
      omega
    have hlocalPayload :
        localSlotCount bits target * localStride bits.length <=
          2 * (superCount * superStrideV) := by
      have hmul := Nat.mul_le_mul_left superCount hslotsMul'
      simpa [localSlotCount, superCount, slots, localStrideV,
        superStrideV, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
    have hsuperBudget :
        2 * (superCount * superStrideV) <= 10 * bits.length := by
      have hscaled := Nat.mul_le_mul_left 2 hsuperCountMul
      have hbudget : 2 * (count + superStrideV) <=
          10 * bits.length := by
        omega
      exact Nat.le_trans
        (by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            hscaled)
        hbudget
    exact Nat.le_trans hlocalPayload hsuperBudget

theorem payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
    {n payload scale : Nat}
    (hmul :
      payload * wordBits n <=
        scale * n * (ell n * (ell n * ell n))) :
    payload <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead (2 * scale) n := by
  let w := wordBits n
  let e := ell n
  let e3 := e * (e * e)
  have hw_pos : 0 < w := by
    simpa [w] using wordBits_pos n
  by_cases hn : n = 0
  · have hzeroMul : payload * w = 0 := by
      have hle0 : payload * w <= 0 := by
        simpa [w, e, e3, hn, wordBits, ell] using hmul
      omega
    have hpayload : payload = 0 := by
      cases payload with
      | zero => rfl
      | succ payload =>
          have hpos : 0 < (payload + 1) * w :=
            Nat.mul_pos (by omega) hw_pos
          omega
    simp [SuccinctSpace.logLogCubedSampledDirectoryOverhead,
      hpayload, hn]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hwordLeN : w <= n := by
      simpa [w, wordBits] using machineWordBits_le_self_of_pos hnPos
    let q := n / w
    have hqPos : 0 < q := Nat.div_pos hwordLeN hw_pos
    have hnLt : n < q * w + w := by
      simpa [q] using Nat.lt_div_mul_add hw_pos (a := n)
    have hnLeQ : n <= 2 * q * w := by
      have hsucc : q + 1 <= 2 * q := by omega
      have hleSucc : n <= (q + 1) * w := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.le_of_lt hnLt
      have hmul := Nat.mul_le_mul_right w hsucc
      exact Nat.le_trans hleSucc
        (by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul)
    have hbudget :
        scale * n * e3 <= (2 * scale) * (q * e3) * w := by
      have hscaled := Nat.mul_le_mul_left scale hnLeQ
      have hell := Nat.mul_le_mul_right e3 hscaled
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hell
    have hpayloadWord :
        payload * w <= (2 * scale) * (q * e3) * w := by
      exact Nat.le_trans
        (by
          simpa [w, e, e3, Nat.mul_assoc, Nat.mul_left_comm,
            Nat.mul_comm] using hmul)
        hbudget
    have hpayloadWordLeft :
        w * payload <= w * ((2 * scale) * (q * e3)) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        hpayloadWord
    have hpayloadLe : payload <= (2 * scale) * (q * e3) :=
      Nat.le_of_mul_le_mul_left hpayloadWordLeft hw_pos
    have hpayloadLe' :
        payload <= scale * (q * (e * (e * (e * 2)))) := by
      simpa [e3, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        hpayloadLe
    simpa [SuccinctSpace.logLogCubedSampledDirectoryOverhead,
      w, e, q, wordBits, ell, SuccinctRank.machineWordBits,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hpayloadLe'

theorem sparseExceptionEffectiveFlagBits_length_mul_wordBits_le
    (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagBits bits target).length *
        wordBits bits.length <=
      20 * ((ell bits.length * (ell bits.length * ell bits.length)) *
        bits.length) := by
  let flagLen := (sparseExceptionEffectiveFlagBits bits target).length
  let m := localSlotCount bits target
  let w := wordBits bits.length
  let stride := localStride bits.length
  let e := ell bits.length
  let e2 := e * e
  let e3 := e * (e * e)
  let n := bits.length
  have heOne : 1 <= e := by
    simpa [e] using ell_pos bits.length
  have hflagLe : flagLen <= m := by
    simpa [flagLen, m, sparseExceptionEffectiveFlagBits_length] using
      sparseExceptionEffectiveLocalSlotCount_le_full bits target
  have hslots : m * stride <= 10 * n := by
    simpa [m, stride, n] using
      localSlotCount_mul_localStride_le_const_length bits target
  have hwordLower : w <= 2 * stride * e2 := by
    simpa [w, stride, e, e2, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using
      wordBits_le_two_mul_localStride_mul_ell_sq bits.length
  have hmul : flagLen * w <= 20 * (e3 * n) := by
    calc
      flagLen * w <= m * w := by
        exact Nat.mul_le_mul_right w hflagLe
      _ <= m * (2 * stride * e2) := by
        exact Nat.mul_le_mul_left m hwordLower
      _ = 2 * (m * stride) * e2 := by
        simp [Nat.mul_left_comm, Nat.mul_comm]
      _ <= 2 * (10 * n) * e2 := by
        have hscaled := Nat.mul_le_mul_left 2 hslots
        exact Nat.mul_le_mul_right e2 hscaled
      _ <= 20 * (e3 * n) := by
        have he2Le : e2 <= e3 := by
          have hmul := Nat.mul_le_mul_left e2 heOne
          simpa [e2, e3, Nat.mul_left_comm, Nat.mul_comm] using hmul
        have hright := Nat.mul_le_mul_left (20 * n) he2Le
        calc
          2 * (10 * n) * e2 = 20 * n * e2 := by
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ <= 20 * n * e3 := by
            simpa using hright
          _ = 20 * (e3 * n) := by
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  simpa [flagLen, w, e, e3, n, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm] using hmul

theorem sparseExceptionEffectiveFlagBits_length_le_overhead
    (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagBits bits target).length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 bits.length := by
  let flagLen := (sparseExceptionEffectiveFlagBits bits target).length
  let w := wordBits bits.length
  let e := ell bits.length
  let e3 := e * (e * e)
  let n := bits.length
  exact
    payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
      (n := bits.length) (payload := flagLen) (scale := 20)
      (by
        simpa [flagLen, w, e, e3, n, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using
          sparseExceptionEffectiveFlagBits_length_mul_wordBits_le bits target)

theorem sparseExceptionEffectiveFlagRankData_auxPayload_le_overhead
    (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagRankData bits target).auxPayload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 bits.length + 16 := by
  let flagBits := sparseExceptionEffectiveFlagBits bits target
  let flagLen := flagBits.length
  let rankWord := sparseExceptionEffectiveFlagRankWordSize bits target
  let w := wordBits bits.length
  let e := ell bits.length
  let e3 := e * (e * e)
  let n := bits.length
  let data := sparseExceptionEffectiveFlagRankData bits target
  have hrankWordPos : 0 < rankWord := by
    simpa [rankWord] using
      sparseExceptionEffectiveFlagRankWordSize_pos bits target
  have hrankWordLeW : rankWord <= w := by
    simpa [rankWord, w, wordBits] using
      sparseExceptionEffectiveFlagRankWordSize_le_machine bits target
  have hauxEq :
      data.auxPayload.length =
        sparseExceptionEffectiveFlagRankSuperOverhead bits target +
          sparseExceptionEffectiveFlagRankBlockOverhead bits target := by
    have hprofile := sparseExceptionEffectiveFlagRankData_profile bits target
    simpa [data] using hprofile.1
  have hsuperLe :
      sparseExceptionEffectiveFlagRankSuperOverhead bits target <=
        2 * (flagLen + rankWord) := by
    unfold sparseExceptionEffectiveFlagRankSuperOverhead
    rw [SuccinctRank.canonicalSuperRankSampleTables_payload_length]
    have hentryLen :
        (SuccinctRank.canonicalSuperRankEntries true flagBits
            rankWord
            (sparseExceptionEffectiveFlagRankBlocksPerSuper
              bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord,
        sparseExceptionEffectiveFlagRankBlocksPerSuper]
    have hentryLenFalse :
        (SuccinctRank.canonicalSuperRankEntries false flagBits
            rankWord
            (sparseExceptionEffectiveFlagRankBlocksPerSuper
              bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord,
        sparseExceptionEffectiveFlagRankBlocksPerSuper]
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
      sparseExceptionEffectiveFlagRankBlockOverhead bits target <=
        2 * (flagLen + rankWord) := by
    unfold sparseExceptionEffectiveFlagRankBlockOverhead
    rw [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length]
    have hentryLen :
        (SuccinctRank.canonicalBlockRankEntries true flagBits
            rankWord
            (sparseExceptionEffectiveFlagRankBlocksPerSuper
              bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRank.canonicalBlockRankEntries, flagBits,
        flagLen, rankWord]
    have hentryLenFalse :
        (SuccinctRank.canonicalBlockRankEntries false flagBits
            rankWord
            (sparseExceptionEffectiveFlagRankBlocksPerSuper
              bits target)).length =
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
      sparseExceptionEffectiveFlagRankSuperOverhead bits target +
          sparseExceptionEffectiveFlagRankBlockOverhead bits target <=
        2 * (flagLen + rankWord) + 2 * (flagLen + rankWord) :=
          Nat.add_le_add hsuperLe hblockLe
      _ = 4 * (flagLen + rankWord) := by omega
  by_cases hnZero : n = 0
  · have hflagZero : flagLen = 0 := by
      have hlen := sparseExceptionEffectiveFlagBits_length bits target
      have hcountZero :
          sparseExceptionEffectiveLocalSlotCount bits target = 0 := by
        have hoccZero : occurrenceCount bits target = 0 := by
          have hoccLe :
              occurrenceCount bits target <= bits.length := by
            simpa [occurrenceCount] using
              RMQ.Succinct.rankPrefix_le_length target bits bits.length
          omega
        unfold sparseExceptionEffectiveLocalSlotCount
        simp [hoccZero]
      simpa [flagBits, flagLen, hcountZero] using hlen
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
      flagLen * w <= 20 * (e3 * n) := by
    simpa [flagBits, flagLen, w, e, e3, n, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using
      sparseExceptionEffectiveFlagBits_length_mul_wordBits_le bits target
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
      data.auxPayload.length * w <= 96 * (e3 * n) := by
    calc
      data.auxPayload.length * w <=
          4 * (flagLen + rankWord) * w := by
            exact Nat.mul_le_mul_right w hauxLe
      _ = 4 * (flagLen * w + rankWord * w) := by
            simp [Nat.add_mul, Nat.mul_assoc]
      _ <= 4 * (20 * (e3 * n) + 4 * (e3 * n)) := by
            exact Nat.mul_le_mul_left 4
              (Nat.add_le_add hflagMul hrankMul)
      _ = 96 * (e3 * n) := by
            let t := e3 * n
            change 4 * (20 * t + 4 * t) = 96 * t
            omega
  exact
    Nat.le_trans
      (payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
        (n := bits.length) (payload := data.auxPayload.length) (scale := 96)
        (by
          simpa [w, e, e3, n, Nat.mul_assoc, Nat.mul_left_comm,
            Nat.mul_comm] using hauxMul))
      (Nat.le_add_right _ _)

end RMQ.GenericSelect
