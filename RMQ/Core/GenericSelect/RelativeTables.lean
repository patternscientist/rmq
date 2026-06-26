import RMQ.Core.GenericSelect.FlagRank

/-!
# Generic select relative and dense table layer

This module contains the relative-offset tables, fixed-width dense-local entry
tables, and payload-budget lemmas used by the generic sparse-exception select
directory.
-/

namespace RMQ.GenericSelect

open SuccinctSpace SuccinctRank
/-! ### Relative-offset tables for long supers and sparse locals -/

/-- Relative offsets stored explicitly for a single long super (empty for short
supers). -/
def longSuperRelativeEntriesForSlot (bits : List Bool) (target : Bool)
    (superSlot : Nat) : List Nat :=
  if superIsLong bits target superSlot then
    let baseOccurrence := superBaseOccurrence bits.length superSlot
    let basePosition := position bits target baseOccurrence
    relativeOffsetsOrZero target bits baseOccurrence (superStride bits.length)
      (superEndOccurrence bits target superSlot) basePosition
  else
    []

def longSuperRelativeEntries (bits : List Bool) (target : Bool) : List Nat :=
  (List.range (superSlotCount bits target)).flatMap
    (longSuperRelativeEntriesForSlot bits target)

/-- Each relative offset fits in a machine word over `bits.length`. -/
def longSuperRelativeWidth (bits : List Bool) : Nat :=
  SuccinctRank.machineWordBits bits.length

theorem longSuperRelativeEntriesForSlot_length
    (bits : List Bool) (target : Bool) (superSlot : Nat) :
    (longSuperRelativeEntriesForSlot bits target superSlot).length =
      if superIsLong bits target superSlot then superStride bits.length
      else 0 := by
  by_cases hlong : superIsLong bits target superSlot = true
  · simp [longSuperRelativeEntriesForSlot, hlong, relativeOffsetsOrZero_length]
  · have hfalse : superIsLong bits target superSlot = false := by
      cases h : superIsLong bits target superSlot
      · rfl
      · contradiction
    simp [longSuperRelativeEntriesForSlot, hfalse]

theorem longSuperRelativeFlatMap_length
    (bits : List Bool) (target : Bool) {n : Nat}
    (hn : n <= superSlotCount bits target) :
    ((List.range n).flatMap
        (longSuperRelativeEntriesForSlot bits target)).length =
      RMQ.Succinct.rankPrefix true (longSuperFlagBits bits target) n *
        superStride bits.length := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix]
  | succ n ih =>
      have hn' : n <= superSlotCount bits target := by omega
      have hslot : n < superSlotCount bits target := by omega
      have hget := longSuperFlagBits_get? bits target (superSlot := n) hslot
      have hrank :=
        rankPrefix_succ_eq_of_get? (target := true)
          (bits := longSuperFlagBits bits target) (n := n) hget
      have hprefix :
          (List.map
              (List.length ∘ longSuperRelativeEntriesForSlot bits target)
              (List.range n)).sum =
            RMQ.Succinct.rankPrefix true (longSuperFlagBits bits target) n *
              superStride bits.length := by
        simpa [List.length_flatMap, Function.comp] using ih hn'
      rw [List.range_succ, List.flatMap_append]
      simp [List.flatMap, longSuperRelativeEntriesForSlot_length, hrank]
      by_cases hlong : superIsLong bits target n = true
      · rw [hprefix]; simp [hlong, Nat.add_mul, Nat.add_comm]
      · have hfalse : superIsLong bits target n = false := by
          cases h : superIsLong bits target n
          · rfl
          · contradiction
        rw [hprefix]; simp [hfalse]

theorem longSuperRelativeEntries_length (bits : List Bool) (target : Bool) :
    (longSuperRelativeEntries bits target).length =
      RMQ.Succinct.rankPrefix true (longSuperFlagBits bits target)
          (superSlotCount bits target) *
        superStride bits.length := by
  simpa [longSuperRelativeEntries] using
    longSuperRelativeFlatMap_length bits target (Nat.le_refl _)

theorem longSuperRelativeEntries_decompose
    (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hslot : superSlot < superSlotCount bits target) :
    longSuperRelativeEntries bits target =
      ((List.range superSlot).flatMap
        (longSuperRelativeEntriesForSlot bits target)) ++
      longSuperRelativeEntriesForSlot bits target superSlot ++
      (((List.range
            (superSlotCount bits target - superSlot - 1)).map
          (fun offset => superSlot + Nat.succ offset)).flatMap
        (longSuperRelativeEntriesForSlot bits target)) := by
  unfold longSuperRelativeEntries
  let tailCount := superSlotCount bits target - superSlot - 1
  have hcount :
      superSlotCount bits target =
        superSlot + (1 + tailCount) := by
    simp [tailCount]
    omega
  calc
    (List.range (superSlotCount bits target)).flatMap
        (longSuperRelativeEntriesForSlot bits target) =
      (List.range (superSlot + (1 + tailCount))).flatMap
        (longSuperRelativeEntriesForSlot bits target) := by
        rw [hcount]
    _ =
      ((List.range superSlot ++
          (List.range (1 + tailCount)).map
            (fun offset => superSlot + offset)).flatMap
        (longSuperRelativeEntriesForSlot bits target)) := by
        rw [List.range_add]
    _ =
      ((List.range superSlot).flatMap
        (longSuperRelativeEntriesForSlot bits target)) ++
      ((List.range (1 + tailCount)).map
          (fun offset => superSlot + offset)).flatMap
        (longSuperRelativeEntriesForSlot bits target) := by
        simp [List.flatMap_append]
    _ =
      ((List.range superSlot).flatMap
        (longSuperRelativeEntriesForSlot bits target)) ++
      longSuperRelativeEntriesForSlot bits target superSlot ++
      (((List.range tailCount).map
          (fun offset => superSlot + Nat.succ offset)).flatMap
        (longSuperRelativeEntriesForSlot bits target)) := by
        have hsucc : 1 + tailCount = tailCount + 1 := by omega
        rw [hsucc, List.range_succ_eq_map]
        simp [List.map, List.flatMap, List.map_map]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro offset _hmem
        rfl

theorem longSuperRelativeEntries_lookup_exact
    (bits : List Bool) (target : Bool)
    {superSlot localOccurrence pos : Nat}
    (hslot : superSlot < superSlotCount bits target)
    (hlong : superIsLong bits target superSlot = true)
    (hocc : localOccurrence < superStride bits.length)
    (hend :
      superBaseOccurrence bits.length superSlot + localOccurrence <
        superEndOccurrence bits target superSlot)
    (hselect :
      RMQ.Succinct.select target bits
          (superBaseOccurrence bits.length superSlot + localOccurrence) =
        some pos) :
    (longSuperRelativeEntries bits target)[
        RMQ.Succinct.rankPrefix true
          (longSuperFlagBits bits target)
          superSlot *
            superStride bits.length +
          localOccurrence]? =
      some
        (pos -
          position bits target
            (superBaseOccurrence bits.length superSlot)) := by
  let pre :=
    (List.range superSlot).flatMap
      (longSuperRelativeEntriesForSlot bits target)
  let slotEntries :=
    longSuperRelativeEntriesForSlot bits target superSlot
  let post :=
    ((List.range
        (superSlotCount bits target - superSlot - 1)).map
      (fun offset => superSlot + Nat.succ offset)).flatMap
        (longSuperRelativeEntriesForSlot bits target)
  have hentries :
      longSuperRelativeEntries bits target =
        pre ++ slotEntries ++ post := by
    simpa [pre, slotEntries, post] using
      longSuperRelativeEntries_decompose bits target hslot
  have hpre :
      pre.length =
        RMQ.Succinct.rankPrefix true
          (longSuperFlagBits bits target)
          superSlot *
            superStride bits.length := by
    simpa [pre] using
      longSuperRelativeFlatMap_length bits target (Nat.le_of_lt hslot)
  have hslotEntries :
      slotEntries =
        relativeOffsetsOrZero target bits
          (superBaseOccurrence bits.length superSlot)
          (superStride bits.length)
          (superEndOccurrence bits target superSlot)
          (position bits target
            (superBaseOccurrence bits.length superSlot)) := by
    simp [slotEntries, longSuperRelativeEntriesForSlot, hlong]
  have hslotLen :
      localOccurrence < slotEntries.length := by
    rw [longSuperRelativeEntriesForSlot_length]
    simp [hlong]
    exact hocc
  have hidx :
      RMQ.Succinct.rankPrefix true
          (longSuperFlagBits bits target)
          superSlot *
            superStride bits.length +
          localOccurrence =
        pre.length + localOccurrence := by
    simp [hpre]
  rw [hentries, hidx]
  rw [List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  have hsub :
      pre.length + localOccurrence - pre.length =
        localOccurrence := by
    omega
  rw [hsub]
  rw [List.getElem?_append_left hslotLen]
  rw [hslotEntries]
  exact
    relativeOffsetsOrZero_lookup_exact
      (target := target)
      (bits := bits)
      (baseOccurrence := superBaseOccurrence bits.length superSlot)
      (count := superStride bits.length)
      (endOccurrence := superEndOccurrence bits target superSlot)
      (basePosition :=
        position bits target
          (superBaseOccurrence bits.length superSlot))
      (localOccurrence := localOccurrence)
      (pos := pos)
      hocc hend hselect

theorem longSuperRelativeEntries_mem_lt_width
    {bits : List Bool} {target : Bool} {entry : Nat}
    (hmem : List.Mem entry (longSuperRelativeEntries bits target)) :
    entry < 2 ^ longSuperRelativeWidth bits := by
  unfold longSuperRelativeEntries at hmem
  rcases List.mem_flatMap.mp hmem with ⟨superSlot, _hslotMem, hentryMem⟩
  by_cases hlong : superIsLong bits target superSlot = true
  · have hmemOffsets :
        List.Mem entry
          (relativeOffsetsOrZero target bits
            (superBaseOccurrence bits.length superSlot)
            (superStride bits.length)
            (superEndOccurrence bits target superSlot)
            (position bits target
              (superBaseOccurrence bits.length superSlot))) := by
      simpa [longSuperRelativeEntriesForSlot, hlong] using hentryMem
    rcases relativeOffsetsOrZero_mem_cases hmemOffsets with hzero | hsome
    · subst entry
      exact Nat.pow_pos (by omega : 0 < 2)
    · rcases hsome with ⟨offset, pos, _hoff, _hend, hselect, hentry⟩
      have hposLen : pos < bits.length := RMQ.Succinct.select_bounds hselect
      have hentryLen : entry < bits.length := by rw [hentry]; omega
      exact Nat.lt_trans hentryLen
        (by
          simpa [longSuperRelativeWidth, SuccinctRank.machineWordBits]
            using (Nat.lt_log2_self (n := bits.length)))
  · have hfalse : superIsLong bits target superSlot = false := by
      cases h : superIsLong bits target superSlot
      · rfl
      · contradiction
    simp [longSuperRelativeEntriesForSlot, hfalse] at hentryMem

def longSuperRelativeTable (bits : List Bool) (target : Bool) :
    SuccinctSpace.FixedWidthNatTable
      (longSuperRelativeEntries bits target) (longSuperRelativeWidth bits) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (longSuperRelativeEntries bits target) (longSuperRelativeWidth bits)
    (by
      intro entry hmem
      exact longSuperRelativeEntries_mem_lt_width hmem)

theorem longSuperRelativeTable_payload_length
    (bits : List Bool) (target : Bool) :
    (longSuperRelativeTable bits target).payload.length =
      RMQ.Succinct.rankPrefix true (longSuperFlagBits bits target)
          (superSlotCount bits target) *
        superStride bits.length * longSuperRelativeWidth bits := by
  rw [(longSuperRelativeTable bits target).payload_length_eq]
  rw [longSuperRelativeEntries_length]

/-- The long-super relative table's payload, scaled by `ell`, is bounded by the
long-super span sum — the o(n) counting bridge. -/
theorem longSuperRelativeTable_payload_mul_ell_le_spanSum
    (bits : List Bool) (target : Bool) :
    (longSuperRelativeTable bits target).payload.length * ell bits.length <=
      longSuperSpanSum bits target (superSlotCount bits target) := by
  have hcount :=
    longSuperExceptionCount_mul_superLongSpan_le_spanSum bits target
      (Nat.le_refl _)
  rw [longSuperRelativeTable_payload_length]
  simpa [longSuperRelativeWidth, superLongSpan, wordBits,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcount

/-- Relative positions stored explicitly for a single sparse local block. -/
def sparseRelativeEntriesForSlot (bits : List Bool) (target : Bool)
    (globalLocalSlot : Nat) : List Nat :=
  if localIsSparse bits target globalLocalSlot then
    let baseOccurrence := localBaseOccurrence bits.length globalLocalSlot
    let basePosition := position bits target baseOccurrence
    (selectPositions target bits baseOccurrence (localStride bits.length)).map
      (fun pos => pos - basePosition)
  else
    []

def sparseRelativeEntries (bits : List Bool) (target : Bool) : List Nat :=
  (List.range (localSlotCount bits target)).flatMap
    (sparseRelativeEntriesForSlot bits target)

theorem sparseRelativeEntriesForSlot_length
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat) :
    (sparseRelativeEntriesForSlot bits target globalLocalSlot).length =
      if localIsSparse bits target globalLocalSlot then localStride bits.length
      else 0 := by
  by_cases hsparse : localIsSparse bits target globalLocalSlot = true
  · simp [sparseRelativeEntriesForSlot, hsparse, selectPositions_length]
  · have hfalse : localIsSparse bits target globalLocalSlot = false := by
      cases h : localIsSparse bits target globalLocalSlot
      · rfl
      · contradiction
    simp [sparseRelativeEntriesForSlot, hfalse]

theorem sparseRelativeEntries_mem_lt_word_pow
    {bits : List Bool} {target : Bool} {entry : Nat}
    (hmem : List.Mem entry (sparseRelativeEntries bits target)) :
    entry < 2 ^ wordBits bits.length := by
  unfold sparseRelativeEntries at hmem
  rcases List.mem_flatMap.mp hmem with ⟨globalLocalSlot, _hslotMem, hentryMem⟩
  unfold sparseRelativeEntriesForSlot at hentryMem
  by_cases hsparse : localIsSparse bits target globalLocalSlot = true
  · simp [hsparse] at hentryMem
    rcases hentryMem with ⟨pos, hposMem, hentryEq⟩
    subst entry
    have hposLe : pos <= bits.length := selectPositions_mem_le_length hposMem
    have hlenLt : bits.length < 2 ^ wordBits bits.length := by
      simpa [wordBits, SuccinctRank.machineWordBits] using
        (Nat.lt_log2_self (n := bits.length))
    omega
  · simp [hsparse] at hentryMem

def sparseRelativeTable (bits : List Bool) (target : Bool) :
    SuccinctSpace.FixedWidthNatTable
      (sparseRelativeEntries bits target) (wordBits bits.length) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (sparseRelativeEntries bits target) (wordBits bits.length)
    (by
      intro entry hmem
      exact sparseRelativeEntries_mem_lt_word_pow hmem)

theorem sparseRelativeTable_payload_length (bits : List Bool) (target : Bool) :
    (sparseRelativeTable bits target).payload.length =
      (sparseRelativeEntries bits target).length * wordBits bits.length :=
  (sparseRelativeTable bits target).payload_length_eq

/-! ### Field widths and fixed-width dense-local entry tables -/

theorem occurrenceCount_le_length (bits : List Bool) (target : Bool) :
    occurrenceCount bits target <= bits.length :=
  RMQ.Succinct.rankPrefix_le_length target bits bits.length

theorem occurrence_lt_count_of_select
    {bits : List Bool} {target : Bool} {occurrence pos : Nat}
    (hselect : RMQ.Succinct.select target bits occurrence = some pos) :
    occurrence < occurrenceCount bits target := by
  have hsucc := rankPrefix_succ_of_select hselect
  have hpos : pos < bits.length := RMQ.Succinct.select_bounds hselect
  have hmono :
      RMQ.Succinct.rankPrefix target bits (pos + 1) <=
        RMQ.Succinct.rankPrefix target bits bits.length :=
    RMQ.Succinct.rankPrefix_mono_limit target bits (Nat.succ_le_of_lt hpos)
  rw [hsucc] at hmono
  have hcount : occurrence + 1 <= occurrenceCount bits target := hmono
  omega

theorem superIsLong_false_span_le
    (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hshort : superIsLong bits target superSlot = false) :
    superSpan bits target superSlot <= superLongSpan bits.length := by
  unfold superIsLong at hshort
  simp at hshort
  omega

/-- In a short (dense) super, any selected position lies within `superLongSpan`
of a local base — the key fact bounding the relative local word-index field. -/
theorem selected_offset_lt_superLongSpan
    (bits : List Bool) (target : Bool) (superSlot : Nat)
    {localBaseOcc q pos : Nat}
    (hshort : superIsLong bits target superSlot = false)
    (hsuperBase : superBaseOccurrence bits.length superSlot <= localBaseOcc)
    (hlocalBase : localBaseOcc <= q)
    (hqEnd : q < superEndOccurrence bits target superSlot)
    (hselect : RMQ.Succinct.select target bits q = some pos) :
    pos - position bits target localBaseOcc < superLongSpan bits.length := by
  let superBase := superBaseOccurrence bits.length superSlot
  let superEnd := superEndOccurrence bits target superSlot
  have hqCount : q < occurrenceCount bits target :=
    occurrence_lt_count_of_select hselect
  have hlocalCount : localBaseOcc < occurrenceCount bits target := by omega
  have hsuperCount : superBase < occurrenceCount bits target := by omega
  rcases select_exists_of_lt_occurrenceCount bits target hlocalCount with
    ⟨localBasePos, hlocalSelect⟩
  rcases select_exists_of_lt_occurrenceCount bits target hsuperCount with
    ⟨superBasePos, hsuperSelect⟩
  have hsuperEndLeCount : superEnd <= occurrenceCount bits target :=
    Nat.min_le_right _ _
  have hsuperEndPos : 0 < superEnd := by omega
  have hlastCount : superEnd - 1 < occurrenceCount bits target := by omega
  rcases select_exists_of_lt_occurrenceCount bits target hlastCount with
    ⟨lastPos, hlastSelect⟩
  have hsuperBasePos_le_localBasePos : superBasePos <= localBasePos :=
    select_index_mono (target := target) (bits := bits)
      (lo := superBase) (hi := localBaseOcc)
      (by simpa [superBase] using hsuperBase) hsuperSelect hlocalSelect
  have hlocalBasePos_le_pos : localBasePos <= pos :=
    select_index_mono (target := target) (bits := bits)
      (lo := localBaseOcc) (hi := q) hlocalBase hlocalSelect hselect
  have hqLeLast : q <= superEnd - 1 := by omega
  have hpos_le_last : pos <= lastPos :=
    select_index_mono (target := target) (bits := bits)
      (lo := q) (hi := superEnd - 1) hqLeLast hselect hlastSelect
  have hspanLe := superIsLong_false_span_le bits target hshort
  have hsuperSelectRaw :
      RMQ.Succinct.select target bits
          (superSlot * superStride bits.length) = some superBasePos := by
    simpa [superBase, superBaseOccurrence] using hsuperSelect
  have hlastSelectRaw :
      RMQ.Succinct.select target bits
          ((superSlot * superStride bits.length + superStride bits.length).min
              (occurrenceCount bits target) - 1) = some lastPos := by
    simpa [superEnd, superEndOccurrence, superBaseOccurrence] using hlastSelect
  have hspanEq :
      superSpan bits target superSlot = lastPos + 1 - superBasePos := by
    simp [superSpan, superBaseOccurrence, superEndOccurrence, position,
      hsuperSelectRaw, hlastSelectRaw]
  rw [hspanEq] at hspanLe
  have hlocalPosEq : position bits target localBaseOcc = localBasePos :=
    position_eq_of_select bits target hlocalSelect
  rw [hlocalPosEq]
  have hoffLt : pos - localBasePos < lastPos + 1 - superBasePos := by omega
  omega

/-- Super-entry field width: a full machine word over `bits.length`. -/
def superFieldWidth (bits : List Bool) : Nat := wordBits bits.length

theorem superEntries_mem_fields_lt_width
    {bits : List Bool} {target : Bool}
    {entry : SparseDenseSelectDenseLocalEntry}
    (hmem : List.Mem entry (superEntries bits target)) :
    entry.baseOccurrence < 2 ^ superFieldWidth bits /\
      entry.baseWordIndex < 2 ^ superFieldWidth bits /\
        entry.rankBefore < 2 ^ superFieldWidth bits /\
          entry.firstOffset < 2 ^ superFieldWidth bits := by
  rcases List.mem_map.mp hmem with ⟨superSlot, hslotMem, rfl⟩
  have hslot : superSlot < superSlotCount bits target :=
    List.mem_range.mp hslotMem
  let wordSize := wordBits bits.length
  let baseOccurrence := superBaseOccurrence bits.length superSlot
  let basePosition := position bits target baseOccurrence
  have hwordPos : 0 < wordSize := by
    simpa [wordSize] using wordBits_pos bits.length
  have hbaseCount : baseOccurrence < occurrenceCount bits target := by
    simpa [baseOccurrence] using superBaseOccurrence_lt_count bits target hslot
  have hbaseLen : baseOccurrence < bits.length :=
    Nat.lt_of_lt_of_le hbaseCount (occurrenceCount_le_length bits target)
  have hlenPow : bits.length < 2 ^ wordSize := by
    simpa [wordSize, wordBits, SuccinctRank.machineWordBits] using
      (Nat.lt_log2_self (n := bits.length))
  have hbasePow : baseOccurrence < 2 ^ wordSize := Nat.lt_trans hbaseLen hlenPow
  have hpositionLen : basePosition <= bits.length := by
    simpa [basePosition] using position_le_length bits target baseOccurrence
  have hwordIndexPow : basePosition / wordSize < 2 ^ wordSize := by
    have hdivLe : basePosition / wordSize <= basePosition := Nat.div_le_self _ _
    exact Nat.lt_of_le_of_lt (Nat.le_trans hdivLe hpositionLen) hlenPow
  have hmarkPow :
      (if superIsLong bits target superSlot then 1 else 0) < 2 ^ wordSize := by
    by_cases hlong : superIsLong bits target superSlot = true
    · simp [hlong, one_lt_two_pow_of_pos hwordPos]
    · have hfalse : superIsLong bits target superSlot = false := by
        cases h : superIsLong bits target superSlot
        · rfl
        · contradiction
      simp [hfalse, Nat.pow_pos (by omega : 0 < 2)]
  have hoffsetLtWord :
      basePosition - basePosition / wordSize * wordSize < wordSize := by
    simpa [Nat.mod_eq_sub_div_mul] using Nat.mod_lt basePosition hwordPos
  have hoffsetPow :
      basePosition - basePosition / wordSize * wordSize < 2 ^ wordSize :=
    Nat.lt_trans hoffsetLtWord
      (by
        have hsucc := SuccinctSpace.nat_succ_le_two_pow wordSize
        omega)
  simpa [superEntry, superFieldWidth, wordSize, baseOccurrence, basePosition]
    using ⟨hbasePow, hwordIndexPow, hmarkPow, hoffsetPow⟩

def superTable (bits : List Bool) (target : Bool) :
    FixedWidthSparseDenseSelectDenseLocalEntryTable
      (superEntries bits target) (superFieldWidth bits) :=
  FixedWidthSparseDenseSelectDenseLocalEntryTable.ofEntries
    (superEntries bits target) (superFieldWidth bits)
    (by
      intro entry hmem
      exact superEntries_mem_fields_lt_width hmem)

/-- Local-entry field width: a machine word over `min bits.length superLongSpan`
(local entries store values relative to their owning super, so a short-super
word suffices). -/
def sparseExceptionRelativeWidth (bits : List Bool) : Nat :=
  SuccinctRank.machineWordBits
    (Nat.min bits.length (superLongSpan bits.length))

def localFieldWidth (bits : List Bool) : Nat := sparseExceptionRelativeWidth bits

theorem sparseExceptionRelativeWidth_le_four_ell (bits : List Bool) :
    sparseExceptionRelativeWidth bits <= 4 * ell bits.length := by
  let w := wordBits bits.length
  let e := ell bits.length
  let m := Nat.min bits.length (superLongSpan bits.length)
  by_cases hm : m = 0
  · have hell_pos : 0 < e := by
      simpa [e] using ell_pos bits.length
    simp [sparseExceptionRelativeWidth, SuccinctRank.machineWordBits,
      m, hm, ell]
    omega
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hw_pos : 0 < w := by
      simpa [w] using wordBits_pos bits.length
    have he_pos : 0 < e := by
      simpa [e] using ell_pos bits.length
    have hw_lt_pow : w < 2 ^ e := by
      simpa [w, e, ell, wordBits, SuccinctRank.machineWordBits] using
        (Nat.lt_log2_self (n := w))
    have hw_le_pow : w <= 2 ^ e := Nat.le_of_lt hw_lt_pow
    have he_le_pow : e <= 2 ^ e := SuccinctSpace.nat_le_two_pow e
    have hww_le : w * w <= 2 ^ e * 2 ^ e :=
      Nat.mul_le_mul hw_le_pow hw_le_pow
    have hww_pos : 0 < w * w := Nat.mul_pos hw_pos hw_pos
    have hwww_lt_step : (w * w) * w < (w * w) * 2 ^ e :=
      Nat.mul_lt_mul_of_pos_left hw_lt_pow hww_pos
    have hwww_le_step :
        (w * w) * 2 ^ e <= (2 ^ e * 2 ^ e) * 2 ^ e :=
      Nat.mul_le_mul_right (2 ^ e) hww_le
    have hwww_lt : w * w * w < 2 ^ e * 2 ^ e * 2 ^ e := by
      exact Nat.lt_of_lt_of_le
        (by simpa [Nat.mul_assoc] using hwww_lt_step)
        (by simpa [Nat.mul_assoc] using hwww_le_step)
    have hleft_lt :
        (w * w * w) * e < (2 ^ e * 2 ^ e * 2 ^ e) * e :=
      Nat.mul_lt_mul_of_pos_right hwww_lt he_pos
    have hright_le :
        (2 ^ e * 2 ^ e * 2 ^ e) * e <=
          (2 ^ e * 2 ^ e * 2 ^ e) * 2 ^ e :=
      Nat.mul_le_mul_left (2 ^ e * 2 ^ e * 2 ^ e) he_le_pow
    have hpows : (2 ^ e * 2 ^ e * 2 ^ e) * 2 ^ e = 2 ^ (4 * e) := by
      calc
        (2 ^ e * 2 ^ e * 2 ^ e) * 2 ^ e =
            (((2 ^ e * 2 ^ e) * 2 ^ e) * 2 ^ e) := by
              simp [Nat.mul_assoc]
        _ = ((2 ^ (e + e) * 2 ^ e) * 2 ^ e) := by
              rw [← Nat.pow_add]
        _ = (2 ^ (e + e + e) * 2 ^ e) := by
              rw [← Nat.pow_add]
        _ = 2 ^ (e + e + e + e) := by
              rw [← Nat.pow_add]
        _ = 2 ^ (4 * e) := by
              congr 1
              omega
    have hsuper_lt : superLongSpan bits.length < 2 ^ (4 * e) := by
      have hraw : (w * w * w) * e < 2 ^ (4 * e) := by
        have h := Nat.lt_of_lt_of_le hleft_lt hright_le
        rwa [hpows] at h
      simpa [superLongSpan, superStride, w, e, Nat.mul_assoc,
        Nat.mul_left_comm, Nat.mul_comm] using hraw
    have hm_lt : m < 2 ^ (4 * e) :=
      Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hsuper_lt
    have hlog := natLog2_succ_le_of_pos_lt_pow hmpos hm_lt
    simpa [sparseExceptionRelativeWidth,
      SuccinctRank.machineWordBits, m, e] using hlog

theorem ell_square_le_sixtyFour_wordBits (n : Nat) :
    ell n * ell n <= 64 * wordBits n := by
  let w := wordBits n
  let q := Nat.log2 w
  have hw_pos : 0 < w := by
    simpa [w] using wordBits_pos n
  by_cases hlarge : 6 <= q
  · have hw_ne : w ≠ 0 := by omega
    have hsq : (q + 1) * (q + 1) <= w :=
      Nat.le_trans
        (nat_succ_square_le_two_pow_of_six_le q hlarge)
        (Nat.log2_self_le hw_ne)
    have hw_le : w <= 64 * w := by omega
    exact Nat.le_trans
      (by simpa [q, w, ell] using hsq)
      hw_le
  · have hq_le : q <= 5 := by omega
    have hell_le : ell n <= 6 := by
      simpa [ell, q, w] using Nat.succ_le_succ hq_le
    have hell_square_le : ell n * ell n <= 6 * 6 :=
      Nat.mul_le_mul hell_le hell_le
    have hconst : 6 * 6 <= 64 * w := by omega
    exact Nat.le_trans hell_square_le hconst

theorem sparseException_localStride_mul_width_mul_ell_le_const_wordBits
    (bits : List Bool) :
    localStride bits.length * sparseExceptionRelativeWidth bits *
        ell bits.length <=
      512 * wordBits bits.length := by
  let w := wordBits bits.length
  let e := ell bits.length
  let denom := e * e
  let q := w / denom
  let stride := localStride bits.length
  let width := sparseExceptionRelativeWidth bits
  have hstride : stride <= q + 1 := by
    have hmax : max 1 q <= q + 1 :=
      Nat.max_le.2 ⟨Nat.succ_pos q, Nat.le_succ q⟩
    simpa [stride, q, denom, w, e, localStride, ell] using hmax
  have hwidth : width <= 4 * e := by
    simpa [width, e] using sparseExceptionRelativeWidth_le_four_ell bits
  have hfirst :
      stride * width * e <= (q + 1) * (4 * e) * e := by
    have hmul := Nat.mul_le_mul hstride hwidth
    exact Nat.mul_le_mul_right e hmul
  have hqdenom : q * denom <= w := Nat.div_mul_le_self w denom
  have hqdenom_succ : (q + 1) * denom <= w + denom := by
    calc
      (q + 1) * denom = q * denom + denom := by
        rw [Nat.add_mul]
        simp
      _ <= w + denom := Nat.add_le_add_right hqdenom denom
  have hell_square : denom <= 64 * w := by
    simpa [denom, e, w] using ell_square_le_sixtyFour_wordBits bits.length
  have hqdenom_budget : 4 * ((q + 1) * denom) <= 512 * w := by
    have hsum : w + denom <= 65 * w := by omega
    have hsucc_le : (q + 1) * denom <= 65 * w :=
      Nat.le_trans hqdenom_succ hsum
    have hmul := Nat.mul_le_mul_left 4 hsucc_le
    omega
  have hright : (q + 1) * (4 * e) * e <= 512 * w := by
    have hrewrite :
        (q + 1) * (4 * e) * e = 4 * ((q + 1) * denom) := by
      simp [denom, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    simpa [hrewrite] using hqdenom_budget
  exact Nat.le_trans hfirst hright

theorem localEntries_mem_fields_lt_width
    {bits : List Bool} {target : Bool}
    {entry : SparseDenseSelectDenseLocalEntry}
    (hmem : List.Mem entry (localEntries bits target)) :
    entry.baseOccurrence < 2 ^ localFieldWidth bits /\
      entry.baseWordIndex < 2 ^ localFieldWidth bits /\
        entry.rankBefore < 2 ^ localFieldWidth bits /\
          entry.firstOffset < 2 ^ localFieldWidth bits := by
  rcases List.mem_map.mp hmem with ⟨globalLocalSlot, _hslotMem, rfl⟩
  let superSlot := localSuperSlot bits.length globalLocalSlot
  let superBase := superBaseOccurrence bits.length superSlot
  let base := localBaseOccurrence bits.length globalLocalSlot
  let superPos := position bits target superBase
  let basePos := position bits target base
  let wordSize := wordBits bits.length
  let longSpan := superLongSpan bits.length
  let relWidth := localFieldWidth bits
  have hwordPos : 0 < wordSize := by
    simpa [wordSize] using wordBits_pos bits.length
  have hellPos : 0 < ell bits.length := ell_pos bits.length
  have hrelPos : 0 < relWidth := by
    simp [relWidth, localFieldWidth, sparseExceptionRelativeWidth,
      SuccinctRank.machineWordBits_pos]
  have hpowPos : 0 < 2 ^ relWidth := Nat.pow_pos (by omega : 0 < 2)
  have hfield_of_lt_min :
      forall {x : Nat}, x < bits.length -> x < longSpan -> x < 2 ^ relWidth := by
    intro x hbp hlong
    have hmin : x < Nat.min bits.length (superLongSpan bits.length) :=
      Nat.lt_min.mpr ⟨hbp, by simpa [longSpan] using hlong⟩
    simpa [relWidth, localFieldWidth, sparseExceptionRelativeWidth] using
      lt_two_pow_machineWordBits_of_lt hmin
  by_cases hlive : compactLocalEntryIsLive bits target globalLocalSlot = true
  · have hliveFacts :
        superIsLong bits target superSlot = false /\
          base < occurrenceCount bits target := by
      unfold compactLocalEntryIsLive at hlive
      by_cases hlong : superIsLong bits target superSlot = true
      · simp [superSlot, hlong] at hlive
      · have hfalse : superIsLong bits target superSlot = false := by
          cases h : superIsLong bits target superSlot
          · rfl
          · contradiction
        simp [superSlot, hfalse] at hlive
        exact ⟨hfalse, hlive⟩
    rcases hliveFacts with ⟨hshort, hbaseCount⟩
    have hsuperBaseLeBase : superBase <= base := by
      simp [superBase, base, superSlot, superBaseOccurrence, localSuperSlot,
        localBaseOccurrence, localSlotInSuperOfGlobal]
    have hbaseBoundary :
        base < superBase + superStride bits.length := by
      simpa [base, superBase, superSlot, superBaseOccurrence, localSuperSlot]
        using localBaseOccurrence_lt_superBoundary bits.length globalLocalSlot
    have hbaseEnd : base < superEndOccurrence bits target superSlot := by
      unfold superEndOccurrence
      exact Nat.lt_min.mpr
        ⟨by simpa [superBase, superBaseOccurrence] using hbaseBoundary,
          hbaseCount⟩
    have hbaseBp : base < bits.length :=
      Nat.lt_of_lt_of_le hbaseCount (occurrenceCount_le_length bits target)
    have hdeltaBp : base - superBase < bits.length := by omega
    have hstrideLeLong : superStride bits.length <= longSpan := by
      have hwordOne : 1 <= wordSize := by omega
      have hellOne : 1 <= ell bits.length := by omega
      have h1 :
          superStride bits.length <= superStride bits.length * wordSize := by
        simpa using Nat.mul_le_mul_left (superStride bits.length) hwordOne
      have h2 :
          superStride bits.length * wordSize <=
            superStride bits.length * wordSize * ell bits.length := by
        simpa using
          Nat.mul_le_mul_left (superStride bits.length * wordSize) hellOne
      exact Nat.le_trans h1 (by
        simpa [longSpan, superLongSpan, superStride, wordSize,
          Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h2)
    have hdeltaLong : base - superBase < longSpan := by
      have hdeltaStride : base - superBase < superStride bits.length := by omega
      exact Nat.lt_of_lt_of_le hdeltaStride hstrideLeLong
    have hbaseField : base - superBase < 2 ^ relWidth :=
      hfield_of_lt_min hdeltaBp hdeltaLong
    have hsuperCount : superBase < occurrenceCount bits target := by omega
    have hbasePosLt : basePos < bits.length := by
      simpa [basePos] using position_lt_length_of_lt_count bits target hbaseCount
    have hsuperPosLt : superPos < bits.length := by
      simpa [superPos] using
        position_lt_length_of_lt_count bits target hsuperCount
    have hposMono : superPos <= basePos := by
      simpa [superPos, basePos] using position_mono bits target hsuperBaseLeBase
    have hindexDeltaLe :
        basePos / wordSize - superPos / wordSize <= basePos - superPos :=
      nat_div_sub_div_le_sub hwordPos hposMono
    have hindexBp :
        basePos / wordSize - superPos / wordSize < bits.length := by
      have hdivLe : basePos / wordSize <= basePos := Nat.div_le_self _ _
      omega
    rcases select_exists_of_lt_occurrenceCount bits target hbaseCount with
      ⟨baseWitness, hbaseSelect⟩
    have hbasePosEq : basePos = baseWitness := by
      simpa [basePos] using position_eq_of_select bits target hbaseSelect
    have hoffLongWitness : baseWitness - superPos < longSpan := by
      have hraw :=
        selected_offset_lt_superLongSpan bits target superSlot
          (localBaseOcc := superBase) (q := base) (pos := baseWitness)
          hshort (by simp [superBase]) hsuperBaseLeBase hbaseEnd hbaseSelect
      simpa [superPos, superBase, longSpan] using hraw
    have hoffLong : basePos - superPos < longSpan := by
      simpa [hbasePosEq] using hoffLongWitness
    have hindexLong :
        basePos / wordSize - superPos / wordSize < longSpan :=
      Nat.lt_of_le_of_lt hindexDeltaLe hoffLong
    have hindexField :
        basePos / wordSize - superPos / wordSize < 2 ^ relWidth :=
      hfield_of_lt_min hindexBp hindexLong
    have hmarkField :
        (if localIsSparseException bits target globalLocalSlot then 1 else 0) <
          2 ^ relWidth := by
      by_cases hflag : localIsSparseException bits target globalLocalSlot = true
      · have hone : 1 < 2 ^ relWidth := one_lt_two_pow_of_pos hrelPos
        simpa [hflag] using hone
      · have hfalse :
            localIsSparseException bits target globalLocalSlot = false := by
          cases h : localIsSparseException bits target globalLocalSlot
          · rfl
          · contradiction
        simp [hfalse, hpowPos]
    have hoffsetLtWord :
        basePos - basePos / wordSize * wordSize < wordSize := by
      simpa [Nat.mod_eq_sub_div_mul] using Nat.mod_lt basePos hwordPos
    have hbpLenPos : 0 < bits.length := by omega
    have hwordLeBp : wordSize <= bits.length := by
      simpa [wordSize, wordBits] using machineWordBits_le_self_of_pos hbpLenPos
    have hwordLeLong : wordSize <= longSpan := by
      have hwordOne : 1 <= wordSize := by omega
      have hellOne : 1 <= ell bits.length := by omega
      have hleStride :
          wordSize <= superStride bits.length * wordSize := by
        have hmul :=
          Nat.mul_le_mul_right wordSize
            (show 1 <= superStride bits.length from superStride_pos bits.length)
        simpa [Nat.mul_comm] using hmul
      have hleLong :
          superStride bits.length * wordSize <= longSpan := by
        have hmul :=
          Nat.mul_le_mul_left (superStride bits.length * wordSize) hellOne
        simpa [longSpan, superLongSpan, superStride, wordSize,
          Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      exact Nat.le_trans hleStride hleLong
    have hoffsetBp :
        basePos - basePos / wordSize * wordSize < bits.length :=
      Nat.lt_of_lt_of_le hoffsetLtWord hwordLeBp
    have hoffsetLong :
        basePos - basePos / wordSize * wordSize < longSpan :=
      Nat.lt_of_lt_of_le hoffsetLtWord hwordLeLong
    have hoffsetField :
        basePos - basePos / wordSize * wordSize < 2 ^ relWidth :=
      hfield_of_lt_min hoffsetBp hoffsetLong
    simpa [localEntry, hlive, localFieldWidth, relWidth, superSlot, superBase,
      base, superPos, basePos, wordSize] using
      ⟨hbaseField, hindexField, hmarkField, hoffsetField⟩
  · have hfalse : compactLocalEntryIsLive bits target globalLocalSlot = false := by
      cases h : compactLocalEntryIsLive bits target globalLocalSlot
      · rfl
      · exact False.elim (hlive h)
    have htuple :
        0 < 2 ^ relWidth /\ 0 < 2 ^ relWidth /\
          0 < 2 ^ relWidth /\ 0 < 2 ^ relWidth :=
      ⟨hpowPos, hpowPos, hpowPos, hpowPos⟩
    simpa [localEntry, hfalse, localFieldWidth, relWidth] using htuple

def localTable (bits : List Bool) (target : Bool) :
    FixedWidthSparseDenseSelectDenseLocalEntryTable
      (localEntries bits target) (localFieldWidth bits) :=
  FixedWidthSparseDenseSelectDenseLocalEntryTable.ofEntries
    (localEntries bits target) (localFieldWidth bits)
    (by
      intro entry hmem
      exact localEntries_mem_fields_lt_width hmem)

/-! ### Sparse-exception relative table (relative offsets within long supers) -/

/-- Relative positions stored explicitly for a single sparse-exception local
block (a sparse local inside a short super). -/
def sparseExceptionRelativeEntriesForSlot (bits : List Bool) (target : Bool)
    (globalLocalSlot : Nat) : List Nat :=
  if localIsSparseException bits target globalLocalSlot then
    let superSlot := localSuperSlot bits.length globalLocalSlot
    let baseOccurrence := localBaseOccurrence bits.length globalLocalSlot
    let basePosition := position bits target baseOccurrence
    relativeOffsetsOrZero target bits baseOccurrence (localStride bits.length)
      (superEndOccurrence bits target superSlot) basePosition
  else
    []

theorem sparseExceptionRelativeEntriesForSlot_length
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat) :
    (sparseExceptionRelativeEntriesForSlot bits target globalLocalSlot).length =
      if localIsSparseException bits target globalLocalSlot then
        localStride bits.length
      else
        0 := by
  by_cases hflag : localIsSparseException bits target globalLocalSlot = true
  · simp [sparseExceptionRelativeEntriesForSlot, hflag,
      relativeOffsetsOrZero_length]
  · have hfalse :
        localIsSparseException bits target globalLocalSlot = false := by
      cases h : localIsSparseException bits target globalLocalSlot
      · rfl
      · contradiction
    simp [sparseExceptionRelativeEntriesForSlot, hfalse]

def sparseExceptionRelativeEntries (bits : List Bool) (target : Bool) :
    List Nat :=
  (List.range (localSlotCount bits target)).flatMap
    (sparseExceptionRelativeEntriesForSlot bits target)

theorem sparseExceptionRelativePrefix_length
    (bits : List Bool) (target : Bool) {n : Nat}
    (hn : n <= localSlotCount bits target) :
    ((List.range n).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)).length =
      RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target) n *
        localStride bits.length := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix]
  | succ n ih =>
      have hn' : n <= localSlotCount bits target := by omega
      have hslot : n < localSlotCount bits target := by omega
      have hget :=
        sparseExceptionFlagBits_get? bits target (globalLocalSlot := n) hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true) (bits := sparseExceptionFlagBits bits target)
          (n := n) hget
      have hprefix :
          (List.map
              (List.length ∘
                sparseExceptionRelativeEntriesForSlot bits target)
              (List.range n)).sum =
            RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target) n *
              localStride bits.length := by
        simpa [List.length_flatMap, Function.comp] using ih hn'
      rw [List.range_succ]
      rw [List.flatMap_append]
      simp [List.flatMap, sparseExceptionRelativeEntriesForSlot_length, hrank]
      by_cases hflag : localIsSparseException bits target n = true
      · rw [hprefix]
        simp [hflag, Nat.add_mul, Nat.add_comm]
      · have hfalse : localIsSparseException bits target n = false := by
          cases h : localIsSparseException bits target n
          · rfl
          · contradiction
        rw [hprefix]
        simp [hfalse]

theorem sparseExceptionRelativeEntries_length
    (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeEntries bits target).length =
      RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target)
        (localSlotCount bits target) *
        localStride bits.length := by
  simpa [sparseExceptionRelativeEntries] using
    sparseExceptionRelativePrefix_length bits target (Nat.le_refl _)

theorem sparseExceptionRelativeEntries_decompose
    (bits : List Bool) (target : Bool) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < localSlotCount bits target) :
    sparseExceptionRelativeEntries bits target =
      ((List.range globalLocalSlot).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)) ++
      sparseExceptionRelativeEntriesForSlot bits target
        globalLocalSlot ++
      (((List.range
            (localSlotCount bits target - globalLocalSlot - 1)).map
          (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)) := by
  unfold sparseExceptionRelativeEntries
  let tailCount := localSlotCount bits target - globalLocalSlot - 1
  have hcount :
      localSlotCount bits target =
        globalLocalSlot + (1 + tailCount) := by
    simp [tailCount]
    omega
  calc
    (List.range (localSlotCount bits target)).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target) =
      (List.range (globalLocalSlot + (1 + tailCount))).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target) := by
        rw [hcount]
    _ =
      ((List.range globalLocalSlot ++
          (List.range (1 + tailCount)).map
            (fun offset => globalLocalSlot + offset)).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)) := by
        rw [List.range_add]
    _ =
      ((List.range globalLocalSlot).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)) ++
      ((List.range (1 + tailCount)).map
          (fun offset => globalLocalSlot + offset)).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target) := by
        simp [List.flatMap_append]
    _ =
      ((List.range globalLocalSlot).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)) ++
      sparseExceptionRelativeEntriesForSlot bits target
        globalLocalSlot ++
      (((List.range tailCount).map
          (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)) := by
        have hsucc : 1 + tailCount = tailCount + 1 := by omega
        rw [hsucc, List.range_succ_eq_map]
        simp [List.map, List.flatMap, List.map_map]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro offset _hmem
        rfl

theorem sparseExceptionRelativeEntries_lookup_exact
    (bits : List Bool) (target : Bool)
    {globalLocalSlot localOccurrence pos : Nat}
    (hslot :
      globalLocalSlot < localSlotCount bits target)
    (hflag :
      localIsSparseException bits target globalLocalSlot = true)
    (hocc :
      localOccurrence < localStride bits.length)
    (hend :
      localBaseOccurrence bits.length globalLocalSlot + localOccurrence <
        superEndOccurrence bits target
          (localSuperSlot bits.length globalLocalSlot))
    (hselect :
      RMQ.Succinct.select target bits
          (localBaseOccurrence bits.length globalLocalSlot + localOccurrence) =
        some pos) :
    (sparseExceptionRelativeEntries bits target)[
        RMQ.Succinct.rankPrefix true
          (sparseExceptionFlagBits bits target)
          globalLocalSlot *
            localStride bits.length +
          localOccurrence]? =
      some
        (pos -
          position bits target
            (localBaseOccurrence bits.length globalLocalSlot)) := by
  let pre :=
    (List.range globalLocalSlot).flatMap
      (sparseExceptionRelativeEntriesForSlot bits target)
  let slotEntries :=
    sparseExceptionRelativeEntriesForSlot bits target globalLocalSlot
  let post :=
    ((List.range
        (localSlotCount bits target - globalLocalSlot - 1)).map
      (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)
  have hentries :
      sparseExceptionRelativeEntries bits target =
        pre ++ slotEntries ++ post := by
    simpa [pre, slotEntries, post] using
      sparseExceptionRelativeEntries_decompose
        bits target hslot
  have hpre :
      pre.length =
        RMQ.Succinct.rankPrefix true
          (sparseExceptionFlagBits bits target)
          globalLocalSlot *
            localStride bits.length := by
    simpa [pre] using
      sparseExceptionRelativePrefix_length bits target (Nat.le_of_lt hslot)
  have hslotEntries :
      slotEntries =
        relativeOffsetsOrZero target bits
          (localBaseOccurrence bits.length globalLocalSlot)
          (localStride bits.length)
          (superEndOccurrence bits target
            (localSuperSlot bits.length globalLocalSlot))
          (position bits target
            (localBaseOccurrence bits.length globalLocalSlot)) := by
    simp [slotEntries,
      sparseExceptionRelativeEntriesForSlot, hflag]
  have hslotLen :
      localOccurrence < slotEntries.length := by
    rw [sparseExceptionRelativeEntriesForSlot_length]
    simp [hflag]
    exact hocc
  have hidx :
      RMQ.Succinct.rankPrefix true
          (sparseExceptionFlagBits bits target)
          globalLocalSlot *
            localStride bits.length +
          localOccurrence =
        pre.length + localOccurrence := by
    simp [hpre]
  rw [hentries, hidx]
  rw [List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  have hsub :
      pre.length + localOccurrence - pre.length =
        localOccurrence := by
    omega
  rw [hsub]
  rw [List.getElem?_append_left hslotLen]
  rw [hslotEntries]
  exact
    relativeOffsetsOrZero_lookup_exact
      (target := target)
      (bits := bits)
      (baseOccurrence :=
        localBaseOccurrence bits.length globalLocalSlot)
      (count := localStride bits.length)
      (endOccurrence :=
        superEndOccurrence bits target
          (localSuperSlot bits.length globalLocalSlot))
      (basePosition :=
        position bits target
          (localBaseOccurrence bits.length globalLocalSlot))
      (localOccurrence := localOccurrence)
      (pos := pos)
      hocc hend hselect

theorem sparseExceptionRelativeEntriesForSlot_mem_lt_width
    (bits : List Bool) (target : Bool) {globalLocalSlot entry : Nat}
    (hmem :
      List.Mem entry
        (sparseExceptionRelativeEntriesForSlot bits target globalLocalSlot)) :
    entry < 2 ^ sparseExceptionRelativeWidth bits := by
  by_cases hflag : localIsSparseException bits target globalLocalSlot = true
  · let superSlot := localSuperSlot bits.length globalLocalSlot
    let localBase := localBaseOccurrence bits.length globalLocalSlot
    let localBasePosition := position bits target localBase
    have hshort :=
      (localIsSparseException_true_short bits target globalLocalSlot hflag).1
    have hmemOffsets :
        List.Mem entry
          (relativeOffsetsOrZero target bits localBase (localStride bits.length)
            (superEndOccurrence bits target superSlot) localBasePosition) := by
      simpa [sparseExceptionRelativeEntriesForSlot, hflag, superSlot, localBase,
        localBasePosition] using hmem
    rcases relativeOffsetsOrZero_mem_cases hmemOffsets with hzero | hsome
    · subst entry
      exact Nat.pow_pos (by omega : 0 < 2)
    · rcases hsome with ⟨offset, pos, _hoff, hqEnd, hselect, hentry⟩
      have hsuperBase :
          superBaseOccurrence bits.length superSlot <= localBase := by
        simp [superSlot, localBase, superBaseOccurrence, localSuperSlot,
          localBaseOccurrence]
      have hoffSuper : pos - localBasePosition < superLongSpan bits.length := by
        simpa [localBase, localBasePosition, superSlot] using
          selected_offset_lt_superLongSpan bits target superSlot hshort
            hsuperBase (by omega) hqEnd hselect
      have hposLen : pos < bits.length := RMQ.Succinct.select_bounds hselect
      have hentryLen : entry < bits.length := by rw [hentry]; omega
      have hentrySuper : entry < superLongSpan bits.length := by
        rw [hentry]; exact hoffSuper
      have hentryMin :
          entry < Nat.min bits.length (superLongSpan bits.length) :=
        Nat.lt_min.mpr ⟨hentryLen, hentrySuper⟩
      exact Nat.lt_trans hentryMin
        (by
          simpa [sparseExceptionRelativeWidth,
            SuccinctRank.machineWordBits] using
            (Nat.lt_log2_self
              (n := Nat.min bits.length (superLongSpan bits.length))))
  · have hfalse : localIsSparseException bits target globalLocalSlot = false := by
      cases h : localIsSparseException bits target globalLocalSlot
      · rfl
      · contradiction
    simp [sparseExceptionRelativeEntriesForSlot, hfalse] at hmem
    cases hmem

theorem sparseExceptionRelativeEntries_mem_lt_width
    (bits : List Bool) (target : Bool) {entry : Nat}
    (hmem : List.Mem entry (sparseExceptionRelativeEntries bits target)) :
    entry < 2 ^ sparseExceptionRelativeWidth bits := by
  unfold sparseExceptionRelativeEntries at hmem
  rcases List.mem_flatMap.mp hmem with ⟨globalLocalSlot, _hslot, hentry⟩
  exact sparseExceptionRelativeEntriesForSlot_mem_lt_width bits target hentry

def sparseExceptionRelativeTable (bits : List Bool) (target : Bool) :
    SuccinctSpace.FixedWidthNatTable
      (sparseExceptionRelativeEntries bits target)
      (sparseExceptionRelativeWidth bits) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (sparseExceptionRelativeEntries bits target)
    (sparseExceptionRelativeWidth bits)
    (by
      intro entry hmem
      exact sparseExceptionRelativeEntries_mem_lt_width bits target hmem)

theorem sparseExceptionRelativeTable_payload_length
    (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeTable bits target).payload.length =
      (sparseExceptionRelativeEntries bits target).length *
        sparseExceptionRelativeWidth bits :=
  (sparseExceptionRelativeTable bits target).payload_length_eq

theorem sparseExceptionRelativeTable_payload_expanded_length
    (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeTable bits target).payload.length =
      RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target)
        (localSlotCount bits target) *
        localStride bits.length *
        sparseExceptionRelativeWidth bits := by
  rw [sparseExceptionRelativeTable_payload_length,
    sparseExceptionRelativeEntries_length]

theorem sparseExceptionRelativeTable_payload_mul_ell_le_const_spanSum
    (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeTable bits target).payload.length *
        ell bits.length <=
      512 * shortSuperLocalSpanSum bits target
        (localSlotCount bits target) := by
  let count :=
    RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target)
      (localSlotCount bits target)
  let stride := localStride bits.length
  let width := sparseExceptionRelativeWidth bits
  let e := ell bits.length
  let w := wordBits bits.length
  let spanSum := shortSuperLocalSpanSum bits target (localSlotCount bits target)
  have hpayload :
      (sparseExceptionRelativeTable bits target).payload.length =
        count * stride * width := by
    simpa [count, stride, width] using
      sparseExceptionRelativeTable_payload_expanded_length bits target
  have hcodec : stride * width * e <= 512 * w := by
    simpa [stride, width, e, w] using
      sparseException_localStride_mul_width_mul_ell_le_const_wordBits bits
  have hpayloadEll :
      count * stride * width * e <= count * (512 * w) := by
    have hmul := Nat.mul_le_mul_left count hcodec
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hcountWord : count * w <= spanSum := by
    simpa [count, w, spanSum] using
      sparseExceptionCount_wordBits_le_spanSum bits target (Nat.le_refl _)
  have hcountScaled : count * (512 * w) <= 512 * spanSum := by
    have hmul := Nat.mul_le_mul_left 512 hcountWord
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  rw [hpayload]
  exact Nat.le_trans hpayloadEll hcountScaled

/-- `o(n)` budget for the sparse-exception relative table, fed the bit length
directly. -/
def sparseExceptionRelativeTableOverhead (n : Nat) : Nat :=
  SuccinctSpace.idDivLogLogOverhead 512 n + 512

theorem sparseExceptionRelativeTableOverhead_littleO :
    SuccinctSpace.LittleOLinear sparseExceptionRelativeTableOverhead := by
  unfold sparseExceptionRelativeTableOverhead
  exact (SuccinctSpace.idDivLogLogOverhead_littleO 512).add_const 512

theorem sparseExceptionRelativeTable_payload_le_overhead_of_spanSum_le_length
    (bits : List Bool) (target : Bool)
    (hspan :
      shortSuperLocalSpanSum bits target (localSlotCount bits target) <=
        bits.length) :
    (sparseExceptionRelativeTable bits target).payload.length <=
      sparseExceptionRelativeTableOverhead bits.length := by
  let payload := (sparseExceptionRelativeTable bits target).payload.length
  let e := ell bits.length
  let n := bits.length
  have he_pos : 0 < e := by
    simpa [e] using ell_pos bits.length
  have hpayloadEll : payload * e <= 512 * n := by
    have hscaled :=
      sparseExceptionRelativeTable_payload_mul_ell_le_const_spanSum bits target
    have hspanScaled :
        512 * shortSuperLocalSpanSum bits target
              (localSlotCount bits target) <=
          512 * n := by
      exact Nat.mul_le_mul_left 512 (by simpa [n] using hspan)
    exact Nat.le_trans (by simpa [payload, e] using hscaled) hspanScaled
  let overheadLen := 512 * (n / e) + 512
  have hn_lt : n < n / e * e + e :=
    Nat.lt_div_mul_add he_pos (a := n)
  have hscaledStrict : 512 * n < overheadLen * e := by
    have hmul := Nat.mul_lt_mul_of_pos_left hn_lt (by decide : 0 < 512)
    simpa [overheadLen, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
      Nat.left_distrib, Nat.right_distrib] using hmul
  have hpayloadStrict : payload * e < overheadLen * e :=
    Nat.lt_of_le_of_lt hpayloadEll hscaledStrict
  have hpayloadStrictLeft : e * payload < e * overheadLen := by
    simpa [Nat.mul_comm] using hpayloadStrict
  have hpayloadLe : payload <= overheadLen :=
    Nat.le_of_mul_le_mul_left (Nat.le_of_lt hpayloadStrictLeft) he_pos
  simpa [payload, overheadLen, sparseExceptionRelativeTableOverhead,
    SuccinctSpace.idDivLogLogOverhead, e, n, ell, wordBits,
    SuccinctRank.machineWordBits] using hpayloadLe

theorem sparseExceptionRelativeTable_payload_le_overhead
    (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeTable bits target).payload.length <=
      sparseExceptionRelativeTableOverhead bits.length := by
  exact
    sparseExceptionRelativeTable_payload_le_overhead_of_spanSum_le_length
      bits target (shortSuperLocalSpanSum_le_length bits target)

def canonicalSparseExceptionDirectoryOverhead (n : Nat) : Nat :=
  SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 n +
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 n + 16) +
      sparseExceptionRelativeTableOverhead n

theorem canonicalSparseExceptionDirectoryOverhead_littleO :
    SuccinctSpace.LittleOLinear
      canonicalSparseExceptionDirectoryOverhead := by
  unfold canonicalSparseExceptionDirectoryOverhead
  have hflags :
      SuccinctSpace.LittleOLinear
        (SuccinctSpace.logLogCubedSampledDirectoryOverhead 40) :=
    SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 40
  have hrank :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 n + 16) :=
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 192).add_const 16
  exact (hflags.add hrank).add sparseExceptionRelativeTableOverhead_littleO

theorem fixedWidthNatTable_word_length_le_of_mem
    {entries : List Nat} {width n : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (hwidth : width <= SuccinctRank.machineWordBits n)
    {word : List Bool}
    (hmem : List.Mem word table.store.words.toList) :
    word.length <= SuccinctRank.machineWordBits n := by
  rcases (List.mem_iff_getElem?.mp hmem) with ⟨i, hgetList⟩
  have hget : table.store.words[i]? = some word := by
    simpa [Array.getElem?_toList] using hgetList
  rw [table.read_word_length_of_some hget]
  exact hwidth

def relativeOffsetReadCosted
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) : Costed (Option Nat) :=
  Costed.map (fun offset? => offset?.map (fun offset => base + offset))
    (table.readCosted slot)

theorem sparseExceptionRelativeWidth_le_machine (bits : List Bool) :
    sparseExceptionRelativeWidth bits <=
      SuccinctRank.machineWordBits bits.length := by
  unfold sparseExceptionRelativeWidth
  exact SuccinctRank.machineWordBits_mono_le
    (Nat.min_le_left bits.length (superLongSpan bits.length))


end RMQ.GenericSelect
