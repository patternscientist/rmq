import RMQ.Core.RankSelectSpec
import RMQ.Core.SuccinctRankProposal
import RMQ.Core.GenericSelect.SelectSource

/-!
# Two-level select and rank/select proposal layer

This module contains the sampled-word select primitives, two-level select data,
rank/select family adapters, and BP close-navigation interface wrappers. It
keeps the historical `RMQ.SuccinctSelectProposal` namespace so public theorem
names remain stable while `SuccinctSelectProposal.lean` is split by role.
-/

namespace RMQ
namespace SuccinctSelectProposal
open SuccinctSpace

def twoLevelSelectOverhead
    (super block : Nat -> Nat) (n : Nat) : Nat :=
  super n + block n

theorem twoLevelSelectOverhead_littleO
    {super block : Nat -> Nat}
    (hsuper : SuccinctSpace.LittleOLinear super)
    (hblock : SuccinctSpace.LittleOLinear block) :
    SuccinctSpace.LittleOLinear
      (twoLevelSelectOverhead super block) := by
  unfold twoLevelSelectOverhead
  exact hsuper.add hblock

/-- Canonical select-superblock budget: `O(n / log n)` bits. -/
def canonicalTwoLevelSelectSuperOverhead (slots : Nat) : Nat -> Nat :=
  SuccinctSpace.sampledDirectoryOverhead slots

/-- Canonical select-local budget: `O(n log log n / log n)` bits. -/
def canonicalTwoLevelSelectBlockOverhead (slots : Nat) : Nat -> Nat :=
  SuccinctSpace.logLogSampledDirectoryOverhead slots

/-- Combined canonical two-level select auxiliary budget. -/
def canonicalTwoLevelSelectOverhead
    (superSlots blockSlots : Nat) : Nat -> Nat :=
  twoLevelSelectOverhead
    (canonicalTwoLevelSelectSuperOverhead superSlots)
    (canonicalTwoLevelSelectBlockOverhead blockSlots)

theorem canonicalTwoLevelSelectSuperOverhead_littleO (slots : Nat) :
    SuccinctSpace.LittleOLinear
      (canonicalTwoLevelSelectSuperOverhead slots) := by
  exact SuccinctSpace.sampledDirectoryOverhead_littleO slots

theorem canonicalTwoLevelSelectBlockOverhead_littleO (slots : Nat) :
    SuccinctSpace.LittleOLinear
      (canonicalTwoLevelSelectBlockOverhead slots) := by
  exact SuccinctSpace.logLogSampledDirectoryOverhead_littleO slots

theorem canonicalTwoLevelSelectOverhead_littleO
    (superSlots blockSlots : Nat) :
    SuccinctSpace.LittleOLinear
      (canonicalTwoLevelSelectOverhead superSlots blockSlots) := by
  exact
    twoLevelSelectOverhead_littleO
      (canonicalTwoLevelSelectSuperOverhead_littleO superSlots)
      (canonicalTwoLevelSelectBlockOverhead_littleO blockSlots)

def addSelectSample
    (base delta : SuccinctSpace.StoredWordSelectSample) :
    SuccinctSpace.StoredWordSelectSample where
  wordIndex := base.wordIndex + delta.wordIndex
  wordStart := base.wordStart + delta.wordStart
  rankBefore := base.rankBefore + delta.rankBefore

/-- Word-aligned start position for the word containing `pos`. -/
def selectWordStart (wordSize pos : Nat) : Nat :=
  (pos / wordSize) * wordSize

/--
Canonical locator sample for a known selected position.

The sample points at the payload word containing `pos`, records that word's
global start offset, and stores the target-rank before the word.  This is the
concrete sample shape the two-level select directory should materialize.
-/
def selectSampleOfSelectedPos
    (target : Bool) (bits : List Bool) (wordSize pos : Nat) :
    SuccinctSpace.StoredWordSelectSample where
  wordIndex := pos / wordSize
  wordStart := selectWordStart wordSize pos
  rankBefore :=
    RMQ.Succinct.rankPrefix target bits (selectWordStart wordSize pos)

/-- Canonical locator for the `occurrence`-th target bit, when it exists. -/
def selectSampleAt?
    (target : Bool) (bits : List Bool) (wordSize occurrence : Nat) :
    Option SuccinctSpace.StoredWordSelectSample :=
  (RMQ.Succinct.select target bits occurrence).map
    (fun pos => selectSampleOfSelectedPos target bits wordSize pos)

theorem selectSampleAt?_none_exact
    {target : Bool} {bits : List Bool} {wordSize occurrence : Nat}
    (h :
      selectSampleAt? target bits wordSize occurrence = none) :
    RMQ.Succinct.select target bits occurrence = none := by
  unfold selectSampleAt? at h
  cases hselect : RMQ.Succinct.select target bits occurrence with
  | none =>
      rfl
  | some pos =>
      simp [hselect] at h

theorem selectSampleAt?_some_fields
    {target : Bool} {bits : List Bool} {wordSize occurrence : Nat}
    {sample : SuccinctSpace.StoredWordSelectSample}
    (h :
      selectSampleAt? target bits wordSize occurrence = some sample) :
    exists pos,
      RMQ.Succinct.select target bits occurrence = some pos /\
        sample = selectSampleOfSelectedPos target bits wordSize pos := by
  unfold selectSampleAt? at h
  cases hselect : RMQ.Succinct.select target bits occurrence with
  | none =>
      simp [hselect] at h
  | some pos =>
      simp [hselect] at h
      exact ⟨pos, rfl, h.symm⟩

theorem selectSampleOfSelectedPos_field_bounds
    {target : Bool} {bits : List Bool} {wordSize fieldWidth occurrence pos : Nat}
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hbits : bits.length < 2 ^ fieldWidth) :
    (selectSampleOfSelectedPos target bits wordSize pos).wordIndex <
        2 ^ fieldWidth /\
      (selectSampleOfSelectedPos target bits wordSize pos).wordStart <
        2 ^ fieldWidth /\
        (selectSampleOfSelectedPos target bits wordSize pos).rankBefore <
          2 ^ fieldWidth := by
  have hpos : pos < bits.length := RMQ.Succinct.select_bounds hselect
  have hindex_le : pos / wordSize <= pos := Nat.div_le_self pos wordSize
  have hstart_le : selectWordStart wordSize pos <= pos := by
    unfold selectWordStart
    exact Nat.div_mul_le_self pos wordSize
  have hrank_le :
      RMQ.Succinct.rankPrefix target bits (selectWordStart wordSize pos) <=
        bits.length :=
    RMQ.Succinct.rankPrefix_le_length target bits (selectWordStart wordSize pos)
  simp [selectSampleOfSelectedPos, selectWordStart]
  constructor
  · exact Nat.lt_of_le_of_lt hindex_le (Nat.lt_trans hpos hbits)
  · constructor
    · exact Nat.lt_of_le_of_lt hstart_le (Nat.lt_trans hpos hbits)
    · exact Nat.lt_of_le_of_lt hrank_le hbits

theorem selectSampleAt?_some_field_bounds
    {target : Bool} {bits : List Bool} {wordSize fieldWidth occurrence : Nat}
    {sample : SuccinctSpace.StoredWordSelectSample}
    (h :
      selectSampleAt? target bits wordSize occurrence = some sample)
    (hbits : bits.length < 2 ^ fieldWidth) :
    sample.wordIndex < 2 ^ fieldWidth /\
      sample.wordStart < 2 ^ fieldWidth /\
        sample.rankBefore < 2 ^ fieldWidth := by
  rcases selectSampleAt?_some_fields h with ⟨pos, hselect, rfl⟩
  exact selectSampleOfSelectedPos_field_bounds hselect hbits

/-- Difference sample whose sum with `base` reconstructs `exact`, when ordered. -/
def selectSampleDelta
    (base exact : SuccinctSpace.StoredWordSelectSample) :
    SuccinctSpace.StoredWordSelectSample where
  wordIndex := exact.wordIndex - base.wordIndex
  wordStart := exact.wordStart - base.wordStart
  rankBefore := exact.rankBefore - base.rankBefore

theorem addSelectSample_selectSampleDelta_eq
    {base exact : SuccinctSpace.StoredWordSelectSample}
    (hwordIndex : base.wordIndex <= exact.wordIndex)
    (hwordStart : base.wordStart <= exact.wordStart)
    (hrankBefore : base.rankBefore <= exact.rankBefore) :
    addSelectSample base (selectSampleDelta base exact) = exact := by
  cases base
  cases exact
  simp [addSelectSample, selectSampleDelta] at *
  constructor <;> omega

theorem selectSampleDelta_field_bounds_of_exact
    {base exact : SuccinctSpace.StoredWordSelectSample} {fieldWidth : Nat}
    (hexact :
      exact.wordIndex < 2 ^ fieldWidth /\
        exact.wordStart < 2 ^ fieldWidth /\
          exact.rankBefore < 2 ^ fieldWidth) :
    (selectSampleDelta base exact).wordIndex < 2 ^ fieldWidth /\
      (selectSampleDelta base exact).wordStart < 2 ^ fieldWidth /\
        (selectSampleDelta base exact).rankBefore < 2 ^ fieldWidth := by
  rcases hexact with ⟨hwordIndex, hwordStart, hrankBefore⟩
  simp [selectSampleDelta]
  exact ⟨Nat.lt_of_le_of_lt (Nat.sub_le _ _) hwordIndex,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hwordStart,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hrankBefore⟩

/-- Occurrence represented by a superblock locator index. -/
def selectSuperOccurrence
    (occurrencesPerSuper superIndex : Nat) : Nat :=
  superIndex * occurrencesPerSuper

/-- Canonical superblock locator entry. -/
def selectSuperSampleEntry?
    (target : Bool) (bits : List Bool) (wordSize occurrencesPerSuper
      superIndex : Nat) :
    Option SuccinctSpace.StoredWordSelectSample :=
  selectSampleAt? target bits wordSize
    (selectSuperOccurrence occurrencesPerSuper superIndex)

/--
Canonical local locator entry for the identity-index finite constructor.

The reusable two-level select API below is parametric in a local block index;
this canonical table keeps the older direct occurrence index as a witness while
compact dense/sparse builders can route many occurrences through fewer local
slots.  The stored entry is the delta from the occurrence's superblock locator
to the exact locator for the occurrence.  If either locator is absent, the
stored entry is absent.
-/
def selectBlockDeltaEntry?
    (target : Bool) (bits : List Bool) (wordSize occurrencesPerSuper
      occurrence : Nat) :
    Option SuccinctSpace.StoredWordSelectSample :=
  match
      selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
        (occurrence / occurrencesPerSuper),
      selectSampleAt? target bits wordSize occurrence with
  | some base, some exact => some (selectSampleDelta base exact)
  | _, _ => none

def selectSuperSampleEntries
    (target : Bool) (bits : List Bool) (wordSize occurrencesPerSuper
      count : Nat) :
    List (Option SuccinctSpace.StoredWordSelectSample) :=
  (List.range count).map
    (fun i =>
      selectSuperSampleEntry? target bits wordSize occurrencesPerSuper i)

def selectBlockDeltaEntries
    (target : Bool) (bits : List Bool) (wordSize occurrencesPerSuper
      count : Nat) :
    List (Option SuccinctSpace.StoredWordSelectSample) :=
  (List.range count).map
    (fun occurrence =>
      selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
        occurrence)

theorem selectSuperSampleEntries_getOpt_exact
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerSuper count i : Nat}
    {entry : Option SuccinctSpace.StoredWordSelectSample}
    (hget :
      (selectSuperSampleEntries target bits wordSize occurrencesPerSuper
        count)[i]? = some entry) :
    entry =
      selectSuperSampleEntry? target bits wordSize occurrencesPerSuper i := by
  unfold selectSuperSampleEntries at hget
  by_cases hlt : i < count
  · simp [List.getElem?_map, List.getElem?_range hlt] at hget
    exact hget.symm
  · simp [hlt] at hget

theorem selectBlockDeltaEntries_getOpt_exact
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerSuper count occurrence : Nat}
    {entry : Option SuccinctSpace.StoredWordSelectSample}
    (hget :
      (selectBlockDeltaEntries target bits wordSize occurrencesPerSuper
        count)[occurrence]? = some entry) :
    entry =
      selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
        occurrence := by
  unfold selectBlockDeltaEntries at hget
  by_cases hlt : occurrence < count
  · simp [List.getElem?_map, List.getElem?_range hlt] at hget
    exact hget.symm
  · simp [hlt] at hget

theorem selectSuperSampleEntries_present_of_lt
    (target : Bool) (bits : List Bool)
    {wordSize occurrencesPerSuper count i : Nat}
    (hi : i < count) :
    exists entry,
      (selectSuperSampleEntries target bits wordSize occurrencesPerSuper
        count)[i]? = some entry := by
  refine ⟨selectSuperSampleEntry? target bits wordSize
      occurrencesPerSuper i, ?_⟩
  simp [selectSuperSampleEntries, List.getElem?_map,
    List.getElem?_range hi]

theorem selectBlockDeltaEntries_present_of_lt
    (target : Bool) (bits : List Bool)
    {wordSize occurrencesPerSuper count occurrence : Nat}
    (hocc : occurrence < count) :
    exists entry,
      (selectBlockDeltaEntries target bits wordSize occurrencesPerSuper
        count)[occurrence]? = some entry := by
  refine ⟨selectBlockDeltaEntry? target bits wordSize
      occurrencesPerSuper occurrence, ?_⟩
  simp [selectBlockDeltaEntries, List.getElem?_map,
    List.getElem?_range hocc]

theorem selectSuperSampleEntry?_some_field_bounds
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerSuper superIndex fieldWidth : Nat}
    {sample : SuccinctSpace.StoredWordSelectSample}
    (hentry :
      selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
        superIndex = some sample)
    (hbits : bits.length < 2 ^ fieldWidth) :
    sample.wordIndex < 2 ^ fieldWidth /\
      sample.wordStart < 2 ^ fieldWidth /\
        sample.rankBefore < 2 ^ fieldWidth := by
  unfold selectSuperSampleEntry? at hentry
  exact selectSampleAt?_some_field_bounds hentry hbits

theorem selectBlockDeltaEntry?_some_field_bounds
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerSuper occurrence fieldWidth : Nat}
    {delta : SuccinctSpace.StoredWordSelectSample}
    (hentry :
      selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
        occurrence = some delta)
    (hbits : bits.length < 2 ^ fieldWidth) :
    delta.wordIndex < 2 ^ fieldWidth /\
      delta.wordStart < 2 ^ fieldWidth /\
        delta.rankBefore < 2 ^ fieldWidth := by
  unfold selectBlockDeltaEntry? at hentry
  cases hsuper :
      selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
        (occurrence / occurrencesPerSuper) with
  | none =>
      simp [hsuper] at hentry
  | some base =>
      cases hexact : selectSampleAt? target bits wordSize occurrence with
      | none =>
          simp [hsuper, hexact] at hentry
      | some exact =>
          simp [hsuper, hexact] at hentry
          subst delta
          exact
            selectSampleDelta_field_bounds_of_exact
              (selectSampleAt?_some_field_bounds hexact hbits)

theorem selectSuperSampleEntries_mem_bound
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerSuper count fieldWidth : Nat}
    {entry : Option SuccinctSpace.StoredWordSelectSample}
    {sample : SuccinctSpace.StoredWordSelectSample}
    (hmem :
      List.Mem entry
        (selectSuperSampleEntries target bits wordSize occurrencesPerSuper
          count))
    (hsome : entry = some sample)
    (hbits : bits.length < 2 ^ fieldWidth) :
    sample.wordIndex < 2 ^ fieldWidth /\
      sample.wordStart < 2 ^ fieldWidth /\
        sample.rankBefore < 2 ^ fieldWidth := by
  rcases List.mem_map.mp hmem with ⟨i, _hi, rfl⟩
  exact selectSuperSampleEntry?_some_field_bounds hsome hbits

theorem selectBlockDeltaEntries_mem_bound
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerSuper count fieldWidth : Nat}
    {entry : Option SuccinctSpace.StoredWordSelectSample}
    {sample : SuccinctSpace.StoredWordSelectSample}
    (hmem :
      List.Mem entry
        (selectBlockDeltaEntries target bits wordSize occurrencesPerSuper
          count))
    (hsome : entry = some sample)
    (hbits : bits.length < 2 ^ fieldWidth) :
    sample.wordIndex < 2 ^ fieldWidth /\
      sample.wordStart < 2 ^ fieldWidth /\
        sample.rankBefore < 2 ^ fieldWidth := by
  rcases List.mem_map.mp hmem with ⟨occurrence, _hocc, rfl⟩
  exact selectBlockDeltaEntry?_some_field_bounds hsome hbits

def canonicalSelectSuperTables
    (bits : List Bool) (wordSize occurrencesPerSuper fieldWidth
      trueCount falseCount : Nat)
    (hbits : bits.length < 2 ^ fieldWidth) :
    SuccinctSpace.FixedWidthSelectSampleTables
      (selectSuperSampleEntries true bits wordSize occurrencesPerSuper
        trueCount)
      (selectSuperSampleEntries false bits wordSize occurrencesPerSuper
        falseCount)
      fieldWidth :=
  SuccinctSpace.FixedWidthSelectSampleTables.ofEntries _ _ fieldWidth
    (by
      intro entry sample hmem hsome
      exact selectSuperSampleEntries_mem_bound hmem hsome hbits)
    (by
      intro entry sample hmem hsome
      exact selectSuperSampleEntries_mem_bound hmem hsome hbits)

def canonicalSelectBlockTables
    (bits : List Bool) (wordSize occurrencesPerSuper fieldWidth
      trueCount falseCount : Nat)
    (hbits : bits.length < 2 ^ fieldWidth) :
    SuccinctSpace.FixedWidthSelectSampleTables
      (selectBlockDeltaEntries true bits wordSize occurrencesPerSuper
        trueCount)
      (selectBlockDeltaEntries false bits wordSize occurrencesPerSuper
        falseCount)
      fieldWidth :=
  SuccinctSpace.FixedWidthSelectSampleTables.ofEntries _ _ fieldWidth
    (by
      intro entry sample hmem hsome
      exact selectBlockDeltaEntries_mem_bound hmem hsome hbits)
    (by
      intro entry sample hmem hsome
      exact selectBlockDeltaEntries_mem_bound hmem hsome hbits)

theorem selectBlockDeltaEntry?_some_of_samples
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerSuper occurrence : Nat}
    {base exact : SuccinctSpace.StoredWordSelectSample}
    (hbase :
      selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
        (occurrence / occurrencesPerSuper) = some base)
    (hexact :
      selectSampleAt? target bits wordSize occurrence = some exact) :
    selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
        occurrence =
      some (selectSampleDelta base exact) := by
  simp [selectBlockDeltaEntry?, hbase, hexact]

theorem selectBlockDeltaEntry?_add_exact_of_le
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerSuper occurrence : Nat}
    {base exact delta : SuccinctSpace.StoredWordSelectSample}
    (hbase :
      selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
        (occurrence / occurrencesPerSuper) = some base)
    (hexact :
      selectSampleAt? target bits wordSize occurrence = some exact)
    (hdelta :
      selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
        occurrence = some delta)
    (hwordIndex : base.wordIndex <= exact.wordIndex)
    (hwordStart : base.wordStart <= exact.wordStart)
    (hrankBefore : base.rankBefore <= exact.rankBefore) :
    addSelectSample base delta = exact := by
  have hcanonical :
      selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
          occurrence =
        some (selectSampleDelta base exact) :=
    selectBlockDeltaEntry?_some_of_samples hbase hexact
  rw [hcanonical] at hdelta
  injection hdelta with hdeltaEq
  subst delta
  exact addSelectSample_selectSampleDelta_eq
    hwordIndex hwordStart hrankBefore

/--
Local word-select exactness, stated for a concrete sample.

This isolates the remaining payload-word proof obligation: once a future
builder proves that the fetched word is the word described by the canonical
sample, this predicate is exactly the `select_some_exact` clause needed by the
two-level select query.
-/
def SelectSampleWordExact
    (target : Bool) (bits : List Bool) (occurrence : Nat)
    (sample : SuccinctSpace.StoredWordSelectSample) (word : List Bool) :
    Prop :=
  (RMQ.RAM.boolSelectInWord target word
      (occurrence - sample.rankBefore)).map
      (fun offset => sample.wordStart + offset) =
    RMQ.Succinct.select target bits occurrence

theorem SelectSampleWordExact.exists_word_offset_of_select
    {target : Bool} {bits word : List Bool}
    {occurrence pos : Nat}
    {sample : SuccinctSpace.StoredWordSelectSample}
    (hexact :
      SelectSampleWordExact target bits occurrence sample word)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos) :
    exists offset,
      RMQ.RAM.boolSelectInWord target word
          (occurrence - sample.rankBefore) = some offset /\
        sample.wordStart + offset = pos := by
  unfold SelectSampleWordExact at hexact
  cases hlocal :
      RMQ.RAM.boolSelectInWord target word
        (occurrence - sample.rankBefore) with
  | none =>
      simp [hlocal, hselect] at hexact
  | some offset =>
      simp [hlocal, hselect] at hexact
      exact ⟨offset, rfl, hexact⟩

theorem SelectSampleWordExact.selected_position_in_read_word
    {target : Bool} {bits word : List Bool}
    {occurrence pos : Nat}
    {sample : SuccinctSpace.StoredWordSelectSample}
    (hexact :
      SelectSampleWordExact target bits occurrence sample word)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos) :
    sample.wordStart <= pos /\ pos < sample.wordStart + word.length := by
  rcases
      SelectSampleWordExact.exists_word_offset_of_select
        hexact hselect with
    ⟨offset, hlocal, hpos⟩
  have hoffset :
      offset < word.length := by
    have hselectWord :
        RMQ.Succinct.select target word
            (occurrence - sample.rankBefore) = some offset := by
      simpa [RMQ.Succinct.ram_boolSelectInWord_eq_select] using hlocal
    exact RMQ.Succinct.select_bounds hselectWord
  constructor <;> omega

/--
If the payload word read by a select sample is an aligned machine chunk, then
local exactness determines its chunk index: it must be the chunk containing the
selected global bit position.

This is the descriptor-select obligation that the compact final builder has to
meet without falling back to one local locator per occurrence.
-/
theorem SelectSampleWordExact.selected_wordIndex_eq_of_aligned_read_word
    {target : Bool} {bits word : List Bool}
    {occurrence pos wordSize : Nat}
    {sample : SuccinctSpace.StoredWordSelectSample}
    (_hwordSize : 0 < wordSize)
    (hexact :
      SelectSampleWordExact target bits occurrence sample word)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hstart : sample.wordStart = sample.wordIndex * wordSize)
    (hwordLen : word.length <= wordSize) :
    pos / wordSize = sample.wordIndex := by
  rcases
      SelectSampleWordExact.selected_position_in_read_word
        hexact hselect with
    ⟨hlo, hhi⟩
  have hlo' : sample.wordIndex * wordSize <= pos := by
    simpa [hstart] using hlo
  have hhi' : pos < (sample.wordIndex + 1) * wordSize := by
    have hbound :
        sample.wordStart + word.length <=
          sample.wordIndex * wordSize + wordSize := by
      omega
    have hpos :
        pos < sample.wordIndex * wordSize + wordSize :=
      Nat.lt_of_lt_of_le hhi hbound
    simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hpos
  exact Nat.div_eq_of_lt_le hlo' hhi'

/--
Rank at the end of a taken prefix agrees with rank in the original bitvector.

This version is convenient when a select proof first restricts the query to
`bits.take limit`: it avoids splitting on whether `limit` is past the payload
end at every use site.
-/
theorem rankPrefix_take_length_eq
    (target : Bool) (bits : List Bool) (limit : Nat) :
    RMQ.Succinct.rankPrefix target (bits.take limit)
        (bits.take limit).length =
      RMQ.Succinct.rankPrefix target bits limit := by
  by_cases hlimit : limit <= bits.length
  · have hlen : (bits.take limit).length = limit := by
      simp [List.length_take, Nat.min_eq_left hlimit]
    have hlimitTake : limit <= (bits.take limit).length := by
      rw [hlen]
      exact Nat.le_refl limit
    rw [hlen]
    exact RMQ.Succinct.rankPrefix_take_eq_of_le
      target bits hlimitTake
  · have hlen_le : bits.length <= limit := Nat.le_of_not_ge hlimit
    have htake : bits.take limit = bits := by
      exact List.take_of_length_le hlen_le
    rw [htake]
    exact
      (RMQ.Succinct.rankPrefix_eq_rankPrefix_length_of_length_le
        target bits hlen_le).symm

/-- A successful select contributes exactly one target bit at `pos + 1`. -/
theorem rankPrefix_succ_of_select
    {target : Bool} {bits : List Bool} {occurrence pos : Nat}
    (hselect : RMQ.Succinct.select target bits occurrence = some pos) :
    RMQ.Succinct.rankPrefix target bits (pos + 1) = occurrence + 1 := by
  induction bits generalizing occurrence pos with
  | nil =>
      simp [RMQ.Succinct.select, RMQ.Succinct.selectFrom] at hselect
  | cons bit rest ih =>
      unfold RMQ.Succinct.select at hselect
      unfold RMQ.Succinct.selectFrom at hselect
      by_cases hbit : bit = target
      · rw [if_pos hbit] at hselect
        by_cases hocc : occurrence = 0
        · rw [if_pos hocc] at hselect
          injection hselect with hpos
          subst occurrence
          subst pos
          simp [RMQ.Succinct.rankPrefix, hbit]
        · rw [if_neg hocc] at hselect
          have hbase :=
            RMQ.Succinct.selectFrom_base_eq
              target rest 1 (occurrence - 1)
          rw [hbase] at hselect
          cases hsel :
              RMQ.Succinct.select target rest (occurrence - 1) with
          | none =>
              simp [hsel] at hselect
          | some inner =>
              simp [hsel] at hselect
              subst pos
              have hrec := ih hsel
              have hocc_pos : 0 < occurrence := Nat.pos_of_ne_zero hocc
              have hinnerSucc : 1 + inner = inner + 1 := by omega
              rw [hinnerSucc]
              simp [RMQ.Succinct.rankPrefix, hbit, hrec]
              omega
      · rw [if_neg hbit] at hselect
        have hbase :=
          RMQ.Succinct.selectFrom_base_eq target rest 1 occurrence
        rw [hbase] at hselect
        cases hsel : RMQ.Succinct.select target rest occurrence with
        | none =>
            simp [hsel] at hselect
        | some inner =>
            simp [hsel] at hselect
            subst pos
            have hrec := ih hsel
            have hinnerSucc : 1 + inner = inner + 1 := by omega
            rw [hinnerSucc]
            simpa [RMQ.Succinct.rankPrefix, hbit] using hrec

/--
If a successful select answer lies before `limit`, then `limit` contains more
than `occurrence` target bits.
-/
theorem occurrence_lt_rankPrefix_of_select_lt
    {target : Bool} {bits : List Bool} {occurrence pos limit : Nat}
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hpos : pos < limit) :
    occurrence < RMQ.Succinct.rankPrefix target bits limit := by
  have hsucc := rankPrefix_succ_of_select hselect
  have hmono :
      RMQ.Succinct.rankPrefix target bits (pos + 1) <=
        RMQ.Succinct.rankPrefix target bits limit :=
    RMQ.Succinct.rankPrefix_mono_limit
      target bits (Nat.succ_le_of_lt hpos)
  omega

theorem rankPrefix_sub_le_span
    (target : Bool) (bits : List Bool) (start span : Nat) :
    RMQ.Succinct.rankPrefix target bits (start + span) -
        RMQ.Succinct.rankPrefix target bits start <= span := by
  by_cases hstart : start <= bits.length
  · let hi := Nat.min (start + span) bits.length
    have hstart_hi : start <= hi := by
      dsimp [hi]
      exact Nat.le_min.mpr ⟨Nat.le_add_right start span, hstart⟩
    have hhi_len : hi <= bits.length := by
      dsimp [hi]
      exact Nat.min_le_right (start + span) bits.length
    have hhi_span : hi - start <= span := by
      dsimp [hi]
      have hhi_le : Nat.min (start + span) bits.length <= start + span :=
        Nat.min_le_left (start + span) bits.length
      omega
    have hdrop :=
      RMQ.Succinct.rankPrefix_drop_eq_sub_of_le
        target bits hstart_hi hhi_len
    have htail :
        RMQ.Succinct.rankPrefix target (bits.drop start) (hi - start) <=
          hi - start :=
      RMQ.Succinct.rankPrefix_le_limit
        target (bits.drop start) (hi - start)
    have hdiff :
        RMQ.Succinct.rankPrefix target bits hi -
            RMQ.Succinct.rankPrefix target bits start <= hi - start := by
      simpa [hdrop] using htail
    have hhi_eq :
        RMQ.Succinct.rankPrefix target bits hi =
          RMQ.Succinct.rankPrefix target bits (start + span) := by
      simpa [hi] using
        (RMQ.Succinct.rankPrefix_min_length_eq
          target bits (start + span))
    rw [<- hhi_eq]
    exact Nat.le_trans hdiff hhi_span
  · have hlen_start : bits.length <= start := Nat.le_of_not_ge hstart
    have hlen_hi : bits.length <= start + span := by omega
    have hstart_eq :=
      RMQ.Succinct.rankPrefix_eq_rankPrefix_length_of_length_le
        target bits hlen_start
    have hhi_eq :=
      RMQ.Succinct.rankPrefix_eq_rankPrefix_length_of_length_le
        target bits hlen_hi
    rw [hhi_eq, hstart_eq]
    simp

/--
Descriptor word-choice for a two-word local run.

The descriptor stores the number of target bits in the first word of the run.
Given the run's `rankBefore`, the query chooses the first payload word exactly
when the local occurrence is below that first-word count.
-/
def twoWordDescriptorChoice
    (rankBefore firstWordCount occurrence : Nat) : Nat :=
  if occurrence - rankBefore < firstWordCount then 0 else 1

def twoWordDescriptorWordIndex
    (baseWordIndex rankBefore firstWordCount occurrence : Nat) : Nat :=
  baseWordIndex +
    twoWordDescriptorChoice rankBefore firstWordCount occurrence

def twoWordDescriptorBaseWordIndex (descriptorIndex : Nat) : Nat :=
  2 * descriptorIndex

def twoWordDescriptorFirstCount
    (target : Bool) (bits : List Bool) (wordSize descriptorIndex : Nat) :
    Nat :=
  let baseWordIndex := twoWordDescriptorBaseWordIndex descriptorIndex
  RMQ.Succinct.rankPrefix target bits ((baseWordIndex + 1) * wordSize) -
    RMQ.Succinct.rankPrefix target bits (baseWordIndex * wordSize)

def twoWordDescriptorFirstCountEntries
    (target : Bool) (bits : List Bool) (wordSize count : Nat) : List Nat :=
  (List.range count).map
    (fun descriptorIndex =>
      twoWordDescriptorFirstCount target bits wordSize descriptorIndex)

theorem twoWordDescriptorFirstCount_le_wordSize
    (target : Bool) (bits : List Bool)
    (wordSize descriptorIndex : Nat) :
    twoWordDescriptorFirstCount target bits wordSize descriptorIndex <=
      wordSize := by
  let baseWordIndex := twoWordDescriptorBaseWordIndex descriptorIndex
  have hspan :=
    rankPrefix_sub_le_span target bits (baseWordIndex * wordSize) wordSize
  have hmul :
      (baseWordIndex + 1) * wordSize =
        baseWordIndex * wordSize + wordSize := by
    rw [Nat.succ_mul]
  change
    RMQ.Succinct.rankPrefix target bits
          ((baseWordIndex + 1) * wordSize) -
        RMQ.Succinct.rankPrefix target bits
          (baseWordIndex * wordSize) <= wordSize
  rw [hmul]
  exact hspan

theorem twoWordDescriptorFirstCountEntries_getOpt_exact
    {target : Bool} {bits : List Bool}
    {wordSize count descriptorIndex firstWordCount : Nat}
    (hget :
      (twoWordDescriptorFirstCountEntries target bits wordSize count)[
          descriptorIndex]? = some firstWordCount) :
    firstWordCount =
      twoWordDescriptorFirstCount target bits wordSize descriptorIndex := by
  unfold twoWordDescriptorFirstCountEntries at hget
  by_cases hlt : descriptorIndex < count
  · simp [List.getElem?_map, List.getElem?_range hlt] at hget
    exact hget.symm
  · simp [hlt] at hget

theorem twoWordDescriptorFirstCountEntries_mem_bound
    {target : Bool} {bits : List Bool}
    {wordSize count fieldWidth entry : Nat}
    (hfield : wordSize < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry
        (twoWordDescriptorFirstCountEntries
          target bits wordSize count)) :
    entry < 2 ^ fieldWidth := by
  unfold twoWordDescriptorFirstCountEntries at hmem
  rcases List.mem_map.mp hmem with ⟨descriptorIndex, _hmem, rfl⟩
  exact Nat.lt_of_le_of_lt
    (twoWordDescriptorFirstCount_le_wordSize
      target bits wordSize descriptorIndex)
    hfield

def twoWordDescriptorFirstCountTables
    (bits : List Bool) (wordSize fieldWidth count : Nat)
    (hfield : wordSize < 2 ^ fieldWidth) :
    SuccinctSpace.FixedWidthRankSampleTables
      (twoWordDescriptorFirstCountEntries true bits wordSize count)
      (twoWordDescriptorFirstCountEntries false bits wordSize count)
      fieldWidth :=
  SuccinctSpace.FixedWidthRankSampleTables.ofEntries
    (twoWordDescriptorFirstCountEntries true bits wordSize count)
    (twoWordDescriptorFirstCountEntries false bits wordSize count)
    fieldWidth
    (fun hmem =>
      twoWordDescriptorFirstCountEntries_mem_bound
        (target := true) (bits := bits) (wordSize := wordSize)
        (count := count) hfield hmem)
    (fun hmem =>
      twoWordDescriptorFirstCountEntries_mem_bound
        (target := false) (bits := bits) (wordSize := wordSize)
        (count := count) hfield hmem)

theorem twoWordDescriptorFirstCountTables_profile
    (bits : List Bool) {wordSize fieldWidth count : Nat}
    (hfield : wordSize < 2 ^ fieldWidth) :
    let tables :=
      twoWordDescriptorFirstCountTables
        bits wordSize fieldWidth count hfield
    tables.payload.length =
        count * fieldWidth + count * fieldWidth /\
      forall target descriptorIndex,
        (tables.sampleCosted target descriptorIndex).cost <= 1 /\
          (tables.sampleCosted target descriptorIndex).erase =
            (tables.entries target)[descriptorIndex]? := by
  intro tables
  have hprofile := tables.profile
  rcases hprofile with ⟨hlen, hread⟩
  constructor
  · simpa [twoWordDescriptorFirstCountTables,
      twoWordDescriptorFirstCountEntries] using hlen
  · exact hread

/--
A concrete two-word descriptor chooses the payload word containing the selected
bit, provided the selected bit is inside that two-word run.

This is the positive local kernel needed by a compact select builder: a charged
descriptor count, not a proof-only locator, determines the final payload word
before `wordSelect` runs.
-/
theorem twoWordDescriptorWordIndex_exact_of_select_in_run
    {target : Bool} {bits : List Bool}
    {occurrence pos wordSize baseWordIndex rankBefore firstWordCount : Nat}
    (_hwordSize : 0 < wordSize)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hrankBefore :
      rankBefore =
        RMQ.Succinct.rankPrefix target bits (baseWordIndex * wordSize))
    (hfirstWordCount :
      firstWordCount =
        RMQ.Succinct.rankPrefix target bits
            ((baseWordIndex + 1) * wordSize) -
          rankBefore)
    (hlo : baseWordIndex * wordSize <= pos)
    (hhi : pos < (baseWordIndex + 2) * wordSize) :
    twoWordDescriptorWordIndex
        baseWordIndex rankBefore firstWordCount occurrence =
      pos / wordSize := by
  let boundary := (baseWordIndex + 1) * wordSize
  have hstart_le_boundary :
      baseWordIndex * wordSize <= boundary := by
    dsimp [boundary]
    exact Nat.mul_le_mul_right wordSize (by omega)
  have hrankBefore_le_boundary :
      rankBefore <= RMQ.Succinct.rankPrefix target bits boundary := by
    rw [hrankBefore]
    exact RMQ.Succinct.rankPrefix_mono_limit
      target bits hstart_le_boundary
  have hfirstWordCount' :
      firstWordCount =
        RMQ.Succinct.rankPrefix target bits boundary - rankBefore := by
    simpa [boundary] using hfirstWordCount
  by_cases hleft : pos < boundary
  · have hocc_lt_boundary :
        occurrence < RMQ.Succinct.rankPrefix target bits boundary :=
      occurrence_lt_rankPrefix_of_select_lt hselect hleft
    have hrankBefore_le_occ :
        rankBefore <= occurrence := by
      rw [hrankBefore]
      exact RMQ.Succinct.rankPrefix_le_occurrence_of_le_select
        hselect hlo
    have hchoice :
        occurrence - rankBefore < firstWordCount := by
      rw [hfirstWordCount']
      omega
    have hdiv :
        pos / wordSize = baseWordIndex := by
      exact Nat.div_eq_of_lt_le hlo hleft
    simp [twoWordDescriptorWordIndex, twoWordDescriptorChoice,
      hchoice, hdiv]
  · have hboundary_le_pos : boundary <= pos := Nat.le_of_not_gt hleft
    have hboundary_rank_le_occ :
        RMQ.Succinct.rankPrefix target bits boundary <= occurrence :=
      RMQ.Succinct.rankPrefix_le_occurrence_of_le_select
        hselect hboundary_le_pos
    have hnotChoice :
        ¬ occurrence - rankBefore < firstWordCount := by
      rw [hfirstWordCount']
      omega
    have hdiv :
        pos / wordSize = baseWordIndex + 1 := by
      exact Nat.div_eq_of_lt_le hboundary_le_pos hhi
    simp [twoWordDescriptorWordIndex, twoWordDescriptorChoice,
      hnotChoice, hdiv]

theorem twoWordDescriptorTableRead_choice_exact_of_select_in_run
    {target : Bool} {bits : List Bool}
    {wordSize fieldWidth count descriptorIndex firstWordCount
      occurrence pos : Nat}
    (hfield : wordSize < 2 ^ fieldWidth)
    (_hwordSize : 0 < wordSize)
    (hread :
      ((twoWordDescriptorFirstCountTables
          bits wordSize fieldWidth count hfield).sampleCosted
          target descriptorIndex).erase = some firstWordCount)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hlo :
      twoWordDescriptorBaseWordIndex descriptorIndex * wordSize <= pos)
    (hhi :
      pos <
        (twoWordDescriptorBaseWordIndex descriptorIndex + 2) * wordSize) :
    twoWordDescriptorWordIndex
        (twoWordDescriptorBaseWordIndex descriptorIndex)
        (RMQ.Succinct.rankPrefix target bits
          (twoWordDescriptorBaseWordIndex descriptorIndex * wordSize))
        firstWordCount occurrence =
      pos / wordSize := by
  have hentry :
      (twoWordDescriptorFirstCountEntries
          target bits wordSize count)[descriptorIndex]? =
        some firstWordCount := by
    cases target <;>
      simpa [twoWordDescriptorFirstCountTables,
        SuccinctSpace.FixedWidthRankSampleTables.entries] using hread
  have hfirst :=
    twoWordDescriptorFirstCountEntries_getOpt_exact hentry
  exact
    twoWordDescriptorWordIndex_exact_of_select_in_run
      (target := target) (bits := bits)
      (occurrence := occurrence) (pos := pos)
      (_hwordSize)
      hselect
      (by rfl)
      (by
        simpa [twoWordDescriptorFirstCount] using hfirst)
      hlo hhi

theorem twoWordDescriptorWordIndex_exact_implies_position_in_run
    {wordSize baseWordIndex rankBefore firstWordCount occurrence pos : Nat}
    (hwordSize : 0 < wordSize)
    (hexact :
      twoWordDescriptorWordIndex
          baseWordIndex rankBefore firstWordCount occurrence =
        pos / wordSize) :
    baseWordIndex * wordSize <= pos /\
      pos < (baseWordIndex + 2) * wordSize := by
  unfold twoWordDescriptorWordIndex twoWordDescriptorChoice at hexact
  by_cases hchoice : occurrence - rankBefore < firstWordCount
  · simp [hchoice] at hexact
    have hlo :
        baseWordIndex * wordSize <= pos := by
      have hbase :
          (pos / wordSize) * wordSize <= pos :=
        Nat.div_mul_le_self pos wordSize
      rwa [<- hexact] at hbase
    have hhi :
        pos < (baseWordIndex + 2) * wordSize := by
      have hnext := Nat.lt_div_mul_add hwordSize (a := pos)
      rw [<- hexact] at hnext
      have hbound :
          baseWordIndex * wordSize + wordSize <=
            (baseWordIndex + 2) * wordSize :=
        by
          have htwo :
              (baseWordIndex + 2) * wordSize =
                (baseWordIndex + 1) * wordSize + wordSize := by
            change Nat.succ (baseWordIndex + 1) * wordSize =
              (baseWordIndex + 1) * wordSize + wordSize
            rw [Nat.succ_mul]
          rw [htwo]
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_right wordSize (by omega)) wordSize
      exact Nat.lt_of_lt_of_le hnext hbound
    exact ⟨hlo, hhi⟩
  · simp [hchoice] at hexact
    have hlo :
        baseWordIndex * wordSize <= pos := by
      have hbase :
          (pos / wordSize) * wordSize <= pos :=
        Nat.div_mul_le_self pos wordSize
      rw [<- hexact] at hbase
      have hstart :
          baseWordIndex * wordSize <=
            (baseWordIndex + 1) * wordSize :=
        Nat.mul_le_mul_right wordSize (by omega)
      exact Nat.le_trans hstart hbase
    have hhi :
        pos < (baseWordIndex + 2) * wordSize := by
      have hnext := Nat.lt_div_mul_add hwordSize (a := pos)
      rw [<- hexact] at hnext
      have htwo :
          (baseWordIndex + 2) * wordSize =
            (baseWordIndex + 1) * wordSize + wordSize := by
        change Nat.succ (baseWordIndex + 1) * wordSize =
          (baseWordIndex + 1) * wordSize + wordSize
        rw [Nat.succ_mul]
      simpa [htwo] using hnext
    exact ⟨hlo, hhi⟩

/--
The bit-blind arithmetic route `descriptorIndex = occurrence / 2` is not a
global select routing.  Sparse target bits can put the requested occurrence in
a later two-word payload run than this index chooses.
-/
theorem occurrencePairTwoWordDescriptorRouting_not_global :
    let bits : List Bool := [false, true, true, false]
    let wordSize : Nat := 1
    let occurrence : Nat := 1
    let descriptorIndex : Nat := occurrence / 2
    exists pos,
      RMQ.Succinct.select false bits occurrence = some pos /\
        ¬ (twoWordDescriptorBaseWordIndex descriptorIndex * wordSize <= pos /\
          pos <
            (twoWordDescriptorBaseWordIndex descriptorIndex + 2) *
              wordSize) := by
  refine ⟨3, ?_, ?_⟩
  · simp [RMQ.Succinct.select, RMQ.Succinct.selectFrom]
  · simp [twoWordDescriptorBaseWordIndex]

/--
More generally, no descriptor route that depends only on the queried
`target/occurrence` pair can cover all bitvectors.  The same query can require
different two-word payload runs in dense and sparse inputs.
-/
theorem occurrenceOnlyTwoWordDescriptorRouting_impossible
    (route : Bool -> Nat -> Nat) :
    ¬ (forall (bits : List Bool) (wordSize : Nat)
          (target : Bool) (occurrence pos : Nat),
        0 < wordSize ->
        RMQ.Succinct.select target bits occurrence = some pos ->
          twoWordDescriptorBaseWordIndex (route target occurrence) *
                wordSize <= pos /\
            pos <
              (twoWordDescriptorBaseWordIndex (route target occurrence) + 2) *
                wordSize) := by
  intro hroute
  have hdense :=
    hroute [false, false] 1 false 1 1 (by omega) (by
      simp [RMQ.Succinct.select, RMQ.Succinct.selectFrom])
  have hsparse :=
    hroute [true, true, false, false] 1 false 1 3 (by omega) (by
      simp [RMQ.Succinct.select, RMQ.Succinct.selectFrom])
  have hroute_eq_zero : route false 1 = 0 := by
    have hle := hdense.left
    simp [twoWordDescriptorBaseWordIndex] at hle
    omega
  have hhi := hsparse.right
  rw [hroute_eq_zero] at hhi
  simp [twoWordDescriptorBaseWordIndex] at hhi

/--
Reading only the coarse locator's payload word and using its two-word run as
the descriptor route is not enough either: the next target occurrence in the
same coarse region may already be outside that run.
-/
theorem coarseBaseTwoWordDescriptorRouting_not_global :
    let bits : List Bool := [false, true, true, false]
    let wordSize : Nat := 1
    let baseOccurrence : Nat := 0
    let occurrence : Nat := 1
    let base :=
      selectSampleOfSelectedPos false bits wordSize 0
    let descriptorIndex : Nat := base.wordIndex / 2
    exists pos,
      selectSampleAt? false bits wordSize baseOccurrence = some base /\
        RMQ.Succinct.select false bits occurrence = some pos /\
          ¬ (twoWordDescriptorBaseWordIndex descriptorIndex * wordSize <= pos /\
            pos <
              (twoWordDescriptorBaseWordIndex descriptorIndex + 2) *
                wordSize) := by
  refine ⟨3, ?_, ?_, ?_⟩
  · simp [selectSampleAt?, RMQ.Succinct.select, RMQ.Succinct.selectFrom,
      selectSampleOfSelectedPos, selectWordStart, RMQ.Succinct.rankPrefix]
  · simp [RMQ.Succinct.select, RMQ.Succinct.selectFrom]
  · simp [twoWordDescriptorBaseWordIndex, selectSampleOfSelectedPos,
      selectWordStart]

/--
A single aligned payload word cannot serve two successful select queries whose
answers lie in different payload chunks.

This is the minimal obstruction behind the descriptor-select fork: if a compact
local entry is shared, the entry must contain a charged way to choose a
different payload word before `wordSelect`; otherwise exactness collapses both
answers to the same chunk index.
-/
theorem SelectSampleWordExact.shared_aligned_read_word_forces_same_wordIndex
    {target : Bool} {bits word : List Bool}
    {occurrenceA occurrenceB posA posB wordSize : Nat}
    {sample : SuccinctSpace.StoredWordSelectSample}
    (hwordSize : 0 < wordSize)
    (hexactA :
      SelectSampleWordExact target bits occurrenceA sample word)
    (hexactB :
      SelectSampleWordExact target bits occurrenceB sample word)
    (hselectA : RMQ.Succinct.select target bits occurrenceA = some posA)
    (hselectB : RMQ.Succinct.select target bits occurrenceB = some posB)
    (hstart : sample.wordStart = sample.wordIndex * wordSize)
    (hwordLen : word.length <= wordSize) :
    posA / wordSize = posB / wordSize := by
  have hA :
      posA / wordSize = sample.wordIndex :=
    SelectSampleWordExact.selected_wordIndex_eq_of_aligned_read_word
      hwordSize hexactA hselectA hstart hwordLen
  have hB :
      posB / wordSize = sample.wordIndex :=
    SelectSampleWordExact.selected_wordIndex_eq_of_aligned_read_word
      hwordSize hexactB hselectB hstart hwordLen
  exact hA.trans hB.symm

theorem selectBlockDeltaEntry?_select_some_exact_of_word
    {target : Bool} {bits word : List Bool}
    {wordSize occurrencesPerSuper occurrence : Nat}
    {base exact delta : SuccinctSpace.StoredWordSelectSample}
    (hbase :
      selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
        (occurrence / occurrencesPerSuper) = some base)
    (hexact :
      selectSampleAt? target bits wordSize occurrence = some exact)
    (hdelta :
      selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
        occurrence = some delta)
    (hwordIndex : base.wordIndex <= exact.wordIndex)
    (hwordStart : base.wordStart <= exact.wordStart)
    (hrankBefore : base.rankBefore <= exact.rankBefore)
    (hword :
      SelectSampleWordExact target bits occurrence exact word) :
    (RMQ.RAM.boolSelectInWord target word
        (occurrence - (addSelectSample base delta).rankBefore)).map
        (fun offset => (addSelectSample base delta).wordStart + offset) =
      RMQ.Succinct.select target bits occurrence := by
  have hadd :=
    selectBlockDeltaEntry?_add_exact_of_le hbase hexact hdelta
      hwordIndex hwordStart hrankBefore
  simpa [SelectSampleWordExact, hadd] using hword

theorem selectFrom_none_of_le_occurrence
    {target : Bool} {bits : List Bool} {base lo hi : Nat}
    (hle : lo <= hi)
    (hlo : RMQ.Succinct.selectFrom target bits base lo = none) :
    RMQ.Succinct.selectFrom target bits base hi = none := by
  induction bits generalizing base lo hi with
  | nil =>
      simp [RMQ.Succinct.selectFrom]
  | cons bit rest ih =>
      by_cases hbit : bit = target
      · by_cases hlozero : lo = 0
        · subst lo
          simp [RMQ.Succinct.selectFrom, hbit] at hlo
        · have hhizero : hi ≠ 0 := by omega
          have htail : lo - 1 <= hi - 1 := by omega
          have hloTail :
              RMQ.Succinct.selectFrom target rest (base + 1) (lo - 1) =
                none := by
            simpa [RMQ.Succinct.selectFrom, hbit, hlozero] using hlo
          simpa [RMQ.Succinct.selectFrom, hbit, hhizero] using
            ih htail hloTail
      · have hloTail :
            RMQ.Succinct.selectFrom target rest (base + 1) lo = none := by
          simpa [RMQ.Succinct.selectFrom, hbit] using hlo
        simpa [RMQ.Succinct.selectFrom, hbit] using ih hle hloTail

theorem select_none_of_le_occurrence
    {target : Bool} {bits : List Bool} {lo hi : Nat}
    (hle : lo <= hi)
    (hlo : RMQ.Succinct.select target bits lo = none) :
    RMQ.Succinct.select target bits hi = none := by
  unfold RMQ.Succinct.select at *
  exact selectFrom_none_of_le_occurrence hle hlo

theorem selectSampleAt?_none_exact_of_le
    {target : Bool} {bits : List Bool} {wordSize lo hi : Nat}
    (hlo : selectSampleAt? target bits wordSize lo = none)
    (hle : lo <= hi) :
    RMQ.Succinct.select target bits hi = none := by
  exact select_none_of_le_occurrence hle
    (selectSampleAt?_none_exact hlo)

theorem selectSuperSampleEntry?_none_exact_of_occurrence
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerSuper occurrence : Nat}
    (hentry :
      selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
        (occurrence / occurrencesPerSuper) = none) :
    RMQ.Succinct.select target bits occurrence = none := by
  unfold selectSuperSampleEntry? at hentry
  exact selectSampleAt?_none_exact_of_le hentry (by
    unfold selectSuperOccurrence
    exact Nat.div_mul_le_self occurrence occurrencesPerSuper)

theorem selectBlockDeltaEntry?_some_fields_of_super
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerSuper occurrence : Nat}
    {base delta : SuccinctSpace.StoredWordSelectSample}
    (hbase :
      selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
        (occurrence / occurrencesPerSuper) = some base)
    (hdelta :
      selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
        occurrence = some delta) :
    exists exact,
      selectSampleAt? target bits wordSize occurrence = some exact /\
        delta = selectSampleDelta base exact := by
  unfold selectBlockDeltaEntry? at hdelta
  rw [hbase] at hdelta
  cases hexact : selectSampleAt? target bits wordSize occurrence with
  | none =>
      simp [hexact] at hdelta
  | some exact =>
      simp [hexact] at hdelta
      exact Exists.intro exact (And.intro rfl hdelta.symm)

theorem selectBlockDeltaEntry?_none_exact_of_super
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerSuper occurrence : Nat}
    {base : SuccinctSpace.StoredWordSelectSample}
    (hbase :
      selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
        (occurrence / occurrencesPerSuper) = some base)
    (hdelta :
      selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
        occurrence = none) :
    RMQ.Succinct.select target bits occurrence = none := by
  unfold selectBlockDeltaEntry? at hdelta
  rw [hbase] at hdelta
  cases hexact : selectSampleAt? target bits wordSize occurrence with
  | none =>
      exact selectSampleAt?_none_exact hexact
  | some exact =>
      simp [hexact] at hdelta

def canonicalSelectSuperCount
    (bits : List Bool) (occurrencesPerSuper : Nat) : Nat :=
  bits.length / occurrencesPerSuper + 1

def canonicalSelectBlockCount (bits : List Bool) : Nat :=
  bits.length + 1

def canonicalSelectSuperTablesFinite
    (bits : List Bool) (wordSize occurrencesPerSuper fieldWidth : Nat)
    (hbits : bits.length < 2 ^ fieldWidth) :
    SuccinctSpace.FixedWidthSelectSampleTables
      (selectSuperSampleEntries true bits wordSize occurrencesPerSuper
        (canonicalSelectSuperCount bits occurrencesPerSuper))
      (selectSuperSampleEntries false bits wordSize occurrencesPerSuper
        (canonicalSelectSuperCount bits occurrencesPerSuper))
      fieldWidth :=
  canonicalSelectSuperTables bits wordSize occurrencesPerSuper fieldWidth
    (canonicalSelectSuperCount bits occurrencesPerSuper)
    (canonicalSelectSuperCount bits occurrencesPerSuper) hbits

def canonicalSelectBlockTablesFinite
    (bits : List Bool) (wordSize occurrencesPerSuper fieldWidth : Nat)
    (hbits : bits.length < 2 ^ fieldWidth) :
    SuccinctSpace.FixedWidthSelectSampleTables
      (selectBlockDeltaEntries true bits wordSize occurrencesPerSuper
        (canonicalSelectBlockCount bits))
      (selectBlockDeltaEntries false bits wordSize occurrencesPerSuper
        (canonicalSelectBlockCount bits))
      fieldWidth :=
  canonicalSelectBlockTables bits wordSize occurrencesPerSuper fieldWidth
    (canonicalSelectBlockCount bits) (canonicalSelectBlockCount bits) hbits

@[simp] theorem canonicalSelectSuperTablesFinite_entries
    {bits : List Bool} {wordSize occurrencesPerSuper fieldWidth : Nat}
    (hbits : bits.length < 2 ^ fieldWidth) (target : Bool) :
    (canonicalSelectSuperTablesFinite
        bits wordSize occurrencesPerSuper fieldWidth hbits).entries target =
      selectSuperSampleEntries target bits wordSize occurrencesPerSuper
        (canonicalSelectSuperCount bits occurrencesPerSuper) := by
  cases target <;> rfl

@[simp] theorem canonicalSelectBlockTablesFinite_entries
    {bits : List Bool} {wordSize occurrencesPerSuper fieldWidth : Nat}
    (hbits : bits.length < 2 ^ fieldWidth) (target : Bool) :
    (canonicalSelectBlockTablesFinite
        bits wordSize occurrencesPerSuper fieldWidth hbits).entries target =
      selectBlockDeltaEntries target bits wordSize occurrencesPerSuper
        (canonicalSelectBlockCount bits) := by
  cases target <;> rfl

theorem canonicalSelectSuperTablesFinite_present
    {bits : List Bool} {wordSize occurrencesPerSuper fieldWidth
      occurrence : Nat}
    (hbits : bits.length < 2 ^ fieldWidth)
    (target : Bool) (hocc : occurrence <= bits.length) :
    exists entry,
      ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper fieldWidth hbits).entries
          target)[occurrence / occurrencesPerSuper]? = some entry := by
  have hindex :
      occurrence / occurrencesPerSuper <
        canonicalSelectSuperCount bits occurrencesPerSuper := by
    unfold canonicalSelectSuperCount
    have hle :
        occurrence / occurrencesPerSuper <=
          bits.length / occurrencesPerSuper := by
      exact Nat.div_le_div_right hocc
    omega
  simpa using
    selectSuperSampleEntries_present_of_lt
      target bits (wordSize := wordSize)
      (occurrencesPerSuper := occurrencesPerSuper)
      (count := canonicalSelectSuperCount bits occurrencesPerSuper)
      (i := occurrence / occurrencesPerSuper) hindex

theorem canonicalSelectBlockTablesFinite_present
    {bits : List Bool} {wordSize occurrencesPerSuper fieldWidth
      occurrence : Nat}
    (hbits : bits.length < 2 ^ fieldWidth)
    (target : Bool) (hocc : occurrence <= bits.length) :
    exists entry,
      ((canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper fieldWidth hbits).entries
          target)[occurrence]? = some entry := by
  have hindex : occurrence < canonicalSelectBlockCount bits := by
    unfold canonicalSelectBlockCount
    omega
  simpa using
    selectBlockDeltaEntries_present_of_lt
      target bits (wordSize := wordSize)
      (occurrencesPerSuper := occurrencesPerSuper)
      (count := canonicalSelectBlockCount bits)
      (occurrence := occurrence) hindex

theorem canonicalSelectSuperTablesFinite_getOpt_exact
    {bits : List Bool} {wordSize occurrencesPerSuper fieldWidth i : Nat}
    {target : Bool} {entry : Option SuccinctSpace.StoredWordSelectSample}
    {hbits : bits.length < 2 ^ fieldWidth}
    (hget :
      ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper fieldWidth hbits).entries
          target)[i]? = some entry) :
    entry =
      selectSuperSampleEntry?
        target bits wordSize occurrencesPerSuper i := by
  have hget' :
      (selectSuperSampleEntries target bits wordSize occurrencesPerSuper
        (canonicalSelectSuperCount bits occurrencesPerSuper))[i]? =
          some entry := by
    simpa using hget
  exact
    selectSuperSampleEntries_getOpt_exact
      (target := target) (bits := bits)
      (wordSize := wordSize)
      (occurrencesPerSuper := occurrencesPerSuper)
      (count := canonicalSelectSuperCount bits occurrencesPerSuper)
      (i := i) hget'

theorem canonicalSelectBlockTablesFinite_getOpt_exact
    {bits : List Bool} {wordSize occurrencesPerSuper fieldWidth
      occurrence : Nat}
    {target : Bool} {entry : Option SuccinctSpace.StoredWordSelectSample}
    {hbits : bits.length < 2 ^ fieldWidth}
    (hget :
      ((canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper fieldWidth hbits).entries
          target)[occurrence]? = some entry) :
    entry =
      selectBlockDeltaEntry?
        target bits wordSize occurrencesPerSuper occurrence := by
  have hget' :
      (selectBlockDeltaEntries target bits wordSize occurrencesPerSuper
        (canonicalSelectBlockCount bits))[occurrence]? = some entry := by
    simpa using hget
  exact
    selectBlockDeltaEntries_getOpt_exact
      (target := target) (bits := bits)
      (wordSize := wordSize)
      (occurrencesPerSuper := occurrencesPerSuper)
      (count := canonicalSelectBlockCount bits)
      (occurrence := occurrence) hget'

theorem selectFrom_index_mono
    {target : Bool} {bits : List Bool} {base lo hi posLo posHi : Nat}
    (hle : lo <= hi)
    (hlo : RMQ.Succinct.selectFrom target bits base lo = some posLo)
    (hhi : RMQ.Succinct.selectFrom target bits base hi = some posHi) :
    posLo <= posHi := by
  induction bits generalizing base lo hi posLo posHi with
  | nil =>
      simp [RMQ.Succinct.selectFrom] at hlo
  | cons bit rest ih =>
      by_cases hbit : bit = target
      · by_cases hlozero : lo = 0
        · subst lo
          simp [RMQ.Succinct.selectFrom, hbit] at hlo
          subst posLo
          exact (RMQ.Succinct.selectFrom_bounds hhi).left
        · have hhizero : hi ≠ 0 := by omega
          have htail : lo - 1 <= hi - 1 := by omega
          have hloTail :
              RMQ.Succinct.selectFrom target rest (base + 1) (lo - 1) =
                some posLo := by
            simpa [RMQ.Succinct.selectFrom, hbit, hlozero] using hlo
          have hhiTail :
              RMQ.Succinct.selectFrom target rest (base + 1) (hi - 1) =
                some posHi := by
            simpa [RMQ.Succinct.selectFrom, hbit, hhizero] using hhi
          exact ih htail hloTail hhiTail
      · have hloTail :
            RMQ.Succinct.selectFrom target rest (base + 1) lo =
              some posLo := by
          simpa [RMQ.Succinct.selectFrom, hbit] using hlo
        have hhiTail :
            RMQ.Succinct.selectFrom target rest (base + 1) hi =
              some posHi := by
          simpa [RMQ.Succinct.selectFrom, hbit] using hhi
        exact ih hle hloTail hhiTail

theorem select_index_mono
    {target : Bool} {bits : List Bool} {lo hi posLo posHi : Nat}
    (hle : lo <= hi)
    (hlo : RMQ.Succinct.select target bits lo = some posLo)
    (hhi : RMQ.Succinct.select target bits hi = some posHi) :
    posLo <= posHi := by
  unfold RMQ.Succinct.select at *
  exact selectFrom_index_mono hle hlo hhi

theorem select_index_strict_mono
    {target : Bool} {bits : List Bool} {lo hi posLo posHi : Nat}
    (hlt : lo < hi)
    (hlo : RMQ.Succinct.select target bits lo = some posLo)
    (hhi : RMQ.Succinct.select target bits hi = some posHi) :
    posLo < posHi := by
  have hle : posLo <= posHi :=
    select_index_mono (Nat.le_of_lt hlt) hlo hhi
  have hne : posLo ≠ posHi := by
    intro heq
    have hloRank := rankPrefix_succ_of_select hlo
    have hhiRank := rankPrefix_succ_of_select hhi
    rw [← heq] at hhiRank
    omega
  exact Nat.lt_of_le_of_ne hle hne

theorem selectSampleAt?_sample_ordered_of_occurrence_le
    {target : Bool} {bits : List Bool}
    {wordSize baseOccurrence occurrence : Nat}
    {base exact : SuccinctSpace.StoredWordSelectSample}
    (hle : baseOccurrence <= occurrence)
    (hbase :
      selectSampleAt? target bits wordSize baseOccurrence = some base)
    (hexact :
      selectSampleAt? target bits wordSize occurrence = some exact) :
    base.wordIndex <= exact.wordIndex /\
      base.wordStart <= exact.wordStart /\
        base.rankBefore <= exact.rankBefore := by
  rcases selectSampleAt?_some_fields hbase with
    ⟨basePos, hbaseSelect, rfl⟩
  rcases selectSampleAt?_some_fields hexact with
    ⟨exactPos, hexactSelect, rfl⟩
  have hpos : basePos <= exactPos :=
    select_index_mono hle hbaseSelect hexactSelect
  have hwordIndex : basePos / wordSize <= exactPos / wordSize :=
    Nat.div_le_div_right hpos
  have hwordStart :
      selectWordStart wordSize basePos <=
        selectWordStart wordSize exactPos := by
    unfold selectWordStart
    exact Nat.mul_le_mul_right wordSize hwordIndex
  have hrankBefore :
      RMQ.Succinct.rankPrefix target bits
          (selectWordStart wordSize basePos) <=
        RMQ.Succinct.rankPrefix target bits
          (selectWordStart wordSize exactPos) :=
    SuccinctRankProposal.rankPrefix_mono_limit target bits hwordStart
  simp [selectSampleOfSelectedPos, hwordIndex, hwordStart, hrankBefore]

theorem selectSuperSampleEntry?_sample_ordered
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerSuper occurrence : Nat}
    {base exact : SuccinctSpace.StoredWordSelectSample}
    (hbase :
      selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
        (occurrence / occurrencesPerSuper) = some base)
    (hexact :
      selectSampleAt? target bits wordSize occurrence = some exact) :
    base.wordIndex <= exact.wordIndex /\
      base.wordStart <= exact.wordStart /\
        base.rankBefore <= exact.rankBefore := by
  unfold selectSuperSampleEntry? at hbase
  exact
    selectSampleAt?_sample_ordered_of_occurrence_le
      (target := target) (bits := bits) (wordSize := wordSize)
      (baseOccurrence :=
        selectSuperOccurrence occurrencesPerSuper
          (occurrence / occurrencesPerSuper))
      (occurrence := occurrence)
      (base := base) (exact := exact)
      (by
        unfold selectSuperOccurrence
        exact Nat.div_mul_le_self occurrence occurrencesPerSuper)
      hbase hexact

structure CanonicalSelectWordBridge
    (bits : List Bool) (wordSize occurrencesPerSuper : Nat)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize) :
    Prop where
  sample_ordered :
    forall (target : Bool) (occurrence : Nat)
        (base exact : SuccinctSpace.StoredWordSelectSample),
      occurrence <= bits.length ->
      selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
          (occurrence / occurrencesPerSuper) = some base ->
      selectSampleAt? target bits wordSize occurrence = some exact ->
        base.wordIndex <= exact.wordIndex /\
          base.wordStart <= exact.wordStart /\
            base.rankBefore <= exact.rankBefore
  word_present :
    forall (target : Bool) (occurrence : Nat)
        (exact : SuccinctSpace.StoredWordSelectSample),
      occurrence <= bits.length ->
      selectSampleAt? target bits wordSize occurrence = some exact ->
        exists word,
          bitWords.store.words[exact.wordIndex]? = some word
  word_exact :
    forall (target : Bool) (occurrence : Nat)
        (exact : SuccinctSpace.StoredWordSelectSample) (word : List Bool),
      occurrence <= bits.length ->
      selectSampleAt? target bits wordSize occurrence = some exact ->
      bitWords.store.words[exact.wordIndex]? = some word ->
        SelectSampleWordExact target bits occurrence exact word

def CanonicalSelectWordBridge.ofLocal
    {bits : List Bool} {wordSize occurrencesPerSuper : Nat}
    {bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize}
    (hwordPresent :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
          exists word,
            bitWords.store.words[exact.wordIndex]? = some word)
    (hwordExact :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample) (word : List Bool),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
        bitWords.store.words[exact.wordIndex]? = some word ->
          SelectSampleWordExact target bits occurrence exact word) :
    CanonicalSelectWordBridge bits wordSize occurrencesPerSuper bitWords where
  sample_ordered := by
    intro target occurrence base exact _hocc hbase hexact
    exact selectSuperSampleEntry?_sample_ordered hbase hexact
  word_present := hwordPresent
  word_exact := hwordExact

theorem selectSampleAt?_word_present_ofChunks
    {target : Bool} {bits : List Bool} {wordSize occurrence : Nat}
    {exact : SuccinctSpace.StoredWordSelectSample}
    (hwordSize : 0 < wordSize)
    (_hocc : occurrence <= bits.length)
    (hexact :
      selectSampleAt? target bits wordSize occurrence = some exact) :
    exists word,
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
          bits hwordSize).store.words[exact.wordIndex]? = some word := by
  rcases selectSampleAt?_some_fields hexact with
    ⟨pos, hselect, rfl⟩
  have hpos : pos < bits.length := RMQ.Succinct.select_bounds hselect
  have hstart_lt : (pos / wordSize) * wordSize < bits.length :=
    Nat.lt_of_le_of_lt (Nat.div_mul_le_self pos wordSize) hpos
  rcases
      SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
        (payload := bits) hwordSize hstart_lt with
    ⟨word, hword⟩
  exact Exists.intro word (by
    simpa [SuccinctSpace.BoundedPayloadWordStore.ofChunks,
      selectSampleOfSelectedPos, Array.getElem?_toList] using hword)

theorem selectSampleAt?_word_eq_take_drop_ofChunks
    {target : Bool} {bits word : List Bool}
    {wordSize occurrence : Nat}
    {exact : SuccinctSpace.StoredWordSelectSample}
    (hwordSize : 0 < wordSize)
    (hexact :
      selectSampleAt? target bits wordSize occurrence = some exact)
    (hword :
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
          bits hwordSize).store.words[exact.wordIndex]? = some word) :
    word = (bits.drop exact.wordStart).take wordSize := by
  rcases selectSampleAt?_some_fields hexact with
    ⟨pos, _hselect, rfl⟩
  have hget :
      (SuccinctSpace.chunkPayloadWords wordSize bits)[pos / wordSize]? =
        some word := by
    simpa [SuccinctSpace.BoundedPayloadWordStore.ofChunks,
      selectSampleOfSelectedPos, Array.getElem?_toList] using hword
  have hchunk :=
    SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hget
  simpa [selectSampleOfSelectedPos, selectWordStart] using hchunk

theorem selectSampleAt?_slice_word_exact
    {target : Bool} {bits word : List Bool}
    {wordSize occurrence : Nat}
    {exact : SuccinctSpace.StoredWordSelectSample}
    (hwordSize : 0 < wordSize)
    (hexact :
      selectSampleAt? target bits wordSize occurrence = some exact)
    (hword : word = (bits.drop exact.wordStart).take wordSize) :
    SelectSampleWordExact target bits occurrence exact word := by
  rcases selectSampleAt?_some_fields hexact with
    ⟨pos, hselect, rfl⟩
  have hstart_le :
      selectWordStart wordSize pos <= pos := by
    unfold selectWordStart
    exact Nat.div_mul_le_self pos wordSize
  have hpos_hi :
      pos < selectWordStart wordSize pos + wordSize := by
    have hdecomp : (pos / wordSize) * wordSize + pos % wordSize = pos :=
      by
        rw [Nat.mul_comm]
        exact Nat.div_add_mod pos wordSize
    have hmod_lt : pos % wordSize < wordSize :=
      Nat.mod_lt pos hwordSize
    unfold selectWordStart
    omega
  have hstartLen :
      selectWordStart wordSize pos <= bits.length := by
    have hposLen : pos < bits.length :=
      RMQ.Succinct.select_bounds hselect
    exact Nat.le_trans hstart_le (Nat.le_of_lt hposLen)
  have hrank :
      RMQ.Succinct.rankPrefix target bits
          (selectWordStart wordSize pos) <= occurrence :=
    RMQ.Succinct.rankPrefix_le_occurrence_of_le_select
      hselect hstart_le
  have hlocal :
      RMQ.Succinct.select target
          ((bits.drop (selectWordStart wordSize pos)).take wordSize)
          (occurrence -
            RMQ.Succinct.rankPrefix target bits
              (selectWordStart wordSize pos)) =
        some (pos - selectWordStart wordSize pos) :=
    RMQ.Succinct.select_drop_take_eq_sub_of_select
      hselect hstart_le hpos_hi hstartLen hrank
  unfold SelectSampleWordExact
  simp [selectSampleOfSelectedPos, hword,
    RMQ.Succinct.ram_boolSelectInWord_eq_select, hlocal, hselect]
  omega

def CanonicalSelectWordBridge.ofChunks
    {bits : List Bool} {wordSize occurrencesPerSuper : Nat}
    (hwordSize : 0 < wordSize)
    (hwordExact :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample) (word : List Bool),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
        (SuccinctSpace.BoundedPayloadWordStore.ofChunks
            bits hwordSize).store.words[exact.wordIndex]? = some word ->
          SelectSampleWordExact target bits occurrence exact word) :
  CanonicalSelectWordBridge bits wordSize occurrencesPerSuper
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hwordSize) :=
  CanonicalSelectWordBridge.ofLocal
    (fun _target _occurrence _exact hocc hexact =>
      selectSampleAt?_word_present_ofChunks hwordSize hocc hexact)
    hwordExact

def CanonicalSelectWordBridge.ofChunksSlice
    {bits : List Bool} {wordSize occurrencesPerSuper : Nat}
    (hwordSize : 0 < wordSize)
    (hwordExact :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample) (word : List Bool),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
        word = (bits.drop exact.wordStart).take wordSize ->
          SelectSampleWordExact target bits occurrence exact word) :
    CanonicalSelectWordBridge bits wordSize occurrencesPerSuper
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hwordSize) :=
  CanonicalSelectWordBridge.ofChunks hwordSize
    (fun target occurrence exact word hocc hexact hword =>
      hwordExact target occurrence exact word hocc hexact
        (selectSampleAt?_word_eq_take_drop_ofChunks
          hwordSize hexact hword))

def CanonicalSelectWordBridge.ofChunksExact
    {bits : List Bool} {wordSize occurrencesPerSuper : Nat}
    (hwordSize : 0 < wordSize) :
    CanonicalSelectWordBridge bits wordSize occurrencesPerSuper
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hwordSize) :=
  CanonicalSelectWordBridge.ofChunksSlice hwordSize
    (fun _target _occurrence _exact _word _hocc hexact hword =>
      selectSampleAt?_slice_word_exact hwordSize hexact hword)

/-!
## Clark occurrence-count chunks

A Clark-style select directory samples by occurrence count.  The positive local
case is a chunk whose selected occurrences all remain in the same payload word
as the chunk base: one sampled locator plus the final word-select primitive is
then enough.  The companion obstruction below records exactly why a compact
builder needs a dense/sparse local route once a chunk crosses a payload-word
boundary.
-/

def clarkSelectChunkBase
    (occurrencesPerChunk occurrence : Nat) : Nat :=
  (occurrence / occurrencesPerChunk) * occurrencesPerChunk

def clarkSelectChunkOffset
    (occurrencesPerChunk occurrence : Nat) : Nat :=
  occurrence - clarkSelectChunkBase occurrencesPerChunk occurrence

theorem clarkSelectChunkBase_le
    (occurrencesPerChunk occurrence : Nat) :
    clarkSelectChunkBase occurrencesPerChunk occurrence <= occurrence := by
  unfold clarkSelectChunkBase
  exact Nat.div_mul_le_self occurrence occurrencesPerChunk

theorem clarkSelectChunkOffset_lt
    {occurrencesPerChunk occurrence : Nat}
    (hchunk : 0 < occurrencesPerChunk) :
    clarkSelectChunkOffset occurrencesPerChunk occurrence <
      occurrencesPerChunk := by
  have hmod := Nat.mod_lt occurrence hchunk
  simpa [clarkSelectChunkOffset, clarkSelectChunkBase,
    Nat.mod_eq_sub_div_mul] using hmod

def ClarkSelectChunkOneWord
    (target : Bool) (bits : List Bool) (wordSize occurrencesPerChunk
      occurrence : Nat) : Prop :=
  forall {basePos pos : Nat},
    RMQ.Succinct.select target bits
        (clarkSelectChunkBase occurrencesPerChunk occurrence) =
      some basePos ->
    RMQ.Succinct.select target bits occurrence = some pos ->
      pos / wordSize = basePos / wordSize

def ClarkSelectTwoWordChunkCovers
    (target : Bool) (bits : List Bool) (wordSize descriptorIndex
      occurrencesPerChunk occurrence : Nat) : Prop :=
  occurrence <
      clarkSelectChunkBase occurrencesPerChunk occurrence +
        occurrencesPerChunk /\
    forall {pos : Nat},
      RMQ.Succinct.select target bits occurrence = some pos ->
        twoWordDescriptorBaseWordIndex descriptorIndex * wordSize <= pos /\
          pos <
            (twoWordDescriptorBaseWordIndex descriptorIndex + 2) * wordSize

theorem clarkSelectTwoWordChunk_descriptor_choice_exact
    {target : Bool} {bits : List Bool}
    {wordSize fieldWidth count descriptorIndex firstWordCount
      occurrencesPerChunk occurrence pos : Nat}
    (hfield : wordSize < 2 ^ fieldWidth)
    (hwordSize : 0 < wordSize)
    (hcover :
      ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
        occurrencesPerChunk occurrence)
    (hread :
      ((twoWordDescriptorFirstCountTables
          bits wordSize fieldWidth count hfield).sampleCosted
          target descriptorIndex).erase = some firstWordCount)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos) :
    twoWordDescriptorWordIndex
        (twoWordDescriptorBaseWordIndex descriptorIndex)
        (RMQ.Succinct.rankPrefix target bits
          (twoWordDescriptorBaseWordIndex descriptorIndex * wordSize))
        firstWordCount occurrence =
      pos / wordSize := by
  rcases hcover with ⟨_hchunk, hcovered⟩
  rcases hcovered hselect with ⟨hlo, hhi⟩
  exact
    twoWordDescriptorTableRead_choice_exact_of_select_in_run
      hfield hwordSize hread hselect hlo hhi

def clarkSelectTwoWordDescriptorSample
    (target : Bool) (bits : List Bool) (wordSize descriptorIndex
      firstWordCount occurrence : Nat) :
    SuccinctSpace.StoredWordSelectSample :=
  let wordIndex :=
    twoWordDescriptorWordIndex
      (twoWordDescriptorBaseWordIndex descriptorIndex)
      (RMQ.Succinct.rankPrefix target bits
        (twoWordDescriptorBaseWordIndex descriptorIndex * wordSize))
      firstWordCount occurrence
  { wordIndex := wordIndex
    wordStart := wordIndex * wordSize
    rankBefore :=
      RMQ.Succinct.rankPrefix target bits (wordIndex * wordSize) }

theorem clarkSelectTwoWordDescriptorSample_eq_selected
    {target : Bool} {bits : List Bool}
    {wordSize fieldWidth count descriptorIndex firstWordCount
      occurrencesPerChunk occurrence pos : Nat}
    (hfield : wordSize < 2 ^ fieldWidth)
    (hwordSize : 0 < wordSize)
    (hcover :
      ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
        occurrencesPerChunk occurrence)
    (hread :
      ((twoWordDescriptorFirstCountTables
          bits wordSize fieldWidth count hfield).sampleCosted
          target descriptorIndex).erase = some firstWordCount)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos) :
    clarkSelectTwoWordDescriptorSample target bits wordSize descriptorIndex
        firstWordCount occurrence =
      selectSampleOfSelectedPos target bits wordSize pos := by
  have hwordIndex :
      twoWordDescriptorWordIndex
          (twoWordDescriptorBaseWordIndex descriptorIndex)
          (RMQ.Succinct.rankPrefix target bits
            (twoWordDescriptorBaseWordIndex descriptorIndex * wordSize))
          firstWordCount occurrence =
        pos / wordSize :=
    clarkSelectTwoWordChunk_descriptor_choice_exact
      hfield hwordSize hcover hread hselect
  simp [clarkSelectTwoWordDescriptorSample, selectSampleOfSelectedPos,
    selectWordStart, hwordIndex]

theorem clarkSelectTwoWordChunk_descriptor_sample_exact
    {target : Bool} {bits word : List Bool}
    {wordSize fieldWidth count descriptorIndex firstWordCount
      occurrencesPerChunk occurrence pos : Nat}
    (hfield : wordSize < 2 ^ fieldWidth)
    (hwordSize : 0 < wordSize)
    (hcover :
      ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
        occurrencesPerChunk occurrence)
    (hread :
      ((twoWordDescriptorFirstCountTables
          bits wordSize fieldWidth count hfield).sampleCosted
          target descriptorIndex).erase = some firstWordCount)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hword :
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
          bits hwordSize).store.words[
            (clarkSelectTwoWordDescriptorSample target bits wordSize
              descriptorIndex firstWordCount occurrence).wordIndex]? =
        some word) :
    SelectSampleWordExact target bits occurrence
      (clarkSelectTwoWordDescriptorSample target bits wordSize
        descriptorIndex firstWordCount occurrence) word := by
  have hsampleEq :
      clarkSelectTwoWordDescriptorSample target bits wordSize
          descriptorIndex firstWordCount occurrence =
        selectSampleOfSelectedPos target bits wordSize pos :=
    clarkSelectTwoWordDescriptorSample_eq_selected
      hfield hwordSize hcover hread hselect
  have hqueryExact :
      selectSampleAt? target bits wordSize occurrence =
        some (clarkSelectTwoWordDescriptorSample target bits wordSize
          descriptorIndex firstWordCount occurrence) := by
    simp [selectSampleAt?, hselect, hsampleEq]
  have hwordSlice :
      word =
        (bits.drop
          (clarkSelectTwoWordDescriptorSample target bits wordSize
            descriptorIndex firstWordCount occurrence).wordStart).take
          wordSize :=
    selectSampleAt?_word_eq_take_drop_ofChunks
      hwordSize hqueryExact hword
  exact selectSampleAt?_slice_word_exact
    hwordSize hqueryExact hwordSlice

def clarkSelectTwoWordDescriptorIndexOfPos
    (wordSize pos : Nat) : Nat :=
  pos / (2 * wordSize)

def clarkSelectTwoWordDescriptorIndexOfOccurrence
    (target : Bool) (bits : List Bool) (wordSize occurrence : Nat) :
    Nat :=
  match RMQ.Succinct.select target bits occurrence with
  | none => 0
  | some pos => clarkSelectTwoWordDescriptorIndexOfPos wordSize pos

def clarkSelectTwoWordDescriptorIndexEntries
    (target : Bool) (bits : List Bool) (wordSize count : Nat) :
    List Nat :=
  (List.range count).map
    (fun occurrence =>
      clarkSelectTwoWordDescriptorIndexOfOccurrence
        target bits wordSize occurrence)

theorem clarkSelectTwoWordDescriptorIndexOfPos_covers
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerChunk occurrence pos descriptorIndex : Nat}
    (hwordSize : 0 < wordSize)
    (hchunk : 0 < occurrencesPerChunk)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hdescriptor :
      descriptorIndex =
        clarkSelectTwoWordDescriptorIndexOfPos wordSize pos) :
    ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
      occurrencesPerChunk occurrence := by
  constructor
  · have hbase := clarkSelectChunkBase_le occurrencesPerChunk occurrence
    have hoff :=
      clarkSelectChunkOffset_lt
        (occurrencesPerChunk := occurrencesPerChunk)
        (occurrence := occurrence) hchunk
    unfold clarkSelectChunkOffset at hoff
    omega
  · intro pos' hselect'
    rw [hselect] at hselect'
    injection hselect' with hposEq
    subst pos'
    subst descriptorIndex
    have hden : 0 < wordSize * 2 := by omega
    constructor
    · have hlo :
          (pos / (wordSize * 2)) * (wordSize * 2) <= pos :=
        Nat.div_mul_le_self pos (wordSize * 2)
      have hnorm :
          twoWordDescriptorBaseWordIndex
              (clarkSelectTwoWordDescriptorIndexOfPos wordSize pos) *
            wordSize =
          (pos / (wordSize * 2)) * (wordSize * 2) := by
        simp [clarkSelectTwoWordDescriptorIndexOfPos,
          twoWordDescriptorBaseWordIndex, Nat.mul_assoc, Nat.mul_comm]
      simpa [hnorm] using hlo
    · have hhi :
          pos <
            (pos / (wordSize * 2)) * (wordSize * 2) +
              (wordSize * 2) :=
        Nat.lt_div_mul_add hden (a := pos)
      have hnorm :
          (pos / (wordSize * 2)) * (wordSize * 2) +
              (wordSize * 2) =
            (twoWordDescriptorBaseWordIndex
                (clarkSelectTwoWordDescriptorIndexOfPos wordSize pos) + 2) *
              wordSize := by
        simp [clarkSelectTwoWordDescriptorIndexOfPos,
          twoWordDescriptorBaseWordIndex, Nat.mul_add, Nat.mul_assoc,
          Nat.mul_comm]
      simpa [hnorm] using hhi

/-- Compatibility name for the neutral generic charged select source. -/
abbrev ChargedSelectPositionSource
    (target : Bool) (bits : List Bool)
    (overhead : Nat -> Nat) (queryCost : Nat) :=
  RMQ.GenericSelect.ChargedSelectPositionSource
    target bits overhead queryCost

namespace ChargedSelectPositionSource

def descriptorIndexCosted
    {target : Bool} {bits : List Bool}
    {overhead : Nat -> Nat} {queryCost : Nat}
    (source :
      ChargedSelectPositionSource target bits overhead queryCost)
    (wordSize occurrence : Nat) : Costed (Option Nat) :=
  Costed.map
    (fun pos? =>
      pos?.map
        (fun pos =>
          clarkSelectTwoWordDescriptorIndexOfPos wordSize pos))
    (source.selectPositionCosted occurrence)

theorem descriptorIndexCosted_cost_le
    {target : Bool} {bits : List Bool}
    {overhead : Nat -> Nat} {queryCost : Nat}
    (source :
      ChargedSelectPositionSource target bits overhead queryCost)
    (wordSize occurrence : Nat) :
    (source.descriptorIndexCosted wordSize occurrence).cost <=
      queryCost := by
  rw [descriptorIndexCosted, Costed.map_cost]
  exact source.selectPositionCosted_cost_le occurrence

theorem descriptorIndexCosted_erase
    {target : Bool} {bits : List Bool}
    {overhead : Nat -> Nat} {queryCost : Nat}
    (source :
      ChargedSelectPositionSource target bits overhead queryCost)
    (wordSize occurrence : Nat) :
    (source.descriptorIndexCosted wordSize occurrence).erase =
      (RMQ.Succinct.select target bits occurrence).map
        (fun pos =>
          clarkSelectTwoWordDescriptorIndexOfPos wordSize pos) := by
  rw [descriptorIndexCosted, Costed.erase_map]
  rw [source.selectPositionCosted_exact occurrence]

theorem descriptorIndexCosted_covers
    {target : Bool} {bits : List Bool}
    {overhead : Nat -> Nat} {queryCost : Nat}
    (source :
      ChargedSelectPositionSource target bits overhead queryCost)
    {wordSize occurrencesPerChunk occurrence descriptorIndex : Nat}
    (hwordSize : 0 < wordSize)
    (hchunk : 0 < occurrencesPerChunk)
    (hread :
      (source.descriptorIndexCosted wordSize occurrence).erase =
        some descriptorIndex) :
    ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
      occurrencesPerChunk occurrence := by
  rw [source.descriptorIndexCosted_erase wordSize occurrence] at hread
  cases hselect : RMQ.Succinct.select target bits occurrence with
  | none =>
      simp [hselect] at hread
  | some pos =>
      simp [hselect] at hread
      exact
        clarkSelectTwoWordDescriptorIndexOfPos_covers
          (target := target) (bits := bits) (wordSize := wordSize)
          (occurrencesPerChunk := occurrencesPerChunk)
          (occurrence := occurrence) (pos := pos)
          (descriptorIndex := descriptorIndex)
          hwordSize hchunk hselect hread.symm

theorem descriptorIndexCosted_profile
    {target : Bool} {bits : List Bool}
    {overhead : Nat -> Nat} {queryCost : Nat}
    (source :
      ChargedSelectPositionSource target bits overhead queryCost)
    {wordSize occurrencesPerChunk : Nat}
    (hwordSize : 0 < wordSize)
    (hchunk : 0 < occurrencesPerChunk) :
    source.payload.length <= overhead source.domainSize /\
      SuccinctSpace.LittleOLinear overhead /\
      (forall occurrence,
        (source.descriptorIndexCosted wordSize occurrence).cost <=
          queryCost) /\
      (forall occurrence,
        (source.descriptorIndexCosted wordSize occurrence).erase =
          (RMQ.Succinct.select target bits occurrence).map
            (fun pos =>
              clarkSelectTwoWordDescriptorIndexOfPos wordSize pos)) /\
      (forall {occurrence descriptorIndex : Nat},
        (source.descriptorIndexCosted wordSize occurrence).erase =
          some descriptorIndex ->
          ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
            occurrencesPerChunk occurrence) /\
      forall {word : List Bool},
        List.Mem word source.readWords ->
          word.length <= SuccinctRankProposal.machineWordBits bits.length := by
  exact
    ⟨source.payload_length_le, source.overhead_littleO,
      source.descriptorIndexCosted_cost_le wordSize,
      source.descriptorIndexCosted_erase wordSize,
      fun {occurrence descriptorIndex} hread =>
        source.descriptorIndexCosted_covers hwordSize hchunk hread,
      source.read_word_length_le_machine⟩

theorem descriptorIndexCosted_table_backed_sample_exact
    {target : Bool} {bits word : List Bool}
    {overhead : Nat -> Nat} {queryCost : Nat}
    (source :
      ChargedSelectPositionSource target bits overhead queryCost)
    {wordSize fieldWidth count occurrencesPerChunk occurrence pos
      descriptorIndex firstWordCount : Nat}
    (hfield : wordSize < 2 ^ fieldWidth)
    (hwordSize : 0 < wordSize)
    (hchunk : 0 < occurrencesPerChunk)
    (hdescriptorRead :
      (source.descriptorIndexCosted wordSize occurrence).erase =
        some descriptorIndex)
    (hfirstRead :
      ((twoWordDescriptorFirstCountTables
          bits wordSize fieldWidth count hfield).sampleCosted
          target descriptorIndex).erase = some firstWordCount)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hword :
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
          bits hwordSize).store.words[
            (clarkSelectTwoWordDescriptorSample target bits wordSize
              descriptorIndex firstWordCount occurrence).wordIndex]? =
        some word) :
    SelectSampleWordExact target bits occurrence
      (clarkSelectTwoWordDescriptorSample target bits wordSize
        descriptorIndex firstWordCount occurrence) word := by
  have hcover :
      ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
        occurrencesPerChunk occurrence :=
    source.descriptorIndexCosted_covers hwordSize hchunk hdescriptorRead
  exact
    clarkSelectTwoWordChunk_descriptor_sample_exact
      hfield hwordSize hcover hfirstRead hselect hword

end ChargedSelectPositionSource

theorem chargedSelectPositionSource_allows_empty_select_oracle
    (target : Bool) (bits : List Bool) :
    Nonempty (ChargedSelectPositionSource target bits (fun _ => 0) 0) := by
  refine
    ⟨{ domainSize := bits.length
       payload := []
       readWords := []
       selectPositionCosted := fun occurrence =>
         Costed.pure (RMQ.Succinct.select target bits occurrence)
       payload_length_le := by
         simp
       overhead_littleO := SuccinctSpace.littleOLinear_zero
       selectPositionCosted_cost_le := by
         intro occurrence
         simp
       selectPositionCosted_exact := by
         intro occurrence
         simp
       read_word_length_le_machine := by
         intro word hmem
         cases hmem }⟩

theorem clarkSelectTwoWordDescriptorIndexEntries_mem_bound
    {target : Bool} {bits : List Bool} {wordSize count fieldWidth entry : Nat}
    (hbits : bits.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry
        (clarkSelectTwoWordDescriptorIndexEntries
          target bits wordSize count)) :
    entry < 2 ^ fieldWidth := by
  unfold clarkSelectTwoWordDescriptorIndexEntries at hmem
  rcases List.mem_map.mp hmem with ⟨occurrence, _hmem, rfl⟩
  unfold clarkSelectTwoWordDescriptorIndexOfOccurrence
  cases hselect : RMQ.Succinct.select target bits occurrence with
  | none =>
      exact Nat.pow_pos (by omega : 0 < 2)
  | some pos =>
      have hpos : pos < bits.length := RMQ.Succinct.select_bounds hselect
      exact Nat.lt_of_le_of_lt
        (Nat.div_le_self pos (2 * wordSize))
        (Nat.lt_trans hpos hbits)

structure ClarkSelectTwoWordDescriptorIndexTable
    (target : Bool) (bits : List Bool)
    (wordSize occurrencesPerChunk fieldWidth : Nat) where
  entries : List Nat
  table : SuccinctSpace.FixedWidthNatTable entries fieldWidth
  slotIndex : Nat -> Nat
  payload_length_le : table.payload.length <= entries.length * fieldWidth
  covers :
    forall {occurrence descriptorIndex : Nat},
      entries[slotIndex occurrence]? = some descriptorIndex ->
        ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
          occurrencesPerChunk occurrence

namespace ClarkSelectTwoWordDescriptorIndexTable

def readCosted
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerChunk fieldWidth : Nat}
    (table :
      ClarkSelectTwoWordDescriptorIndexTable target bits wordSize
        occurrencesPerChunk fieldWidth)
    (occurrence : Nat) : Costed (Option Nat) :=
  table.table.readCosted (table.slotIndex occurrence)

theorem readCosted_cost_le_one
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerChunk fieldWidth : Nat}
    (table :
      ClarkSelectTwoWordDescriptorIndexTable target bits wordSize
        occurrencesPerChunk fieldWidth)
    (occurrence : Nat) :
    (table.readCosted occurrence).cost <= 1 := by
  exact table.table.readCosted_cost_le_one _

theorem readCosted_erase
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerChunk fieldWidth : Nat}
    (table :
      ClarkSelectTwoWordDescriptorIndexTable target bits wordSize
        occurrencesPerChunk fieldWidth)
    (occurrence : Nat) :
    (table.readCosted occurrence).erase =
      table.entries[table.slotIndex occurrence]? := by
  simp [readCosted]

theorem readCosted_covers
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerChunk fieldWidth : Nat}
    (table :
      ClarkSelectTwoWordDescriptorIndexTable target bits wordSize
        occurrencesPerChunk fieldWidth)
    {occurrence descriptorIndex : Nat}
    (hread :
      (table.readCosted occurrence).erase = some descriptorIndex) :
    ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
      occurrencesPerChunk occurrence := by
  exact table.covers (by
    simpa [readCosted_erase] using hread)

theorem profile
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerChunk fieldWidth : Nat}
    (table :
      ClarkSelectTwoWordDescriptorIndexTable target bits wordSize
        occurrencesPerChunk fieldWidth) :
    table.table.payload.length <= table.entries.length * fieldWidth /\
      forall occurrence,
        (table.readCosted occurrence).cost <= 1 /\
          (table.readCosted occurrence).erase =
            table.entries[table.slotIndex occurrence]? := by
  exact ⟨table.payload_length_le,
    fun occurrence =>
      ⟨table.readCosted_cost_le_one occurrence,
        table.readCosted_erase occurrence⟩⟩

end ClarkSelectTwoWordDescriptorIndexTable

def clarkSelectTwoWordDescriptorIndexTable
    (target : Bool) (bits : List Bool)
    (wordSize occurrencesPerChunk fieldWidth count : Nat)
    (hwordSize : 0 < wordSize)
    (hchunk : 0 < occurrencesPerChunk)
    (hbits : bits.length < 2 ^ fieldWidth) :
    ClarkSelectTwoWordDescriptorIndexTable target bits wordSize
      occurrencesPerChunk fieldWidth where
  entries :=
    clarkSelectTwoWordDescriptorIndexEntries
      target bits wordSize count
  table :=
    SuccinctSpace.FixedWidthNatTable.ofEntries
      (clarkSelectTwoWordDescriptorIndexEntries
        target bits wordSize count)
      fieldWidth
      (fun hmem =>
        clarkSelectTwoWordDescriptorIndexEntries_mem_bound hbits hmem)
  slotIndex := fun occurrence => occurrence
  payload_length_le := by
    simp [SuccinctSpace.FixedWidthNatTable.payload_length]
  covers := by
    intro occurrence descriptorIndex hget
    constructor
    · have hbase :=
        clarkSelectChunkBase_le occurrencesPerChunk occurrence
      have hoff :=
        clarkSelectChunkOffset_lt
          (occurrencesPerChunk := occurrencesPerChunk)
          (occurrence := occurrence) hchunk
      unfold clarkSelectChunkOffset at hoff
      omega
    · intro pos hselect
      have hdescriptor :
          descriptorIndex =
            clarkSelectTwoWordDescriptorIndexOfPos wordSize pos := by
        unfold clarkSelectTwoWordDescriptorIndexEntries at hget
        by_cases hlt : occurrence < count
        · simp [List.getElem?_map, List.getElem?_range hlt,
            clarkSelectTwoWordDescriptorIndexOfOccurrence, hselect] at hget
          exact hget.symm
        · simp [hlt] at hget
      have hcover :=
        clarkSelectTwoWordDescriptorIndexOfPos_covers
          (target := target) (bits := bits) (wordSize := wordSize)
          (occurrencesPerChunk := occurrencesPerChunk)
          (occurrence := occurrence) (pos := pos)
          (descriptorIndex := descriptorIndex)
          hwordSize hchunk hselect hdescriptor
      exact hcover.2 hselect

theorem clarkSelectTwoWordDescriptorIndexTable_read_covers
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerChunk fieldWidth count occurrence
      descriptorIndex : Nat}
    (hwordSize : 0 < wordSize)
    (hchunk : 0 < occurrencesPerChunk)
    (hbits : bits.length < 2 ^ fieldWidth)
    (hread :
      ((clarkSelectTwoWordDescriptorIndexTable
          target bits wordSize occurrencesPerChunk fieldWidth count
          hwordSize hchunk hbits).readCosted occurrence).erase =
        some descriptorIndex) :
    ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
      occurrencesPerChunk occurrence := by
  exact
    (clarkSelectTwoWordDescriptorIndexTable
      target bits wordSize occurrencesPerChunk fieldWidth count
      hwordSize hchunk hbits).readCosted_covers hread

theorem clarkSelectTwoWordDescriptorIndexTable_profile
    (target : Bool) (bits : List Bool)
    {wordSize occurrencesPerChunk fieldWidth count : Nat}
    (hwordSize : 0 < wordSize)
    (hchunk : 0 < occurrencesPerChunk)
    (hbits : bits.length < 2 ^ fieldWidth) :
    let table :=
      clarkSelectTwoWordDescriptorIndexTable
        target bits wordSize occurrencesPerChunk fieldWidth count
        hwordSize hchunk hbits
    table.table.payload.length = count * fieldWidth /\
      (forall occurrence,
        (table.readCosted occurrence).cost <= 1 /\
          (table.readCosted occurrence).erase =
            table.entries[table.slotIndex occurrence]?) /\
      (forall {occurrence descriptorIndex : Nat},
        (table.readCosted occurrence).erase = some descriptorIndex ->
          ClarkSelectTwoWordChunkCovers target bits wordSize
            descriptorIndex occurrencesPerChunk occurrence) := by
  intro table
  constructor
  · simp [table, clarkSelectTwoWordDescriptorIndexTable,
      clarkSelectTwoWordDescriptorIndexEntries,
      SuccinctSpace.FixedWidthNatTable.payload_length]
  · constructor
    · exact (table.profile).2
    · intro occurrence descriptorIndex hread
      exact table.readCosted_covers hread

theorem clarkSelectTwoWordIdentityDescriptorRoute_profile
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerChunk fieldWidth occurrence pos : Nat}
    (hwordSize : 0 < wordSize)
    (hchunk : 0 < occurrencesPerChunk)
    (hbits : bits.length < 2 ^ fieldWidth)
    (hfield : wordSize < 2 ^ fieldWidth)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos) :
    let descriptorTable :=
      clarkSelectTwoWordDescriptorIndexTable
        target bits wordSize occurrencesPerChunk fieldWidth
        (bits.length + 1) hwordSize hchunk hbits
    exists descriptorIndex firstWordCount,
      (descriptorTable.readCosted occurrence).cost <= 1 /\
        (descriptorTable.readCosted occurrence).erase =
          some descriptorIndex /\
        ((twoWordDescriptorFirstCountTables
            bits wordSize fieldWidth (bits.length + 1) hfield).sampleCosted
            target descriptorIndex).cost <= 1 /\
        ((twoWordDescriptorFirstCountTables
            bits wordSize fieldWidth (bits.length + 1) hfield).sampleCosted
            target descriptorIndex).erase = some firstWordCount /\
        ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
          occurrencesPerChunk occurrence /\
        twoWordDescriptorWordIndex
            (twoWordDescriptorBaseWordIndex descriptorIndex)
            (RMQ.Succinct.rankPrefix target bits
              (twoWordDescriptorBaseWordIndex descriptorIndex * wordSize))
            firstWordCount occurrence =
          pos / wordSize := by
  intro descriptorTable
  let descriptorIndex :=
    clarkSelectTwoWordDescriptorIndexOfPos wordSize pos
  have hdescriptor_lt :
      descriptorIndex < bits.length + 1 := by
    have hpos : pos < bits.length := RMQ.Succinct.select_bounds hselect
    exact Nat.lt_succ_of_le
      (Nat.le_trans
        (Nat.div_le_self pos (2 * wordSize))
        (Nat.le_of_lt hpos))
  have hocc_lt : occurrence < bits.length + 1 := by
    have hocc_rank := RMQ.Succinct.select_rankPrefix_eq hselect
    have hrank_le :
        RMQ.Succinct.rankPrefix target bits pos <= bits.length :=
      RMQ.Succinct.rankPrefix_le_length target bits pos
    omega
  have hdescriptorRead :
      (descriptorTable.readCosted occurrence).erase =
        some descriptorIndex := by
    simp [descriptorTable, clarkSelectTwoWordDescriptorIndexTable,
      ClarkSelectTwoWordDescriptorIndexTable.readCosted,
      SuccinctSpace.FixedWidthNatTable.readCosted_erase,
      clarkSelectTwoWordDescriptorIndexEntries,
      List.getElem?_map, List.getElem?_range hocc_lt,
      clarkSelectTwoWordDescriptorIndexOfOccurrence, hselect,
      descriptorIndex]
  have hcover :
      ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
        occurrencesPerChunk occurrence :=
    descriptorTable.readCosted_covers hdescriptorRead
  have hfirstRead :
      ((twoWordDescriptorFirstCountTables
          bits wordSize fieldWidth (bits.length + 1) hfield).sampleCosted
          target descriptorIndex).erase =
        some (twoWordDescriptorFirstCount
          target bits wordSize descriptorIndex) := by
    cases target <;>
      simp [twoWordDescriptorFirstCountTables,
        SuccinctSpace.FixedWidthRankSampleTables.sampleCosted,
        SuccinctSpace.FixedWidthNatTable.readCosted_erase,
        twoWordDescriptorFirstCountEntries,
        List.getElem?_map, List.getElem?_range hdescriptor_lt]
  refine
    ⟨descriptorIndex,
      twoWordDescriptorFirstCount target bits wordSize descriptorIndex,
      ?_, hdescriptorRead, ?_, hfirstRead, hcover, ?_⟩
  · exact descriptorTable.readCosted_cost_le_one occurrence
  · exact
      (twoWordDescriptorFirstCountTables
        bits wordSize fieldWidth (bits.length + 1) hfield).profile.2
        target descriptorIndex |>.1
  · exact
      clarkSelectTwoWordChunk_descriptor_choice_exact
        hfield hwordSize hcover hfirstRead hselect

theorem clarkSelectTwoWordChunk_table_backed_sample_exact
    {target : Bool} {bits word : List Bool}
    {wordSize fieldWidth count occurrencesPerChunk occurrence pos
      descriptorIndex firstWordCount : Nat}
    (descriptorTable :
      ClarkSelectTwoWordDescriptorIndexTable target bits wordSize
        occurrencesPerChunk fieldWidth)
    (hfield : wordSize < 2 ^ fieldWidth)
    (hwordSize : 0 < wordSize)
    (hdescriptorRead :
      (descriptorTable.readCosted occurrence).erase =
        some descriptorIndex)
    (hfirstRead :
      ((twoWordDescriptorFirstCountTables
          bits wordSize fieldWidth count hfield).sampleCosted
          target descriptorIndex).erase = some firstWordCount)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hword :
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
          bits hwordSize).store.words[
            (clarkSelectTwoWordDescriptorSample target bits wordSize
              descriptorIndex firstWordCount occurrence).wordIndex]? =
        some word) :
    SelectSampleWordExact target bits occurrence
      (clarkSelectTwoWordDescriptorSample target bits wordSize
        descriptorIndex firstWordCount occurrence) word := by
  have hcover :
      ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
        occurrencesPerChunk occurrence :=
    descriptorTable.readCosted_covers hdescriptorRead
  exact
    clarkSelectTwoWordChunk_descriptor_sample_exact
      hfield hwordSize hcover hfirstRead hselect hword

theorem shared_descriptor_index_forces_same_two_word_run
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerChunk descriptorIndex
      occurrenceA occurrenceB posA posB : Nat}
    (hcoverA :
      ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
        occurrencesPerChunk occurrenceA)
    (hcoverB :
      ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
        occurrencesPerChunk occurrenceB)
    (hselectA :
      RMQ.Succinct.select target bits occurrenceA = some posA)
    (hselectB :
      RMQ.Succinct.select target bits occurrenceB = some posB) :
    posA / (2 * wordSize) = posB / (2 * wordSize) := by
  rcases hcoverA with ⟨_hchunkA, hcoveredA⟩
  rcases hcoverB with ⟨_hchunkB, hcoveredB⟩
  rcases hcoveredA hselectA with ⟨hloA, hhiA⟩
  rcases hcoveredB hselectB with ⟨hloB, hhiB⟩
  have hspan :
      (twoWordDescriptorBaseWordIndex descriptorIndex + 2) * wordSize =
        (descriptorIndex + 1) * (2 * wordSize) := by
    simp [twoWordDescriptorBaseWordIndex, Nat.add_mul, Nat.mul_add,
      Nat.mul_comm, Nat.mul_left_comm]
  have hbase :
      twoWordDescriptorBaseWordIndex descriptorIndex * wordSize =
        descriptorIndex * (2 * wordSize) := by
    simp [twoWordDescriptorBaseWordIndex, Nat.mul_comm, Nat.mul_left_comm]
  have hA :
      posA / (2 * wordSize) = descriptorIndex := by
    exact Nat.div_eq_of_lt_le (by simpa [hbase] using hloA)
      (by simpa [hspan] using hhiA)
  have hB :
      posB / (2 * wordSize) = descriptorIndex := by
    exact Nat.div_eq_of_lt_le (by simpa [hbase] using hloB)
      (by simpa [hspan] using hhiB)
  exact hA.trans hB.symm

theorem shared_descriptor_index_contradicts_distinct_two_word_run
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerChunk descriptorIndex
      occurrenceA occurrenceB posA posB : Nat}
    (hcoverA :
      ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
        occurrencesPerChunk occurrenceA)
    (hcoverB :
      ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
        occurrencesPerChunk occurrenceB)
    (hselectA :
      RMQ.Succinct.select target bits occurrenceA = some posA)
    (hselectB :
      RMQ.Succinct.select target bits occurrenceB = some posB)
    (hdistinct :
      posA / (2 * wordSize) = posB / (2 * wordSize) -> False) :
    False := by
  exact hdistinct
    (shared_descriptor_index_forces_same_two_word_run
      hcoverA hcoverB hselectA hselectB)

theorem shared_descriptor_table_read_contradicts_distinct_two_word_run
    {target : Bool} {bits : List Bool}
    {wordSize occurrencesPerChunk fieldWidth descriptorIndex
      occurrenceA occurrenceB posA posB : Nat}
    (descriptorTable :
      ClarkSelectTwoWordDescriptorIndexTable target bits wordSize
        occurrencesPerChunk fieldWidth)
    (hreadA :
      (descriptorTable.readCosted occurrenceA).erase =
        some descriptorIndex)
    (hreadB :
      (descriptorTable.readCosted occurrenceB).erase =
        some descriptorIndex)
    (hselectA :
      RMQ.Succinct.select target bits occurrenceA = some posA)
    (hselectB :
      RMQ.Succinct.select target bits occurrenceB = some posB)
    (hdistinct :
      posA / (2 * wordSize) = posB / (2 * wordSize) -> False) :
    False := by
  have hcoverA :
      ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
        occurrencesPerChunk occurrenceA :=
    descriptorTable.readCosted_covers hreadA
  have hcoverB :
      ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
        occurrencesPerChunk occurrenceB :=
    descriptorTable.readCosted_covers hreadB
  exact
    shared_descriptor_index_contradicts_distinct_two_word_run
      hcoverA hcoverB hselectA hselectB hdistinct

theorem selectSampleOfSelectedPos_eq_of_same_wordIndex
    {target : Bool} {bits : List Bool}
    {wordSize basePos pos : Nat}
    (hsame : pos / wordSize = basePos / wordSize) :
    selectSampleOfSelectedPos target bits wordSize pos =
      selectSampleOfSelectedPos target bits wordSize basePos := by
  simp [selectSampleOfSelectedPos, selectWordStart, hsame]

theorem clarkSelectChunkBaseSample_exact_of_one_word
    {target : Bool} {bits word : List Bool}
    {wordSize occurrencesPerChunk occurrence basePos pos : Nat}
    (hwordSize : 0 < wordSize)
    (hone :
      ClarkSelectChunkOneWord target bits wordSize occurrencesPerChunk
        occurrence)
    (hbase :
      RMQ.Succinct.select target bits
          (clarkSelectChunkBase occurrencesPerChunk occurrence) =
        some basePos)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hword :
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
          bits hwordSize).store.words[
            (selectSampleOfSelectedPos target bits wordSize basePos).wordIndex]? =
        some word) :
    SelectSampleWordExact target bits occurrence
      (selectSampleOfSelectedPos target bits wordSize basePos) word := by
  have hsame : pos / wordSize = basePos / wordSize :=
    hone hbase hselect
  have hbaseExact :
      selectSampleAt? target bits wordSize
          (clarkSelectChunkBase occurrencesPerChunk occurrence) =
        some (selectSampleOfSelectedPos target bits wordSize basePos) := by
    simp [selectSampleAt?, hbase]
  have hwordSlice :
      word =
        (bits.drop
            (selectSampleOfSelectedPos target bits wordSize basePos).wordStart).take
          wordSize :=
    selectSampleAt?_word_eq_take_drop_ofChunks
      hwordSize hbaseExact hword
  have hsampleEq :
      selectSampleOfSelectedPos target bits wordSize pos =
        selectSampleOfSelectedPos target bits wordSize basePos :=
    selectSampleOfSelectedPos_eq_of_same_wordIndex hsame
  have hqueryExact :
      selectSampleAt? target bits wordSize occurrence =
        some (selectSampleOfSelectedPos target bits wordSize basePos) := by
    simp [selectSampleAt?, hselect, hsampleEq]
  exact selectSampleAt?_slice_word_exact hwordSize hqueryExact hwordSlice

theorem clarkSelectChunk_payload_router_exact
    {target : Bool} {bits word : List Bool}
    {wordSize fieldWidth count occurrencesPerChunk occurrence pos : Nat}
    {sample : SuccinctSpace.StoredWordSelectSample}
    (hfield : wordSize < 2 ^ fieldWidth)
    (hwordSize : 0 < wordSize)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hroute :
      (exists basePos,
        ClarkSelectChunkOneWord target bits wordSize occurrencesPerChunk
          occurrence /\
        RMQ.Succinct.select target bits
            (clarkSelectChunkBase occurrencesPerChunk occurrence) =
          some basePos /\
        sample = selectSampleOfSelectedPos target bits wordSize basePos) \/
      (exists descriptorIndex firstWordCount,
        ClarkSelectTwoWordChunkCovers target bits wordSize descriptorIndex
          occurrencesPerChunk occurrence /\
        ((twoWordDescriptorFirstCountTables
            bits wordSize fieldWidth count hfield).sampleCosted
            target descriptorIndex).erase = some firstWordCount /\
        sample =
          clarkSelectTwoWordDescriptorSample target bits wordSize
            descriptorIndex firstWordCount occurrence))
    (hword :
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
          bits hwordSize).store.words[sample.wordIndex]? = some word) :
    SelectSampleWordExact target bits occurrence sample word := by
  rcases hroute with
    ⟨basePos, hone, hbase, rfl⟩ |
    ⟨descriptorIndex, firstWordCount, hcover, hread, rfl⟩
  · exact
      clarkSelectChunkBaseSample_exact_of_one_word
        hwordSize hone hbase hselect hword
  · exact
      clarkSelectTwoWordChunk_descriptor_sample_exact
        hfield hwordSize hcover hread hselect hword

theorem clarkSelectChunkBaseSample_exact_forces_same_wordIndex
    {target : Bool} {bits word : List Bool}
    {wordSize occurrence basePos pos : Nat}
    (hwordSize : 0 < wordSize)
    (hexact :
      SelectSampleWordExact target bits occurrence
        (selectSampleOfSelectedPos target bits wordSize basePos) word)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hwordLen : word.length <= wordSize) :
    pos / wordSize = basePos / wordSize := by
  have hstart :
      (selectSampleOfSelectedPos target bits wordSize basePos).wordStart =
        (selectSampleOfSelectedPos target bits wordSize basePos).wordIndex *
          wordSize := by
    rfl
  simpa [selectSampleOfSelectedPos] using
    SelectSampleWordExact.selected_wordIndex_eq_of_aligned_read_word
      hwordSize hexact hselect hstart hwordLen

theorem clarkSelectChunkBaseSample_cross_word_obstruction
    {target : Bool} {bits word : List Bool}
    {wordSize occurrence basePos pos : Nat}
    (hwordSize : 0 < wordSize)
    (hexact :
      SelectSampleWordExact target bits occurrence
        (selectSampleOfSelectedPos target bits wordSize basePos) word)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hwordLen : word.length <= wordSize)
    (hdiff : Not (pos / wordSize = basePos / wordSize)) :
    False := by
  exact hdiff
    (clarkSelectChunkBaseSample_exact_forces_same_wordIndex
      hwordSize hexact hselect hwordLen)

/-!
## Two-level select target

The older sampled wrapper below is useful migration scaffolding, but the final
word-RAM select story needs the same discipline as the rank side: payload words
must be machine-word bounded, and the query must be forced through counted
coarse-locator, local-delta, payload-word, and word-select operations.
-/

structure TwoLevelPayloadLiveStoredWordSelectData
    (bits : List Bool)
    (superOverhead blockOverhead queryCost : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  wordSize_le_machine :
    wordSize <= SuccinctRankProposal.machineWordBits bits.length
  occurrencesPerSuper : Nat
  occurrencesPerSuper_pos : 0 < occurrencesPerSuper
  /--
  Address used for the local locator table.  This is deliberately independent
  of the queried occurrence, so a concrete dense/sparse select codec is not
  forced to materialize one local table word at every occurrence index.
  -/
  blockIndex : Bool -> Nat -> Nat
  superFieldWidth : Nat
  blockFieldWidth : Nat
  superTrueEntries :
    List (Option SuccinctSpace.StoredWordSelectSample)
  superFalseEntries :
    List (Option SuccinctSpace.StoredWordSelectSample)
  blockTrueEntries :
    List (Option SuccinctSpace.StoredWordSelectSample)
  blockFalseEntries :
    List (Option SuccinctSpace.StoredWordSelectSample)
  superTables :
    SuccinctSpace.FixedWidthSelectSampleTables
      superTrueEntries superFalseEntries superFieldWidth
  blockTables :
    SuccinctSpace.FixedWidthSelectSampleTables
      blockTrueEntries blockFalseEntries blockFieldWidth
  bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize
  superPayload_length : superTables.payload.length = superOverhead
  blockPayload_length : blockTables.payload.length = blockOverhead
  queryCost_ge_four : 4 <= queryCost
  super_entry_present :
    forall (target : Bool) (occurrence : Nat),
      occurrence <= bits.length ->
      exists entry : Option SuccinctSpace.StoredWordSelectSample,
        (superTables.entries target)[occurrence / occurrencesPerSuper]? =
          some entry
  block_entry_present :
    forall (target : Bool) (occurrence : Nat),
      occurrence <= bits.length ->
      exists entry : Option SuccinctSpace.StoredWordSelectSample,
        (blockTables.entries target)[blockIndex target occurrence]? =
          some entry
  word_present_of_sample :
    forall (target : Bool) (occurrence : Nat)
        (super delta : SuccinctSpace.StoredWordSelectSample),
      occurrence <= bits.length ->
      (superTables.entries target)[occurrence / occurrencesPerSuper]? =
          some (some super) ->
      (blockTables.entries target)[blockIndex target occurrence]? =
          some (some delta) ->
        exists word,
          bitWords.store.words[(addSelectSample super delta).wordIndex]? =
            some word
  select_some_exact :
    forall (target : Bool) (occurrence : Nat)
        (super delta : SuccinctSpace.StoredWordSelectSample)
        (word : List Bool),
      occurrence <= bits.length ->
      (superTables.entries target)[occurrence / occurrencesPerSuper]? =
          some (some super) ->
      (blockTables.entries target)[blockIndex target occurrence]? =
          some (some delta) ->
      bitWords.store.words[(addSelectSample super delta).wordIndex]? =
          some word ->
        (RMQ.RAM.boolSelectInWord target word
            (occurrence - (addSelectSample super delta).rankBefore)).map
            (fun offset =>
              (addSelectSample super delta).wordStart + offset) =
          RMQ.Succinct.select target bits occurrence
  select_none_exact_of_super :
    forall (target : Bool) (occurrence : Nat),
      occurrence <= bits.length ->
      (superTables.entries target)[occurrence / occurrencesPerSuper]? =
          some (none : Option SuccinctSpace.StoredWordSelectSample) ->
        RMQ.Succinct.select target bits occurrence = none
  select_none_exact_of_block :
    forall (target : Bool) (occurrence : Nat)
        (super : SuccinctSpace.StoredWordSelectSample),
      occurrence <= bits.length ->
      (superTables.entries target)[occurrence / occurrencesPerSuper]? =
          some (some super) ->
      (blockTables.entries target)[blockIndex target occurrence]? =
          some (none : Option SuccinctSpace.StoredWordSelectSample) ->
        RMQ.Succinct.select target bits occurrence = none

namespace TwoLevelPayloadLiveStoredWordSelectData

def queryOccurrence
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (_data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (occurrence : Nat) : Nat :=
  Nat.min occurrence bits.length

def superIndex
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (occurrence : Nat) : Nat :=
  data.queryOccurrence occurrence / data.occurrencesPerSuper

def superPayload
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost) :
    List Bool :=
  data.superTables.payload

def blockPayload
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost) :
    List Bool :=
  data.blockTables.payload

def auxPayload
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost) :
    List Bool :=
  data.superPayload ++ data.blockPayload

def selectCosted
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (occurrence : Nat) :
    RMQ.Costed (Option Nat) :=
  RMQ.Costed.bind
    (data.superTables.sampleCosted target (data.superIndex occurrence))
    fun super? =>
      RMQ.Costed.bind
        (data.blockTables.sampleCosted target
          (data.blockIndex target (data.queryOccurrence occurrence)))
        fun delta? =>
          match super?, delta? with
          | some (some super), some (some delta) =>
              let sample := addSelectSample super delta
              RMQ.Costed.bind
                (data.bitWords.store.readWordCosted sample.wordIndex)
                fun word? =>
                  match word? with
                  | none => RMQ.Costed.pure none
                  | some word =>
                      RMQ.Costed.map
                        (fun (local? : Option Nat) =>
                          local?.map fun offset =>
                            sample.wordStart + offset)
                        (RMQ.RAM.selectBoolWord target word
                          (data.queryOccurrence occurrence -
                            sample.rankBefore)).toCosted
          | _, _ => RMQ.Costed.pure none

theorem auxPayload_length
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost) :
    data.auxPayload.length = superOverhead + blockOverhead := by
  simp [auxPayload, superPayload, blockPayload,
    data.superPayload_length, data.blockPayload_length]

theorem payload_words_erase
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost) :
    SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        bits := by
  exact data.bitWords.erases

set_option linter.unusedSimpArgs false in
theorem selectCosted_cost_le_four
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= 4 := by
  unfold selectCosted
  cases hsuper :
      (data.superTables.sampleCosted
        target (data.superIndex occurrence)).value <;>
    cases hdelta :
      (data.blockTables.sampleCosted
        target (data.blockIndex target
          (data.queryOccurrence occurrence))).value <;>
    try
      simp [RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
        hsuper, hdelta]
  case some.some superEntry deltaEntry =>
    cases superEntry <;> cases deltaEntry <;>
      try
        simp [RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
          hsuper, hdelta]
    case some.some super delta =>
      cases hword :
          (data.bitWords.store.readWordCosted
            (addSelectSample super delta).wordIndex).value <;>
        simp [RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
          hsuper, hdelta, hword]

theorem selectCosted_cost_le
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= queryCost := by
  exact Nat.le_trans
    (data.selectCosted_cost_le_four target occurrence)
    data.queryCost_ge_four

theorem selectCosted_exact
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      RMQ.Succinct.select target bits occurrence := by
  have hq : data.queryOccurrence occurrence <= bits.length := by
    exact Nat.min_le_right occurrence bits.length
  have hclamp :
      RMQ.Succinct.select target bits (data.queryOccurrence occurrence) =
        RMQ.Succinct.select target bits occurrence := by
    unfold queryOccurrence
    exact RMQ.Succinct.select_min_length_eq target bits occurrence
  rcases data.super_entry_present
      target (data.queryOccurrence occurrence) hq with
    ⟨superEntry, hsuper⟩
  rcases data.block_entry_present
      target (data.queryOccurrence occurrence) hq with
    ⟨deltaEntry, hdelta⟩
  have hsuperValue :
      (data.superTables.sampleCosted
        target (data.superIndex occurrence)).value = some superEntry := by
    have h :=
      data.superTables.sampleCosted_erase
        target (data.superIndex occurrence)
    change
      (data.superTables.sampleCosted
        target (data.superIndex occurrence)).value =
          (data.superTables.entries target)[data.superIndex occurrence]? at h
    rw [show data.superIndex occurrence =
        data.queryOccurrence occurrence / data.occurrencesPerSuper by rfl] at h
    rw [hsuper] at h
    exact h
  have hdeltaValue :
      (data.blockTables.sampleCosted
        target (data.blockIndex target
          (data.queryOccurrence occurrence))).value =
        some deltaEntry := by
    have h :=
      data.blockTables.sampleCosted_erase
        target (data.blockIndex target
          (data.queryOccurrence occurrence))
    change
      (data.blockTables.sampleCosted
        target (data.blockIndex target
          (data.queryOccurrence occurrence))).value =
        (data.blockTables.entries target)[
          data.blockIndex target (data.queryOccurrence occurrence)]? at h
    rw [hdelta] at h
    exact h
  cases superEntry with
  | none =>
      have hnoneQ :=
        data.select_none_exact_of_super
          target (data.queryOccurrence occurrence) hq hsuper
      have hnone :
          RMQ.Succinct.select target bits occurrence = none := by
        exact hclamp ▸ hnoneQ
      unfold selectCosted
      simp [RMQ.Costed.bind, RMQ.Costed.pure, RMQ.Costed.erase,
        hsuperValue, hdeltaValue, hnone]
  | some super =>
      cases deltaEntry with
      | none =>
          have hnoneQ :=
            data.select_none_exact_of_block
              target (data.queryOccurrence occurrence) super
              hq hsuper hdelta
          have hnone :
              RMQ.Succinct.select target bits occurrence = none := by
            exact hclamp ▸ hnoneQ
          unfold selectCosted
          simp [RMQ.Costed.bind, RMQ.Costed.pure, RMQ.Costed.erase,
            hsuperValue, hdeltaValue, hnone]
      | some delta =>
          rcases data.word_present_of_sample
              target (data.queryOccurrence occurrence) super delta
              hq hsuper hdelta with
            ⟨word, hword⟩
          have hwordValue :
              (data.bitWords.store.readWordCosted
                (addSelectSample super delta).wordIndex).value =
                  some word := by
            have hread :=
              data.bitWords.store.readWordCosted_erase
                (addSelectSample super delta).wordIndex
            change
              (data.bitWords.store.readWordCosted
                (addSelectSample super delta).wordIndex).value =
                  data.bitWords.store.words[
                    (addSelectSample super delta).wordIndex]? at hread
            rw [hword] at hread
            exact hread
          have hexact :=
            data.select_some_exact
              target (data.queryOccurrence occurrence) super delta word
              hq hsuper hdelta hword
          unfold selectCosted
          simp [RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
            RMQ.Costed.erase, hsuperValue, hdeltaValue, hwordValue,
            hexact, hclamp]

theorem selected_position_in_read_word_of_sample
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    {target : Bool} {occurrence pos : Nat}
    {super delta : SuccinctSpace.StoredWordSelectSample}
    {word : List Bool}
    (hocc : occurrence <= bits.length)
    (hsuper :
      (data.superTables.entries target)[occurrence / data.occurrencesPerSuper]? =
        some (some super))
    (hdelta :
      (data.blockTables.entries target)[data.blockIndex target occurrence]? =
        some (some delta))
    (hword :
      data.bitWords.store.words[(addSelectSample super delta).wordIndex]? =
        some word)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos) :
    (addSelectSample super delta).wordStart <= pos /\
      pos < (addSelectSample super delta).wordStart + word.length := by
  have hexact :
      SelectSampleWordExact target bits occurrence
        (addSelectSample super delta) word :=
    data.select_some_exact target occurrence super delta word
      hocc hsuper hdelta hword
  exact
    SelectSampleWordExact.selected_position_in_read_word
      hexact hselect

theorem selected_wordIndex_eq_of_sample
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    {target : Bool} {occurrence pos : Nat}
    {super delta : SuccinctSpace.StoredWordSelectSample}
    {word : List Bool}
    (hocc : occurrence <= bits.length)
    (hsuper :
      (data.superTables.entries target)[occurrence / data.occurrencesPerSuper]? =
        some (some super))
    (hdelta :
      (data.blockTables.entries target)[data.blockIndex target occurrence]? =
        some (some delta))
    (hword :
      data.bitWords.store.words[(addSelectSample super delta).wordIndex]? =
        some word)
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hstart :
      (addSelectSample super delta).wordStart =
        (addSelectSample super delta).wordIndex * data.wordSize) :
    pos / data.wordSize = (addSelectSample super delta).wordIndex := by
  have hexact :
      SelectSampleWordExact target bits occurrence
        (addSelectSample super delta) word :=
    data.select_some_exact target occurrence super delta word
      hocc hsuper hdelta hword
  have hlist :
      data.bitWords.store.words.toList[
          (addSelectSample super delta).wordIndex]? = some word := by
    simpa [Array.getElem?_toList] using hword
  have hwordLen : word.length <= data.wordSize :=
    data.bitWords.word_length_le (List.mem_of_getElem? hlist)
  exact
    SelectSampleWordExact.selected_wordIndex_eq_of_aligned_read_word
      data.wordSize_pos hexact hselect hstart hwordLen

/--
If the two-level select query reads the same super locator, the same local
locator, and therefore the same aligned payload word for two successful
occurrences, both selected positions must lie in the same payload chunk.

Consequently a compact descriptor that shares one local entry across a sampled
run must read charged descriptor payload that can choose the final payload word;
the current shared-aligned-locator path cannot be the witness.
-/
theorem shared_local_locator_forces_same_selected_wordIndex
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    {target : Bool} {occurrenceA occurrenceB posA posB : Nat}
    {super delta : SuccinctSpace.StoredWordSelectSample}
    {word : List Bool}
    (hoccA : occurrenceA <= bits.length)
    (hoccB : occurrenceB <= bits.length)
    (hsuperA :
      (data.superTables.entries target)[
          occurrenceA / data.occurrencesPerSuper]? =
        some (some super))
    (hsuperB :
      (data.superTables.entries target)[
          occurrenceB / data.occurrencesPerSuper]? =
        some (some super))
    (hdeltaA :
      (data.blockTables.entries target)[
          data.blockIndex target occurrenceA]? =
        some (some delta))
    (hdeltaB :
      (data.blockTables.entries target)[
          data.blockIndex target occurrenceB]? =
        some (some delta))
    (hword :
      data.bitWords.store.words[(addSelectSample super delta).wordIndex]? =
        some word)
    (hselectA :
      RMQ.Succinct.select target bits occurrenceA = some posA)
    (hselectB :
      RMQ.Succinct.select target bits occurrenceB = some posB)
    (hstart :
      (addSelectSample super delta).wordStart =
        (addSelectSample super delta).wordIndex * data.wordSize) :
    posA / data.wordSize = posB / data.wordSize := by
  have hA :
      posA / data.wordSize =
        (addSelectSample super delta).wordIndex :=
    data.selected_wordIndex_eq_of_sample
      hoccA hsuperA hdeltaA hword hselectA hstart
  have hB :
      posB / data.wordSize =
        (addSelectSample super delta).wordIndex :=
    data.selected_wordIndex_eq_of_sample
      hoccB hsuperB hdeltaB hword hselectB hstart
  exact hA.trans hB.symm

theorem shared_local_locator_contradicts_distinct_selected_wordIndex
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    {target : Bool} {occurrenceA occurrenceB posA posB : Nat}
    {super delta : SuccinctSpace.StoredWordSelectSample}
    {word : List Bool}
    (hoccA : occurrenceA <= bits.length)
    (hoccB : occurrenceB <= bits.length)
    (hsuperA :
      (data.superTables.entries target)[
          occurrenceA / data.occurrencesPerSuper]? =
        some (some super))
    (hsuperB :
      (data.superTables.entries target)[
          occurrenceB / data.occurrencesPerSuper]? =
        some (some super))
    (hdeltaA :
      (data.blockTables.entries target)[
          data.blockIndex target occurrenceA]? =
        some (some delta))
    (hdeltaB :
      (data.blockTables.entries target)[
          data.blockIndex target occurrenceB]? =
        some (some delta))
    (hword :
      data.bitWords.store.words[(addSelectSample super delta).wordIndex]? =
        some word)
    (hselectA :
      RMQ.Succinct.select target bits occurrenceA = some posA)
    (hselectB :
      RMQ.Succinct.select target bits occurrenceB = some posB)
    (hstart :
      (addSelectSample super delta).wordStart =
        (addSelectSample super delta).wordIndex * data.wordSize)
    (hdistinct :
      posA / data.wordSize = posB / data.wordSize -> False) :
    False := by
  exact hdistinct
    (data.shared_local_locator_forces_same_selected_wordIndex
      hoccA hoccB hsuperA hsuperB hdeltaA hdeltaB hword
      hselectA hselectB hstart)

theorem payload_word_length_le_machine
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    {word : List Bool}
    (hmem : List.Mem word data.bitWords.store.words.toList) :
    word.length <= SuccinctRankProposal.machineWordBits bits.length := by
  exact Nat.le_trans
    (data.bitWords.word_length_le hmem)
    data.wordSize_le_machine

theorem profile
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost) :
    data.auxPayload.length = superOverhead + blockOverhead /\
      data.wordSize <= SuccinctRankProposal.machineWordBits bits.length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        bits /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <= SuccinctRankProposal.machineWordBits bits.length) /\
      forall target occurrence,
        (data.selectCosted target occurrence).cost <= queryCost /\
          (data.selectCosted target occurrence).erase =
            RMQ.Succinct.select target bits occurrence := by
  constructor
  · exact data.auxPayload_length
  · constructor
    · exact data.wordSize_le_machine
    · constructor
      · exact data.payload_words_erase
      · constructor
        · intro word hmem
          exact data.payload_word_length_le_machine hmem
        · intro target occurrence
          exact ⟨data.selectCosted_cost_le target occurrence,
            data.selectCosted_exact target occurrence⟩

end TwoLevelPayloadLiveStoredWordSelectData

def canonicalTwoLevelSelectData
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (hquery : 4 <= queryCost)
    (bridge :
      CanonicalSelectWordBridge bits wordSize occurrencesPerSuper bitWords) :
    TwoLevelPayloadLiveStoredWordSelectData bits
      ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper superFieldWidth
          hsuperBits).payload.length)
      ((canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper blockFieldWidth
          hblockBits).payload.length)
      queryCost where
  wordSize := wordSize
  wordSize_pos := hwordSize
  wordSize_le_machine := hwordMachine
  occurrencesPerSuper := occurrencesPerSuper
  occurrencesPerSuper_pos := hoccurrences
  blockIndex := fun _ occurrence => occurrence
  superFieldWidth := superFieldWidth
  blockFieldWidth := blockFieldWidth
  superTrueEntries :=
    selectSuperSampleEntries true bits wordSize occurrencesPerSuper
      (canonicalSelectSuperCount bits occurrencesPerSuper)
  superFalseEntries :=
    selectSuperSampleEntries false bits wordSize occurrencesPerSuper
      (canonicalSelectSuperCount bits occurrencesPerSuper)
  blockTrueEntries :=
    selectBlockDeltaEntries true bits wordSize occurrencesPerSuper
      (canonicalSelectBlockCount bits)
  blockFalseEntries :=
    selectBlockDeltaEntries false bits wordSize occurrencesPerSuper
      (canonicalSelectBlockCount bits)
  superTables :=
    canonicalSelectSuperTablesFinite
      bits wordSize occurrencesPerSuper superFieldWidth hsuperBits
  blockTables :=
    canonicalSelectBlockTablesFinite
      bits wordSize occurrencesPerSuper blockFieldWidth hblockBits
  bitWords := bitWords
  superPayload_length := rfl
  blockPayload_length := rfl
  queryCost_ge_four := hquery
  super_entry_present := by
    intro target occurrence hocc
    exact canonicalSelectSuperTablesFinite_present
      (bits := bits) (wordSize := wordSize)
      (occurrencesPerSuper := occurrencesPerSuper)
      (fieldWidth := superFieldWidth) hsuperBits target hocc
  block_entry_present := by
    intro target occurrence hocc
    exact canonicalSelectBlockTablesFinite_present
      (bits := bits) (wordSize := wordSize)
      (occurrencesPerSuper := occurrencesPerSuper)
      (fieldWidth := blockFieldWidth) hblockBits target hocc
  word_present_of_sample := by
    intro target occurrence super delta hocc hsuper hdelta
    have hbase :
        selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
          (occurrence / occurrencesPerSuper) = some super := by
      exact
        (canonicalSelectSuperTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := superFieldWidth)
          (i := occurrence / occurrencesPerSuper)
          (target := target) (entry := some super)
          (hbits := hsuperBits) hsuper).symm
    have hblock :
        selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
          occurrence = some delta := by
      exact
        (canonicalSelectBlockTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := blockFieldWidth)
          (occurrence := occurrence)
          (target := target) (entry := some delta)
          (hbits := hblockBits) hdelta).symm
    rcases
        selectBlockDeltaEntry?_some_fields_of_super hbase hblock with
      ⟨exact, hexact, _hdeltaEq⟩
    rcases bridge.sample_ordered
        target occurrence super exact hocc hbase hexact with
      ⟨hwordIndex, hwordStart, hrankBefore⟩
    have hadd :
        addSelectSample super delta = exact :=
      selectBlockDeltaEntry?_add_exact_of_le hbase hexact hblock
        hwordIndex hwordStart hrankBefore
    rcases bridge.word_present
        target occurrence exact hocc hexact with
      ⟨word, hword⟩
    exact Exists.intro word (by simpa [hadd] using hword)
  select_some_exact := by
    intro target occurrence super delta word hocc hsuper hdelta hword
    have hbase :
        selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
          (occurrence / occurrencesPerSuper) = some super := by
      exact
        (canonicalSelectSuperTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := superFieldWidth)
          (i := occurrence / occurrencesPerSuper)
          (target := target) (entry := some super)
          (hbits := hsuperBits) hsuper).symm
    have hblock :
        selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
          occurrence = some delta := by
      exact
        (canonicalSelectBlockTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := blockFieldWidth)
          (occurrence := occurrence)
          (target := target) (entry := some delta)
          (hbits := hblockBits) hdelta).symm
    rcases
        selectBlockDeltaEntry?_some_fields_of_super hbase hblock with
      ⟨exact, hexact, _hdeltaEq⟩
    rcases bridge.sample_ordered
        target occurrence super exact hocc hbase hexact with
      ⟨hwordIndex, hwordStart, hrankBefore⟩
    have hadd :
        addSelectSample super delta = exact :=
      selectBlockDeltaEntry?_add_exact_of_le hbase hexact hblock
        hwordIndex hwordStart hrankBefore
    have hwordExactIndex :
        bitWords.store.words[exact.wordIndex]? = some word := by
      simpa [hadd] using hword
    have hwordExact :
        SelectSampleWordExact target bits occurrence exact word :=
      bridge.word_exact
        target occurrence exact word hocc hexact hwordExactIndex
    exact
      selectBlockDeltaEntry?_select_some_exact_of_word
        hbase hexact hblock hwordIndex hwordStart hrankBefore hwordExact
  select_none_exact_of_super := by
    intro target occurrence hocc hsuper
    have hentry :
        selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
          (occurrence / occurrencesPerSuper) = none := by
      exact
        (canonicalSelectSuperTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := superFieldWidth)
          (i := occurrence / occurrencesPerSuper)
          (target := target)
          (entry := (none :
            Option SuccinctSpace.StoredWordSelectSample))
          (hbits := hsuperBits) hsuper).symm
    exact selectSuperSampleEntry?_none_exact_of_occurrence hentry
  select_none_exact_of_block := by
    intro target occurrence super hocc hsuper hdelta
    have hbase :
        selectSuperSampleEntry? target bits wordSize occurrencesPerSuper
          (occurrence / occurrencesPerSuper) = some super := by
      exact
        (canonicalSelectSuperTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := superFieldWidth)
          (i := occurrence / occurrencesPerSuper)
          (target := target) (entry := some super)
          (hbits := hsuperBits) hsuper).symm
    have hblock :
        selectBlockDeltaEntry? target bits wordSize occurrencesPerSuper
          occurrence = none := by
      exact
        (canonicalSelectBlockTablesFinite_getOpt_exact
          (bits := bits) (wordSize := wordSize)
          (occurrencesPerSuper := occurrencesPerSuper)
          (fieldWidth := blockFieldWidth)
          (occurrence := occurrence)
          (target := target)
          (entry := (none :
            Option SuccinctSpace.StoredWordSelectSample))
          (hbits := hblockBits) hdelta).symm
    exact selectBlockDeltaEntry?_none_exact_of_super hbase hblock

theorem canonicalTwoLevelSelectData_selectCosted_profile
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (hquery : 4 <= queryCost)
    (bridge :
      CanonicalSelectWordBridge bits wordSize occurrencesPerSuper bitWords)
    (target : Bool) (occurrence : Nat) :
    ((canonicalTwoLevelSelectData bits hwordSize hwordMachine hoccurrences
        hsuperBits hblockBits bitWords hquery bridge).selectCosted
        target occurrence).cost <= queryCost /\
      ((canonicalTwoLevelSelectData bits hwordSize hwordMachine hoccurrences
        hsuperBits hblockBits bitWords hquery bridge).selectCosted
        target occurrence).erase =
        RMQ.Succinct.select target bits occurrence := by
  let data :=
    canonicalTwoLevelSelectData bits hwordSize hwordMachine hoccurrences
      hsuperBits hblockBits bitWords hquery bridge
  exact And.intro
    (data.selectCosted_cost_le target occurrence)
    (data.selectCosted_exact target occurrence)

def canonicalTwoLevelSelectDataOfLocal
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (hquery : 4 <= queryCost)
    (hwordPresent :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
          exists word,
            bitWords.store.words[exact.wordIndex]? = some word)
    (hwordExact :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample) (word : List Bool),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
        bitWords.store.words[exact.wordIndex]? = some word ->
          SelectSampleWordExact target bits occurrence exact word) :
    TwoLevelPayloadLiveStoredWordSelectData bits
      ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper superFieldWidth
          hsuperBits).payload.length)
      ((canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper blockFieldWidth
          hblockBits).payload.length)
      queryCost :=
  canonicalTwoLevelSelectData bits hwordSize hwordMachine hoccurrences
    hsuperBits hblockBits bitWords hquery
    (CanonicalSelectWordBridge.ofLocal hwordPresent hwordExact)

theorem canonicalTwoLevelSelectDataOfLocal_selectCosted_profile
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (hquery : 4 <= queryCost)
    (hwordPresent :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
          exists word,
            bitWords.store.words[exact.wordIndex]? = some word)
    (hwordExact :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample) (word : List Bool),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
        bitWords.store.words[exact.wordIndex]? = some word ->
          SelectSampleWordExact target bits occurrence exact word)
    (target : Bool) (occurrence : Nat) :
    ((canonicalTwoLevelSelectDataOfLocal bits hwordSize hwordMachine
        hoccurrences hsuperBits hblockBits bitWords hquery
        hwordPresent hwordExact).selectCosted target occurrence).cost <=
        queryCost /\
      ((canonicalTwoLevelSelectDataOfLocal bits hwordSize hwordMachine
        hoccurrences hsuperBits hblockBits bitWords hquery
        hwordPresent hwordExact).selectCosted target occurrence).erase =
        RMQ.Succinct.select target bits occurrence := by
  exact
    canonicalTwoLevelSelectData_selectCosted_profile bits hwordSize
      hwordMachine hoccurrences hsuperBits hblockBits bitWords hquery
      (CanonicalSelectWordBridge.ofLocal hwordPresent hwordExact)
      target occurrence

def canonicalTwoLevelSelectDataOfChunks
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (hquery : 4 <= queryCost)
    (hwordExact :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample) (word : List Bool),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
        (SuccinctSpace.BoundedPayloadWordStore.ofChunks
            bits hwordSize).store.words[exact.wordIndex]? = some word ->
          SelectSampleWordExact target bits occurrence exact word) :
    TwoLevelPayloadLiveStoredWordSelectData bits
      ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper superFieldWidth
          hsuperBits).payload.length)
      ((canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper blockFieldWidth
          hblockBits).payload.length)
      queryCost :=
  canonicalTwoLevelSelectData bits hwordSize hwordMachine hoccurrences
    hsuperBits hblockBits
    (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hwordSize)
    hquery
    (CanonicalSelectWordBridge.ofChunks hwordSize hwordExact)

theorem canonicalTwoLevelSelectDataOfChunks_selectCosted_profile
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (hquery : 4 <= queryCost)
    (hwordExact :
      forall (target : Bool) (occurrence : Nat)
          (exact : SuccinctSpace.StoredWordSelectSample) (word : List Bool),
        occurrence <= bits.length ->
        selectSampleAt? target bits wordSize occurrence = some exact ->
        (SuccinctSpace.BoundedPayloadWordStore.ofChunks
            bits hwordSize).store.words[exact.wordIndex]? = some word ->
          SelectSampleWordExact target bits occurrence exact word)
    (target : Bool) (occurrence : Nat) :
    ((canonicalTwoLevelSelectDataOfChunks bits hwordSize hwordMachine
        hoccurrences hsuperBits hblockBits hquery hwordExact).selectCosted
        target occurrence).cost <= queryCost /\
      ((canonicalTwoLevelSelectDataOfChunks bits hwordSize hwordMachine
        hoccurrences hsuperBits hblockBits hquery hwordExact).selectCosted
        target occurrence).erase =
        RMQ.Succinct.select target bits occurrence := by
  exact
    canonicalTwoLevelSelectData_selectCosted_profile bits hwordSize
      hwordMachine hoccurrences hsuperBits hblockBits
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hwordSize)
      hquery (CanonicalSelectWordBridge.ofChunks hwordSize hwordExact)
      target occurrence

def canonicalTwoLevelSelectDataOfChunksExact
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (hquery : 4 <= queryCost) :
    TwoLevelPayloadLiveStoredWordSelectData bits
      ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper superFieldWidth
          hsuperBits).payload.length)
      ((canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper blockFieldWidth
          hblockBits).payload.length)
      queryCost :=
  canonicalTwoLevelSelectData bits hwordSize hwordMachine hoccurrences
    hsuperBits hblockBits
    (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hwordSize)
    hquery
    (CanonicalSelectWordBridge.ofChunksExact hwordSize)

theorem canonicalTwoLevelSelectDataOfChunksExact_selectCosted_profile
    (bits : List Bool)
    {wordSize occurrencesPerSuper superFieldWidth blockFieldWidth
      queryCost : Nat}
    (hwordSize : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits bits.length)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hsuperBits : bits.length < 2 ^ superFieldWidth)
    (hblockBits : bits.length < 2 ^ blockFieldWidth)
    (hquery : 4 <= queryCost)
    (target : Bool) (occurrence : Nat) :
    ((canonicalTwoLevelSelectDataOfChunksExact bits hwordSize hwordMachine
        hoccurrences hsuperBits hblockBits hquery).selectCosted
        target occurrence).cost <= queryCost /\
      ((canonicalTwoLevelSelectDataOfChunksExact bits hwordSize hwordMachine
        hoccurrences hsuperBits hblockBits hquery).selectCosted
        target occurrence).erase =
        RMQ.Succinct.select target bits occurrence := by
  exact
    canonicalTwoLevelSelectData_selectCosted_profile bits hwordSize
      hwordMachine hoccurrences hsuperBits hblockBits
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hwordSize)
      hquery (CanonicalSelectWordBridge.ofChunksExact hwordSize)
      target occurrence

structure TwoLevelPayloadLiveStoredWordSelectFamily
    (super block : Nat -> Nat) (queryCost : Nat) where
  component :
    forall bits : List Bool,
      TwoLevelPayloadLiveStoredWordSelectData
        bits (super bits.length) (block bits.length) queryCost
  super_littleO : SuccinctSpace.LittleOLinear super
  block_littleO : SuccinctSpace.LittleOLinear block

namespace TwoLevelPayloadLiveStoredWordSelectFamily

def overhead
    {super block : Nat -> Nat} {queryCost : Nat}
    (_family :
      TwoLevelPayloadLiveStoredWordSelectFamily
        super block queryCost) : Nat -> Nat :=
  twoLevelSelectOverhead super block

theorem overhead_littleO
    {super block : Nat -> Nat} {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordSelectFamily
        super block queryCost) :
    SuccinctSpace.LittleOLinear family.overhead := by
  exact
    twoLevelSelectOverhead_littleO
      family.super_littleO family.block_littleO

theorem constant_query_profile
    {super block : Nat -> Nat} {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordSelectFamily
        super block queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall bits : List Bool,
        ((family.component bits).auxPayload.length =
          family.overhead bits.length) /\
        ((family.component bits).wordSize <=
          SuccinctRankProposal.machineWordBits bits.length) /\
        SuccinctSpace.flattenPayloadWords
            (family.component bits).bitWords.store.words.toList = bits /\
        (forall {word : List Bool},
          List.Mem word
              (family.component bits).bitWords.store.words.toList ->
            word.length <=
              SuccinctRankProposal.machineWordBits bits.length) /\
        forall target occurrence,
          ((family.component bits).selectCosted target occurrence).cost <=
              queryCost /\
            ((family.component bits).selectCosted target occurrence).erase =
              RMQ.Succinct.select target bits occurrence := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    exact (family.component bits).profile

end TwoLevelPayloadLiveStoredWordSelectFamily

/-!
## Non-oracular Clark select-position source

`chargedSelectPositionSource_allows_empty_select_oracle` shows the
`ChargedSelectPositionSource` interface, taken alone, can be inhabited by a
zero-payload semantic-select oracle (`payload := []`,
`selectPositionCosted := Costed.pure (Succinct.select ...)`).  The builder below
is the constructive contrast: it backs the source with the genuine two-level
`selectCosted` query, whose answer is decoded from the stored super sample,
block delta sample, and indexed payload word via the charged
`RAM.selectBoolWord` primitive.  The payload is the actual super/block sample
tables and `readWords` are the actual stored payload words, so the source no
longer hides a semantic-select shortcut.
-/

/--
Build a `ChargedSelectPositionSource` from genuine two-level select data.

The query is `data.selectCosted target` (charged super/block/word reads + word
select), never `Succinct.select` directly; the payload is `data.auxPayload`
(the real sample tables) and `readWords` are the real stored payload words.  The
caller supplies the overhead envelope and its `LittleOLinear` proof, plus a
bound placing the concrete `superOverhead + blockOverhead` table size inside
that envelope.
-/
def ChargedSelectPositionSource.ofTwoLevelSelectData
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (target : Bool)
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (overhead : Nat -> Nat)
    (hlittleO : SuccinctSpace.LittleOLinear overhead)
    (hpayload : superOverhead + blockOverhead <= overhead bits.length) :
    ChargedSelectPositionSource target bits overhead queryCost where
  domainSize := bits.length
  payload := data.auxPayload
  readWords := data.bitWords.store.words.toList
  selectPositionCosted := fun occurrence => data.selectCosted target occurrence
  payload_length_le := by
    simpa [data.auxPayload_length] using hpayload
  overhead_littleO := hlittleO
  selectPositionCosted_cost_le := fun occurrence =>
    data.selectCosted_cost_le target occurrence
  selectPositionCosted_exact := fun occurrence =>
    data.selectCosted_exact target occurrence
  read_word_length_le_machine := fun hmem =>
    data.payload_word_length_le_machine hmem

/--
The built source is genuinely non-oracular: its `selectPositionCosted` is
definitionally the two-level `selectCosted` query and its `payload` is the real
sample-table payload.  The remaining facts are exact select, constant cost, and
machine-word bounded reads, inherited from the two-level select data.
-/
theorem ChargedSelectPositionSource.ofTwoLevelSelectData_profile
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (target : Bool)
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (overhead : Nat -> Nat)
    (hlittleO : SuccinctSpace.LittleOLinear overhead)
    (hpayload : superOverhead + blockOverhead <= overhead bits.length) :
    let source :=
      ChargedSelectPositionSource.ofTwoLevelSelectData
        target data overhead hlittleO hpayload
    (source.selectPositionCosted =
        fun occurrence => data.selectCosted target occurrence) /\
      source.payload = data.auxPayload /\
      source.payload.length = superOverhead + blockOverhead /\
      SuccinctSpace.LittleOLinear overhead /\
      (forall occurrence,
        (source.selectPositionCosted occurrence).cost <= queryCost) /\
      (forall occurrence,
        (source.selectPositionCosted occurrence).erase =
          RMQ.Succinct.select target bits occurrence) /\
      forall {word : List Bool},
        List.Mem word source.readWords ->
          word.length <= SuccinctRankProposal.machineWordBits bits.length := by
  refine ⟨rfl, rfl, ?_, hlittleO, ?_, ?_, ?_⟩
  · exact data.auxPayload_length
  · intro occurrence
    exact data.selectCosted_cost_le target occurrence
  · intro occurrence
    exact data.selectCosted_exact target occurrence
  · intro word hmem
    exact data.payload_word_length_le_machine hmem

/--
Family-level non-oracular two-level Clark select source.

For every bitvector, produce a `ChargedSelectPositionSource` backed by the
two-level select family's component data.  Because the family carries genuine
`super_littleO`/`block_littleO`, the source overhead `twoLevelSelectOverhead
super block` is genuinely `LittleOLinear` (not a constant-function escape), so
this is a real `o(n)`-payload Clark select source -- reduced to supplying a
two-level select family with `o(n)` super and block budgets.
-/
def TwoLevelPayloadLiveStoredWordSelectFamily.toChargedSelectPositionSource
    {super block : Nat -> Nat} {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordSelectFamily super block queryCost)
    (target : Bool) (bits : List Bool) :
    ChargedSelectPositionSource target bits
      (twoLevelSelectOverhead super block) queryCost :=
  ChargedSelectPositionSource.ofTwoLevelSelectData target
    (family.component bits)
    (twoLevelSelectOverhead super block)
    (twoLevelSelectOverhead_littleO family.super_littleO family.block_littleO)
    (Nat.le_refl _)

theorem TwoLevelPayloadLiveStoredWordSelectFamily.toChargedSelectPositionSource_profile
    {super block : Nat -> Nat} {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordSelectFamily super block queryCost)
    (target : Bool) :
    SuccinctSpace.LittleOLinear (twoLevelSelectOverhead super block) /\
      forall bits : List Bool,
        let source := family.toChargedSelectPositionSource target bits
        (source.selectPositionCosted =
            fun occurrence =>
              (family.component bits).selectCosted target occurrence) /\
          source.payload = (family.component bits).auxPayload /\
          source.payload.length =
            twoLevelSelectOverhead super block bits.length /\
          (forall occurrence,
            (source.selectPositionCosted occurrence).cost <= queryCost) /\
          (forall occurrence,
            (source.selectPositionCosted occurrence).erase =
              RMQ.Succinct.select target bits occurrence) /\
          forall {word : List Bool},
            List.Mem word source.readWords ->
              word.length <=
                SuccinctRankProposal.machineWordBits bits.length := by
  refine
    ⟨twoLevelSelectOverhead_littleO family.super_littleO family.block_littleO,
      ?_⟩
  intro bits
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · show ((family.component bits).auxPayload).length =
        twoLevelSelectOverhead super block bits.length
    rw [(family.component bits).auxPayload_length]
    rfl
  · intro occurrence
    exact (family.component bits).selectCosted_cost_le target occurrence
  · intro occurrence
    exact (family.component bits).selectCosted_exact target occurrence
  · intro word hmem
    exact (family.component bits).payload_word_length_le_machine hmem

def twoLevelRankSelectOverhead
    (rankSuper rankBlock selectSuper selectBlock : Nat -> Nat)
    (n : Nat) : Nat :=
  SuccinctRankProposal.twoLevelRankOverhead rankSuper rankBlock n +
    twoLevelSelectOverhead selectSuper selectBlock n

theorem twoLevelRankSelectOverhead_littleO
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    (hrankSuper : SuccinctSpace.LittleOLinear rankSuper)
    (hrankBlock : SuccinctSpace.LittleOLinear rankBlock)
    (hselectSuper : SuccinctSpace.LittleOLinear selectSuper)
    (hselectBlock : SuccinctSpace.LittleOLinear selectBlock) :
    SuccinctSpace.LittleOLinear
      (twoLevelRankSelectOverhead
        rankSuper rankBlock selectSuper selectBlock) := by
  unfold twoLevelRankSelectOverhead
  exact
      (SuccinctRankProposal.twoLevelRankOverhead_littleO
      hrankSuper hrankBlock).add
      (twoLevelSelectOverhead_littleO hselectSuper hselectBlock)

/-- Canonical rank/select directory overhead under `Theta(log n)` words. -/
def canonicalTwoLevelRankSelectOverhead
    (rankSuperSlots rankBlockSlots selectSuperSlots selectBlockSlots :
      Nat) : Nat -> Nat :=
  twoLevelRankSelectOverhead
    (SuccinctRankProposal.canonicalTwoLevelRankSuperOverhead
      rankSuperSlots)
    (SuccinctRankProposal.canonicalTwoLevelRankBlockOverhead
      rankBlockSlots)
    (canonicalTwoLevelSelectSuperOverhead selectSuperSlots)
    (canonicalTwoLevelSelectBlockOverhead selectBlockSlots)

theorem canonicalTwoLevelRankSelectOverhead_littleO
    (rankSuperSlots rankBlockSlots selectSuperSlots selectBlockSlots :
      Nat) :
    SuccinctSpace.LittleOLinear
      (canonicalTwoLevelRankSelectOverhead
        rankSuperSlots rankBlockSlots selectSuperSlots selectBlockSlots) := by
  exact
    twoLevelRankSelectOverhead_littleO
      (SuccinctRankProposal.canonicalTwoLevelRankSuperOverhead_littleO
        rankSuperSlots)
      (SuccinctRankProposal.canonicalTwoLevelRankBlockOverhead_littleO
        rankBlockSlots)
      (canonicalTwoLevelSelectSuperOverhead_littleO selectSuperSlots)
      (canonicalTwoLevelSelectBlockOverhead_littleO selectBlockSlots)

def twoLevelRankSelectDirectory
    {bits : List Bool}
    {rankSuper rankBlock selectSuper selectBlock queryCost : Nat}
    (rankData :
      SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
        bits rankSuper rankBlock queryCost)
    (selectData :
      TwoLevelPayloadLiveStoredWordSelectData
        bits selectSuper selectBlock queryCost) :
    SuccinctSpace.RankSelectDirectory
      bits ((rankSuper + rankBlock) + (selectSuper + selectBlock))
      queryCost where
  Aux := Unit
  buildAux := ()
  encodeAux _ := rankData.auxPayload ++ selectData.auxPayload
  rankCosted _ target pos := rankData.rankCosted target pos
  selectCosted _ target occurrence :=
    selectData.selectCosted target occurrence
  aux_length_eq := by
    simp [rankData.auxPayload_length, selectData.auxPayload_length]
  rank_cost_le := by
    intro target pos
    exact rankData.rankCosted_cost_le target pos
  select_cost_le := by
    intro target occurrence
    exact selectData.selectCosted_cost_le target occurrence
  rank_exact := by
    intro target pos
    exact rankData.rankCosted_exact target pos
  select_exact := by
    intro target occurrence
    exact selectData.selectCosted_exact target occurrence

theorem twoLevelRankSelectDirectory_profile
    {bits : List Bool}
    {rankSuper rankBlock selectSuper selectBlock queryCost : Nat}
    (rankData :
      SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
        bits rankSuper rankBlock queryCost)
    (selectData :
      TwoLevelPayloadLiveStoredWordSelectData
        bits selectSuper selectBlock queryCost) :
    (twoLevelRankSelectDirectory rankData selectData).auxPayload.length =
        (rankSuper + rankBlock) + (selectSuper + selectBlock) /\
      (forall target pos,
        ((twoLevelRankSelectDirectory rankData selectData).rankQueryCosted
            target pos).cost <= queryCost /\
          ((twoLevelRankSelectDirectory rankData selectData).rankQueryCosted
              target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((twoLevelRankSelectDirectory rankData selectData).selectQueryCosted
            target occurrence).cost <= queryCost /\
          ((twoLevelRankSelectDirectory rankData selectData).selectQueryCosted
              target occurrence).erase =
            RMQ.Succinct.select target bits occurrence) := by
  constructor
  · exact
      (twoLevelRankSelectDirectory rankData selectData).auxPayload_length
  · constructor
    · intro target pos
      let directory := twoLevelRankSelectDirectory rankData selectData
      exact ⟨directory.rankQueryCosted_cost_le target pos,
        directory.rankQueryCosted_erase target pos⟩
    · intro target occurrence
      let directory := twoLevelRankSelectDirectory rankData selectData
      exact ⟨directory.selectQueryCosted_cost_le target occurrence,
        directory.selectQueryCosted_erase target occurrence⟩

def canonicalTwoLevelRankSelectDirectoryOfChunksExact
    (bits : List Bool)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : bits.length < 2 ^ rankBlockWidth)
    (hselectSuperBits : bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    SuccinctSpace.RankSelectDirectory bits
      (((SuccinctRankProposal.canonicalSuperRankSampleTables
          bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRankProposal.canonicalBlockRankSampleTables
          bits wordSize blocksPerSuper rankBlockWidth
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length))
      queryCost :=
  twoLevelRankSelectDirectory
    (SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExact
      bits hword hwordMachine hblocks hrankSuperBits hrankBlockBits hquery)
    (canonicalTwoLevelSelectDataOfChunksExact
      bits hword hwordMachine hoccurrences hselectSuperBits
        hselectBlockBits hquery)

theorem canonicalTwoLevelRankSelectDirectoryOfChunksExact_profile
    (bits : List Bool)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : bits.length < 2 ^ rankBlockWidth)
    (hselectSuperBits : bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    (canonicalTwoLevelRankSelectDirectoryOfChunksExact bits hword
        hwordMachine hblocks hoccurrences hrankSuperBits hrankBlockBits
        hselectSuperBits hselectBlockBits hquery).auxPayload.length =
        (((SuccinctRankProposal.canonicalSuperRankSampleTables
          bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRankProposal.canonicalBlockRankSampleTables
          bits wordSize blocksPerSuper rankBlockWidth
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length)) /\
      (forall target pos,
        ((canonicalTwoLevelRankSelectDirectoryOfChunksExact bits hword
            hwordMachine hblocks hoccurrences hrankSuperBits hrankBlockBits
            hselectSuperBits hselectBlockBits hquery).rankQueryCosted
              target pos).cost <= queryCost /\
          ((canonicalTwoLevelRankSelectDirectoryOfChunksExact bits hword
            hwordMachine hblocks hoccurrences hrankSuperBits hrankBlockBits
            hselectSuperBits hselectBlockBits hquery).rankQueryCosted
              target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((canonicalTwoLevelRankSelectDirectoryOfChunksExact bits hword
            hwordMachine hblocks hoccurrences hrankSuperBits hrankBlockBits
            hselectSuperBits hselectBlockBits hquery).selectQueryCosted
              target occurrence).cost <= queryCost /\
          ((canonicalTwoLevelRankSelectDirectoryOfChunksExact bits hword
            hwordMachine hblocks hoccurrences hrankSuperBits hrankBlockBits
            hselectSuperBits hselectBlockBits hquery).selectQueryCosted
              target occurrence).erase =
            RMQ.Succinct.select target bits occurrence) := by
  exact
    twoLevelRankSelectDirectory_profile
      (SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExact
        bits hword hwordMachine hblocks hrankSuperBits hrankBlockBits hquery)
      (canonicalTwoLevelSelectDataOfChunksExact
        bits hword hwordMachine hoccurrences hselectSuperBits
          hselectBlockBits hquery)

def canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
    (bits : List Bool)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : blocksPerSuper * wordSize < 2 ^ rankBlockWidth)
    (hselectSuperBits : bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    SuccinctSpace.RankSelectDirectory bits
      (((SuccinctRankProposal.canonicalSuperRankSampleTables
          bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan
          bits wordSize blocksPerSuper rankBlockWidth hblocks
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length))
      queryCost :=
  twoLevelRankSelectDirectory
    (SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock
      bits hword hwordMachine hblocks hrankSuperBits hrankBlockBits hquery)
    (canonicalTwoLevelSelectDataOfChunksExact
      bits hword hwordMachine hoccurrences hselectSuperBits
        hselectBlockBits hquery)

theorem canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock_profile
    (bits : List Bool)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : blocksPerSuper * wordSize < 2 ^ rankBlockWidth)
    (hselectSuperBits : bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    (canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
        bits hword hwordMachine hblocks hoccurrences hrankSuperBits
        hrankBlockBits hselectSuperBits hselectBlockBits hquery).auxPayload.length =
        (((SuccinctRankProposal.canonicalSuperRankSampleTables
          bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan
          bits wordSize blocksPerSuper rankBlockWidth hblocks
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length)) /\
      (forall target pos,
        ((canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
            bits hword hwordMachine hblocks hoccurrences hrankSuperBits
            hrankBlockBits hselectSuperBits hselectBlockBits hquery).rankQueryCosted
              target pos).cost <= queryCost /\
          ((canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
            bits hword hwordMachine hblocks hoccurrences hrankSuperBits
            hrankBlockBits hselectSuperBits hselectBlockBits hquery).rankQueryCosted
              target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
            bits hword hwordMachine hblocks hoccurrences hrankSuperBits
            hrankBlockBits hselectSuperBits hselectBlockBits hquery).selectQueryCosted
              target occurrence).cost <= queryCost /\
          ((canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
            bits hword hwordMachine hblocks hoccurrences hrankSuperBits
            hrankBlockBits hselectSuperBits hselectBlockBits hquery).selectQueryCosted
              target occurrence).erase =
            RMQ.Succinct.select target bits occurrence) := by
  exact
    twoLevelRankSelectDirectory_profile
      (SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock
        bits hword hwordMachine hblocks hrankSuperBits hrankBlockBits hquery)
      (canonicalTwoLevelSelectDataOfChunksExact
        bits hword hwordMachine hoccurrences hselectSuperBits
          hselectBlockBits hquery)

def canonicalTwoLevelBalancedParensAccessOfChunksExact
    (parens : RMQ.Succinct.BalancedParens)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits parens.bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : parens.bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : parens.bits.length < 2 ^ rankBlockWidth)
    (hselectSuperBits : parens.bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : parens.bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    SuccinctSpace.BalancedParensAccess parens
      (((SuccinctRankProposal.canonicalSuperRankSampleTables
          parens.bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRankProposal.canonicalBlockRankSampleTables
          parens.bits wordSize blocksPerSuper rankBlockWidth
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          parens.bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          parens.bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length))
      queryCost where
  rankSelect :=
    canonicalTwoLevelRankSelectDirectoryOfChunksExact
      parens.bits hword hwordMachine hblocks hoccurrences
      hrankSuperBits hrankBlockBits hselectSuperBits hselectBlockBits
      hquery

theorem canonicalTwoLevelBalancedParensAccessOfChunksExact_profile
    (parens : RMQ.Succinct.BalancedParens)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits parens.bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : parens.bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : parens.bits.length < 2 ^ rankBlockWidth)
    (hselectSuperBits : parens.bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : parens.bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    let access :=
      canonicalTwoLevelBalancedParensAccessOfChunksExact
        parens hword hwordMachine hblocks hoccurrences hrankSuperBits
        hrankBlockBits hselectSuperBits hselectBlockBits hquery
    access.rankSelect.auxPayload.length =
        (((SuccinctRankProposal.canonicalSuperRankSampleTables
          parens.bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRankProposal.canonicalBlockRankSampleTables
          parens.bits wordSize blocksPerSuper rankBlockWidth
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          parens.bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          parens.bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length)) /\
      (forall target pos,
        (access.rankCosted target pos).cost <= queryCost /\
          (access.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target parens.bits pos) /\
      (forall target occurrence,
        (access.selectCosted target occurrence).cost <= queryCost /\
          (access.selectCosted target occurrence).erase =
            RMQ.Succinct.select target parens.bits occurrence) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          (access.rankCosted false pos).erase <=
            (access.rankCosted true pos).erase) /\
      ((access.rankCosted true parens.bits.length).erase =
        (access.rankCosted false parens.bits.length).erase) /\
      (forall pos,
        (access.excessCosted pos).cost <= 2 * queryCost /\
          (access.excessCosted pos).erase =
            RMQ.Succinct.rankPrefix true parens.bits pos -
              RMQ.Succinct.rankPrefix false parens.bits pos) := by
  dsimp
  let access :=
    canonicalTwoLevelBalancedParensAccessOfChunksExact
      parens hword hwordMachine hblocks hoccurrences hrankSuperBits
      hrankBlockBits hselectSuperBits hselectBlockBits hquery
  change
    access.rankSelect.auxPayload.length = _ /\
      (forall target pos,
        (access.rankCosted target pos).cost <= queryCost /\
          (access.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target parens.bits pos) /\
      (forall target occurrence,
        (access.selectCosted target occurrence).cost <= queryCost /\
          (access.selectCosted target occurrence).erase =
            RMQ.Succinct.select target parens.bits occurrence) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          (access.rankCosted false pos).erase <=
            (access.rankCosted true pos).erase) /\
      ((access.rankCosted true parens.bits.length).erase =
        (access.rankCosted false parens.bits.length).erase) /\
      (forall pos,
        (access.excessCosted pos).cost <= 2 * queryCost /\
          (access.excessCosted pos).erase =
            RMQ.Succinct.rankPrefix true parens.bits pos -
              RMQ.Succinct.rankPrefix false parens.bits pos)
  constructor
  · exact access.auxPayload_length
  · constructor
    · intro target pos
      exact ⟨access.rankCosted_cost_le target pos,
        access.rankCosted_erase target pos⟩
    · constructor
      · intro target occurrence
        exact ⟨access.selectCosted_cost_le target occurrence,
          access.selectCosted_erase target occurrence⟩
      · constructor
        · intro pos hpos
          exact access.close_rank_le_open_rank hpos
        · constructor
          · exact access.final_rank_eq
          · intro pos
            exact ⟨access.excessCosted_cost_le pos,
              access.excessCosted_erase pos⟩

def canonicalTwoLevelBalancedParensAccessOfChunksExactLocalRankBlock
    (parens : RMQ.Succinct.BalancedParens)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits parens.bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : parens.bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : blocksPerSuper * wordSize < 2 ^ rankBlockWidth)
    (hselectSuperBits : parens.bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : parens.bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    SuccinctSpace.BalancedParensAccess parens
      (((SuccinctRankProposal.canonicalSuperRankSampleTables
          parens.bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan
          parens.bits wordSize blocksPerSuper rankBlockWidth hblocks
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          parens.bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          parens.bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length))
      queryCost where
  rankSelect :=
    canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
      parens.bits hword hwordMachine hblocks hoccurrences
      hrankSuperBits hrankBlockBits hselectSuperBits hselectBlockBits
      hquery

theorem canonicalTwoLevelBalancedParensAccessOfChunksExactLocalRankBlock_profile
    (parens : RMQ.Succinct.BalancedParens)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRankProposal.machineWordBits parens.bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : parens.bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : blocksPerSuper * wordSize < 2 ^ rankBlockWidth)
    (hselectSuperBits : parens.bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : parens.bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    let access :=
      canonicalTwoLevelBalancedParensAccessOfChunksExactLocalRankBlock
        parens hword hwordMachine hblocks hoccurrences hrankSuperBits
        hrankBlockBits hselectSuperBits hselectBlockBits hquery
    access.rankSelect.auxPayload.length =
        (((SuccinctRankProposal.canonicalSuperRankSampleTables
          parens.bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan
          parens.bits wordSize blocksPerSuper rankBlockWidth hblocks
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          parens.bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          parens.bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length)) /\
      (forall target pos,
        (access.rankCosted target pos).cost <= queryCost /\
          (access.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target parens.bits pos) /\
      (forall target occurrence,
        (access.selectCosted target occurrence).cost <= queryCost /\
          (access.selectCosted target occurrence).erase =
            RMQ.Succinct.select target parens.bits occurrence) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          (access.rankCosted false pos).erase <=
            (access.rankCosted true pos).erase) /\
      ((access.rankCosted true parens.bits.length).erase =
        (access.rankCosted false parens.bits.length).erase) /\
      (forall pos,
        (access.excessCosted pos).cost <= 2 * queryCost /\
          (access.excessCosted pos).erase =
            RMQ.Succinct.rankPrefix true parens.bits pos -
              RMQ.Succinct.rankPrefix false parens.bits pos) := by
  dsimp
  let access :=
    canonicalTwoLevelBalancedParensAccessOfChunksExactLocalRankBlock
      parens hword hwordMachine hblocks hoccurrences hrankSuperBits
      hrankBlockBits hselectSuperBits hselectBlockBits hquery
  change
    access.rankSelect.auxPayload.length = _ /\
      (forall target pos,
        (access.rankCosted target pos).cost <= queryCost /\
          (access.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target parens.bits pos) /\
      (forall target occurrence,
        (access.selectCosted target occurrence).cost <= queryCost /\
          (access.selectCosted target occurrence).erase =
            RMQ.Succinct.select target parens.bits occurrence) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          (access.rankCosted false pos).erase <=
            (access.rankCosted true pos).erase) /\
      ((access.rankCosted true parens.bits.length).erase =
        (access.rankCosted false parens.bits.length).erase) /\
      (forall pos,
        (access.excessCosted pos).cost <= 2 * queryCost /\
          (access.excessCosted pos).erase =
            RMQ.Succinct.rankPrefix true parens.bits pos -
              RMQ.Succinct.rankPrefix false parens.bits pos)
  constructor
  · exact access.auxPayload_length
  · constructor
    · intro target pos
      exact ⟨access.rankCosted_cost_le target pos,
        access.rankCosted_erase target pos⟩
    · constructor
      · intro target occurrence
        exact ⟨access.selectCosted_cost_le target occurrence,
          access.selectCosted_erase target occurrence⟩
      · constructor
        · intro pos hpos
          exact access.close_rank_le_open_rank hpos
        · constructor
          · exact access.final_rank_eq
          · intro pos
            exact ⟨access.excessCosted_cost_le pos,
              access.excessCosted_erase pos⟩

structure TwoLevelPayloadLiveStoredWordRankSelectFamily
    (rankSuper rankBlock selectSuper selectBlock : Nat -> Nat)
    (queryCost : Nat) where
  rankComponent :
    forall bits : List Bool,
      SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
        bits (rankSuper bits.length) (rankBlock bits.length) queryCost
  selectComponent :
    forall bits : List Bool,
      TwoLevelPayloadLiveStoredWordSelectData
        bits (selectSuper bits.length) (selectBlock bits.length) queryCost
  rankSuper_littleO : SuccinctSpace.LittleOLinear rankSuper
  rankBlock_littleO : SuccinctSpace.LittleOLinear rankBlock
  selectSuper_littleO : SuccinctSpace.LittleOLinear selectSuper
  selectBlock_littleO : SuccinctSpace.LittleOLinear selectBlock

namespace TwoLevelPayloadLiveStoredWordRankSelectFamily

def overhead
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (_family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    Nat -> Nat :=
  twoLevelRankSelectOverhead
    rankSuper rankBlock selectSuper selectBlock

theorem overhead_littleO
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    SuccinctSpace.LittleOLinear family.overhead := by
  exact
    twoLevelRankSelectOverhead_littleO
      family.rankSuper_littleO family.rankBlock_littleO
      family.selectSuper_littleO family.selectBlock_littleO

def directory
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost)
    (bits : List Bool) :
    SuccinctSpace.RankSelectDirectory
      bits (family.overhead bits.length) queryCost :=
  twoLevelRankSelectDirectory
    (family.rankComponent bits) (family.selectComponent bits)

def toRankSelectFamily
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    SuccinctSpace.RankSelectFamily family.overhead queryCost where
  directory bits := family.directory bits
  overhead_littleO := family.overhead_littleO

def toBitVectorRankSelectFamily
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost)
    (haccess : 1 <= queryCost) :
    RankSelectSpec.BitVectorRankSelectFamily
      family.overhead queryCost where
  directory bits :=
    RankSelectSpec.BitVectorRankSelectDirectory.ofRankSelectDirectoryWithStoredBits
      (family.directory bits) haccess
  overhead_littleO := family.overhead_littleO

theorem constant_query_profile
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall bits : List Bool,
        ((family.directory bits).auxPayload.length =
          family.overhead bits.length) /\
        (forall target pos,
          ((family.directory bits).rankQueryCosted target pos).cost <=
              queryCost /\
            ((family.directory bits).rankQueryCosted target pos).erase =
              RMQ.Succinct.rankPrefix target bits pos) /\
        (forall target occurrence,
          ((family.directory bits).selectQueryCosted target occurrence).cost <=
              queryCost /\
            ((family.directory bits).selectQueryCosted target occurrence).erase =
              RMQ.Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    exact twoLevelRankSelectDirectory_profile
      (family.rankComponent bits) (family.selectComponent bits)

theorem n_plus_o_constant_query_profile
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost)
    (haccess : 1 <= queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall bits : List Bool,
        let directory :=
          (family.toBitVectorRankSelectFamily haccess).directory bits
        directory.payload.length =
          bits.length + family.overhead bits.length /\
          (forall i,
            (directory.accessQueryCosted i).cost <= queryCost /\
              (directory.accessQueryCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankQueryCosted target pos).cost <= queryCost /\
              (directory.rankQueryCosted target pos).erase =
                RMQ.Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectQueryCosted target occurrence).cost <= queryCost /\
              (directory.selectQueryCosted target occurrence).erase =
                RMQ.Succinct.select target bits occurrence) := by
  simpa using
    RankSelectSpec.BitVectorRankSelectFamily.n_plus_o_constant_query_profile
        (family.toBitVectorRankSelectFamily haccess)

/--
Rank/select profile with the word-RAM side condition exposed.

This strengthens `constant_query_profile`: in addition to exact queries and
sublinear auxiliary payload, both payload stores erase to the same bit vector
and every stored word is bounded by `machineWordBits bits.length`.
-/
theorem word_bounded_constant_query_profile
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall bits : List Bool,
        ((family.directory bits).auxPayload.length =
          family.overhead bits.length) /\
        ((family.rankComponent bits).wordSize <=
          SuccinctRankProposal.machineWordBits bits.length) /\
        SuccinctSpace.flattenPayloadWords
            (family.rankComponent bits).bitWords.store.words.toList =
          bits /\
        (forall {word : List Bool},
          List.Mem word
              (family.rankComponent bits).bitWords.store.words.toList ->
            word.length <=
              SuccinctRankProposal.machineWordBits bits.length) /\
        ((family.selectComponent bits).wordSize <=
          SuccinctRankProposal.machineWordBits bits.length) /\
        SuccinctSpace.flattenPayloadWords
            (family.selectComponent bits).bitWords.store.words.toList =
          bits /\
        (forall {word : List Bool},
          List.Mem word
              (family.selectComponent bits).bitWords.store.words.toList ->
            word.length <=
              SuccinctRankProposal.machineWordBits bits.length) /\
        (forall target pos,
          ((family.directory bits).rankQueryCosted target pos).cost <=
              queryCost /\
            ((family.directory bits).rankQueryCosted target pos).erase =
              RMQ.Succinct.rankPrefix target bits pos) /\
        (forall target occurrence,
          ((family.directory bits).selectQueryCosted target occurrence).cost <=
              queryCost /\
            ((family.directory bits).selectQueryCosted target occurrence).erase =
              RMQ.Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    rcases twoLevelRankSelectDirectory_profile
        (family.rankComponent bits) (family.selectComponent bits) with
      ⟨haux, hrankQuery, hselectQuery⟩
    rcases (family.rankComponent bits).profile with
      ⟨_hrankAux, hrankWord, hrankErase, hrankWordBound,
        _hrankProfile⟩
    rcases (family.selectComponent bits).profile with
      ⟨_hselectAux, hselectWord, hselectErase, hselectWordBound,
        _hselectProfile⟩
    exact
      ⟨haux, hrankWord, hrankErase, hrankWordBound, hselectWord,
        hselectErase, hselectWordBound, hrankQuery, hselectQuery⟩

theorem word_bounded_n_plus_o_constant_query_profile
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost)
    (haccess : 1 <= queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall bits : List Bool,
        let directory :=
          (family.toBitVectorRankSelectFamily haccess).directory bits
        directory.payload.length =
          bits.length + family.overhead bits.length /\
        ((family.rankComponent bits).wordSize <=
          SuccinctRankProposal.machineWordBits bits.length) /\
        SuccinctSpace.flattenPayloadWords
            (family.rankComponent bits).bitWords.store.words.toList =
          bits /\
        (forall {word : List Bool},
          List.Mem word
              (family.rankComponent bits).bitWords.store.words.toList ->
            word.length <=
              SuccinctRankProposal.machineWordBits bits.length) /\
        ((family.selectComponent bits).wordSize <=
          SuccinctRankProposal.machineWordBits bits.length) /\
        SuccinctSpace.flattenPayloadWords
            (family.selectComponent bits).bitWords.store.words.toList =
          bits /\
        (forall {word : List Bool},
          List.Mem word
              (family.selectComponent bits).bitWords.store.words.toList ->
            word.length <=
              SuccinctRankProposal.machineWordBits bits.length) /\
        (forall i,
          (directory.accessQueryCosted i).cost <= queryCost /\
            (directory.accessQueryCosted i).erase = bits[i]?) /\
        (forall target pos,
          (directory.rankQueryCosted target pos).cost <= queryCost /\
            (directory.rankQueryCosted target pos).erase =
              RMQ.Succinct.rankPrefix target bits pos) /\
        (forall target occurrence,
          (directory.selectQueryCosted target occurrence).cost <= queryCost /\
            (directory.selectQueryCosted target occurrence).erase =
              RMQ.Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    rcases family.word_bounded_constant_query_profile.2 bits with
      ⟨_haux, hrankWord, hrankErase, hrankWordBound, hselectWord,
        hselectErase, hselectWordBound, _hrankQuery, _hselectQuery⟩
    rcases
      RankSelectSpec.BitVectorRankSelectDirectory.profile
        ((family.toBitVectorRankSelectFamily haccess).directory bits) with
      ⟨hpayload, haccessProfile, hrankProfile, hselectProfile⟩
    exact
      ⟨hpayload, hrankWord, hrankErase, hrankWordBound, hselectWord,
        hselectErase, hselectWordBound, haccessProfile, hrankProfile,
        hselectProfile⟩

def toBalancedParensAccessFamily
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    SuccinctSpace.BalancedParensAccessFamily family.overhead queryCost where
  access parens :=
    { rankSelect := family.directory parens.bits }
  overhead_littleO := family.overhead_littleO

theorem bp_constant_query_profile
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall parens : RMQ.Succinct.BalancedParens,
        (((family.toBalancedParensAccessFamily).access parens).rankSelect.auxPayload.length =
          family.overhead parens.bits.length) /\
        (forall target pos,
          (((family.toBalancedParensAccessFamily).access parens).rankCosted
              target pos).cost <= queryCost /\
            (((family.toBalancedParensAccessFamily).access parens).rankCosted
              target pos).erase =
              RMQ.Succinct.rankPrefix target parens.bits pos) /\
        (forall target occurrence,
          (((family.toBalancedParensAccessFamily).access parens).selectCosted
              target occurrence).cost <= queryCost /\
            (((family.toBalancedParensAccessFamily).access parens).selectCosted
              target occurrence).erase =
              RMQ.Succinct.select target parens.bits occurrence) /\
        (forall {pos : Nat},
          pos <= parens.bits.length ->
            (((family.toBalancedParensAccessFamily).access parens).rankCosted
              false pos).erase <=
              (((family.toBalancedParensAccessFamily).access parens).rankCosted
                true pos).erase) /\
        ((((family.toBalancedParensAccessFamily).access parens).rankCosted
          true parens.bits.length).erase =
          (((family.toBalancedParensAccessFamily).access parens).rankCosted
            false parens.bits.length).erase) /\
        (forall pos,
          (((family.toBalancedParensAccessFamily).access parens).excessCosted
              pos).cost <= 2 * queryCost /\
            (((family.toBalancedParensAccessFamily).access parens).excessCosted
              pos).erase =
              RMQ.Succinct.rankPrefix true parens.bits pos -
                RMQ.Succinct.rankPrefix false parens.bits pos) := by
  exact family.toBalancedParensAccessFamily.constant_query_profile

end TwoLevelPayloadLiveStoredWordRankSelectFamily

/-!
## Two-level BP close-navigation target

This is the stateful BP/RMQ composition using the two-level rank/select
components above plus the existing payload-live BP LCA-close table.
-/

def twoLevelBPCloseNavigationOverhead
    (rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat)
    (n : Nat) : Nat :=
  twoLevelRankSelectOverhead
      rankSuper rankBlock selectSuper selectBlock n +
    lca n

theorem twoLevelBPCloseNavigationOverhead_littleO
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    (hrankSuper : SuccinctSpace.LittleOLinear rankSuper)
    (hrankBlock : SuccinctSpace.LittleOLinear rankBlock)
    (hselectSuper : SuccinctSpace.LittleOLinear selectSuper)
    (hselectBlock : SuccinctSpace.LittleOLinear selectBlock)
    (hlca : SuccinctSpace.LittleOLinear lca) :
    SuccinctSpace.LittleOLinear
      (twoLevelBPCloseNavigationOverhead
        rankSuper rankBlock selectSuper selectBlock lca) := by
  unfold twoLevelBPCloseNavigationOverhead
  exact
    (twoLevelRankSelectOverhead_littleO
      hrankSuper hrankBlock hselectSuper hselectBlock).add hlca

structure TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
    (n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat) where
  rankData :
    (shape : Cartesian.CartesianShape) ->
      SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
        shape.bpCode rankSuper rankBlock queryCost
  selectData :
    (shape : Cartesian.CartesianShape) ->
      TwoLevelPayloadLiveStoredWordSelectData
        shape.bpCode selectSuper selectBlock queryCost
  lcaDirectory : SuccinctSpace.PayloadLiveBPCloseLCADirectory n lcaOverhead

namespace TwoLevelPayloadLiveBPCloseRMQNavigationDirectory

def overhead
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (_directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost) : Nat :=
  (rankSuper + rankBlock) + (selectSuper + selectBlock) + lcaOverhead

def encodeAux
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) : List Bool :=
  (directory.rankData shape).auxPayload ++
    (directory.selectData shape).auxPayload ++
      directory.lcaDirectory.encodeAux
        (directory.lcaDirectory.buildAux shape)

def payload
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) : List Bool :=
  shape.bpCode ++ directory.encodeAux shape

def selectCloseCosted
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    RMQ.Costed (Option Nat) :=
  (directory.selectData shape).selectCosted false idx

def lcaCloseCosted
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    RMQ.Costed (Option Nat) :=
  directory.lcaDirectory.lcaCloseCosted
    (directory.lcaDirectory.buildAux shape) leftClose rightClose

def rankCloseCosted
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    RMQ.Costed Nat :=
  (directory.rankData shape).rankCosted false pos

def queryBuiltCosted
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    RMQ.Costed (Option Nat) :=
  RMQ.Costed.bind (directory.selectCloseCosted shape left)
    fun leftClose? =>
      RMQ.Costed.bind
        (directory.selectCloseCosted shape (right - 1))
        fun rightClose? =>
          match leftClose?, rightClose? with
          | some leftClose, some rightClose =>
              RMQ.Costed.bind
                (directory.lcaCloseCosted shape leftClose rightClose)
                fun answerClose? =>
                  match answerClose? with
                  | some answerClose =>
                      RMQ.Costed.map
                        (fun closeRank => some (closeRank - 1))
                        (directory.rankCloseCosted shape (answerClose + 1))
                  | none => RMQ.Costed.pure none
          | _, _ => RMQ.Costed.pure none

theorem encodeAux_length
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (directory.encodeAux shape).length =
      (rankSuper + rankBlock) + (selectSuper + selectBlock) +
        lcaOverhead := by
  have hrank :
      (directory.rankData shape).auxPayload.length =
        rankSuper + rankBlock :=
    (directory.rankData shape).auxPayload_length
  have hselect :
      (directory.selectData shape).auxPayload.length =
        selectSuper + selectBlock :=
    (directory.selectData shape).auxPayload_length
  have hlca :
      (directory.lcaDirectory.encodeAux
          (directory.lcaDirectory.buildAux shape)).length =
        lcaOverhead :=
    directory.lcaDirectory.aux_length_eq (shape := shape) hshape
  simp [encodeAux, hrank, hselect, hlca]
  omega

theorem payload_length
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (directory.payload shape).length =
      2 * n +
        ((rankSuper + rankBlock) + (selectSuper + selectBlock) +
          lcaOverhead) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hbp : shape.bpCode.length = 2 * n :=
    Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshapeSize
  have haux := directory.encodeAux_length hshape
  simp [payload, hbp, haux]

theorem selectCloseCosted_cost_le
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (directory.selectCloseCosted shape idx).cost <= queryCost := by
  exact (directory.selectData shape).selectCosted_cost_le false idx

theorem lcaCloseCosted_cost_le_one
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted shape leftClose rightClose).cost <= 1 := by
  exact directory.lcaDirectory.lcaCloseCosted_cost_le_one
    (directory.lcaDirectory.buildAux shape) leftClose rightClose

theorem rankCloseCosted_cost_le
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (directory.rankCloseCosted shape pos).cost <= queryCost := by
  exact (directory.rankData shape).rankCosted_cost_le false pos

theorem queryBuiltCosted_cost_le
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (directory.queryBuiltCosted shape left right).cost <=
      3 * queryCost + 1 := by
  unfold queryBuiltCosted selectCloseCosted lcaCloseCosted rankCloseCosted
  have hleft := (directory.selectData shape).selectCosted_cost_le false left
  have hright :=
    (directory.selectData shape).selectCosted_cost_le false (right - 1)
  cases hleftValue :
      ((directory.selectData shape).selectCosted false left).value with
  | none =>
      simp [RMQ.Costed.bind, hleftValue]
      omega
  | some leftClose =>
      cases hrightValue :
          ((directory.selectData shape).selectCosted false (right - 1)).value with
      | none =>
          simp [RMQ.Costed.bind, hleftValue, hrightValue]
          omega
      | some rightClose =>
          have hlca :=
            directory.lcaDirectory.lcaCloseCosted_cost_le_one
              (directory.lcaDirectory.buildAux shape) leftClose rightClose
          cases hlcaValue :
              (directory.lcaDirectory.lcaCloseCosted
                (directory.lcaDirectory.buildAux shape)
                leftClose rightClose).value with
          | none =>
              simp [RMQ.Costed.bind, hleftValue, hrightValue, hlcaValue]
              omega
          | some answerClose =>
              have hrank :=
                (directory.rankData shape).rankCosted_cost_le
                  false (answerClose + 1)
              simp [RMQ.Costed.bind, RMQ.Costed.map, hleftValue,
                hrightValue, hlcaValue]
              omega

theorem selectCloseCosted_exact
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (directory.selectCloseCosted shape idx).erase =
      SuccinctSpace.bpCloseOfInorder? shape idx := by
  calc
    (directory.selectCloseCosted shape idx).erase =
        RMQ.Succinct.select false shape.bpCode idx := by
      exact (directory.selectData shape).selectCosted_exact false idx
    _ = SuccinctSpace.bpCloseOfInorder? shape idx := by
      exact SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx

theorem rankCloseCosted_exact
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (directory.rankCloseCosted shape pos).erase =
      RMQ.Succinct.rankPrefix false shape.bpCode pos := by
  exact (directory.rankData shape).rankCosted_exact false pos

theorem queryBuiltCosted_exact
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (directory.queryBuiltCosted shape left (left + len)).erase =
      some (scanWindow shape.representative left len) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hleftLt : left < n := by omega
  have hrightLt : left + len - 1 < n := by omega
  have hleftLtShape : left < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hleftLt
  have hrightLtShape : left + len - 1 < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hrightLt
  have hscanBounds :=
    Cartesian.scanWindow_bounds shape.representative left len hlen
  have hscanLt :
      scanWindow shape.representative left len < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    omega
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt
      shape hleftLtShape with
    ⟨leftClose, hleftClose⟩
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt
      shape hrightLtShape with
    ⟨rightClose, hrightClose⟩
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt shape hscanLt with
    ⟨answerClose, hanswerClose⟩
  have hselectLeft :
      (directory.selectCloseCosted shape left).value = some leftClose := by
    have h := directory.selectCloseCosted_exact shape left
    simpa [RMQ.Costed.erase, hleftClose] using h
  have hselectRight :
      (directory.selectCloseCosted shape (left + len - 1)).value =
        some rightClose := by
    have h := directory.selectCloseCosted_exact shape (left + len - 1)
    simpa [RMQ.Costed.erase, hrightClose] using h
  have hlca :
      (directory.lcaCloseCosted shape leftClose rightClose).value =
        some answerClose := by
    have h :=
      directory.lcaDirectory.lcaCloseCosted_exact hshape hlen hbound
        hleftClose hrightClose
    simpa [RMQ.Costed.erase, lcaCloseCosted, hanswerClose] using h
  have hrank :
      (directory.rankCloseCosted shape (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    have hrankExact :=
      directory.rankCloseCosted_exact shape (answerClose + 1)
    have hrankRecover :=
      SuccinctSpace.bpCloseOfInorder?_rankFalse_succ shape hanswerClose
    calc
      (directory.rankCloseCosted shape (answerClose + 1)).value =
          RMQ.Succinct.rankPrefix false shape.bpCode (answerClose + 1) := by
        simpa [RMQ.Costed.erase] using hrankExact
      _ = scanWindow shape.representative left len + 1 := hrankRecover
  have hselectLeftRaw :
      ((directory.selectData shape).selectCosted false left).value =
        some leftClose := by
    simpa [selectCloseCosted] using hselectLeft
  have hselectRightRaw :
      ((directory.selectData shape).selectCosted false (left + len - 1)).value =
        some rightClose := by
    simpa [selectCloseCosted] using hselectRight
  have hlcaRaw :
      (directory.lcaDirectory.lcaCloseCosted
          (directory.lcaDirectory.buildAux shape)
          leftClose rightClose).value =
        some answerClose := by
    simpa [lcaCloseCosted] using hlca
  have hrankRaw :
      ((directory.rankData shape).rankCosted false (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    simpa [rankCloseCosted] using hrank
  have hrankSub :
      scanWindow shape.representative left len + 1 - 1 =
        scanWindow shape.representative left len := by
    omega
  unfold queryBuiltCosted
  simp [selectCloseCosted, lcaCloseCosted, rankCloseCosted,
    RMQ.Costed.erase, RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
    hselectLeftRaw, hselectRightRaw, hlcaRaw, hrankRaw, hrankSub]

theorem profile
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost) :
    (forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (directory.payload shape).length =
          2 * n + directory.overhead) /\
      (forall shape left right,
        (directory.queryBuiltCosted shape left right).cost <=
          3 * queryCost + 1) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len : Nat},
            0 < len ->
              left + len <= n ->
                (directory.queryBuiltCosted shape left (left + len)).erase =
                  some (scanWindow shape.representative left len)) := by
  constructor
  · intro shape hshape
    simpa [overhead] using directory.payload_length hshape
  · constructor
    · intro shape left right
      exact directory.queryBuiltCosted_cost_le shape left right
    · intro shape hshape left len hlen hbound
      exact directory.queryBuiltCosted_exact hshape hlen hbound

end TwoLevelPayloadLiveBPCloseRMQNavigationDirectory

structure TwoLevelPayloadLiveBPCloseRMQNavigationFamily
    (rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat)
    (queryCost : Nat) where
  directory :
    forall n : Nat,
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory n
        (rankSuper n) (rankBlock n) (selectSuper n) (selectBlock n)
        (lca n) queryCost
  rankSuper_littleO : SuccinctSpace.LittleOLinear rankSuper
  rankBlock_littleO : SuccinctSpace.LittleOLinear rankBlock
  selectSuper_littleO : SuccinctSpace.LittleOLinear selectSuper
  selectBlock_littleO : SuccinctSpace.LittleOLinear selectBlock
  lca_littleO : SuccinctSpace.LittleOLinear lca

namespace TwoLevelPayloadLiveBPCloseRMQNavigationFamily

def overhead
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (_family :
      TwoLevelPayloadLiveBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    Nat -> Nat :=
  twoLevelBPCloseNavigationOverhead
    rankSuper rankBlock selectSuper selectBlock lca

theorem overhead_littleO
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    SuccinctSpace.LittleOLinear family.overhead := by
  exact
    twoLevelBPCloseNavigationOverhead_littleO
      family.rankSuper_littleO family.rankBlock_littleO
      family.selectSuper_littleO family.selectBlock_littleO
      family.lca_littleO

theorem two_n_plus_o_built_query_profile
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((family.directory n).payload shape).length =
              2 * n + family.overhead n) /\
        (forall shape left right,
          ((family.directory n).queryBuiltCosted shape left right).cost <=
            3 * queryCost + 1) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryBuiltCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  constructor
  · exact family.overhead_littleO
  · intro n
    constructor
    · have hbase :=
        EncodingLowerBound.canonicalRepresentativePayloadSpaceBounds_lower_le_upper n
      simp [overhead, twoLevelBPCloseNavigationOverhead,
        twoLevelRankSelectOverhead,
        SuccinctRankProposal.twoLevelRankOverhead,
        twoLevelSelectOverhead]
      omega
    · constructor
      · intro shape hshape
        simpa [overhead, twoLevelBPCloseNavigationOverhead,
          twoLevelRankSelectOverhead,
          SuccinctRankProposal.twoLevelRankOverhead,
          twoLevelSelectOverhead,
          TwoLevelPayloadLiveBPCloseRMQNavigationDirectory.overhead]
          using (family.directory n).payload_length hshape
      · constructor
        · intro shape left right
          exact (family.directory n).queryBuiltCosted_cost_le shape left right
        · intro shape hshape left len hlen hbound
          exact (family.directory n).queryBuiltCosted_exact
            hshape hlen hbound

end TwoLevelPayloadLiveBPCloseRMQNavigationFamily

structure TwoLevelEncodedBPCloseRMQNavigationView
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost) where
  selectCloseEncoded : List Bool -> Nat -> RMQ.Costed (Option Nat)
  lcaCloseEncoded : List Bool -> Nat -> Nat -> RMQ.Costed (Option Nat)
  rankCloseEncoded : List Bool -> Nat -> RMQ.Costed Nat
  select_cost_le :
    forall payload idx, (selectCloseEncoded payload idx).cost <= queryCost
  lca_cost_le :
    forall payload leftClose rightClose,
      (lcaCloseEncoded payload leftClose rightClose).cost <= 1
  rank_cost_le :
    forall payload pos, (rankCloseEncoded payload pos).cost <= queryCost
  select_agrees_on_built_payload :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall idx,
          selectCloseEncoded (directory.payload shape) idx =
            directory.selectCloseCosted shape idx
  lca_agrees_on_built_payload :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall leftClose rightClose,
          lcaCloseEncoded (directory.payload shape)
              leftClose rightClose =
            directory.lcaCloseCosted shape leftClose rightClose
  rank_agrees_on_built_payload :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall pos,
          rankCloseEncoded (directory.payload shape) pos =
            directory.rankCloseCosted shape pos

namespace TwoLevelEncodedBPCloseRMQNavigationView

def toBPCloseRMQNavigationDirectory
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    {directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost}
    (view : TwoLevelEncodedBPCloseRMQNavigationView directory) :
    SuccinctSpace.BPCloseRMQNavigationDirectory n
      ((rankSuper + rankBlock) + (selectSuper + selectBlock) +
        lcaOverhead)
      queryCost 1 queryCost where
  Aux := Cartesian.CartesianShape
  buildAux shape := shape
  encodeAux shape := directory.encodeAux shape
  selectCloseCosted := view.selectCloseEncoded
  lcaCloseCosted := view.lcaCloseEncoded
  rankCloseCosted := view.rankCloseEncoded
  aux_length_eq := by
    intro shape hshape
    exact directory.encodeAux_length hshape
  select_cost_le := by
    intro payload idx
    exact view.select_cost_le payload idx
  lca_cost_le := by
    intro payload leftClose rightClose
    exact view.lca_cost_le payload leftClose rightClose
  rank_cost_le := by
    intro payload pos
    exact view.rank_cost_le payload pos
  select_close_exact := by
    intro shape hshape idx hidx
    have hagree := view.select_agrees_on_built_payload hshape idx
    calc
      (view.selectCloseEncoded
          (shape.bpCode ++ directory.encodeAux shape) idx).erase =
          (directory.selectCloseCosted shape idx).erase := by
            simpa [TwoLevelPayloadLiveBPCloseRMQNavigationDirectory.payload]
              using congrArg RMQ.Costed.erase hagree
      _ = SuccinctSpace.bpCloseOfInorder? shape idx := by
            exact directory.selectCloseCosted_exact shape idx
  lca_close_exact := by
    intro shape hshape left len leftClose rightClose
      hlen hbound hleftClose hrightClose
    have hagree :=
      view.lca_agrees_on_built_payload hshape leftClose rightClose
    calc
      (view.lcaCloseEncoded
          (shape.bpCode ++ directory.encodeAux shape)
          leftClose rightClose).erase =
          (directory.lcaCloseCosted shape leftClose rightClose).erase := by
            simpa [TwoLevelPayloadLiveBPCloseRMQNavigationDirectory.payload]
              using congrArg RMQ.Costed.erase hagree
      _ = SuccinctSpace.bpCloseOfInorder? shape
            (scanWindow shape.representative left len) := by
            exact directory.lcaDirectory.lcaCloseCosted_exact
              hshape hlen hbound hleftClose hrightClose
  rank_close_exact := by
    intro shape hshape idx close hclose
    have hagree := view.rank_agrees_on_built_payload hshape (close + 1)
    calc
      (view.rankCloseEncoded
          (shape.bpCode ++ directory.encodeAux shape)
          (close + 1)).erase =
          (directory.rankCloseCosted shape (close + 1)).erase := by
            simpa [TwoLevelPayloadLiveBPCloseRMQNavigationDirectory.payload]
              using congrArg RMQ.Costed.erase hagree
      _ = RMQ.Succinct.rankPrefix false shape.bpCode (close + 1) := by
            exact directory.rankCloseCosted_exact shape (close + 1)

end TwoLevelEncodedBPCloseRMQNavigationView

structure TwoLevelEncodedBPCloseRMQNavigationFamily
    (rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat)
    (queryCost : Nat) where
  directory :
    forall n : Nat,
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory n
        (rankSuper n) (rankBlock n) (selectSuper n) (selectBlock n)
        (lca n) queryCost
  view :
    forall n : Nat,
      TwoLevelEncodedBPCloseRMQNavigationView (directory n)
  rankSuper_littleO : SuccinctSpace.LittleOLinear rankSuper
  rankBlock_littleO : SuccinctSpace.LittleOLinear rankBlock
  selectSuper_littleO : SuccinctSpace.LittleOLinear selectSuper
  selectBlock_littleO : SuccinctSpace.LittleOLinear selectBlock
  lca_littleO : SuccinctSpace.LittleOLinear lca

namespace TwoLevelEncodedBPCloseRMQNavigationFamily

def overhead
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (_family :
      TwoLevelEncodedBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    Nat -> Nat :=
  twoLevelBPCloseNavigationOverhead
    rankSuper rankBlock selectSuper selectBlock lca

def toBPCloseRMQNavigationFamily
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelEncodedBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    SuccinctSpace.BPCloseRMQNavigationFamily
      family.overhead queryCost 1 queryCost where
  directory n := (family.view n).toBPCloseRMQNavigationDirectory
  overhead_littleO :=
    twoLevelBPCloseNavigationOverhead_littleO
      family.rankSuper_littleO family.rankBlock_littleO
      family.selectSuper_littleO family.selectBlock_littleO
      family.lca_littleO

theorem overhead_littleO
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelEncodedBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    SuccinctSpace.LittleOLinear family.overhead := by
  exact family.toBPCloseRMQNavigationFamily.overhead_littleO

def Profile
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelEncodedBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) : Prop :=
  SuccinctSpace.LittleOLinear family.overhead /\
    forall n : Nat,
      EncodingLowerBound.logSlackLower n <= 2 * n + family.overhead n /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          ((((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).stateEncoding).payloadOf shape =
            shape.bpCode ++
              ((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).encodeAux
                (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).buildAux shape)) /\
          (((((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).stateEncoding).payloadView).payloadBitCount
            ((((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).stateEncoding).buildState shape) =
              2 * n + family.overhead n)) /\
      (forall
        (state : ((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).State)
        left right,
        (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).queryStateCosted
          state left right).cost <=
            2 * queryCost + 1 + queryCost) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len : Nat},
            0 < len ->
              left + len <= n ->
                (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).queryStateCosted
                  (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).buildState shape)
                  left (left + len)).erase =
                    some (scanWindow shape.representative left len))

theorem two_n_plus_o_encoded_query_profile
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelEncodedBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    family.Profile := by
  exact
    SuccinctSpace.BPCloseRMQNavigationFamily.two_n_plus_o_close_navigation_profile
      family.toBPCloseRMQNavigationFamily

end TwoLevelEncodedBPCloseRMQNavigationFamily

end SuccinctSelectProposal
end RMQ
